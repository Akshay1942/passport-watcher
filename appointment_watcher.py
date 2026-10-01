#!/usr/bin/env python3
"""
CGI Hamburg appointment watcher.

Every 10 minutes: opens the appointment form, selects "Passport Services",
reads the selectable dates in "Appointment Date" and emails you immediately
if any date is EARLIER than your current appointment (default 16 Nov 2026).

It only NOTIFIES. Booking needs a captcha, so you finish the booking yourself.

Setup:
    pip install playwright
    playwright install chromium

Config via environment variables:
    SMTP_HOST      e.g. smtp.gmail.com
    SMTP_PORT      default 587 (STARTTLS)
    SMTP_USER      your SMTP login (for Gmail: your address)
    SMTP_PASSWORD  for Gmail: an "App Password" (not your normal password)
    EMAIL_TO       where alerts go (default: SMTP_USER)
    CURRENT_DATE   default 2026-11-16 (alert only for dates before this)
    INTERVAL_MIN   default 10

Usage:
    python appointment_watcher.py --test-email   # verify email works
    python appointment_watcher.py --once --debug # one visible run, saves debug files
    python appointment_watcher.py                # run forever, every 10 min
"""
import argparse
import json
import logging
import sys
import os
import re
import smtplib
import ssl
import time
from datetime import date, datetime
from email.message import EmailMessage

from playwright.sync_api import sync_playwright

URL = "https://www.cgihamburg.gov.in/get-appointment"
SERVICE_LABEL = "Passport Services"
CURRENT = date.fromisoformat(os.getenv("CURRENT_DATE", "2026-11-16"))
INTERVAL = int(os.getenv("INTERVAL_MIN", "10")) * 60
MAX_MONTHS_TO_SCAN = 4
FAILURES_BEFORE_WARNING = 6  # ~1 hour of consecutive errors

log = logging.getLogger("watcher")

STATE_FILE = os.getenv("STATE_FILE", "state.json")


def load_alerted() -> set:
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            return {date.fromisoformat(x) for x in json.load(f)}
    except Exception:
        return set()


def save_alerted(alerted: set) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(sorted(d.isoformat() for d in alerted), f)


# ----------------------------------------------------------------- email
def send_email(subject: str, body: str) -> None:
    user = os.environ["SMTP_USER"]
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = user
    msg["To"] = os.getenv("EMAIL_TO", user)
    msg.set_content(body)
    host, port = os.environ["SMTP_HOST"], int(os.getenv("SMTP_PORT", "587"))
    with smtplib.SMTP(host, port, timeout=30) as s:
        s.starttls(context=ssl.create_default_context())
        s.login(user, os.environ["SMTP_PASSWORD"])
        s.send_message(msg)
    log.info("Email sent: %s", subject)


# ------------------------------------------------------- date extraction
# Reads every day cell of the visible calendar(s) and classifies it.
# A day is AVAILABLE only if it is not disabled, not struck-through, not red.
JS_READ_CALENDAR = """
() => {
  const out = [];
  const isRed = (el) => {
    const m = getComputedStyle(el).color.match(/\\d+/g);
    return m && (+m[0] > +m[1] + 60) && (+m[0] > +m[2] + 60);
  };
  const struck = (el) => [el, ...el.querySelectorAll('*')].some(
      e => (getComputedStyle(e).textDecorationLine || '').includes('line-through'));

  // ---- jQuery UI datepicker (what cgihamburg.gov.in uses) ----
  document.querySelectorAll('.ui-datepicker-calendar td').forEach(td => {
    const txt = td.innerText.trim();
    if (!/^\\d+$/.test(txt)) return;                       // empty cell
    if (td.classList.contains('ui-datepicker-other-month')) return;
    const root = td.closest('.ui-datepicker');
    let y, m;
    const ys = root.querySelector('select.ui-datepicker-year');
    const ms = root.querySelector('select.ui-datepicker-month');
    if (ys && ms) { y = +ys.value; m = +ms.value + 1; }
    else {
      const t = Date.parse('1 ' + root.querySelector('.ui-datepicker-title').innerText);
      const d = new Date(t); y = d.getFullYear(); m = d.getMonth() + 1;
    }
    const inner = td.querySelector('a, span') || td;
    const cls = td.className + ' ' + inner.className;
    const disabled = /ui-state-disabled|ui-datepicker-unselectable/.test(cls)
                     || !td.hasAttribute('data-handler');
    const why = disabled ? 'disabled-class' : struck(td) ? 'strikethrough'
              : isRed(inner) ? 'red' : '';
    out.push({y, m, d: +txt, ok: !why, why});
  });

  // ---- flatpickr ----
  document.querySelectorAll('.flatpickr-day').forEach(el => {
    const c = el.classList;
    if (c.contains('prevMonthDay') || c.contains('nextMonthDay')) return;
    const t = Date.parse(el.getAttribute('aria-label')); if (isNaN(t)) return;
    const d = new Date(t);
    const bad = c.contains('flatpickr-disabled') || c.contains('notAllowed') || struck(el);
    out.push({y: d.getFullYear(), m: d.getMonth() + 1, d: d.getDate(), ok: !bad, why: bad ? 'disabled' : ''});
  });
  return out;
}
"""

NEXT_BUTTONS = (
    ".ui-datepicker-next:not(.ui-state-disabled), "
    ".flatpickr-next-month:not(.flatpickr-disabled)"
)

DATE_FIELD_JS = """
() => {
  const els = [...document.querySelectorAll('input, select')];
  const f = els.find(e => /date|appoint/i.test((e.name||'') + (e.id||'')) &&
                          !/birth|dob|time/i.test((e.name||'') + (e.id||'')));
  return f ? (f.id ? '#' + CSS.escape(f.id) : `[name="${f.name}"]`) : null;
}
"""

DATE_RE = [
    (re.compile(r"\b(\d{4})-(\d{2})-(\d{2})\b"), ("y", "m", "d")),
    (re.compile(r"\b(\d{2})[-/.](\d{2})[-/.](\d{4})\b"), ("d", "m", "y")),
]


def parse_dates(text: str) -> set:
    found = set()
    for rx, order in DATE_RE:
        for m in rx.finditer(text):
            parts = dict(zip(order, map(int, m.groups())))
            try:
                found.add(date(parts["y"], parts["m"], parts["d"]))
            except ValueError:
                pass
    return found


def collect_dates(page, _unused=None) -> set:
    """Return ONLY the dates that are really selectable in the calendar."""
    dates = set()
    field = page.evaluate(DATE_FIELD_JS)
    log.debug("Date field selector: %s", field)
    if not field:
        raise RuntimeError("Could not find the Appointment Date field")

    # Plain <select> of dates (fallback)
    if page.evaluate(f"document.querySelector('{field}').tagName") == "SELECT":
        for opt in page.locator(f"{field} option").all_text_contents():
            dates |= parse_dates(opt)
        return dates

    page.click(field)
    page.wait_for_timeout(600)
    for i in range(MAX_MONTHS_TO_SCAN):
        cells = page.evaluate(JS_READ_CALENDAR)
        if not cells:
            raise RuntimeError("Calendar opened but no day cells were found")
        ok = []
        today = date.today()
        for c in cells:
            try:
                d = date(c["y"], c["m"], c["d"])
            except ValueError:
                continue
            # Only care about: today <= d < CURRENT (earlier than current appointment)
            if not (today <= d < CURRENT):
                continue
            log.debug("  %s %s %s", d, "AVAILABLE" if c["ok"] else "x", c["why"])
            if c["ok"]:
                dates.add(d)
                ok.append(d.day)
        log.info("%02d/%d: available before %s -> %s",
                 cells[0]["m"], cells[0]["y"], f"{CURRENT:%d %b %Y}", ok or "none")
        # Stop once the visible month is already at/after the current appointment month
        if (cells[0]["y"], cells[0]["m"]) >= (CURRENT.year, CURRENT.month):
            break
        nxt = page.locator(NEXT_BUTTONS).first
        if not nxt.count():
            break
        nxt.click()
        page.wait_for_timeout(500)
    return dates


# ------------------------------------------------------------- one check
def check_once(pw, debug: bool) -> set:
    browser = pw.chromium.launch(headless=not debug)
    try:
        page = browser.new_page()
        page.set_default_timeout(30000)
        page.goto(URL, wait_until="networkidle")
        page.select_option("select >> nth=0", label=SERVICE_LABEL)
        page.wait_for_timeout(2500)  # let the date list load

        dates = collect_dates(page)
        if debug:
            page.screenshot(path="debug.png", full_page=True)
            open("debug.html", "w", encoding="utf-8").write(page.content())
            log.info("Saved debug.png / debug.html")
        return dates
    finally:
        browser.close()


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--debug", action="store_true", help="visible browser + save screenshot/HTML")
    ap.add_argument("--test-email", action="store_true")
    args = ap.parse_args()
    logging.basicConfig(level=logging.DEBUG if args.debug else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s")

    if args.test_email:
        send_email("Appointment watcher: test", "Email setup works.")
        return

    alerted, failures = load_alerted(), 0
    exit_code = 0
    with sync_playwright() as pw:
        while True:
            try:
                dates = check_once(pw, args.debug)
                failures = 0
                earlier = sorted(d for d in dates if date.today() <= d < CURRENT)
                if earlier:
                    log.info("EARLIER SLOTS FOUND: %s", ", ".join(f"{d:%d %b}" for d in earlier))
                else:
                    log.info("No slot earlier than %s", f"{CURRENT:%d %b %Y}")
                new = [d for d in earlier if d not in alerted]
                if new:
                    send_email(
                        f"EARLIER PASSPORT SLOT: {new[0]:%d %b %Y}",
                        "Earlier appointment date(s) available at CGI Hamburg "
                        f"(yours: {CURRENT:%d %b %Y}):\n\n"
                        + "\n".join(f"  - {d:%A, %d %B %Y}" for d in earlier)
                        + f"\n\nBook now: {URL}\n"
                        f"Checked at {datetime.now():%Y-%m-%d %H:%M:%S}",
                    )
                    alerted.update(new)
                    save_alerted(alerted)
            except Exception as e:
                failures += 1
                exit_code = 1
                log.error("Check failed (%d in a row): %s", failures, e)
                if failures == FAILURES_BEFORE_WARNING:
                    try:
                        send_email("Appointment watcher is failing",
                                   f"{failures} checks in a row failed.\nLast error: {e}\n"
                                   "The site layout may have changed.")
                    except Exception as mail_err:
                        log.error("Could not send warning email: %s", mail_err)
            if args.once:
                break
            time.sleep(INTERVAL)
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
