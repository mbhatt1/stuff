#!/usr/bin/env python3
"""
Love Notes at Weird Hours
Sends sweet notifications at the oddest times of day.
"""

import random
import subprocess
import time
from datetime import datetime, timedelta

MESSAGES = [
    "Your laugh is my favorite sound in any universe",
    "I still get butterflies when you walk into the room",
    "You make even grocery shopping feel like an adventure",
    "The way you scrunch your nose when you laugh... perfect",
    "I'd choose you in every timeline, every multiverse",
    "You're the reason I smile at my phone like a weirdo",
    "My favorite place in the world is next to you",
    "You make my brain go brrr in the best way",
    "I love how you pretend to be annoyed but smile anyway",
    "You're the plot twist I never saw coming but always needed",
    "Even my autocorrect knows your name by now",
    "You're proof that the universe has good taste",
    "I love how you steal my hoodies and act innocent",
    "Thinking about you right now. That's it. That's the note.",
    "You make 'doing nothing together' the best plan ever",
    "Your existence makes the world objectively better",
    "I love how passionate you get about things you care about",
    "You're the human equivalent of a perfectly ripe avocado",
    "I wrote you a message at a weird hour because you deserve chaos and love",
    "Fun fact: you're incredible. This has been a public service announcement.",
    "I love how you always know when I need a hug",
    "You're my favorite notification",
    "The way you care about people is genuinely beautiful",
    "I'd sit through any bad movie just to be next to you",
    "You turned my life from grayscale to 4K HDR",
]

# Weird times: the minutes/hours nobody expects a love note
WEIRD_HOURS = [
    (3, 14),   # 3:14 AM - pi o'clock
    (4, 44),   # 4:44 AM - angel numbers but make it unhinged
    (2, 22),   # 2:22 AM - triple twos
    (5, 7),    # 5:07 AM - prime time (literally)
    (11, 11),  # 11:11 AM - make a wish
    (13, 37),  # 1:37 PM - leet o'clock
    (15, 15),  # 3:15 PM - the post-lunch void
    (17, 38),  # 5:38 PM - oddly specific
    (20, 20),  # 8:20 PM - double 20
    (22, 22),  # 10:22 PM - palindrome vibes
    (23, 58),  # 11:58 PM - almost midnight but not quite
    (0, 1),    # 12:01 AM - brand new day, same love
    (1, 11),   # 1:11 AM - insomniac love
    (6, 9),    # 6:09 AM - nice
    (16, 4),   # 4:04 PM - love not found... jk here it is
    (19, 19),  # 7:19 PM - prime dinner hour
    (21, 21),  # 9:21 PM - counting down to bedtime
]


def send_notification(title: str, message: str):
    """Send a macOS notification."""
    script = f'display notification "{message}" with title "{title}" sound name "Crystal"'
    subprocess.run(["osascript", "-e", script], check=True)


def pick_todays_weird_times(count=3):
    """Pick a few random weird times for today."""
    now = datetime.now()
    times = []
    candidates = random.sample(WEIRD_HOURS, min(count, len(WEIRD_HOURS)))
    for hour, minute in candidates:
        t = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
        if t <= now:
            t += timedelta(days=1)
        times.append(t)
    return sorted(times)


def run():
    print("--- Love Notes at Weird Hours ---")
    print(f"Started at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    used_messages = []

    while True:
        schedule = pick_todays_weird_times(count=random.randint(2, 5))
        print(f"Today's weird times:")
        for t in schedule:
            print(f"  {t.strftime('%I:%M %p')} - a love note awaits...")
        print()

        for target_time in schedule:
            now = datetime.now()
            if target_time <= now:
                continue

            wait_seconds = (target_time - now).total_seconds()
            print(f"Next note at {target_time.strftime('%I:%M %p')} "
                  f"(in {wait_seconds/60:.0f} min)")
            time.sleep(wait_seconds)

            # Pick a message we haven't used recently
            available = [m for m in MESSAGES if m not in used_messages]
            if not available:
                used_messages.clear()
                available = MESSAGES
            msg = random.choice(available)
            used_messages.append(msg)

            titles = [
                "hey you",
                "psst",
                "a weird hour love note",
                "notification from your biggest fan",
                "important announcement",
                "breaking news",
                "this just in",
            ]

            send_notification(random.choice(titles), msg)
            print(f"  Sent at {datetime.now().strftime('%I:%M %p')}: {msg}")

        # Sleep until midnight + a bit, then pick new times
        tomorrow = (datetime.now() + timedelta(days=1)).replace(
            hour=0, minute=0, second=5, microsecond=0
        )
        wait = (tomorrow - datetime.now()).total_seconds()
        if wait > 0:
            print(f"\nAll done for today. Picking new weird times after midnight...")
            time.sleep(wait)


if __name__ == "__main__":
    run()
