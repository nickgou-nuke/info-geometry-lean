import os
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO_ROOT / "lean"

def honest_rewrite():
    # Regexes to find structural obfuscation and replace with sorry
    replacements = [
        # Replace `:= Nonempty ...` with `:= sorry` when it's assigned to a Prop
        (re.compile(r':=\s*Nonempty\s+.*$', re.MULTILINE), ':= sorry'),
        # Replace `exact ⟨fun _ => 0⟩` with `exact sorry`
        (re.compile(r'exact\s+⟨fun\s+_\s*=>\s*0⟩'), 'exact sorry'),
        # Replace `exact ⟨0, rfl⟩` with `exact sorry`
        (re.compile(r'exact\s+⟨0,\s*rfl⟩'), 'exact sorry'),
    ]

    count = 0
    for root, _, files in os.walk(LEAN_DIR):
        for file in files:
            if not file.endswith(".lean"):
                continue
            path = Path(root) / file
            if not path.is_file():
                continue
            try:
                text = path.read_text(encoding="utf-8")
            except OSError:
                continue
            original = text
            for pattern, replacement in replacements:
                text = pattern.sub(replacement, text)
            if text != original:
                path.write_text(text, encoding="utf-8")
                count += 1
                print(f"Rewrote dishonest debt in {path.relative_to(REPO_ROOT)}")

    print(f"Total files rewritten: {count}")

if __name__ == "__main__":
    honest_rewrite()
