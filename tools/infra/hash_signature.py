#!/usr/bin/env python3
import hashlib
import re
import sys


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: python3 tools/infra/hash_signature.py '<type-signature>'")
        return 1

    signature = normalize_ws(sys.argv[1])
    print(hashlib.sha256(signature.encode("utf-8")).hexdigest())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
