import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.infra.run_locked_lake_build import main

if __name__ == "__main__":
    raise SystemExit(main())
