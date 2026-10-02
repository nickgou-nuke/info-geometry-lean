# WARNING: NEVER RUN LAKE EXE CACHE GET OR CLEAN

This repository is heavily customized and strictly pinned to v4.28.1.
Mathlib caches for v4.28.1 DO NOT EXIST on Azure.
If you run `lake exe cache get` or `lake clean`, it will permanently wipe out the locally compiled `.olean` files that took hours to build, and it will fail to replace them because they do not exist online.

UNDER NO CIRCUMSTANCES should any agent, script, or user run `lake exe cache get` or `lake clean` here.

If the cache is broken, the ONLY valid recovery method is native local compilation from source via `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock -- -R`.
