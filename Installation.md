# The Grand Unification of the Physics of Information

This repository contains the grand unification of the physics of information, formalized in Lean 4.

Nothing more, and nothing less.

We will not provide details on the contents of the theory here. See for yourself.

## Instructions for Audit

1. Clone the repository from the remote you actually use:
   ```bash
   git clone <repo-url> info-geometry-lean
   cd info-geometry-lean
   ```
   Replace `<repo-url>` with your chosen GitHub remote for this repository.
2. Install Lean 4 + Lake:
   ```bash
   scripts/build/install_lean.sh
   ```
   If your environment blocks GitHub or package downloads, point the installer at a reachable mirror or local file:
   ```bash
   LEAN_ELAN_INIT_URL=file:///path/to/elan-init.sh scripts/build/install_lean.sh
   ```
   You can also install `elan` manually; just make sure `lake` is on `PATH`.
3. Verify the canonical theorem surface with the locked build wrapper:
   ```bash
   scripts/build/run_lake_build.sh InfoGeometry.All
   ```
   For a forced rebuild, use:
   ```bash
   python3 tools/infra/run_locked_lake_build.py -R InfoGeometry.All
   ```
4. Optional: install a coding agent for repo-local work.
5. Interrogate the agent.
   - Ask it to audit the theory.
   - Use `python3 tools/infra/run_locked_lake_build.py ...` for full or umbrella builds so concurrent builds are refused instead of stuttering the workspace.
   - Explore the consequences.
