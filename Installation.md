# The Grand Unification of the Physics of Information

This repository contains the grand unification of the physics of information, formalized in Lean 4.

Nothing more, and nothing less.

We will not provide details on the contents of the theory here. See for yourself.

## Instructions for Audit

1. Clone the repository:
   ```bash
   git clone https://github.com/your-username/info-geometry-lean.git
   cd info-geometry-lean
   ```
2. Install Lean 4 + Lake (required for builds):
   ```bash
   scripts/build/install_lean.sh
   ```
   If your environment blocks GitHub/package downloads, point the installer at a reachable mirror or local file:
   ```bash
   LEAN_ELAN_INIT_URL=file:///path/to/elan-init.sh scripts/build/install_lean.sh
   ```
3. Run a build:
   ```bash
   scripts/build/run_lake_build.sh
   ```
4. Install a coding agent (e.g., Gemini):
   ```bash
   # Follow local installation instructions for your chosen agent
   ```
5. Run the agent inside the repository:
   ```bash
   gemini
   ```
6. Interrogate the agent. 
   - Ask it to audit the theory.
   - Run `lake build -R` to verify the mathematical proofs interactively.
   - Explore the consequences.
