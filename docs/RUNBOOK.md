# The Rosetta Runbook
**Execution Guide for the Info-Geometry-Lean Synthesis**

This runbook outlines the exact procedure required to reproduce the 8400+ job Lean build, execute the SymPy physical witnesses, and ingest the external Betti certificates.

## Prerequisites
* **Lean 4 Toolchain**: `leanprover/lean4:v4.28.0` (managed via `elan`).
* **Python**: `3.10+` with `sympy`, `numpy`, and `scipy`.

## Phase 1: The Finite SymPy Witnesses
Before building the Lean theorem stack, we computationally verify the matrix symmetries of the topological phase transitions.

```bash
# 1. Verify Andreev Horizon Unitarity (Class DIII Symmetries)
python3 formalizations/andreev_horizon_witness.py

# 2. Verify Fibonacci MZM Fast Scrambling (F & R Matrix Unitarity)
python3 formalizations/mzm_braid_scrambling.py

# 3. Verify octonionic-horizon Cuntz/q-CCR scramble corridor
python3 octonionic_cuntz_scrambling.py
```
**Status Verification Definitions:**
* **Verified**: Script executes with `exit 0` and prints final `SUCCESS` flags. All numerical checks strictly close.
* **Timed/Fallback**: Execution exceeds bounds or returns `AssertionError`. This means the topological phase matrix has decayed or misaligned parameters.

## Phase 2: Evidence Artifacts & Betti Ingestion
The structural rank of the horizon is supplied by a pre-computed Betti certificate.

### Artifact Schema Example (`betti_certificate.json`)
```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Betti Configuration Certificate",
  "type": "object",
  "properties": {
    "dim_ambient": { "type": "integer", "const": 8 },
    "is_verified": { "type": "boolean", "const": true },
    "total_rank": { "type": "integer", "const": 8 },
    "target_geometry": { "type": "integer", "const": 32 }
  },
  "required": ["dim_ambient", "is_verified", "total_rank", "target_geometry"]
}
```

```bash
# Verify the ingestion payload parses successfully
cat schemas/betti_certificate.json | jq .
```
The Lean module `NonIsoConf3RankIngestion` connects to this socket to formally extract the Rank 32 constraint.

## Phase 3: The Lean 4 DAG Build

```bash
# Build the master synthesis module
lake build InfoGeometry.Projective.All
```

### Critical Verified Theorems for Citations:
1. `InfoGeometry.Projective.AndreevHorizonUnitarity.finite_andreev_packet`
2. `InfoGeometry.Projective.KasparovKreinDIIIBridge.klein_bottle_trace_absorption`
3. `InfoGeometry.Projective.KasparovKreinDIIIBridge.d3_particle_hole_symmetry`
4. `InfoGeometry.Projective.HorizonInformationScrambling.black_hole_fast_scrambling`
5. `InfoGeometry.Projective.NonIsoConf3RankIngestion.discharge_rank_decision`

**Expected Outcome**: 
The build engine (`lake`) evaluates exactly **8442 jobs** with zero active `sorry`, `admit`, or `axiom` backdoors in the active projective stack.

## Phase 4: Validating Artifact Purity
The codebase incorporates a strict semantic quarantine. Run the final DAG audit to ensure no false axioms leaked into the DIII synthesis:
```bash
python3 tools/infra/check_sorry.py --module InfoGeometry.Projective.All
```
*Zero unverified closure debts should remain in the active projective stack.*
