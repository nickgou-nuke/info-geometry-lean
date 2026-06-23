# AQL Functorial Bridge: Hestenes-Krein Bivector Mapping

## Overview

This module implements the **functorial bridge** between discrete combinatorial limits and continuous geometric limits in the info-geometry-lean framework.

**Mathematical Statement:**
```
F: Discrete → Continuous
```

where:
- **Discrete**: p-adic valuations, Mersenne primes, golden ratio powers (from `CantorianFractalSpacetime.lean`)
- **Continuous**: Clifford algebras, Krein spaces, Hestenes rotors (from `HestenesKreinModularGeometry.lean`, `FiveGradedCentralizer.lean`)

## Files

```
tools/infra/aql/
├── aql_functorial_bridge.py        # Python CLI for bridge execution
├── functorial_bridge_mapping.aql   # AQL query templates
└── README_functorial_bridge.md     # This file
```

## Mathematical Foundation

### 1. Object Mapping

| Discrete Structure | Continuous Structure | Mapping Formula |
|-------------------|---------------------|-----------------|
| Mersenne prime M_p = 2^p - 1 | Clifford algebra Cl(p,p) | M_p ↦ Cl(p,p) |
| p-adic valuation v_p(n) | Krein signature (p+, q-) | v₂(137) = 0 ↦ trace(S) = 0 |
| Golden power τ^n | Hestenes rotor R(θ) | τ^n ↦ e^{-nφ·I/2} |

### 2. Morphism Preservation

**Fibonacci Recurrence → Rotor Composition:**
```
Discrete:  F_{n+2} = F_{n+1} + F_n
Continuous: R(θ₁) ∘ R(θ₂) = R(θ₁ + θ₂)
```

**Trace-Zero Anomaly Cancellation:**
```
Discrete:  v₂(137) = 0 (137 is odd)
Continuous: trace(moebiusParity) = 0 (Möbius parity is traceless)
```

### 3. Key Invariants

**Fine Structure Constant:**
- Discrete: 137 = M₂ + M₃ + M₇ = 3 + 7 + 127
- Discrete: v₂(137) = 0 (2-adic stability)
- Continuous: dim(Spin(5,5)) = 45 (conjectural correspondence)
- Continuous: trace(S) = 0 (Gromov-Witten anomaly cancellation)

## Usage

### Prerequisites

1. **ArangoDB running locally or remotely**
   ```bash
   # Install ArangoDB (Ubuntu/Debian)
   wget -neO - https://download.arangodb.com/arangodb39/KEY.gpg | sudo apt-key add -
   echo 'deb https://download.arangodb.com/arangodb39/stable/ /' | sudo tee /etc/apt/sources.list.d/arangodb.list
   sudo apt-get update && sudo apt-get install arangodb39
   ```

2. **Python arango library**
   ```bash
   source .venv  # or .venv-123
   pip install python-arango
   ```

### CLI Commands

**Full bridge execution (populate + map + summary):**
```bash
cd /home/goutev/repos/info-geometry-lean
python3 tools/infra/aql/aql_functorial_bridge.py --full-bridge
```

**Individual operations:**
```bash
# Populate discrete data (Mersenne primes, p-adic valuations, golden powers)
python3 tools/infra/aql/aql_functorial_bridge.py --populate-discrete

# Populate continuous data (Clifford algebras, Krein spaces, Hestenes rotors)
python3 tools/infra/aql/aql_functorial_bridge.py --populate-continuous

# Run functorial mapping queries
python3 tools/infra/aql/aql_functorial_bridge.py --run-mappings

# Print database summary
python3 tools/infra/aql/aql_functorial_bridge.py --summary

# Print AQL query templates
python3 tools/infra/aql/aql_functorial_bridge.py --print-aql
```

**Custom ArangoDB connection:**
```bash
python3 tools/infra/aql/aql_functorial_bridge.py \
  --arangodb-url http://localhost:8530 \
  --username root \
  --password mypassword \
  --database infogeometry \
  --full-bridge
```

## Database Schema

### Collections (Discrete)

**mersenne_primes:**
```json
{
  "p": 7,
  "value": 127,
  "is_prime": true
}
```

**padic_valuations:**
```json
{
  "prime": 2,
  "n": 137,
  "valuation": 0
}
```

**golden_powers:**
```json
{
  "n": 4,
  "tau_n": 6.8541,
  "fib_n": 3,
  "fib_n_plus_1": 5
}
```

### Collections (Continuous)

**clifford_algebras:**
```json
{
  "p": 5,
  "q": 5,
  "dimension": 1024,
  "bivector_dimension": 45,
  "spin_group_dim": 45
}
```

**krein_spaces:**
```json
{
  "signature_p": 5,
  "signature_q": 3,
  "fundamental_symmetry": "J_(5,3)",
  "indefinite_form": "⟨u,v⟩_J = u^T η v where η = diag(+++++---)"
}
```

**hestenes_rotors:**
```json
{
  "n": 3,
  "angle": 1.8541,
  "bivector": "I = γ₂γ₁ (spacetime bivector)",
  "rotor_expr": "e^(-1.8541·I/2)"
}
```

### Edge Collection

**functorial_mappings:**
```json
{
  "_from": "mersenne_primes/7",
  "_to": "clifford_algebras/77627",
  "mapping_id": "mersenne_to_clifford_7",
  "discrete_type": "MersennePrime",
  "continuous_type": "CliffordAlgebra",
  "discrete_key": "M_7",
  "continuous_key": "Cl(7,7)",
  "mapping_type": "mersenne_to_clifford",
  "mapping_formula": "M_7 = 127 ↦ Cl(7,7)",
  "preserved_structure": ["dimension", "Z2_grading", "center", "spin_group"],
  "mathematical_justification": "Bott periodicity: Cl(p,p) has real dimension 2^(2p)...",
  "physical_interpretation": "Mersenne prime exponent determines Clifford signature..."
}
```

## Example Output

```
======================================================================
EXECUTING FULL FUNCTORIAL BRIDGE
======================================================================

=== Inserting Mersenne primes ===
  ✓ M_2 = 3
  ✓ M_3 = 7
  ✓ M_5 = 31
  ✓ M_7 = 127

=== Inserting p-adic valuations ===
  ✓ v₂(137) = 0

=== Inserting golden powers ===
  ✓ τ^1 ≈ 1.6180 (F_1 = 1)
  ✓ τ^2 ≈ 2.6180 (F_2 = 1)
  ✓ τ^3 ≈ 4.2360 (F_3 = 2)
  ...

=== Inserting Clifford algebras ===
  ✓ Cl(2,2) dim=16, bivector_dim=6
  ✓ Cl(3,3) dim=64, bivector_dim=15
  ✓ Cl(5,5) dim=1024, bivector_dim=45
  ✓ Cl(7,7) dim=16384, bivector_dim=91

=== Inserting Krein spaces ===
  ✓ Krein(2,0)
  ✓ Krein(3,0)
  ✓ Krein(5,3)
  ✓ Krein(7,2)

=== Inserting Hestenes rotors ===
  ✓ R(1φ) = e^(-0.6180·I/2)
  ✓ R(2φ) = e^(-1.2361·I/2)
  ...

=== Running Mersenne → Clifford mapping ===
  ✓ Created 4 Clifford mappings

=== Running Mersenne → Krein mapping ===
  ✓ Created 4 Krein mappings

=== Running Golden → Rotor mapping ===
  ✓ Created 9 Rotor mappings

=== Running p-adic → Anomaly resolution mapping ===
  ✓ Created 1 anomaly resolution mappings

======================================================================
FUNCTORIAL BRIDGE SUMMARY
======================================================================
Mersenne Primes (Discrete)              :   4
p-adic Valuations (Discrete)            :   1
Golden Powers (Discrete)                :   9
Clifford Algebras (Continuous)          :   4
Krein Spaces (Continuous)               :   4
Hestenes Rotors (Continuous)            :   9
Functorial Mappings                     :  18
Anomaly Resolutions                     :   1

=== Functorial Mappings Detail ===
  1. M_2 → Cl(2,2)
     Formula: M_2 ↦ Cl(2,2)
  2. M_3 → Cl(3,3)
     Formula: M_3 ↦ Cl(3,3)
  ...
```

## Theoretical Context

### Connection to Hestenes-Krein Geometry

The functorial bridge realizes the mathematical insight that:

1. **Bivectors as Complex Structure**: The almost complex structure `S : V → V` with `S² = -I` in `FiveGradedCentralizer.lean` is geometrically realized as right-multiplication by a unit bivector `I` in the Clifford algebra:
   ```
   S(v) = vI
   (a + bi)·v = a·v + b·S(v)  ↔  z·v = (a + bI)v
   ```

2. **Trace-Zero as Bivector Purity**: In geometric algebra, the trace of an operator corresponds to the scalar part `⟨M⟩₀`. For a pure bivector `I`:
   ```
   ⟨I⟩₀ = 0  ↔  trace(S) = 0
   ```
   This is the anomaly cancellation mechanism: the Möbius parity operator has no scalar (dilational) component, only rotational.

3. **Krein Adjoint and Causality**: The fundamental symmetry `J` in the Krein space corresponds to the timelike vector `γ₀` in spacetime algebra. For spatial bivectors:
   ```
   I† = -I  (anti-Hermitian under Clifford reversal)
   U(θ) = e^{-θI/2} is Krein-unitary
   ```
   This ensures Lorentz transformations preserve the light cone structure.

### Next Steps

1. **Integrate with SageMath/Macaulay2**: Extend the pipeline to consume computational output from the discrete side (p-adic valuations, zeta function zeros, etc.)

2. **Lean Verification**: Import the mapped continuous structures into Lean and verify they satisfy the axioms in `HestenesKreinModularGeometry.lean`.

3. **Anomaly Resolution Proofs**: Formalize the correspondence `v₂(137) = 0 ↔ trace(S) = 0` as a theorem relating arithmetic and geometric anomaly cancellation.

## Testing

### Idempotency Regression Test

The bridge includes a regression test that verifies repeated runs do not accumulate duplicate mapping edges:

```bash
# Run with automatic scratch database (preferred)
python3 tools/infra/aql/test_bridge_idempotency.py

# Fallback to shared database if scratch DB creation fails
python3 tools/infra/aql/test_bridge_idempotency.py --allow-shared-db-fallback

# Custom database
python3 tools/infra/aql/test_bridge_idempotency.py --database my_test_db
```

**What the test does:**
1. Creates a scratch database (or uses configured DB with fallback flag)
2. Runs `--full-bridge` twice
3. Parses `--summary` output after each run
4. Asserts all collection counts remain unchanged
5. Drops the scratch database on completion

**Expected output:**
```
======================================================================
✓ IDEMPOTENCY TEST PASSED
  All summary counts remained stable across two runs.
======================================================================
```

The test exercises the same CLI path as manual usage, ensuring the UPSERT-based idempotency verified in development holds in CI/regression runs.

## References

- `CantorianFractalSpacetime.lean`: Discrete structures
- `HestenesKreinModularGeometry.lean`: Continuous Krein geometry
- `FiveGradedCentralizer.lean`: Complex module construction
- Hestenes, D. (1966). *Spacetime Algebra*
- Castro, C. (2002). *Cantorian-Fractal Spacetime and Fractal Strings* (hep-th/0203086)