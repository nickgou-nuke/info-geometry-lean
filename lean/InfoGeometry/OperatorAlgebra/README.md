# Operator Algebra Bridges: Status & Memory

This directory contains the formal bridges between the Info-Geometry abstract theory and external rigorous implementations.

## Bridge Status Registry

| Module | Status | Certified | Mandate IX | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `VirasoroProjectBridge` | **CERTIFIED** | 2026-05-09 | VERIFIED | Bridge to `kkytola/VirasoroProject`. |
| `AffineVirasoroBridge` | **STABLE** | N/A | N/A | Abstract  interface definitions. |

## Key Learnings (Memorized)

### 1. Virasoro Scaling Identity
When bridging `VirasoroDatum` (abstract) to `VirasoroAlgebra` (concrete), a scaling mismatch often occurs due to the distribution of scalar multiplication over the central term's `if-then-else` structure.
- **Fix**: Use `rw [← smul_ite_zero]` or `simp only [smul_ite, smul_zero]`.
- **Reason**: The scalar multiplication must be pushed inside the `ite` to match the implementation's bracket law.

### 2. Mandate IX Compliance
To satisfy Mandate IX (Genuine Witness Dependency), avoid hollow existential proofs like `∃ D, True`.
- **Pattern**: Define a `Realizes` predicate that constrains the witness to the concrete implementation generators, then prove `∃ D, Realizes D`.

### 3. Heisenberg Case
The `heisenbergSugawaraDatum` provides a reference calibration for the $c=1$ case (single boson, abelian affine algebra).

> [!IMPORTANT]
> All bridges in this directory must pass `lake build` and have zero `sorryAx` before being marked as **CERTIFIED**.
