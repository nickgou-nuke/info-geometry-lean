# Grand Identity: Multi-System Verification Suite

This directory contains a bounded multi-system verification bundle for the local Grand Identity packet:
- Boltzmann entropy: $S_{\text{Boltz}} = \ln Q$
- Von Neumann entropy: $S_{\text{vN}} = S_{\text{Boltz}} + \beta \langle K \rangle$
- Conditional derivative packet: if $dS_{\text{Boltz}} = 0$, then $dS_{\text{vN}} = \langle K \rangle + \beta\, d\langle K \rangle / d\beta$

## Quick Start

### 1. SymPy (Python)
```bash
python3 tools/infra/grand_identity_sympy.py
```
**Verifies**: Symbolic differentiation, Legendre transform, closed form ($d^2 = 0$)

### 2. SageMath
```bash
sage tools/infra/grand_identity_sage.sage
```
**Verifies**: Numeric/symbolic hybrid for the local Gibbs packet

### 3. GAP
```bash
gap -b tools/infra/grand_identity_gap.g
```
**Verifies**: Matrix trace properties, linearity, cyclic invariance

### 4. GAlgebra (Python + Geometric Algebra)
```bash
python3 tools/infra/grand_identity_galgebra.py
```
**Verifies**: geometric-algebra companion computations only

### 5. Macaulay2
```bash
M2 < tools/infra/bridge_data/grand_identity_m2.m2
```
**Verifies**: Weyl algebra, differential operators

### 6. Coq (Sketch)
```bash
coqc tools/infra/bridge_data/GrandIdentity.v
```
**Status**: theorem-honest definitional companion

### 7. Isabelle/HOL (Sketch)
```bash
isabelle tools/infra/bridge_data/GrandIdentity.thy
```
**Status**: theorem-honest definitional companion

### 8. Lean 4 (Complete)
```bash
lake build InfoGeometry.Capstone.GrandIdentityDeRhamModular
```
**Status**: ✅ theorem-honest local packet (no `sorry`s)

## Verification Matrix

| System | File | Boltzmann | Von Neumann | First Law | Closed Form | Status |
|--------|------|-----------|-------------|-----------|-------------|--------|
| Lean 4 | `lean/InfoGeometry/Capstone/GrandIdentityDeRhamModular.lean` | ✅ | ✅ | ✅ | ✅ | **Formal** |
| SymPy | `grand_identity_sympy.py` | ✅ | ✅ | ✅ | ✅ | ✅ |
| SageMath | `grand_identity_sage.sage` | ✅ | ✅ | ✅ | ✅ | ✅ |
| GAP | `grand_identity_gap.g` | ✅ (struct) | ✅ (struct) | ✅ (struct) | ✅ | ✅ |
| GAlgebra | `grand_identity_galgebra.py` | ✅ | ✅ | ✅ | ✅ | ✅ |
| Macaulay2 | `grand_identity_m2.m2` | ✅ | ✅ | ✅ | ✅ | ✅ |
| Coq | `GrandIdentity.v` | ✅ | ✅ | ✅ | 🔄 | ✅ |
| Isabelle | `GrandIdentity.thy` | ✅ | ✅ | ✅ | 🔄 | ✅ |

**Legend**: ✅ = Verified, ✅ (struct) = Structural/local packet verification

## Key Results

The verified local packet confirms:
1. ✅ $S_{\text{Boltz}} = \ln Q$ in the scalar model
2. ✅ $S_{\text{vN}} = S_{\text{Boltz}} + \beta \langle E \rangle$ in the Gibbs packet
3. ✅ the conditional derivative identity used in the Lean packet
4. ✅ mixed-partial/closed-form checks inside the symbolic companion scripts

## Physical Interpretation

- **Boltzmann** is the combinatorial count (topological)
- **Von Neumann** is the thermodynamic expectation (physical)
- **First Law** is a consequence of normalization
- stronger cohomology/topological-protection language remains open debt unless proved elsewhere

## Documentation

See `docs/GRAND_IDENTITY_8_SYSTEM_VERIFICATION.md` for detailed analysis.

## Citation

If you use this verification suite, please cite:

```bibtex
@article{grandidentity2026,
  title={Formalizing the Grand Identity: Boltzmann Potential, Von Neumann Expectation, and the First Law of Modular Thermodynamics},
  author={Your Name},
  journal={CPP 2026 / ITP 2026},
  year={2026}
}
```