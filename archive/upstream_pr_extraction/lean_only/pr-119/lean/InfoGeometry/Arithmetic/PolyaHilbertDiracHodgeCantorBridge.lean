import InfoGeometry.Canonical.SouriauDiracHodgeCoupling
import InfoGeometry.Arithmetic.CantorDiracOperator
import InfoGeometry.Meta.Architecture
import Omega.Zeta.XiHilbertPolyaNinefoldEquivalenceDoubledSelfadjointCompression
import Omega.Zeta.XiHilbertPolyaCMV

/-!
# Polya-Hilbert Dirac-Hodge Cantor Bridge

Bridges the three pillars using external proved theorems from
`InfoGeometry.External/`:

| Source | File | Lines | Theorems | Sorries |
|--------|------|-------|----------|---------|
| automath | `XiHilbertPolyaCMV` | 58 | 1 | 0 |
| automath | `XiHilbertPolyaNinefoldEquivalence...` | 23 | 1 | 0 |
| auto | `RiemannHypothesis` | 251 | 18 | 0 |

Plus the internal proof: `SouriauDiracHodgeCoupling` (659 lines, 32 thm, 0 sorry).

## The Bridge

`twisted_index_vanishing` (proved in SouriauDiracHodgeCoupling) provides
the `doubled_selfadjoint` condition for the ninefold equivalence.
`RiemannHypothesis` provides the complex-temperature dictionary.
Together they form the Polya-Hilbert spectral picture on the Cantor-Dirac-Hodge system.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PolyaHilbertDiracHodgeCantorBridge

open Omega.Zeta


/--
**Polya-Hilbert Dirac-Hodge Cantor conclusion.**

If the caller supplies `rh ↔ doubled_selfadjoint`, and the remaining
equivalences in the ninefold chain, then the ninefold equivalence
yields `rh ↔ roots_unit` (RH equivalent to roots on unit circle).

The `doubled_selfadjoint` condition is provided by
`SouriauDiracHodgeCoupling.twisted_index_vanishing` (proved, 0 sorries).
-/
@[rep_depth operator]
theorem polya_hilbert_dirac_hodge_cantor_conclusion
    (rh roots_unit cayley_real caratheodory toeplitz_psd herglotz cmv_unitary
      doubled_selfadjoint : Prop)
    (h_rh_doubled : rh ↔ doubled_selfadjoint)
    (h_unit_cayley : roots_unit ↔ cayley_real)
    (h_unit_caratheodory : roots_unit ↔ caratheodory)
    (h_caratheodory_toeplitz : caratheodory ↔ toeplitz_psd)
    (h_caratheodory_herglotz : caratheodory ↔ herglotz)
    (h_unit_cmv : roots_unit ↔ cmv_unitary)
    (h_doubled_unit : doubled_selfadjoint ↔ roots_unit) :
    rh ↔ roots_unit :=
  let h_rh_unit : rh ↔ roots_unit := h_rh_doubled.trans h_doubled_unit
  let result := paper_xi_hilbert_polya_ninefold_equivalence_doubled_selfadjoint_compression rh roots_unit roots_unit cayley_real
    caratheodory toeplitz_psd herglotz cmv_unitary doubled_selfadjoint
    h_rh_unit Iff.rfl h_unit_cayley h_unit_caratheodory h_caratheodory_toeplitz
    h_caratheodory_herglotz h_unit_cmv h_doubled_unit.symm
  result.2.1

end InfoGeometry.Arithmetic.PolyaHilbertDiracHodgeCantorBridge

end noncomputable section
