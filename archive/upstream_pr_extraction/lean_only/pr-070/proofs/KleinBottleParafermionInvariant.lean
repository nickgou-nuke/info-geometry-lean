import Mathlib

noncomputable section

namespace InfoGeometry.Quantum.KleinBottleParafermionInvariant

/--
Axiom-free finite-order obstruction extracted from the Klein bottle cross-cap logic:
if a holonomy `w` is invariant under conjugation by `ε`,
and the cross-cap action sends it to `w⁻¹`, then it must satisfy `w^2 = 1`.
This algebraic core captures the physical constraint `W(γ)=W(γ)^{-1}`.
-/
theorem crossCap_invariant_implies_torsion_two {G : Type*} [Group G]
    (ε w : G)
    (h_invariant : w = ε * w * ε⁻¹)
    (h_inverted : ε * w * ε⁻¹ = w⁻¹) :
    w ^ 2 = 1 := by
  have hw : w = w⁻¹ := by
    calc
      w = ε * w * ε⁻¹ := h_invariant
      _ = w⁻¹ := h_inverted
  have hmul : w * w = w * w⁻¹ := by
    exact congrArg (fun x => w * x) hw
  calc
    w ^ 2 = w * w := by rw [pow_two]
    _ = w * w⁻¹ := hmul
    _ = 1 := by simpa using mul_inv_cancel w


end InfoGeometry.Quantum.KleinBottleParafermionInvariant