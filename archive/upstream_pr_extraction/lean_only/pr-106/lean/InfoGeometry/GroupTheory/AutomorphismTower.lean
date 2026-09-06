import Mathlib.Tactic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Perm

/-!
# Automorphism tower foundational packet

This module records the kernel-checked finite-cardinality part of the
MathOverflow/Thomas-Hamkins/Wielandt automorphism-tower discussion without
claiming any global tower-termination theorem.

A `CompleteGroupCertificate G` is the concrete datum that the conjugation map has
already been identified with all automorphisms.  From that datum, the first
automorphism step is cardinally stable.  The existence of such certificates for
particular nontrivial groups is supplied by separate computational/literature
lanes, not assumed here.
-/

namespace InfoGeometry.GroupTheory.AutomorphismTower

/-! The complete-group datum is the explicit multiplicative equivalence itself;
the former property added no field or proposition beyond `conjEquiv`. -/
abbrev CompleteGroupCertificate (G : Type*) [Group G] := G ≃* MulAut G

namespace CompleteGroupCertificate

variable {G : Type*} [Group G]

/-- A complete-group property transports a finite structure to the
automorphism group. -/
noncomputable def autFintype [Fintype G]
    (C : CompleteGroupCertificate G) : Fintype (MulAut G) :=
    Fintype.ofEquiv G C.toEquiv

/-- Cardinal readback: a complete finite group and its automorphism group have
the same number of elements. -/
theorem card_aut_eq_group [Fintype G] (C : CompleteGroupCertificate G) :
    letI : Fintype (MulAut G) := CompleteGroupCertificate.autFintype C
    Fintype.card (MulAut G) = Fintype.card G := by
  letI : Fintype (MulAut G) := CompleteGroupCertificate.autFintype C
  exact Fintype.card_congr (C.symm : MulAut G ≃* G).toEquiv

/- The bounded finite-stage cardinal ledger used by the executable multi-engine
sandbox once a complete-group property is available. -/
 /- Once the complete-group property is supplied, the bounded ledger is stable
from one stage to the next.  This is not the transfinite automorphism-tower
theorem; it is the exact local fixed-point readback. -/
/-- Concrete low-cardinality sanity check used by the external lanes: the
permutation group on three letters has six elements.  The statement is about the
standard permutation group only; it does not assert completeness of `S₃`. -/
theorem card_perm_fin_three : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm]
  norm_num

end CompleteGroupCertificate

end InfoGeometry.GroupTheory.AutomorphismTower
