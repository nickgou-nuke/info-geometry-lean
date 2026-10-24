/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.BosonMajoranaFermionTransmutation
import InfoGeometry.Core.AnticommutingSum
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Native universal-algebra representations of Jordan–Wigner generators

The same-parity fermions lift to `ExteriorAlgebra`; the split Majoranas lift to
`CliffordAlgebra` of the native weighted sum-of-squares form. These are actual
`AlgHom`s, with basis-generator evaluation, uniqueness, and naturality proved.
No faithfulness, surjectivity onto the ambient algebra, or inverse of two is
assumed or asserted. For an arbitrary ring, take the coefficient ring to be `ℤ`.
-/
noncomputable section
namespace InfoGeometry.Core.BosonParityString.IsCommutingBosonSystem
open scoped BigOperators
open InfoGeometry.Core.AnticommutingSum

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {N : ℕ} {d B : Fin N → A} (h : IsCommutingBosonSystem d B)

/-- The entire exterior algebra acts, not just its basis generators. -/
def exteriorRepresentation (c : Bool) : ExteriorAlgebra R (Fin N → R) →ₐ[R] A :=
  ExteriorAlgebra.lift R ⟨(Pi.basisFun R (Fin N)).constr R (h.dressed c),
    basis_square_zero _ (fun i j _ => h.dressed_self_car c i j) (h.dressed_sq c)⟩

@[simp] theorem exteriorRepresentation_ι (c : Bool) (x : Fin N → R) :
    h.exteriorRepresentation c (ExteriorAlgebra.ι R x) = ∑ i, x i • h.dressed c i := by
  rw [exteriorRepresentation, ExteriorAlgebra.lift_ι_apply]
  simp [Module.Basis.constr_apply_fintype]

@[simp] theorem exteriorRepresentation_basis (c : Bool) (i : Fin N) :
    h.exteriorRepresentation (R := R) c (ExteriorAlgebra.ι R (Pi.single i 1)) =
      h.dressed c i := by
  simp [exteriorRepresentation_ι, Pi.single_apply]

/-- The basis images uniquely specify the map on every exterior element. -/
theorem exteriorRepresentation_unique (c : Bool)
    (f : ExteriorAlgebra R (Fin N → R) →ₐ[R] A)
    (hf : ∀ i, f (ExteriorAlgebra.ι R (Pi.single i 1)) = h.dressed c i) :
    f = h.exteriorRepresentation c := by
  apply ExteriorAlgebra.hom_ext
  apply (Pi.basisFun R (Fin N)).ext
  intro i
  simpa using (hf i).trans (h.exteriorRepresentation_basis (R := R) c i).symm

/-- The split Majorana family on the standard positive/negative sum index. -/
def majoranaFamily : Fin N ⊕ Fin N → A := Sum.elim h.plus h.minus

lemma majoranaFamily_anti (i j : Fin N ⊕ Fin N) (hne : i ≠ j) :
    h.majoranaFamily i * h.majoranaFamily j + h.majoranaFamily j * h.majoranaFamily i = 0 := by
  rcases i with i | i <;> rcases j with j | j
  · exact (h.majorana_same_sign_anti (fun he => hne (congrArg Sum.inl he))).1
  · exact h.majorana_mixed_anti i j
  · simpa only [majoranaFamily, Sum.elim_inl, Sum.elim_inr, add_comm] using h.majorana_mixed_anti j i
  · exact (h.majorana_same_sign_anti (fun he => hne (congrArg Sum.inr he))).2

lemma majoranaFamily_square (i : Fin N ⊕ Fin N) :
    h.majoranaFamily i * h.majoranaFamily i =
      algebraMap R A (Sum.elim (fun _ : Fin N => (1 : R)) (fun _ : Fin N => -1) i) := by
  rcases i with i | i
  · simpa only [majoranaFamily, Sum.elim_inl, map_one] using (h.majorana_squares i).1
  · simpa only [majoranaFamily, Sum.elim_inr, map_neg, map_one] using (h.majorana_squares i).2

/-- The native split Clifford representation, over arbitrary central coefficients. -/
def cliffordRepresentation :
    CliffordAlgebra (QuadraticMap.weightedSumSquares R
      (Sum.elim (fun _ : Fin N => (1 : R)) (fun _ : Fin N => -1))) →ₐ[R] A :=
  CliffordAlgebra.lift _ ⟨(Pi.basisFun R (Fin N ⊕ Fin N)).constr R h.majoranaFamily,
    basis_square _ _ h.majoranaFamily_anti (h.majoranaFamily_square (R := R))⟩

@[simp] theorem cliffordRepresentation_ι (x : (Fin N ⊕ Fin N) → R) :
    h.cliffordRepresentation (CliffordAlgebra.ι _ x) = ∑ i, x i • h.majoranaFamily i := by
  rw [cliffordRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [Module.Basis.constr_apply_fintype]

@[simp] theorem cliffordRepresentation_basis (i : Fin N ⊕ Fin N) :
    h.cliffordRepresentation (R := R) (CliffordAlgebra.ι _ (Pi.single i 1)) =
      h.majoranaFamily i := by
  simp [cliffordRepresentation_ι, Pi.single_apply]

/-- The split Clifford representation is uniquely determined on its `2N` generators. -/
theorem cliffordRepresentation_unique
    (f : CliffordAlgebra (QuadraticMap.weightedSumSquares R
      (Sum.elim (fun _ : Fin N => (1 : R)) (fun _ : Fin N => -1))) →ₐ[R] A)
    (hf : ∀ i, f (CliffordAlgebra.ι _ (Pi.single i 1)) = h.majoranaFamily i) :
    f = h.cliffordRepresentation := by
  apply CliffordAlgebra.hom_ext
  apply (Pi.basisFun R (Fin N ⊕ Fin N)).ext
  intro i
  simpa using (hf i).trans (h.cliffordRepresentation_basis (R := R) i).symm

variable {C : Type*} [Ring C] [Algebra R C]

/-- Naturality on the whole exterior algebra, not merely on generators. -/
theorem exteriorRepresentation_natural (f : A →ₐ[R] C) (c : Bool) :
    f.comp (h.exteriorRepresentation c) = (h.map f.toRingHom).exteriorRepresentation c := by
  apply (h.map f.toRingHom).exteriorRepresentation_unique
  intro i
  simp only [AlgHom.comp_apply, h.exteriorRepresentation_basis]
  exact h.map_dressed f.toRingHom c i

/-- Naturality on the whole split Clifford algebra. -/
theorem cliffordRepresentation_natural (f : A →ₐ[R] C) :
    f.comp h.cliffordRepresentation = (h.map f.toRingHom).cliffordRepresentation := by
  apply (h.map f.toRingHom).cliffordRepresentation_unique
  intro i
  simp only [AlgHom.comp_apply, h.cliffordRepresentation_basis]
  rcases i with i | i
  · exact (h.map_majorana f.toRingHom i).1
  · exact (h.map_majorana f.toRingHom i).2

end InfoGeometry.Core.BosonParityString.IsCommutingBosonSystem
