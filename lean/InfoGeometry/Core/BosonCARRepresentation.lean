/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.BosonCliffordExterior
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-!
# Native neutral Clifford representation of both CAR families

The quadratic form is Mathlib's `QuadraticForm.dualProd R (Fin N → R)`:
`Q (φ,v) = φ v`. This presentation works without dividing by two, even when
the positive and negative Majorana combinations coincide in characteristic two.
-/
noncomputable section
namespace InfoGeometry.Core.BosonParityString.IsCommutingBosonSystem
open scoped BigOperators
open InfoGeometry.Core.AnticommutingSum

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {N : ℕ} {d B : Fin N → A} (h : IsCommutingBosonSystem d B)

/-- The neutral generator map on the actual native dual module and vector module. -/
def carGenerator : (Module.Dual R (Fin N → R) × (Fin N → R)) →ₗ[R] A :=
  ((Pi.basisFun R (Fin N)).dualBasis.constr R (h.dressed true)).coprod
    ((Pi.basisFun R (Fin N)).constr R (h.dressed false))

lemma carGenerator_apply (φ : Module.Dual R (Fin N → R)) (v : Fin N → R) :
    h.carGenerator (φ, v) = (∑ i, φ (Pi.single i 1) • h.dressed true i) +
      ∑ i, v i • h.dressed false i := by
  simp [carGenerator, Module.Basis.constr_apply_fintype, Module.Basis.dualBasis_equivFun]

lemma carGenerator_square (x : Module.Dual R (Fin N → R) × (Fin N → R)) :
    h.carGenerator x * h.carGenerator x =
      algebraMap R A (QuadraticForm.dualProd R (Fin N → R) x) := by
  obtain ⟨φ, v⟩ := x
  have hs (c : Bool) (w : Fin N → R) :
      (∑ i, w i • h.dressed c i) * (∑ i, w i • h.dressed c i) = 0 := by
    simpa [Module.Basis.constr_apply_fintype] using
      basis_square_zero (h.dressed c) (fun i j _ => h.dressed_self_car c i j)
        (h.dressed_sq c) w
  have hp : ∑ i, v i * φ (Pi.single i 1) = φ v := by
    have hv : (∑ i, v i • (Pi.single i (1 : R) : Fin N → R)) = v := by
      ext j; simp [Pi.single_apply]
    conv_rhs => rw [← hv, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [carGenerator_apply]
  calc
    ((∑ i, φ (Pi.single i 1) • h.dressed true i) + ∑ i, v i • h.dressed false i) *
        ((∑ i, φ (Pi.single i 1) • h.dressed true i) + ∑ i, v i • h.dressed false i) =
      (∑ i, v i • h.dressed false i) * (∑ i, v i • h.dressed false i) +
      ((∑ i, v i • h.dressed false i) * (∑ i, φ (Pi.single i 1) • h.dressed true i) +
       (∑ i, φ (Pi.single i 1) • h.dressed true i) * (∑ i, v i • h.dressed false i)) +
      (∑ i, φ (Pi.single i 1) • h.dressed true i) *
        (∑ i, φ (Pi.single i 1) • h.dressed true i) := by noncomm_ring
    _ = algebraMap R A (QuadraticForm.dualProd R (Fin N → R) (φ, v)) := by
      rw [hs, hs, mixed_sum_car _ _ h.dressed_mixed_car, hp, zero_add, add_zero]
      rfl

/-- The CAR representation on Mathlib's neutral Clifford algebra. -/
def carRepresentation :
    CliffordAlgebra (QuadraticForm.dualProd R (Fin N → R)) →ₐ[R] A :=
  CliffordAlgebra.lift _ ⟨h.carGenerator, h.carGenerator_square⟩

@[simp] lemma carRepresentation_ι (x : Module.Dual R (Fin N → R) × (Fin N → R)) :
    h.carRepresentation (CliffordAlgebra.ι _ x) = h.carGenerator x :=
  CliffordAlgebra.lift_ι_apply _ _ x

@[simp] lemma carRepresentation_create (i : Fin N) :
    h.carRepresentation (R := R)
      (CliffordAlgebra.ι _ ((Pi.basisFun R (Fin N)).dualBasis i, 0)) = h.dressed true i := by
  rw [carRepresentation_ι]
  simp [carGenerator, Pi.single_apply]

@[simp] lemma carRepresentation_annihilate (i : Fin N) :
    h.carRepresentation (R := R) (CliffordAlgebra.ι _ (0, Pi.single i 1)) = h.dressed false i := by
  rw [carRepresentation_ι]
  simp [carGenerator]

/-- Both sets of basis generators uniquely determine the representation. -/
theorem carRepresentation_unique
    (f : CliffordAlgebra (QuadraticForm.dualProd R (Fin N → R)) →ₐ[R] A)
    (hc : ∀ i, f (CliffordAlgebra.ι _ ((Pi.basisFun R (Fin N)).dualBasis i, 0)) = h.dressed true i)
    (ha : ∀ i, f (CliffordAlgebra.ι _ (0, Pi.single i 1)) = h.dressed false i) :
    f = h.carRepresentation := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.prod_ext
  · apply (Pi.basisFun R (Fin N)).dualBasis.ext
    intro i
    simpa using (hc i).trans (h.carRepresentation_create (R := R) i).symm
  · apply (Pi.basisFun R (Fin N)).ext
    intro i
    simpa using (ha i).trans (h.carRepresentation_annihilate (R := R) i).symm

/-- Naturality holds on the full neutral Clifford algebra. -/
theorem carRepresentation_natural {C : Type*} [Ring C] [Algebra R C] (f : A →ₐ[R] C) :
    f.comp h.carRepresentation = (h.map f.toRingHom).carRepresentation := by
  apply (h.map f.toRingHom).carRepresentation_unique
  · intro i
    simp only [AlgHom.comp_apply, h.carRepresentation_create]
    exact h.map_dressed f.toRingHom true i
  · intro i
    simp only [AlgHom.comp_apply, h.carRepresentation_annihilate]
    exact h.map_dressed f.toRingHom false i

end InfoGeometry.Core.BosonParityString.IsCommutingBosonSystem
