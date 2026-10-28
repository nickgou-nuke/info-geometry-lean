/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.TracialGNSDirichlet
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! # Unitary gauge covariance on the completed tracial GNS carrier

The conjugating bounded operator is constructed as left multiplication by
`u` followed by right multiplication by `u*`. Its unitarity and its action on
commutators are proved on the native dense GNS representatives and extended
by continuity. The resulting Dirichlet covariance is an operator identity,
and its spectral consequence uses Mathlib's actual spectrum.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace
open InfoGeometry.Analysis.OperatorDirichletLaplacian

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (htr : ∀ a b : A, f (a * b) = f (b * a))

/-- The completed conjugation action, constructed from the existing two actions. -/
def tracialConjugationGNS (u : unitary A) : f.GNS →L[ℂ] f.GNS :=
  f.gnsStarAlgHom (u : A) * f.rightMulMapGNS htr (star (u : A))

@[simp] theorem tracialConjugationGNS_coe (u : unitary A) (x : f.PreGNS) :
    f.tracialConjugationGNS htr u (x : f.GNS) =
      (f.toPreGNS ((u : A) * f.ofPreGNS x * star (u : A)) : f.GNS) := by
  simp [tracialConjugationGNS, gnsStarAlgHom, mul_assoc]

@[simp] theorem tracialConjugationGNS_toPreGNS (u : unitary A) (a : A) :
    f.tracialConjugationGNS htr u (f.toPreGNS a : f.GNS) =
      (f.toPreGNS ((u : A) * a * star (u : A)) : f.GNS) := by
  simp

@[simp] theorem tracialConjugationGNS_one :
    f.tracialConjugationGNS htr (1 : unitary A) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp

theorem tracialConjugationGNS_mul (u v : unitary A) :
    f.tracialConjugationGNS htr (u * v) =
      f.tracialConjugationGNS htr u * f.tracialConjugationGNS htr v := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [mul_apply_eq_comp, tracialConjugationGNS_coe]
    exact congrArg (fun a : A => (f.toPreGNS a : f.GNS))
      (Unitary.conjStarAlgAut_mul_apply (S := ℂ) u v (f.ofPreGNS x))

/-- The constructed conjugation action has the expected adjoint. -/
theorem tracialConjugationGNS_star (u : unitary A) :
    star (f.tracialConjugationGNS htr u) = f.tracialConjugationGNS htr (star u) := by
  simp only [tracialConjugationGNS, star_mul, rightMulMapGNS_star,
    star_star, ← map_star, Unitary.coe_star]
  exact (f.left_rightMulMapGNS_commute htr (star (u : A)) (u : A)).eq.symm

/-- No abstract intertwiner or isometry assumption is supplied. -/
def tracialConjugationUnitaryGNS (u : unitary A) : unitary (f.GNS →L[ℂ] f.GNS) :=
  ⟨f.tracialConjugationGNS htr u, by
    constructor
    · rw [f.tracialConjugationGNS_star htr,
        ← f.tracialConjugationGNS_mul htr, Unitary.star_mul_self,
        f.tracialConjugationGNS_one htr]
    · rw [f.tracialConjugationGNS_star htr,
        ← f.tracialConjugationGNS_mul htr, Unitary.mul_star_self,
        f.tracialConjugationGNS_one htr]⟩

@[simp] theorem tracialConjugationUnitaryGNS_coe (u : unitary A) :
    (f.tracialConjugationUnitaryGNS htr u : f.GNS →L[ℂ] f.GNS) =
      f.tracialConjugationGNS htr u := rfl

/-- Conjugation intertwines the actual GNS commutator operators. -/
theorem tracialCommutatorGNS_gauge_intertwine (u : unitary A) (H : A) :
    f.tracialCommutatorGNS htr ((u : A) * H * star (u : A)) *
        f.tracialConjugationGNS htr u =
      f.tracialConjugationGNS htr u * f.tracialCommutatorGNS htr H := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [mul_apply_eq_comp, tracialConjugationGNS_coe, tracialCommutatorGNS_coe]
    apply congrArg (fun a : A => (f.toPreGNS a : f.GNS))
    let φ := Unitary.conjStarAlgAut ℂ A u
    change φ H * φ (f.ofPreGNS x) - φ (f.ofPreGNS x) * φ H =
      φ (H * f.ofPreGNS x - f.ofPreGNS x * H)
    simp only [map_sub, map_mul]

/-- Gauge covariance is equality with a constructed unitary conjugate. -/
theorem tracialCommutatorGNS_gauge (u : unitary A) (H : A) :
    f.tracialCommutatorGNS htr ((u : A) * H * star (u : A)) =
      f.tracialConjugationGNS htr u * f.tracialCommutatorGNS htr H *
        star (f.tracialConjugationGNS htr u) := by
  have hu : f.tracialConjugationGNS htr u *
      star (f.tracialConjugationGNS htr u) = 1 :=
    Unitary.mul_star_self_of_mem (f.tracialConjugationUnitaryGNS htr u).property
  calc
    _ = f.tracialCommutatorGNS htr ((u : A) * H * star (u : A)) *
        (f.tracialConjugationGNS htr u * star (f.tracialConjugationGNS htr u)) := by
          rw [hu, mul_one]
    _ = _ := by rw [← mul_assoc, f.tracialCommutatorGNS_gauge_intertwine htr]

variable {ι : Type*} [Fintype ι]

/-- The complete Dirichlet operator is gauge covariant on the same Hilbert carrier. -/
theorem tracialDirichletGNS_gauge (u : unitary A) (H : ι → A) :
    f.tracialDirichletGNS htr (fun i => (u : A) * H i * star (u : A)) =
      f.tracialConjugationGNS htr u * f.tracialDirichletGNS htr H *
        star (f.tracialConjugationGNS htr u) := by
  simp only [tracialDirichletGNS, tracialCommutatorGNS_gauge]
  exact laplacian_unitary_conjugate
    (fun i => f.tracialCommutatorGNS htr (H i))
    (f.tracialConjugationUnitaryGNS htr u)

/-- The native spectrum is unchanged, not merely a separately declared gap readout. -/
theorem spectrum_tracialDirichletGNS_gauge (u : unitary A) (H : ι → A) :
    spectrum ℂ (f.tracialDirichletGNS htr
      (fun i => (u : A) * H i * star (u : A))) =
      spectrum ℂ (f.tracialDirichletGNS htr H) := by
  rw [f.tracialDirichletGNS_gauge htr]
  exact Unitary.spectrum_star_right_conjugate
    (U := f.tracialConjugationUnitaryGNS htr u)

end PositiveLinearMap
