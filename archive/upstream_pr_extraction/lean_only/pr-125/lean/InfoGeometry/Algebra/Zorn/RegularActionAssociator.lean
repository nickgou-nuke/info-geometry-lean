import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.Zorn.Associator

/-!
# Regular-action associator

The left and right regular actions of a nonassociative algebra are genuine
linear maps.  Their mixed commutator is the operator form of the associator;
no associative multiplication on the carrier is introduced here.
-/

namespace InfoGeometry.Algebra

variable {R A : Type*}
variable [CommRing R]
variable [NonUnitalNonAssocRing A]
variable [Module R A]
variable [IsScalarTower R A A]
variable [SMulCommClass R A A]

def leftRightCommutator (x y : A) : A →ₗ[R] A :=
  (L_map (R := R) x).comp (R_map (R := R) y) -
    (R_map (R := R) y).comp (L_map (R := R) x)

noncomputable def leftRightCommutatorBilin :
    A →ₗ[R] A →ₗ[R] (A →ₗ[R] A) :=
  LinearMap.mk₂ R
    (fun x y => leftRightCommutator (R := R) x y)
    (by
      intro x₁ x₂ y
      apply LinearMap.ext
      intro z
      simp [leftRightCommutator, L_map, R_map, add_mul, mul_add]
      abel)
    (by
      intro r x y
      apply LinearMap.ext
      intro z
      simp [leftRightCommutator, L_map, R_map, smul_mul_assoc, mul_smul_comm,
        smul_sub])
    (by
      intro x y₁ y₂
      apply LinearMap.ext
      intro z
      simp [leftRightCommutator, L_map, R_map, add_mul, mul_add]
      abel)
    (by
      intro r x y
      apply LinearMap.ext
      intro z
      change x * (z * (r • y)) - (x * z) * (r • y) =
        r • (x * (z * y) - (x * z) * y)
      simp only [mul_smul_comm, smul_sub])

theorem leftRightCommutator_apply (x y z : A) :
    leftRightCommutator (R := R) x y z = -_root_.associator x z y := by
  simp [leftRightCommutator, L_map, R_map, associator_apply]

theorem leftRightCommutator_apply_of_alternative
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    leftRightCommutator (R := R) x y z = _root_.associator x y z := by
  rw [leftRightCommutator_apply]
  simpa using (alternative_associator_swap23 hright x y z).symm

theorem leftRightCommutatorBilin_swap_neg
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y : A) :
    leftRightCommutatorBilin (R := R) y x =
      -leftRightCommutatorBilin (R := R) x y := by
  apply LinearMap.ext
  intro z
  simp only [leftRightCommutatorBilin, LinearMap.mk₂_apply, LinearMap.neg_apply]
  rw [leftRightCommutator_apply_of_alternative hright,
    leftRightCommutator_apply_of_alternative hright,
      alternative_associator_swap12 hleft y x z]

theorem leftRightCommutator_cyclic_sum_of_alternative
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    leftRightCommutator (R := R) x y z +
        leftRightCommutator (R := R) y z x +
        leftRightCommutator (R := R) z x y =
      (3 : R) • _root_.associator x y z := by
  have hxy := leftRightCommutator_apply_of_alternative
    (R := R) hright x y z
  have hyz := leftRightCommutator_apply_of_alternative
    (R := R) hright y z x
  have hzx := leftRightCommutator_apply_of_alternative
    (R := R) hright z x y
  have hcyc1 : _root_.associator y z x = _root_.associator x y z :=
    alternative_associator_cycle hleft hright x y z
  have hcyc2 : _root_.associator z x y = _root_.associator x y z := by
    exact (alternative_associator_cycle hleft hright y z x).trans hcyc1
  rw [hxy, hyz, hzx]
  rw [hcyc1, hcyc2]
  module

theorem leftRightCommutator_self_apply_of_alternative
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x z : A) :
    leftRightCommutator (R := R) x x z = 0 := by
  rw [leftRightCommutator_apply_of_alternative hright]
  simp [associator_apply, hleft]

theorem leftRightCommutatorBilin_self_of_alternative
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x : A) :
    leftRightCommutatorBilin (R := R) x x = 0 := by
  apply LinearMap.ext
  intro z
  simpa using leftRightCommutator_self_apply_of_alternative
    (R := R) hleft hright x z

noncomputable def leftRightCommutatorAlternating
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x)) :
    A [⋀^Fin 2]→ₗ[R] (A →ₗ[R] A) := by
  classical
  let f : MultilinearMap R (fun _ : Fin 2 => A) (A →ₗ[R] A) :=
    { toFun := fun v => leftRightCommutatorBilin (R := R) (v 0) (v 1)
      map_update_add' := by
        intro _ v i x y
        fin_cases i
        · simpa [Function.update] using
            congrArg (fun F : A →ₗ[R] A => F)
              (map_add (leftRightCommutatorBilin (R := R)) x y)
        · simpa [Function.update] using
            congrArg (fun F : A →ₗ[R] A => F)
              (map_add (leftRightCommutatorBilin (R := R) (v 0)) x y)
      map_update_smul' := by
        intro _ v i r x
        fin_cases i
        · simpa [Function.update] using
            congrArg (fun F : A →ₗ[R] A => F)
              (map_smul (leftRightCommutatorBilin (R := R)) r x)
        · simpa [Function.update] using
            congrArg (fun F : A →ₗ[R] A => F)
              (map_smul (leftRightCommutatorBilin (R := R) (v 0)) r x) }
  exact AlternatingMap.mk f (by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change leftRightCommutatorBilin (R := R) (v 0) (v 1) = 0
      have h : v 0 = v 1 := by simpa using hij
      rw [h]
      exact leftRightCommutatorBilin_self_of_alternative
        (R := R) hleft hright (v 1)
    · change leftRightCommutatorBilin (R := R) (v 0) (v 1) = 0
      have h : v 1 = v 0 := by simpa using hij
      rw [h]
      exact leftRightCommutatorBilin_self_of_alternative
        (R := R) hleft hright (v 0)
    · exact (hne rfl).elim)

end InfoGeometry.Algebra
