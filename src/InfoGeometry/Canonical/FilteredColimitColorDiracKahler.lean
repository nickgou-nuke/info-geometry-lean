import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit

namespace InfoGeometry.Canonical

/-!
# Nilpotent differentials on a linear filtered-colimit cone

This file deliberately uses Mathlib linear maps rather than a custom
"colimit" record.  The target `AInf` is a genuine cone target; when it is
instantiated with a categorical colimit, `jointly_surjective` is the concrete
representative property needed by the nilpotence transport theorem below.
-/

section

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (AInf : Type*) [AddCommGroup AInf] [Module R AInf]

/-! ## Cone commutation and the existing tensor-tower owner -/

theorem colimitDifferential_commutes_with_stage
    (d : ∀ n, A n →ₗ[R] A n)
    (dInf : AInf →ₗ[R] AInf)
    (psi : ∀ n, A n →ₗ[R] AInf)
    (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
    (n : ℕ) (x : A n) :
    dInf (psi n x) = psi n (d n x) := by
  simpa using congrArg (fun f : A n →ₗ[R] AInf => f x) (d_comm n)

theorem colimitCone_desc_after_steps
    (iota : ∀ n, A n →ₗ[R] A (n + 1))
    (psi : ∀ n, A n →ₗ[R] AInf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (n m : ℕ) :
    (psi (n + m)).comp (iota_seq A iota n m) = psi n :=
  psi_comp_iota_seq A iota AInf psi psi_comm n m

/-! ## Nilpotence transport -/

theorem colimitDifferential_sq_zero
    (d : ∀ n, A n →ₗ[R] A n)
    (dInf : AInf →ₗ[R] AInf)
    (psi : ∀ n, A n →ₗ[R] AInf)
    (d_sq_zero : ∀ n, (d n).comp (d n) = 0)
    (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
    (jointly_surjective : ∀ x : AInf, ∃ n : ℕ, ∃ y : A n, psi n y = x) :
    dInf.comp dInf = 0 := by
  ext x
  rcases jointly_surjective x with ⟨n, y, rfl⟩
  have h₁ : dInf (psi n y) = psi n (d n y) := by
    exact colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n y
  have h₂ : dInf (psi n (d n y)) = psi n (d n (d n y)) := by
    exact colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n (d n y)
  have hzero : d n (d n y) = 0 := by
    have h := congrArg (fun f : A n →ₗ[R] A n => f y) (d_sq_zero n)
    simpa using h
  change dInf (dInf (psi n y)) = 0
  rw [h₁, h₂, hzero]
  exact (psi n).map_zero

theorem colimitDifferential_sq_zero_on_stage
    (d : ∀ n, A n →ₗ[R] A n)
    (dInf : AInf →ₗ[R] AInf)
    (psi : ∀ n, A n →ₗ[R] AInf)
    (d_sq_zero : ∀ n, (d n).comp (d n) = 0)
    (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
    (n : ℕ) (x : A n) :
    dInf (dInf (psi n x)) = 0 := by
  have h₁ : dInf (psi n x) = psi n (d n x) := by
    exact colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n x
  have h₂ : dInf (psi n (d n x)) = psi n (d n (d n x)) := by
    exact colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n (d n x)
  have hzero : d n (d n x) = 0 := by
    have h := congrArg (fun f : A n →ₗ[R] A n => f x) (d_sq_zero n)
    simpa using h
  calc
    dInf (dInf (psi n x)) = dInf (psi n (d n x)) := by rw [h₁]
    _ = psi n (d n (d n x)) := by rw [h₂]
    _ = psi n 0 := by rw [hzero]
    _ = 0 := by simp

/-! ## Stagewise predicates transported to the cone -/

theorem colimitPredicate_desc
    (proj : ∀ n, A n → Prop)
    (projInf : AInf → Prop)
    (psi : ∀ n, A n →ₗ[R] AInf)
    (compatible : ∀ n x, projInf (psi n x) ↔ proj n x)
    (n : ℕ) (x : A n) :
    projInf (psi n x) ↔ proj n x :=
  compatible n x

end

end InfoGeometry.Canonical
