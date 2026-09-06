import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Exceptional.FreudenthalSymplecticAction
import InfoGeometry.Exceptional.CyclotomicExceptionalGaloisActionBridge

/-! Conjugation transport for the existing symplectic operator carrier. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def conjugateSymplecticOperator
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (T : Module.End ℝ (FreudenthalCharge J)) :
    Module.End ℝ (FreudenthalCharge J) :=
  e.toLinearMap.comp (T.comp e.symm.toLinearMap)

theorem conjugateSymplecticOperator_comp
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (S T : Module.End ℝ (FreudenthalCharge J)) :
    conjugateSymplecticOperator e (S.comp T) =
      (conjugateSymplecticOperator e S).comp
        (conjugateSymplecticOperator e T) := by
  apply LinearMap.ext
  intro x
  simp [conjugateSymplecticOperator, LinearMap.comp_apply]

theorem conjugateSymplecticOperator_add
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (S T : Module.End ℝ (FreudenthalCharge J)) :
    conjugateSymplecticOperator e (S + T) =
      conjugateSymplecticOperator e S + conjugateSymplecticOperator e T := by
  apply LinearMap.ext
  intro x
  simp [conjugateSymplecticOperator, LinearMap.comp_apply]

theorem conjugateSymplecticOperator_sub
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (S T : Module.End ℝ (FreudenthalCharge J)) :
    conjugateSymplecticOperator e (S - T) =
      conjugateSymplecticOperator e S - conjugateSymplecticOperator e T := by
  apply LinearMap.ext
  intro x
  simp [conjugateSymplecticOperator, LinearMap.comp_apply]

theorem conjugateSymplecticOperator_lie
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (S T : Module.End ℝ (FreudenthalCharge J)) :
    conjugateSymplecticOperator e ⁅S, T⁆ =
      ⁅conjugateSymplecticOperator e S,
        conjugateSymplecticOperator e T⁆ := by
  apply LinearMap.ext
  intro x
  simp only [Ring.lie_def, conjugateSymplecticOperator,
    LinearMap.comp_apply]
  simp [← map_sub]

theorem conjugateSymplecticOperator_zeroBracket
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (T U : SymplecticTKKZero D) :
    conjugateSymplecticOperator e
        (⁅(T : Module.End ℝ (FreudenthalCharge J)),
          (U : Module.End ℝ (FreudenthalCharge J))⁆) =
      ⁅conjugateSymplecticOperator e (T : Module.End ℝ (FreudenthalCharge J)),
        conjugateSymplecticOperator e (U : Module.End ℝ (FreudenthalCharge J))⁆ := by
  exact conjugateSymplecticOperator_lie e T U

theorem conjugateSymplecticOperator_isSymplectic
    (e : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)
    (he : ∀ x y : FreudenthalCharge J,
      FreudenthalCharge.symplecticForm D (e x) (e y) =
        FreudenthalCharge.symplecticForm D x y)
    (T : Module.End ℝ (FreudenthalCharge J))
    (hT : IsSymplecticOperator D T) :
    IsSymplecticOperator D (conjugateSymplecticOperator e T) := by
  intro x y
  change FreudenthalCharge.symplecticForm D
      (e (T (e.symm x))) y +
    FreudenthalCharge.symplecticForm D x (e (T (e.symm y))) = 0
  calc
    FreudenthalCharge.symplecticForm D (e (T (e.symm x))) y +
        FreudenthalCharge.symplecticForm D x (e (T (e.symm y))) =
      FreudenthalCharge.symplecticForm D (T (e.symm x)) (e.symm y) +
        FreudenthalCharge.symplecticForm D (e.symm x) (T (e.symm y)) := by
          rw [← he (T (e.symm x)) (e.symm y),
            ← he (e.symm x) (T (e.symm y))]
          simp
    _ = 0 := hT (e.symm x) (e.symm y)

theorem conjugate_mixedSymplecticBracket
    {N : ℕ} (rep : InfoGeometry.Exceptional.Galois.CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (x y : FreudenthalCharge J) :
    conjugateSymplecticOperator (rep.act g)
        (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) =
      (mixedSymplecticBracket D (rep.act g x) (rep.act g y) :
        Module.End ℝ (FreudenthalCharge J)) := by
  apply LinearMap.ext
  intro z
  change rep.act g
      ((mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J))
        ((rep.act g).symm z)) = _
  simpa using
    (InfoGeometry.Exceptional.Galois.CyclotomicSymplecticRepresentation.mixedBracket_intertwine
      D rep g x y ((rep.act g).symm z))

end InfoGeometry.Exceptional.Freudenthal
