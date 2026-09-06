import proofs.KleinSixStateBundle
import Mathlib.Data.ZMod.Basic

/-!
# Algebraic projectivization of the six-state fibre

`ProjectiveSixState` is the quotient of nonzero six-state vectors by nonzero
complex rescaling.  It is the algebraic carrier of CP⁵; no manifold topology
or chart atlas is asserted here.
-/

noncomputable section
namespace KleinProjectiveSixState

open KleinSixStateBundle TwoSheetThreeColorWeyl

abbrev Vec := Fin 2 × Fin 3 → ℂ
abbrev NonzeroVec := {v : Vec // v ≠ 0}

def projectiveRel (v w : NonzeroVec) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ w.1 = c • v.1

theorem projectiveRel_refl (v : NonzeroVec) : projectiveRel v v := by
  exact ⟨1, one_ne_zero, by simp⟩

theorem projectiveRel_symm {v w : NonzeroVec} (h : projectiveRel v w) :
    projectiveRel w v := by
  rcases h with ⟨c, hc, hw⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hw, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem projectiveRel_trans {u v w : NonzeroVec}
    (huv : projectiveRel u v) (hvw : projectiveRel v w) :
    projectiveRel u w := by
  rcases huv with ⟨c, hc, hv⟩
  rcases hvw with ⟨d, hd, hw⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  rw [hw, hv, smul_smul]

def projectiveSetoid : Setoid NonzeroVec where
  r := projectiveRel
  iseqv := ⟨projectiveRel_refl, projectiveRel_symm, projectiveRel_trans⟩

/-- Algebraic projective six-state fibre, the CP⁵ carrier. -/
abbrev ProjectiveSixState := Quotient projectiveSetoid

def projectiveMk : NonzeroVec → ProjectiveSixState :=
  @Quotient.mk' _ projectiveSetoid

/-- The internal involution preserves nonzero vectors. -/
def thetaOnNonzero (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    NonzeroVec → NonzeroVec := fun v =>
  ⟨theta.mulVec v.1, by
    intro hz
    have hz' := congrArg (fun x => theta.mulVec x) hz
    change theta.mulVec (theta.mulVec v.1) = theta.mulVec 0 at hz'
    rw [Matrix.mulVec_mulVec, theta_sq ω hω, Matrix.one_mulVec] at hz'
    exact v.2 (by simpa using hz')⟩

theorem thetaOnNonzero_respects (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    {v w : NonzeroVec} (h : projectiveRel v w) :
    projectiveRel (thetaOnNonzero ω hω v) (thetaOnNonzero ω hω w) := by
  rcases h with ⟨c, hc, hw⟩
  refine ⟨c, hc, ?_⟩
  change theta.mulVec w.1 = c • theta.mulVec v.1
  rw [hw, Matrix.mulVec_smul]

def projectiveTheta (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ProjectiveSixState → ProjectiveSixState :=
  Quotient.map (thetaOnNonzero ω hω)
    (by intro v w h; exact thetaOnNonzero_respects ω hω h)

@[simp] theorem projectiveTheta_mk (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (v : NonzeroVec) :
    projectiveTheta ω hω (projectiveMk v) = projectiveMk (thetaOnNonzero ω hω v) := rfl

theorem thetaOnNonzero_involutive (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (v : NonzeroVec) :
    thetaOnNonzero ω hω (thetaOnNonzero ω hω v) = v := by
  apply Subtype.ext
  change theta.mulVec (theta.mulVec v.1) = v.1
  rw [Matrix.mulVec_mulVec, theta_sq ω hω, Matrix.one_mulVec]

theorem projectiveTheta_involutive (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Involutive (projectiveTheta ω hω) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  change projectiveTheta ω hω (projectiveTheta ω hω (projectiveMk v)) = projectiveMk v
  rw [projectiveTheta_mk, projectiveTheta_mk]
  rw [thetaOnNonzero_involutive]

end KleinProjectiveSixState
end noncomputable section
