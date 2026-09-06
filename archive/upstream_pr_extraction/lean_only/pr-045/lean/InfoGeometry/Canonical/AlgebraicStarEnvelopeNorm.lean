import InfoGeometry.Canonical.AlgebraicStarEnvelope
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Norms and topology pulled back from a faithful C-star realization

The algebraic star-colimit does not carry a norm merely by being a colimit.
This owner records the honest additional datum: a faithful star-algebra
homomorphism into a previously normed `CStarAlgebra`.  The norm, normed-ring
structure, and induced topology are then transported from that realization.
No completion or analytic existence claim is made here.
-/

noncomputable section

namespace CStarStateColimit.Native

universe u v

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {B : Type v} [CStarAlgebra B]

/-- A faithful concrete norming realization of a star algebra. -/
structure FaithfulStarRepresentation where
  rep : A →⋆ₐ[ℂ] B
  faithful : Function.Injective rep

namespace FaithfulStarRepresentation

variable (R : FaithfulStarRepresentation (A := A) (B := B))

/-- The norm pulled back along the faithful star-algebra realization. -/
def pulledNorm (a : A) : ℝ := ‖R.rep a‖

@[simp] theorem pulledNorm_zero : R.pulledNorm 0 = 0 := by
  simp [pulledNorm]

theorem pulledNorm_add_le (a b : A) :
    R.pulledNorm (a + b) ≤ R.pulledNorm a + R.pulledNorm b := by
  simpa [pulledNorm] using norm_add_le (R.rep a) (R.rep b)

theorem pulledNorm_mul_le (a b : A) :
    R.pulledNorm (a * b) ≤ R.pulledNorm a * R.pulledNorm b := by
  simpa [pulledNorm] using norm_mul_le (R.rep a) (R.rep b)

@[simp] theorem pulledNorm_neg (a : A) :
    R.pulledNorm (-a) = R.pulledNorm a := by
  simp [pulledNorm]

@[simp] theorem pulledNorm_star (a : A) :
    R.pulledNorm (star a) = R.pulledNorm a := by
  simp only [pulledNorm, map_star, norm_star]

theorem pulledNorm_eq_zero_iff (a : A) :
    R.pulledNorm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply R.faithful
    simpa using (norm_eq_zero.mp h)
  · intro h
    subst h
    exact R.pulledNorm_zero

/-- The faithful pullback is a genuine `RingNorm`, not merely a seminorm. -/
def pulledRingNorm : RingNorm A where
  toFun := R.pulledNorm
  map_zero' := R.pulledNorm_zero
  add_le' := R.pulledNorm_add_le
  neg' := R.pulledNorm_neg
  eq_zero_of_map_eq_zero' := by
    intro a h
    exact R.pulledNorm_eq_zero_iff a |>.mp h
  mul_le' := R.pulledNorm_mul_le

@[simp] theorem pulledRingNorm_apply (a : A) :
    R.pulledRingNorm a = R.pulledNorm a := rfl

theorem pulledRingNorm_star_mul_self (a : A) :
    R.pulledRingNorm (star a * a) = R.pulledRingNorm a * R.pulledRingNorm a := by
  change R.pulledNorm (star a * a) = R.pulledNorm a * R.pulledNorm a
  simp only [pulledNorm, map_mul, map_star]
  exact CStarRing.norm_star_mul_self

/-! The following local structure is the canonical normed topology induced by
the representation.  It is deliberately supplied as a value, so no global
norm instance is silently installed on the algebraic colimit. -/

noncomputable def pulledNormedRing : NormedRing A :=
  RingNorm.toNormedRing R.pulledRingNorm

theorem pulledNormedRing_norm (a : A) :
    letI := R.pulledNormedRing
    ‖a‖ = R.pulledNorm a := rfl

theorem pulledNormedRing_norm_mul_le (a b : A) :
    letI := R.pulledNormedRing
    ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by
  simpa [pulledNormedRing_norm] using (pulledNorm_mul_le R a b)

/-- The realization is an isometric embedding for the transported topology. -/
theorem rep_isometry :
    letI := R.pulledNormedRing
    Isometry R.rep := by
  letI := R.pulledNormedRing
  intro a b
  rw [edist_dist, edist_dist]
  apply congrArg ENNReal.ofReal
  rw [dist_eq_norm, dist_eq_norm]
  rw [← map_sub R.rep]
  rfl

theorem rep_continuous :
    letI := R.pulledNormedRing
    Continuous R.rep := by
  letI := R.pulledNormedRing
  exact (R.rep_isometry).continuous

end FaithfulStarRepresentation

end CStarStateColimit.Native
