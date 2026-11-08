import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Lift
import InfoGeometry.Twistor.NullProjective

/-!
# Drazin / Projective / Clifford Bridge

Thin repo-native connection layer.

This file does not introduce Drazin inverses, idempotents, projective geometry,
or split `Cl(1,1)` data. Those are already owned by:

* `InfoGeometry.Canonical.Drazin`
* `InfoGeometry.Canonical.DrazinKreinCompatibility`
* `InfoGeometry.Convex.ProjectiveRays`
* `InfoGeometry.Twistor.NullProjective`
* `InfoGeometry.Clifford.Lift`

The purpose here is only to expose the existing chain in one place.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinProjectiveCliffordBridge

open scoped LinearAlgebra.Projectivization

open InfoGeometry.Krein
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.DrazinKreinCompatibility

/-! ## Canonical Drazin projector facts -/

section Drazin

variable {R : Type*} [Ring R]
variable {a b : R} {k : ℕ}

/-- The Drazin regular projector `P = a * b` is already idempotent. -/
@[rep_depth krein]
theorem drazinProjection_idempotent
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse.projection a b * IsDrazinInverse.projection a b =
      IsDrazinInverse.projection a b :=
  IsDrazinInverse.projection_is_idempotent h

/-- The Drazin defect projector `P₀ = 1 - P` is already idempotent. -/
@[rep_depth krein]
theorem drazinComplementaryProjection_idempotent
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse.complementaryProjection a b *
        IsDrazinInverse.complementaryProjection a b =
      IsDrazinInverse.complementaryProjection a b :=
  IsDrazinInverse.complementaryProjection_is_idempotent h

/-- The regular and defect Drazin projectors are left-orthogonal. -/
@[rep_depth krein]
theorem drazinProjection_mul_complementaryProjection
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse.projection a b *
        IsDrazinInverse.complementaryProjection a b = 0 :=
  IsDrazinInverse.projection_mul_complementaryProjection h

/-- The defect and regular Drazin projectors are right-orthogonal. -/
@[rep_depth krein]
theorem drazinComplementaryProjection_mul_projection
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse.complementaryProjection a b *
        IsDrazinInverse.projection a b = 0 :=
  IsDrazinInverse.complementaryProjection_mul_projection h

/-- The Drazin regular/defect projectors decompose the identity. -/
@[rep_depth krein]
theorem drazinProjection_add_complementaryProjection :
    IsDrazinInverse.projection a b +
        IsDrazinInverse.complementaryProjection a b = (1 : R) :=
  IsDrazinInverse.projection_add_complementaryProjection

end Drazin

/-! ## Doubled-Krein Drazin projector facts -/

section KreinDrazin

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
On the doubled Krein carrier, the regular Drazin projector is exactly the
repo-owned `Preg` and is idempotent.
-/
@[rep_depth krein]
theorem doubledDrazinRegularProjector_idempotent
    {T TD : DoubledSpace E →L[ℝ] DoubledSpace E} {k : ℕ}
    (h : KreinGradedDrazinCompatibility (E := E) T TD k) :
    Preg (E := E) T TD * Preg (E := E) T TD = Preg (E := E) T TD :=
  Preg_idempotent (E := E) (T := T) (TD := TD) (k := k) h

/--
On the doubled Krein carrier, the defect Drazin projector is exactly the
repo-owned `Pzero` and is idempotent.
-/
@[rep_depth krein]
theorem doubledDrazinDefectProjector_idempotent
    {T TD : DoubledSpace E →L[ℝ] DoubledSpace E} {k : ℕ}
    (h : KreinGradedDrazinCompatibility (E := E) T TD k) :
    Pzero (E := E) T TD * Pzero (E := E) T TD = Pzero (E := E) T TD :=
  Pzero_idempotent (E := E) (T := T) (TD := TD) (k := k) h

/-- The doubled-Krein Drazin regular and defect lanes are orthogonal. -/
@[rep_depth krein]
theorem doubledDrazinRegular_mul_defect
    {T TD : DoubledSpace E →L[ℝ] DoubledSpace E} {k : ℕ}
    (h : KreinGradedDrazinCompatibility (E := E) T TD k) :
    Preg (E := E) T TD * Pzero (E := E) T TD = 0 :=
  Preg_mul_Pzero (E := E) (T := T) (TD := TD) (k := k) h

/-- The doubled-Krein Drazin defect and regular lanes are orthogonal. -/
@[rep_depth krein]
theorem doubledDrazinDefect_mul_regular
    {T TD : DoubledSpace E →L[ℝ] DoubledSpace E} {k : ℕ}
    (h : KreinGradedDrazinCompatibility (E := E) T TD k) :
    Pzero (E := E) T TD * Preg (E := E) T TD = 0 :=
  Pzero_mul_Preg (E := E) (T := T) (TD := TD) (k := k) h

omit [CompleteSpace E] in
/-- The doubled-Krein Drazin regular/defect lanes decompose the identity. -/
@[rep_depth krein]
theorem doubledDrazinRegular_add_defect
    (T TD : DoubledSpace E →L[ℝ] DoubledSpace E) :
    Preg (E := E) T TD + Pzero (E := E) T TD =
      (1 : DoubledSpace E →L[ℝ] DoubledSpace E) :=
  Preg_add_Pzero (E := E) (T := T) (TD := TD)

end KreinDrazin

/-! ## Projective-ray facts -/

section Projective

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Projective geometry is already represented by rays of doubled states. -/
abbrev DoubledProjectiveState : Type _ :=
  InfoGeometry.Convex.ProjectiveState (E := E)

/-- Projectivization is invariant under nonzero real scaling. -/
theorem doubledProjectiveRay_scale_invariant
    (a : ℝ) (ha : a ≠ 0)
    (v : DoubledSpace E) (hv : v ≠ 0) :
    InfoGeometry.Convex.projectivize (E := E) (a • v) (smul_ne_zero ha hv) =
      InfoGeometry.Convex.projectivize (E := E) v hv :=
  InfoGeometry.Convex.projectivize_smul (E := E) a ha v hv

end Projective

/-! ## Split `Cl(1,1)` facts -/

section Clifford

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The first split `Cl(1,1)` generator acts as an involution on doubled space. -/
theorem cl11_first_generator_squares_to_one :
    InfoGeometry.Clifford.Lift.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.Lift.Q11 (1, 0)) *
      InfoGeometry.Clifford.Lift.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.Lift.Q11 (1, 0)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  InfoGeometry.Clifford.Lift.cl11Rep_ι_one_zero_sq (E := E)

/-- The second split `Cl(1,1)` generator squares to `-1` on doubled space. -/
theorem cl11_second_generator_squares_to_neg_one :
    InfoGeometry.Clifford.Lift.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.Lift.Q11 (0, 1)) *
      InfoGeometry.Clifford.Lift.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.Lift.Q11 (0, 1)) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
  InfoGeometry.Clifford.Lift.cl11Rep_ι_zero_one_sq (E := E)

/-- The split `Cl(1,1)` pseudoscalar is the doubled spectral sign `ε`. -/
theorem cl11_pseudoscalar_is_spectral_epsilon :
    InfoGeometry.Clifford.Lift.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.Lift.Q11 (1, 0) *
          CliffordAlgebra.ι InfoGeometry.Clifford.Lift.Q11 (0, 1)) =
      spectral_epsilon (E := E) :=
  InfoGeometry.Clifford.Lift.cl11Rep_pseudoscalar (E := E)

end Clifford

/-! ## Projective null-cone facts -/

section Twistor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On projectivized doubled states, nullness is exactly nullness of a representative. -/
theorem doubledProjectiveNull_iff
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : DoubledSpace E) (hv : v ≠ 0) :
    InfoGeometry.Twistor.IsNull Q
        (InfoGeometry.Convex.projectivize (E := E) v hv) ↔ Q v = 0 :=
  InfoGeometry.Twistor.isNull_projectivize_iff (E := E) Q v hv

end Twistor

end InfoGeometry.Canonical.DrazinProjectiveCliffordBridge
