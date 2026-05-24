import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.ClNNBilinear
import InfoGeometry.Canonical.Cl44ConformalNormalization
import InfoGeometry.Projective.NullBoundary
import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Twistor.PenroseTwistor

/-!
# Split `Cl(4,4)` causal envelope

This file packages the theorem-safe part of the split-algebra causality story.

What is proved here:

* `Cl(4,4)` is the fourth stage of the repo's recursive split `Cl(n,n)` tower;
* the head null vectors in the fourth stage are isotropic and pair nontrivially;
* their Clifford generators satisfy the normalized split-null CAR;
* the projective null boundary is the projectivized null cone of the
  `(4,4)` quadratic form;
* the quadratic conformal-envelope dimension count is the `so(5,5)` count,
  and triality is placed in the `so(4,4)` Levi layer.

What is deliberately not proved here:

* no split-octonion classification theorem;
* no `Spin(4,4)` triality theorem;
* no `E₈` representation theorem;
* no derivation of Lorentz signature `(3,1)` from an eta invariant.

The last item is not represented by an interface here.  This file keeps
only explicit split `(4,4)` facts and does not provide an eta-to-Lorentz
reduction object.
-/

namespace InfoGeometry.Clifford.SplitCl44CausalEnvelope

open scoped TensorProduct

open InfoGeometry.Projective
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ClNNBilinear
open InfoGeometry.Canonical.Cl44ConformalNormalization

/-! ## Split `Cl(4,4)` carrier and projective null boundary -/

/-- The split `Cl(4,4)` carrier: four hyperbolic planes, hence signature `(4,4)`. -/
@[rep_depth krein]
abbrev SplitCl44Carrier := HyperbolicSpace 4

/-- The split `Cl(4,4)` quadratic form from the recursive `Cl(n,n)` tower. -/
@[rep_depth krein]
noncomputable abbrev SplitCl44Quad : QuadraticForm ℝ SplitCl44Carrier :=
  hyperbolicQuadratic 4

/-- The split `Cl(4,4)` bilinear form from the recursive `Cl(n,n)` tower. -/
@[rep_depth krein]
noncomputable abbrev SplitCl44Bilinear :
    SplitCl44Carrier →ₗ[ℝ] SplitCl44Carrier →ₗ[ℝ] ℝ :=
  hyperbolicBilinear 4

/-- The split `Cl(4,4)` Clifford algebra in the repo's Bott tower. -/
@[rep_depth krein]
abbrev SplitCl44Algebra := Cl44

/-- The projective null boundary of the split `(4,4)` quadratic carrier. -/
@[rep_depth krein]
noncomputable abbrev ProjectiveNullBoundary44 : Type _ :=
  InfoGeometry.Twistor.TwistorSpace (K := ℝ) (V := SplitCl44Carrier) SplitCl44Quad

/--
The split `(4,4)` quadratic carrier as a generic projective-null datum.

This is the shared quotient pattern used by the repo's twistor and Zorn
projective-null layers.
-/
@[rep_depth krein]
noncomputable def splitCl44ProjectiveNullBoundaryDatum :
    ProjectiveNullBoundaryDatum ℝ ℝ SplitCl44Carrier where
  q := SplitCl44Quad
  zero := 0
  scale := fun u v => (u : ℝ) • v
  scale_one := by
    intro v
    simp
  scale_mul := by
    intro u v w
    simp [smul_smul]
  null_scale := by
    intro u v
    constructor
    · intro h
      have hmul : ((u : ℝ) * (u : ℝ)) * SplitCl44Quad v = 0 := by
        simpa [SplitCl44Quad.map_smul] using h
      rcases mul_eq_zero.mp hmul with hsq | hq
      · exfalso
        have hu : (u : ℝ) ≠ 0 := Units.ne_zero u
        exact (mul_ne_zero hu hu) hsq
      · exact hq
    · intro h
      simp [SplitCl44Quad.map_smul, h]
  scale_ne_zero := by
    intro u v hv
    exact smul_ne_zero (Units.ne_zero u) hv

/-- The split `(4,4)` projective null reps in the shared quotient layer. -/
@[rep_depth krein]
abbrev splitCl44ProjectiveNullRep :=
  ProjectiveNullBoundaryDatum.NullRep splitCl44ProjectiveNullBoundaryDatum

/-- The split `(4,4)` projective null boundary in the shared quotient layer. -/
@[rep_depth krein]
abbrev splitCl44ProjectiveNullSpace :=
  ProjectiveNullBoundaryDatum.ProjectiveNullBoundary splitCl44ProjectiveNullBoundaryDatum

/-- `Cl(4,4)` is the fourth split Bott stage of the recursive tower. -/
@[rep_depth krein]
theorem splitCl44_is_fourth_split_bott_stage :
    SplitCl44Algebra = SplitBottClifford 4 :=
  rfl

/-- `Cl(4,4)` is one split Bott step over `Cl(3,3)`. -/
@[rep_depth krein]
noncomputable def splitCl44_as_head_cl11_tensor_tail_cl33 :
    SplitCl44Algebra
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (SplitBottQuad 3)) :=
  cl44_as_splitBottStep

/-- A nonzero split `(4,4)` null vector defines a projective boundary point. -/
@[rep_depth krein]
noncomputable def projectiveNullBoundary44_mk
    (v : SplitCl44Carrier) (hv : v ≠ 0) (hQ : SplitCl44Quad v = 0) :
    ProjectiveNullBoundary44 :=
  InfoGeometry.Twistor.twistorMk SplitCl44Quad v hv hQ

/-
Honest boundary debt:
the repo still lacks a source theorem identifying the Penrose twistor carrier
`ℂ^4` with the split `Cl(4,4)` carrier in a way that preserves the null
quadratic readout.  The next theorem states exactly that missing model as
explicit debt, rather than hiding it behind a wrapper.
-/
theorem penroseTwistor_has_splitCl44_null_model :
    ∃ L : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier →ₗ[ℝ] SplitCl44Carrier,
      Function.Injective L ∧
        ∀ z : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier,
          SplitCl44Quad (L z) = InfoGeometry.Twistor.PenroseTwistor.helicity z := by
  sorry

/--
If the missing Penrose-to-split `Cl(4,4)` null model is supplied, any nonzero
Penrose null representative yields a projective split-null boundary point.
-/
noncomputable def penroseNullTwistor_toProjectiveNullBoundary44
    (z : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier)
    (hz : z ≠ 0)
    (hnull : InfoGeometry.Twistor.PenroseTwistor.helicity z = 0)
    (hmodel :
      ∃ L : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier →ₗ[ℝ] SplitCl44Carrier,
        Function.Injective L ∧
          ∀ z : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier,
            SplitCl44Quad (L z) = InfoGeometry.Twistor.PenroseTwistor.helicity z) :
    ProjectiveNullBoundary44 := by
  classical
  let L : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier →ₗ[ℝ] SplitCl44Carrier :=
    Classical.choose hmodel
  have hLin : Function.Injective L := (Classical.choose_spec hmodel).1
  have hQ :
      ∀ z : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier,
        SplitCl44Quad (L z) = InfoGeometry.Twistor.PenroseTwistor.helicity z :=
    (Classical.choose_spec hmodel).2
  have hLz_ne_zero : L z ≠ 0 := by
    intro hzero
    exact hz <| hLin <| by simpa using hzero
  exact projectiveNullBoundary44_mk (L z) hLz_ne_zero (by simpa [hQ z] using hnull)

/-! ## Built-in null directions in the split carrier -/

/-- The first normalized head null vector in the fourth split stage is isotropic. -/
@[rep_depth krein, simp]
theorem splitCl44_headNullMinus_isotropic :
    SplitCl44Quad (headNullMinus 3) = 0 :=
  hyperbolic_headNullMinus_isotropic 3

/-- The second normalized head null vector in the fourth split stage is isotropic. -/
@[rep_depth krein, simp]
theorem splitCl44_headNullPlus_isotropic :
    SplitCl44Quad (headNullPlus 3) = 0 :=
  hyperbolic_headNullPlus_isotropic 3

/-- The two normalized head null vectors pair to `1/2`. -/
@[rep_depth krein, simp]
theorem splitCl44_headNull_pairing :
    SplitCl44Bilinear (headNullMinus 3) (headNullPlus 3) = 1 / 2 :=
  hyperbolic_headNullMinus_headNullPlus_pairing 3

/--
The split `Cl(4,4)` head null generators satisfy the normalized CAR relation.

This is the algebraic light-cone fact available in the current repo; it is not
a current-algebra or Virasoro theorem.
-/
@[rep_depth krein]
theorem splitCl44_headNull_clifford_car :
    gammaHeadNullMinus 3 * gammaHeadNullPlus 3
      + gammaHeadNullPlus 3 * gammaHeadNullMinus 3 = 1 :=
  gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap_from_hyperbolic_pairing 3

/-! ## Conformal-envelope accounting -/

/--
Quadratic light-space conformal closure count:
`V₈⁻ ⊕ (so(4,4) ⊕ R) ⊕ V₈⁺` has dimension `45`, the `so(5,5)` count.
-/
@[rep_depth krein]
theorem splitCl44_quadratic_conformal_count :
    quadraticLightSpaceDim
      + (quadraticLeviRotationDim + dilationCharacterDim)
      + quadraticLightSpaceDim
        = quadraticConformalClosureDim :=
  quadratic_light_conformal_count

/--
Triality is placed in the `D₄ = so(4,4)` Levi layer of the quadratic route.

This is a dimension-normalized placement theorem, not the full `Spin(4,4)`
triality theorem.
-/
@[rep_depth krein]
def splitCl44_triality_levi_placement : TrialityLeviPlacement :=
  TrialityLeviPlacement.canonical

/--
The unital spin-factor route is not the same dimension count as the quadratic
`Cl(4,4) → V_{4,4} → so(5,5)` route.
-/
@[rep_depth krein]
theorem splitCl44_spin_factor_route_not_so55_count :
    ¬ spinFactorDim
        + (spinFactorStructureRotationDim + dilationCharacterDim)
        + spinFactorDim
          = quadraticConformalClosureDim :=
  SpinFactorConformalRoute.canonical_not_so55_count

/-! ## Weyl-neutral versus null: separate predicates -/

/-- Scale-neutral Weyl/log-density slice. -/
def IsWeylNeutral (ell : ℝ) : Prop :=
  ell = 0

/-- Metric-null condition for the split `(4,4)` quadratic form. -/
def IsMetricNull44 (v : SplitCl44Carrier) : Prop :=
  SplitCl44Quad v = 0

@[simp] theorem isWeylNeutral_iff (ell : ℝ) :
    IsWeylNeutral ell ↔ ell = 0 :=
  Iff.rfl

@[simp] theorem isMetricNull44_iff (v : SplitCl44Carrier) :
    IsMetricNull44 v ↔ SplitCl44Quad v = 0 :=
  Iff.rfl

/-- Explicit metric log-scale readout: use the split `(4,4)` quadratic value itself. -/
noncomputable def splitCl44MetricLogScale (v : SplitCl44Carrier) : ℝ :=
  SplitCl44Quad v

/--
For the explicit quadratic readout, Weyl-neutrality is exactly metric nullness.

This is not a general collapse of Weyl scale and nullness; it is the concrete
choice `ell(v) = Q(v)`.
-/
theorem splitCl44MetricLogScale_neutral_iff_metric_null
    (v : SplitCl44Carrier) :
    IsWeylNeutral (splitCl44MetricLogScale v) ↔ IsMetricNull44 v :=
  Iff.rfl

end InfoGeometry.Clifford.SplitCl44CausalEnvelope
