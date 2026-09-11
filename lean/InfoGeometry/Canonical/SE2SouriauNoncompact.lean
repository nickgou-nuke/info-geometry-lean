import InfoGeometry.Canonical.SE2SouriauCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The non-compact translation direction in `SE(2)`

The rotation-only carrier used for compact orbit arguments is compact.  The
full Euclidean carrier also contains an unrestricted translation coordinate,
so it cannot be compact.  This file records that distinction constructively.
-/

namespace InfoGeometry.Canonical.SE2SouriauCocycle

noncomputable def circleTranslationCarrier
    (p : Circle × Point2) : SE2RotationCarrier :=
  ⟨((p.1 : ℂ).re, (p.1 : ℂ).im, p.2.1, p.2.2), by
    have hz := p.1.2
    change (p.1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1 at hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Complex.norm_def] at hz
    have hnorm : Complex.normSq ((p.1 : ℂ)) = 1 := by
      nlinarith [Real.sq_sqrt (Complex.normSq_nonneg (p.1 : ℂ))]
    change (p.1 : ℂ).re ^ 2 + (p.1 : ℂ).im ^ 2 = 1
    simpa [pow_two, Complex.normSq_apply] using hnorm⟩

instance : PathConnectedSpace Circle := by
  exact ((AddCircle.homeomorphCircle (T := 2 * Real.pi) (by positivity)).surjective).pathConnectedSpace
    (AddCircle.homeomorphCircle (T := 2 * Real.pi) (by positivity)).continuous_toFun

theorem continuous_circleTranslationCarrier :
    Continuous (circleTranslationCarrier : Circle × Point2 → SE2RotationCarrier) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Circle × Point2 =>
    (((p.1 : ℂ).re, (p.1 : ℂ).im, p.2.1, p.2.2) : SE2Parameters))
  fun_prop

theorem circleTranslationCarrier_surjective :
    Function.Surjective circleTranslationCarrier := by
  intro g
  let z : Circle :=
    ⟨(g.1.1 : ℂ) + g.1.2.1 * Complex.I, by
      change (g.1.1 : ℂ) + g.1.2.1 * Complex.I ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right]
      rw [Complex.norm_def]
      have hnorm : Complex.normSq ((g.1.1 : ℂ) + g.1.2.1 * Complex.I) = 1 := by
        rw [Complex.normSq_apply]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im]
        have hg : g.1.1 ^ 2 + g.1.2.1 ^ 2 = 1 := by
          exact g.2
        nlinarith [hg]
      rw [hnorm]
      norm_num⟩
  refine ⟨(z, (g.1.2.2.1, g.1.2.2.2)), ?_⟩
  apply Subtype.ext
  change ((z : ℂ).re, (z : ℂ).im, g.1.2.2.1, g.1.2.2.2) = g.1
  simp [z]

instance : PathConnectedSpace SE2RotationCarrier := by
  letI : PathConnectedSpace Point2 := by
    rw [pathConnectedSpace_iff]
    constructor
    · exact ⟨(0, 0)⟩
    · intro x y
      exact ⟨(Joined.somePath ((pathConnectedSpace_iff ℝ).mp inferInstance |>.2 x.1 y.1)).prod
          (Joined.somePath ((pathConnectedSpace_iff ℝ).mp inferInstance |>.2 x.2 y.2))⟩
  letI : PathConnectedSpace (Circle × Point2) := by
    rw [pathConnectedSpace_iff]
    constructor
    · let z0 : Circle := ⟨1, by
        change (1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1
        simp⟩
      exact ⟨(z0, (0, 0))⟩
    · intro x y
      exact ⟨(Joined.somePath ((pathConnectedSpace_iff Circle).mp inferInstance |>.2 x.1 y.1)).prod
          (Joined.somePath ((pathConnectedSpace_iff Point2).mp inferInstance |>.2 x.2 y.2))⟩
  exact circleTranslationCarrier_surjective.pathConnectedSpace
    continuous_circleTranslationCarrier

def translationX (g : SE2RotationCarrier) : ℝ :=
  g.1.2.2.1

theorem continuous_translationX : Continuous translationX := by
  unfold translationX
  fun_prop

def translationLine (x : ℝ) : SE2RotationCarrier :=
  ⟨(1, 0, x, 0), by
    simp [se2RotationParameters, rotationConstraint]⟩

theorem translationX_translationLine (x : ℝ) :
    translationX (translationLine x) = x := rfl

theorem translationLine_zero :
    translationLine 0 = (1 : SE2RotationCarrier) := by
  apply Subtype.ext
  change (1, 0, 0, 0) = se2ParameterIdentity
  rfl

theorem translationLine_add (x y : ℝ) :
    translationLine (x + y) = translationLine x * translationLine y := by
  apply Subtype.ext
  change (1, 0, x + y, 0) =
    se2ParameterProduct 1 0 x 0 1 0 y 0
  dsimp [se2ParameterProduct]
  ring

theorem translationLine_neg (x : ℝ) :
    translationLine (-x) = (translationLine x)⁻¹ := by
  apply Subtype.ext
  change (1, 0, -x, 0) = se2ParameterInverse (1, 0, x, 0)
  dsimp [se2ParameterInverse]
  ring

theorem continuous_translationLine :
    Continuous translationLine := by
  unfold translationLine
  apply Continuous.subtype_mk
  fun_prop

theorem translationLine_injective :
    Function.Injective translationLine := by
  intro x y hxy
  have hreadout : translationX (translationLine x) =
      translationX (translationLine y) := congrArg translationX hxy
  simpa [translationX_translationLine] using hreadout

theorem translationLine_leftInverse :
    Function.LeftInverse translationX translationLine := by
  intro x
  exact translationX_translationLine x

theorem isEmbedding_translationLine :
    Topology.IsEmbedding translationLine := by
  exact translationLine_leftInverse.isEmbedding
    continuous_translationX continuous_translationLine

def translationLineLocus : Set SE2RotationCarrier :=
  {g | g.1.1 = 1 ∧ g.1.2.1 = 0 ∧ g.1.2.2.2 = 0}

theorem translationLine_range_eq_locus :
    Set.range translationLine = translationLineLocus := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    simp [translationLine, translationLineLocus]
  · intro hg
    refine ⟨g.1.2.2.1, ?_⟩
    apply Subtype.ext
    change (1, 0, g.1.2.2.1, 0) = g.1
    ext
    · exact hg.1.symm
    · exact hg.2.1.symm
    · rfl
    · exact hg.2.2.symm

theorem isClosed_translationLineLocus :
    IsClosed translationLineLocus := by
  have hc : IsClosed {g : SE2RotationCarrier | g.1.1 = (1 : ℝ)} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hs : IsClosed {g : SE2RotationCarrier | g.1.2.1 = (0 : ℝ)} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hty : IsClosed {g : SE2RotationCarrier | g.1.2.2.2 = (0 : ℝ)} := by
    exact isClosed_eq (by fun_prop) continuous_const
  simpa [translationLineLocus, Set.setOf_and] using (hc.inter (hs.inter hty))

def translationLineLocusHomeomorph :
    ℝ ≃ₜ translationLineLocus where
  toFun := fun x =>
    ⟨translationLine x, by
      rw [← translationLine_range_eq_locus]
      exact ⟨x, rfl⟩⟩
  invFun := fun g => translationX g.1
  left_inv := by
    intro x
    exact translationX_translationLine x
  right_inv := by
    intro g
    have hgrange : g.1 ∈ Set.range translationLine := by
      rw [translationLine_range_eq_locus]
      exact g.2
    rcases hgrange with ⟨x, hx⟩
    apply Subtype.ext
    have hcoord := congrArg translationX hx
    rw [translationX_translationLine] at hcoord
    change translationLine (translationX g.1) = g.1
    rw [← hcoord]
    exact hx
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_translationLine
  continuous_invFun :=
    continuous_translationX.comp continuous_subtype_val

theorem isClosedEmbedding_translationLine :
    Topology.IsClosedEmbedding translationLine := by
  refine Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap
    isEmbedding_translationLine ?_
  intro s hs
  have himage : Set.image translationLine s =
      translationLineLocus ∩ translationX ⁻¹' s := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← translationLine_range_eq_locus]
        exact ⟨x, rfl⟩
      · simpa [translationX_translationLine] using hx
    · rintro ⟨hg, hg_s⟩
      have hgrange : g ∈ Set.range translationLine := by
        rw [translationLine_range_eq_locus]
        exact hg
      rcases hgrange with ⟨x, hx⟩
      have hx_s : x ∈ s := by
        have hcoord := congrArg translationX hx
        rw [translationX_translationLine] at hcoord
        rw [hcoord]
        exact hg_s
      exact ⟨x, hx_s, hx⟩
  rw [himage]
  exact isClosed_translationLineLocus.inter (hs.preimage continuous_translationX)

theorem isClosedMap_translationLine :
    IsClosedMap translationLine := by
  exact isClosedEmbedding_translationLine.isClosedMap

theorem isProperMap_translationLine :
    IsProperMap translationLine := by
  exact isClosedEmbedding_translationLine.isProperMap

instance : PathConnectedSpace translationLineLocus := by
  exact translationLineLocusHomeomorph.surjective.pathConnectedSpace
    translationLineLocusHomeomorph.continuous_toFun

instance : ConnectedSpace translationLineLocus := by
  infer_instance

def translationLineContinuousMap :
    C(ℝ, SE2RotationCarrier) :=
  { toFun := translationLine
    continuous_toFun := continuous_translationLine }

theorem translationLineContinuousMap_apply (x : ℝ) :
    translationLineContinuousMap x = translationLine x := rfl

def translationLineContinuousMonoidHom :
    Multiplicative ℝ →ₜ* SE2RotationCarrier where
  toMonoidHom :=
    { toFun := fun x => translationLine x
      map_one' := translationLine_zero
      map_mul' := by
        intro x y
        change translationLine (Multiplicative.toAdd x + Multiplicative.toAdd y) =
          translationLine (Multiplicative.toAdd x) *
            translationLine (Multiplicative.toAdd y)
        exact translationLine_add (Multiplicative.toAdd x) (Multiplicative.toAdd y) }
  continuous_toFun := by
    exact continuous_translationLine

theorem range_translationX : Set.range translationX = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    exact ⟨translationLine x, translationX_translationLine x⟩

theorem not_compactSpace_SE2RotationCarrier :
    ¬ CompactSpace SE2RotationCarrier := by
  intro hcompact
  letI : CompactSpace SE2RotationCarrier := hcompact
  have hcompact_range : IsCompact (Set.range translationX) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image continuous_translationX
  have hcompact_real : IsCompact (Set.univ : Set ℝ) := by
    simpa [range_translationX] using hcompact_range
  letI : CompactSpace ℝ := ⟨hcompact_real⟩
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) inferInstance

end InfoGeometry.Canonical.SE2SouriauCocycle
