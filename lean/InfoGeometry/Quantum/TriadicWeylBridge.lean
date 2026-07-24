import InfoGeometry.Quantum.TriadicBogoliubovBridge
import InfoGeometry.Canonical.MongeAmpereDualSheetBridge
import InfoGeometry.Canonical.WeylGaugeOperatorLift
import InfoGeometry.Canonical.DrazinInfiniteCore

namespace InfoGeometry.Quantum.TriadicWeylBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.WeylGaugeOperatorLift
open InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut
open InfoGeometry.Quantum.TriadicBogoliubovBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
/-- A doubled-space generator is Weyl-compatible when both cross-sheet blocks vanish. -/
@[rep_depth operator]
def IsWeylCompatible (H : EndH) : Prop :=
  plusToMinusBlockMap (E := E) H = 0 ∧ minusToPlusBlockMap (E := E) H = 0

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem to_doubled_eq_plusPoint_add_minusPoint
    (x ξ : E) :
    (to_doubled x ξ : H₂) = plusPoint (E := E) x + minusPoint (E := E) ξ := by
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint, to_doubled]

omit [CompleteSpace E] in
private theorem apply_plusPoint_eq_of_isWeylCompatible
    {H : EndH} (hH : IsWeylCompatible (E := E) H) (x : E) :
    H (plusPoint (E := E) x) = plusPoint (E := E) (plusBlockMap (E := E) H x) := by
  apply DoubledSpace.ext
  · simp [plusBlockMap, plusPointL, ContinuousLinearMap.comp_apply]
  · have hsnd := congrArg (fun A : E →L[ℝ] E => A x) hH.1
    simpa [plusToMinusBlockMap, plusPointL, plusPoint, ContinuousLinearMap.comp_apply] using hsnd

omit [CompleteSpace E] in
private theorem apply_minusPoint_eq_of_isWeylCompatible
    {H : EndH} (hH : IsWeylCompatible (E := E) H) (ξ : E) :
    H (minusPoint (E := E) ξ) = minusPoint (E := E) (minusBlockMap (E := E) H ξ) := by
  apply DoubledSpace.ext
  · have hfst := congrArg (fun A : E →L[ℝ] E => A ξ) hH.2
    simpa [minusToPlusBlockMap, minusPointL, minusPoint, ContinuousLinearMap.comp_apply] using hfst
  · simp [minusBlockMap, minusPointL, ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
private theorem apply_to_doubled_eq_of_isWeylCompatible
    {H : EndH} (hH : IsWeylCompatible (E := E) H) (x ξ : E) :
    H (to_doubled x ξ : H₂) =
      to_doubled (plusBlockMap (E := E) H x) (minusBlockMap (E := E) H ξ) := by
  rw [to_doubled_eq_plusPoint_add_minusPoint (E := E) x ξ, map_add,
    apply_plusPoint_eq_of_isWeylCompatible (E := E) hH x,
    apply_minusPoint_eq_of_isWeylCompatible (E := E) hH ξ]
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint, to_doubled]

omit [CompleteSpace E] in
/-- Structural form: Weyl compatibility is exactly commutation with the doubled-sheet sign
involution `ε`. -/
@[rep_depth operator]
theorem isWeylCompatible_iff_comp_spectralEpsilon
    (H : EndH) :
    IsWeylCompatible (E := E) H ↔
      H.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp H := by
  constructor
  · intro hH
    apply ContinuousLinearMap.ext
    intro u
    have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
      apply DoubledSpace.ext <;> simp [to_doubled]
    rw [← hu]
    calc
      H.comp (spectral_epsilon (E := E)) (to_doubled (WithLp.fst u) (WithLp.snd u))
          = H (to_doubled (WithLp.fst u) (-WithLp.snd u)) := by
              simp [ContinuousLinearMap.comp_apply]
      _ = to_doubled (plusBlockMap (E := E) H (WithLp.fst u))
            (minusBlockMap (E := E) H (-WithLp.snd u)) := by
              rw [apply_to_doubled_eq_of_isWeylCompatible (E := E) hH]
      _ = to_doubled (plusBlockMap (E := E) H (WithLp.fst u))
            (-(minusBlockMap (E := E) H (WithLp.snd u))) := by
              simp
      _ = spectral_epsilon (E := E) (to_doubled (plusBlockMap (E := E) H (WithLp.fst u))
            (minusBlockMap (E := E) H (WithLp.snd u))) := by
              simp
      _ = (spectral_epsilon (E := E)) (H (to_doubled (WithLp.fst u) (WithLp.snd u))) := by
              rw [apply_to_doubled_eq_of_isWeylCompatible (E := E) hH]
      _ = (spectral_epsilon (E := E)).comp H (to_doubled (WithLp.fst u) (WithLp.snd u)) := by
              rfl
  · intro hcomm
    constructor
    · ext x
      have hx := congrArg (fun F : EndH => F (plusPoint (E := E) x)) hcomm
      have hsnd : WithLp.snd (H (plusPoint (E := E) x)) = -WithLp.snd (H (plusPoint (E := E) x)) := by
        simpa [ContinuousLinearMap.comp_apply, plusPoint] using congrArg WithLp.snd hx
      rw [eq_neg_iff_add_eq_zero] at hsnd
      have htwo : (2 : ℝ) • WithLp.snd (H (plusPoint (E := E) x)) = 0 := by
        simpa [two_smul] using hsnd
      have hzero : WithLp.snd (H (plusPoint (E := E) x)) = 0 :=
        (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      simpa [plusToMinusBlockMap, plusPointL, ContinuousLinearMap.comp_apply] using hzero
    · ext ξ
      have hξ := congrArg (fun F : EndH => F (minusPoint (E := E) ξ)) hcomm
      have hminus : spectral_epsilon (E := E) (minusPoint (E := E) ξ) = -(minusPoint (E := E) ξ) := by
        apply DoubledSpace.ext <;> simp [minusPoint, spectral_epsilon_apply]
      have hξ' : H (-(minusPoint (E := E) ξ)) = spectral_epsilon (E := E) (H (minusPoint (E := E) ξ)) := by
        calc
          H (-(minusPoint (E := E) ξ)) = H (spectral_epsilon (E := E) (minusPoint (E := E) ξ)) := by rw [hminus]
          _ = spectral_epsilon (E := E) (H (minusPoint (E := E) ξ)) := by
                simpa [ContinuousLinearMap.comp_apply] using hξ
      have hfst : -WithLp.fst (H (minusPoint (E := E) ξ)) = WithLp.fst (H (minusPoint (E := E) ξ)) := by
        simpa [ContinuousLinearMap.map_neg] using congrArg WithLp.fst hξ'
      have hfst' : WithLp.fst (H (minusPoint (E := E) ξ)) = -WithLp.fst (H (minusPoint (E := E) ξ)) := by
        simpa using congrArg Neg.neg hfst
      rw [eq_neg_iff_add_eq_zero] at hfst'
      have htwo : (2 : ℝ) • WithLp.fst (H (minusPoint (E := E) ξ)) = 0 := by
        simpa [two_smul] using hfst'
      have hzero : WithLp.fst (H (minusPoint (E := E) ξ)) = 0 :=
        (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      simpa [minusToPlusBlockMap, minusPointL, ContinuousLinearMap.comp_apply] using hzero

omit [CompleteSpace E] in
@[simp] theorem plusProjectorFlux_eq_zero_of_isWeylCompatible
    {H : EndH} (hH : IsWeylCompatible (E := E) H) :
    plusProjectorFlux (E := E) H = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  simp [plusProjectorFlux, spectralPlusProj_apply_to_doubled,
    apply_to_doubled_eq_of_isWeylCompatible (E := E) hH, plusPoint, to_doubled]

omit [CompleteSpace E] in
@[simp] theorem minusProjectorFlux_eq_zero_of_isWeylCompatible
    {H : EndH} (hH : IsWeylCompatible (E := E) H) :
    minusProjectorFlux (E := E) H = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  simp [minusProjectorFlux, spectralMinusProj_apply_to_doubled,
    apply_to_doubled_eq_of_isWeylCompatible (E := E) hH, minusPoint, to_doubled]

omit [CompleteSpace E] in
theorem isWeylCompatible_of_plusProjectorFlux_eq_zero
    {H : EndH} (hflux : plusProjectorFlux (E := E) H = 0) :
    IsWeylCompatible (E := E) H := by
  constructor
  · ext x
    have hx := congrArg (fun F : EndH => F (plusPoint (E := E) x)) hflux
    have hsnd : -WithLp.snd (H (plusPoint (E := E) x)) = 0 := by
      simpa [plusProjectorFlux, ContinuousLinearMap.comp_apply,
        spectralPlusProj_apply_eq_plusPoint, plusPoint] using congrArg WithLp.snd hx
    have hzero : WithLp.snd (H (plusPoint (E := E) x)) = 0 := by
      simpa using neg_eq_iff_add_eq_zero.mp hsnd
    simpa [plusToMinusBlockMap, plusPointL, ContinuousLinearMap.comp_apply] using hzero
  · ext ξ
    have hξ := congrArg (fun F : EndH => F (minusPoint (E := E) ξ)) hflux
    have hfst' : WithLp.fst (H (minusPoint (E := E) ξ)) - WithLp.fst (H (to_doubled 0 0 : H₂)) = 0 := by
      simpa [plusProjectorFlux, ContinuousLinearMap.comp_apply,
        spectralPlusProj_apply_eq_plusPoint, minusPoint, plusPoint, to_doubled] using congrArg WithLp.fst hξ
    have hH0 : H (to_doubled 0 0 : H₂) = 0 := by
      have h0 : (to_doubled 0 0 : H₂) = 0 := by apply DoubledSpace.ext <;> simp [to_doubled]
      rw [h0, H.map_zero]
    have hzero0 : WithLp.fst (H (to_doubled 0 0 : H₂)) = 0 := by
      rw [hH0]
      simp
    have hfst : WithLp.fst (H (minusPoint (E := E) ξ)) = 0 := by
      rw [hzero0, sub_zero] at hfst'
      exact hfst'
    simpa [minusToPlusBlockMap, minusPointL, ContinuousLinearMap.comp_apply] using hfst

omit [CompleteSpace E] in
theorem isWeylCompatible_of_minusProjectorFlux_eq_zero
    {H : EndH} (hflux : minusProjectorFlux (E := E) H = 0) :
    IsWeylCompatible (E := E) H := by
  constructor
  · ext x
    have hx := congrArg (fun F : EndH => F (plusPoint (E := E) x)) hflux
    have hsnd' : WithLp.snd (H (plusPoint (E := E) x)) - WithLp.snd (H (to_doubled 0 0 : H₂)) = 0 := by
      simpa [minusProjectorFlux, ContinuousLinearMap.comp_apply,
        spectralMinusProj_apply_eq_minusPoint, plusPoint, minusPoint, to_doubled] using congrArg WithLp.snd hx
    have hH0 : H (to_doubled 0 0 : H₂) = 0 := by
      have h0 : (to_doubled 0 0 : H₂) = 0 := by apply DoubledSpace.ext <;> simp [to_doubled]
      rw [h0, H.map_zero]
    have hzero0 : WithLp.snd (H (to_doubled 0 0 : H₂)) = 0 := by
      rw [hH0]
      simp
    have hsnd : WithLp.snd (H (plusPoint (E := E) x)) = 0 := by
      rw [hzero0, sub_zero] at hsnd'
      exact hsnd'
    simpa [plusToMinusBlockMap, plusPointL, ContinuousLinearMap.comp_apply] using hsnd
  · ext ξ
    have hξ := congrArg (fun F : EndH => F (minusPoint (E := E) ξ)) hflux
    have hfst : -WithLp.fst (H (minusPoint (E := E) ξ)) = 0 := by
      simpa [minusProjectorFlux, ContinuousLinearMap.comp_apply,
        spectralMinusProj_apply_eq_minusPoint, minusPoint] using congrArg WithLp.fst hξ
    have hzero : WithLp.fst (H (minusPoint (E := E) ξ)) = 0 := by
      simpa using neg_eq_iff_add_eq_zero.mp hfst
    simpa [minusToPlusBlockMap, minusPointL, ContinuousLinearMap.comp_apply] using hzero

omit [CompleteSpace E] in
theorem isWeylCompatible_iff_plusProjectorFlux_eq_zero
    (H : EndH) :
    IsWeylCompatible (E := E) H ↔ plusProjectorFlux (E := E) H = 0 := by
  constructor
  · exact plusProjectorFlux_eq_zero_of_isWeylCompatible (E := E)
  · exact isWeylCompatible_of_plusProjectorFlux_eq_zero (E := E)

omit [CompleteSpace E] in
theorem isWeylCompatible_iff_minusProjectorFlux_eq_zero
    (H : EndH) :
    IsWeylCompatible (E := E) H ↔ minusProjectorFlux (E := E) H = 0 := by
  constructor
  · exact minusProjectorFlux_eq_zero_of_isWeylCompatible (E := E)
  · exact isWeylCompatible_of_minusProjectorFlux_eq_zero (E := E)

omit [CompleteSpace E] in
theorem isWeylCompatible_iff_commutes_spectralPlusProj
    (H : EndH) :
    IsWeylCompatible (E := E) H ↔
      (spectralPlusProj (E := E)).comp H = H.comp (spectralPlusProj (E := E)) := by
  rw [isWeylCompatible_iff_plusProjectorFlux_eq_zero]
  unfold plusProjectorFlux
  exact sub_eq_zero

omit [CompleteSpace E] in
theorem isWeylCompatible_iff_commutes_spectralMinusProj
    (H : EndH) :
    IsWeylCompatible (E := E) H ↔
      (spectralMinusProj (E := E)).comp H = H.comp (spectralMinusProj (E := E)) := by
  rw [isWeylCompatible_iff_minusProjectorFlux_eq_zero]
  unfold minusProjectorFlux
  exact sub_eq_zero

private theorem kreinInner_plusSheet_minusPoint_eq_zero
    {u : H₂} (hu : u ∈ plusSheet (E := E)) (ξ : E) :
    KreinSpace.kreinInner (H := H₂) u (minusPoint (E := E) ξ) = 0 := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu, krein_inner_prod_l2 (E := E)]
  simp [plusPoint, minusPoint, to_doubled]

private theorem kreinInner_minusSheet_plusPoint_eq_zero
    {u : H₂} (hu : u ∈ minusSheet (E := E)) (x : E) :
    KreinSpace.kreinInner (H := H₂) u (plusPoint (E := E) x) = 0 := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu, krein_inner_prod_l2 (E := E)]
  simp [plusPoint, minusPoint, to_doubled]

/-- A Krein dyad with both legs on the positive spectral sheet is Weyl-compatible. -/
theorem dyadicKrein_isWeylCompatible_of_mem_plusSheet
    {u v : H₂}
    (hu : u ∈ plusSheet (E := E)) (hv : v ∈ plusSheet (E := E)) :
    IsWeylCompatible (E := E) (dyadicKrein (E := E) u v) := by
  constructor
  · ext x
    have hsnd : WithLp.snd u = 0 := (mem_plusSheet_iff_snd_eq_zero (E := E) u).mp hu
    change WithLp.snd (dyadicKrein (E := E) u v (plusPoint (E := E) x)) = 0
    rw [dyadicKrein_apply]
    simp [hsnd]
  · ext ξ
    have hmix : KreinSpace.kreinInner (H := H₂) v (minusPoint (E := E) ξ) = 0 :=
      kreinInner_plusSheet_minusPoint_eq_zero (E := E) hv ξ
    change WithLp.fst (dyadicKrein (E := E) u v (minusPoint (E := E) ξ)) = 0
    rw [dyadicKrein_apply, hmix]
    simp

/-- A Krein dyad with both legs on the negative spectral sheet is Weyl-compatible. -/
theorem dyadicKrein_isWeylCompatible_of_mem_minusSheet
    {u v : H₂}
    (hu : u ∈ minusSheet (E := E)) (hv : v ∈ minusSheet (E := E)) :
    IsWeylCompatible (E := E) (dyadicKrein (E := E) u v) := by
  constructor
  · ext x
    have hmix : KreinSpace.kreinInner (H := H₂) v (plusPoint (E := E) x) = 0 :=
      kreinInner_minusSheet_plusPoint_eq_zero (E := E) hv x
    change WithLp.snd (dyadicKrein (E := E) u v (plusPoint (E := E) x)) = 0
    rw [dyadicKrein_apply, hmix]
    simp
  · ext ξ
    have hfst : WithLp.fst u = 0 := (mem_minusSheet_iff_fst_eq_zero (E := E) u).mp hu
    change WithLp.fst (dyadicKrein (E := E) u v (minusPoint (E := E) ξ)) = 0
    rw [dyadicKrein_apply]
    simp [hfst]

@[simp] theorem plusToMinusBlockMap_triadicGenerator {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂) :
    plusToMinusBlockMap (E := E) (triadicGenerator (E := E) w q a) =
      ∑ i, w i • plusToMinusBlockMap (E := E) (dyadicKrein (E := E) (q i) (a i)) := by
  ext x
  simp [plusToMinusBlockMap, triadicGenerator, ContinuousLinearMap.comp_apply]

@[simp] theorem minusToPlusBlockMap_triadicGenerator {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂) :
    minusToPlusBlockMap (E := E) (triadicGenerator (E := E) w q a) =
      ∑ i, w i • minusToPlusBlockMap (E := E) (dyadicKrein (E := E) (q i) (a i)) := by
  ext x
  simp [minusToPlusBlockMap, triadicGenerator, ContinuousLinearMap.comp_apply]

@[rep_depth operator]
theorem triadicGenerator_blockDiagonal_of_compatibility {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂)
    (h_compat : ∀ i, IsWeylCompatible (E := E) (dyadicKrein (E := E) (q i) (a i))) :
    IsWeylCompatible (E := E) (triadicGenerator (E := E) w q a) := by
  constructor
  · rw [plusToMinusBlockMap_triadicGenerator]
    apply Finset.sum_eq_zero
    intro i _
    simp [(h_compat i).1]
  · rw [minusToPlusBlockMap_triadicGenerator]
    apply Finset.sum_eq_zero
    intro i _
    simp [(h_compat i).2]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Under Weyl compatibility and scalar diagonal block hypotheses, an operator is exactly the
common-plus-relative `ε` form. -/
@[rep_depth operator]
theorem eq_common_relative_form_of_scalarBlocks
    (H : EndH) {α β : ℝ}
    (hH : IsWeylCompatible (E := E) H)
    (hplus : plusBlockMap (E := E) H = α • ContinuousLinearMap.id ℝ E)
    (hminus : minusBlockMap (E := E) H = β • ContinuousLinearMap.id ℝ E) :
    H = ((α + β) / 2) • (ContinuousLinearMap.id ℝ H₂)
      + ((α - β) / 2) • (spectral_epsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  apply DoubledSpace.ext
  · have hplusu := congrArg (fun A : E →L[ℝ] E => A (WithLp.fst u)) hplus
    have hα : ((α + β) / 2 : ℝ) + (α - β) / 2 = α := by ring
    calc
      WithLp.fst (H (to_doubled (WithLp.fst u) (WithLp.snd u)))
          = plusBlockMap (E := E) H (WithLp.fst u) := by
              rw [apply_to_doubled_eq_of_isWeylCompatible (E := E) hH]
              simp [to_doubled]
      _ = α • WithLp.fst u := by
              simpa [ContinuousLinearMap.id_apply] using hplusu
      _ = (((α + β) / 2 : ℝ) + (α - β) / 2) • WithLp.fst u := by rw [hα]
      _ = WithLp.fst ((((α + β) / 2) • (ContinuousLinearMap.id ℝ H₂)
            + ((α - β) / 2) • (spectral_epsilon (E := E))) (to_doubled (WithLp.fst u) (WithLp.snd u))) := by
              simp [ContinuousLinearMap.add_apply, spectral_epsilon_apply, to_doubled, add_smul]
  · have hminusu := congrArg (fun A : E →L[ℝ] E => A (WithLp.snd u)) hminus
    have hβ : ((α + β) / 2 : ℝ) + -((α - β) / 2) = β := by ring
    calc
      WithLp.snd (H (to_doubled (WithLp.fst u) (WithLp.snd u)))
          = minusBlockMap (E := E) H (WithLp.snd u) := by
              rw [apply_to_doubled_eq_of_isWeylCompatible (E := E) hH]
              simp [to_doubled]
      _ = β • WithLp.snd u := by
              simpa [ContinuousLinearMap.id_apply] using hminusu
      _ = (((α + β) / 2 : ℝ) + -((α - β) / 2)) • WithLp.snd u := by rw [hβ]
      _ = WithLp.snd ((((α + β) / 2) • (ContinuousLinearMap.id ℝ H₂)
            + ((α - β) / 2) • (spectral_epsilon (E := E))) (to_doubled (WithLp.fst u) (WithLp.snd u))) := by
              simp [ContinuousLinearMap.add_apply, spectral_epsilon_apply, to_doubled, add_smul, neg_smul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Exact logarithmic Weyl identification under explicit scalar block hypotheses. -/
@[rep_depth operator]
theorem eq_logarithmicGenerator_of_scalarSheetBlocks
    (H : EndH) (g : LiftedSheetAut (E := E))
    (hH : IsWeylCompatible (E := E) H)
    (hplus : plusBlockMap (E := E) H = logPlusVolume g • ContinuousLinearMap.id ℝ E)
    (hminus : minusBlockMap (E := E) H = logMinusVolume g • ContinuousLinearMap.id ℝ E) :
    H = logarithmicGenerator g := by
  simpa [logarithmicGenerator, commonLogCoordinate, relativeLogCoordinate,
    InfoGeometry.Krein.spectral_epsilon] using
    eq_common_relative_form_of_scalarBlocks (E := E) H hH hplus hminus

end FiniteDimensional

end InfoGeometry.Quantum.TriadicWeylBridge
