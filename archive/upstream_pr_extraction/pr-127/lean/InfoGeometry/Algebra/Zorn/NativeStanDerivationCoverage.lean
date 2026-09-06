import InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationTrace
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction
import InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge

noncomputable section
namespace InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage

open scoped BigOperators

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornDerivationTrace
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction
open InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical

abbrev VZ := ZornVectorMatrix ℝ
abbrev VDer := ZornVectorMatrix.Derivation (R := ℝ)
abbrev CZ := InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn
abbrev CDer := canonicalZornDerivations

theorem circularOperator_stanDerMap (x y z : CZ) :
    circularCoordinateLinearEquiv (directCanonicalStanDerMap x y z) =
      circularL x (circularL y (circularCoordinateLinearEquiv z)) -
          circularL y (circularL x (circularCoordinateLinearEquiv z)) +
        (circularL x (circularR y (circularCoordinateLinearEquiv z)) -
          circularR y (circularL x (circularCoordinateLinearEquiv z))) +
        (circularR x (circularR y (circularCoordinateLinearEquiv z)) -
          circularR y (circularR x (circularCoordinateLinearEquiv z))) := by
  rw [directCanonicalStanDerMap_apply]
  simp only [circularL_apply, circularR_apply,
    map_add, map_sub, LinearEquiv.symm_apply_apply]

theorem canonicalVectorEquiv_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → CZ) :
    canonicalVectorEquiv (s.sum f) = s.sum (fun i => canonicalVectorEquiv (f i)) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, canonicalVectorEquiv_add, ih]
      simp only [Finset.sum_insert ha, InfoGeometry.Algebra.zvm_add_def]

noncomputable def nativeCircularBasis (i : Fin 8) : VZ :=
  canonicalVectorEquiv
    (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i)

theorem chiralOperatorNativeReadout_nativeCircularBasis
    (g : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    nativeCircularBasis (chiralGeneratorIndex g) =
      canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
          (chiralOperatorNativeReadout g)) := by
  simp [nativeCircularBasis, chiralOperatorNativeReadout,
    chiralGeneratorIndex,
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularBasis_apply]

theorem chiralGeneratorIndex_surjective :
    Function.Surjective chiralGeneratorIndex := by
  native_decide

noncomputable def chiralNativeBasis
    (g : InfoGeometry.OperatorAlgebra.ChiralGenerator) : VZ :=
  nativeCircularBasis (chiralGeneratorIndex g)

theorem nativeCircularBasis_span_top :
    Submodule.span ℝ (Set.range nativeCircularBasis) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro X
  let Z : CZ := canonicalVectorEquiv.symm X
  have h := InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_reconstruct Z
  have hX := congrArg canonicalVectorEquiv h
  rw [canonicalVectorEquiv_sum] at hX
  have hZX : canonicalVectorEquiv Z = X := by simp [Z]
  have hm : ∑ i : Fin 8,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularCoordinate
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm Z) i •
        nativeCircularBasis i ∈
      Submodule.span ℝ (Set.range nativeCircularBasis) := by
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [← hZX, ← hX]
  simpa only [nativeCircularBasis, canonicalVectorEquiv_smul] using hm

theorem chiralNativeBasis_span_top :
    Submodule.span ℝ (Set.range chiralNativeBasis) = ⊤ := by
  have hrange : Set.range chiralNativeBasis = Set.range nativeCircularBasis := by
    ext X
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨chiralGeneratorIndex g, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases chiralGeneratorIndex_surjective i with ⟨g, hg⟩
      exact ⟨g, by simp [chiralNativeBasis, hg]⟩
  rw [hrange]
  exact nativeCircularBasis_span_top

noncomputable def chiralReadoutBasis
    (g : InfoGeometry.OperatorAlgebra.ChiralGenerator) : VZ :=
  canonicalVectorEquiv
    (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
      (chiralOperatorNativeReadout g))

theorem chiralReadoutBasis_eq_nativeCircularBasis
    (g : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    chiralReadoutBasis g = chiralNativeBasis g := by
  exact (chiralOperatorNativeReadout_nativeCircularBasis g).symm

theorem chiralReadoutBasis_injective :
    Function.Injective chiralReadoutBasis := by
  intro g h eq
  have hnative : chiralNativeBasis g = chiralNativeBasis h := by
    rw [← chiralReadoutBasis_eq_nativeCircularBasis g,
      ← chiralReadoutBasis_eq_nativeCircularBasis h]
    exact eq
  have hindex : chiralGeneratorIndex g = chiralGeneratorIndex h := by
    apply InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.injective
    exact congrArg canonicalVectorEquiv.symm hnative
  exact chiralGeneratorIndex_injective hindex

theorem chiralReadoutBasis_span_top :
    Submodule.span ℝ (Set.range chiralReadoutBasis) = ⊤ := by
  have hrange : Set.range chiralReadoutBasis = Set.range chiralNativeBasis := by
    ext X
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, (chiralReadoutBasis_eq_nativeCircularBasis g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, chiralReadoutBasis_eq_nativeCircularBasis g⟩
  rw [hrange]
  exact chiralNativeBasis_span_top

theorem canonicalVectorEquiv_stanDerMap (x y : VZ) (z : CZ) :
    stanDerMap (R := ℝ) x y (canonicalVectorEquiv z) =
      canonicalVectorEquiv
        (directCanonicalStanDerMap (canonicalVectorEquiv.symm x)
          (canonicalVectorEquiv.symm y) z) := by
  rw [directCanonicalStanDerMap_apply]
  simp only [stanDerMap, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, L_map, R_map, canonicalVectorEquiv_add,
    canonicalVectorEquiv_sub, canonicalVectorEquiv_mul]
  rfl

theorem vector_inner_to_canonical (x y : VZ) :
    vectorCanonicalLinearEquiv (innerDerivation x y) =
      canonicalStandardDerivationOfCanonical
        (canonicalVectorEquiv.symm x) (canonicalVectorEquiv.symm y) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  change canonicalVectorEquiv.symm
      (innerDerivation x y (canonicalVectorEquiv z)) = _
  rw [innerDerivation_apply_value, canonicalVectorEquiv_stanDerMap]
  rfl

theorem nativeInner_circularOperator (x y z : CZ) :
    circularCoordinateLinearEquiv
        (canonicalVectorEquiv.symm
          (innerDerivation (canonicalVectorEquiv x)
            (canonicalVectorEquiv y) (canonicalVectorEquiv z))) =
      circularL x (circularL y (circularCoordinateLinearEquiv z)) -
          circularL y (circularL x (circularCoordinateLinearEquiv z)) +
        (circularL x (circularR y (circularCoordinateLinearEquiv z)) -
          circularR y (circularL x (circularCoordinateLinearEquiv z))) +
        (circularR x (circularR y (circularCoordinateLinearEquiv z)) -
          circularR y (circularR x (circularCoordinateLinearEquiv z))) := by
  have h := canonicalVectorEquiv_stanDerMap
    (canonicalVectorEquiv x) (canonicalVectorEquiv y) z
  have h' := congrArg canonicalVectorEquiv.symm h
  have hcanon :
      canonicalVectorEquiv.symm
          (stanDerMap (R := ℝ) (canonicalVectorEquiv x)
            (canonicalVectorEquiv y) (canonicalVectorEquiv z)) =
        directCanonicalStanDerMap x y z := by
    simpa only [LinearEquiv.symm_apply_apply] using h'
  rw [innerDerivation_apply_value, hcanon]
  exact circularOperator_stanDerMap x y z

/-! The preceding transport identifies the span of native inner derivations
with the already-proved span of canonical standard derivations. -/
theorem vector_inner_derivations_span_top :
    Submodule.span ℝ
        (Set.range (fun p : VZ × VZ => innerDerivation p.1 p.2)) = ⊤ := by
  let S : Set VDer := Set.range (fun p : VZ × VZ => innerDerivation p.1 p.2)
  have hmap :
      (Submodule.span ℝ S).map
          (vectorCanonicalLinearEquiv : VDer →ₗ[ℝ] CDer) = ⊤ := by
    rw [Submodule.map_span]
    have himage :
        vectorCanonicalLinearEquiv '' S =
          Set.range (fun p : CZ × CZ =>
            canonicalStandardDerivationOfCanonical p.1 p.2) := by
      ext D
      constructor
      · rintro ⟨v, ⟨p, rfl⟩, rfl⟩
        rcases p with ⟨x, y⟩
        exact ⟨(canonicalVectorEquiv.symm x, canonicalVectorEquiv.symm y),
          (vector_inner_to_canonical x y).symm⟩
      · rintro ⟨p, rfl⟩
        rcases p with ⟨x, y⟩
        exact ⟨innerDerivation (canonicalVectorEquiv x)
            (canonicalVectorEquiv y),
          ⟨(canonicalVectorEquiv x, canonicalVectorEquiv y), rfl⟩,
          vector_inner_to_canonical (canonicalVectorEquiv x)
            (canonicalVectorEquiv y)⟩
    change Submodule.span ℝ (vectorCanonicalLinearEquiv '' S) = ⊤
    rw [himage]
    exact standardDerivations_span_top
  exact (Submodule.map_eq_top_iff
    (e := vectorCanonicalLinearEquiv)).mp hmap

theorem innerDerivation_pair_span_of_span_top
    {ι : Type*} (b : ι → VZ)
    (hb : Submodule.span ℝ (Set.range b) = ⊤) :
    Submodule.span ℝ
        (Set.range (fun p : ι × ι => innerDerivation (b p.1) (b p.2))) = ⊤ := by
  let T : Submodule ℝ VDer := Submodule.span ℝ
    (Set.range (fun p : ι × ι => innerDerivation (b p.1) (b p.2)))
  have hxy : ∀ x y : VZ, innerDerivation x y ∈ T := by
    intro x y
    have hx : x ∈ Submodule.span ℝ (Set.range b) := by
      rw [hb]
      exact Submodule.mem_top
    have hleft : ∀ x' : VZ,
        x' ∈ Submodule.span ℝ (Set.range b) →
        ∀ y' : VZ, y' ∈ Submodule.span ℝ (Set.range b) →
        innerDerivation x' y' ∈ T := by
      intro x' hx'
      refine Submodule.span_induction (p := fun u _hu =>
        ∀ v : VZ, v ∈ Submodule.span ℝ (Set.range b) →
          innerDerivation u v ∈ T) ?_ ?_ ?_ ?_ hx'
      · intro i hi v hv
        rcases hi with ⟨i, rfl⟩
        refine Submodule.span_induction (p := fun w _hw =>
          innerDerivation (b i) w ∈ T) ?_ ?_ ?_ ?_ hv
        · intro j hj
          rcases hj with ⟨j, rfl⟩
          exact Submodule.subset_span ⟨(i, j), rfl⟩
        · change innerDerivation (b i) 0 ∈ T
          rw [(innerDerivation (b i)).map_zero]
          exact T.zero_mem
        · intro w₁ w₂ hw₁ hw₂ h₁ h₂
          change innerDerivation (b i) (w₁ + w₂) ∈ T
          rw [(innerDerivation (b i)).map_add]
          exact T.add_mem h₁ h₂
        · intro r w hw h
          change innerDerivation (b i) (r • w) ∈ T
          rw [(innerDerivation (b i)).map_smul]
          exact T.smul_mem r h
      · intro v hv
        change innerDerivation 0 v ∈ T
        rw [innerDerivation.map_zero]
        exact T.zero_mem
      · intro u₁ u₂ hu₁ hu₂ h₁ h₂ v hv
        change innerDerivation (u₁ + u₂) v ∈ T
        rw [innerDerivation.map_add]
        exact T.add_mem (h₁ v hv) (h₂ v hv)
      · intro r u hu h v hv
        change innerDerivation (r • u) v ∈ T
        rw [innerDerivation.map_smul]
        exact T.smul_mem r (h v hv)
    exact hleft x hx y (by rw [hb]; exact Submodule.mem_top)
  apply Submodule.eq_top_iff'.mpr
  intro D
  have hD : D ∈ Submodule.span ℝ
      (Set.range (fun p : VZ × VZ => innerDerivation p.1 p.2)) := by
    rw [vector_inner_derivations_span_top]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun D _hD => D ∈ T) ?_ ?_ ?_ ?_ hD
  · intro D hD'
    rcases hD' with ⟨⟨x, y⟩, rfl⟩
    exact hxy x y
  · exact T.zero_mem
  · intro D E hD hE hD' hE'
    exact T.add_mem hD' hE'
  · intro r D hD hD'
    exact T.smul_mem r hD'

theorem circularPeirceBasis_vector_span_top :
    Submodule.span ℝ
        (Set.range (fun i : Fin 8 =>
          canonicalVectorLinearEquiv
            (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i))) = ⊤ := by
  simpa only [Module.Basis.map_apply] using
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.map
      canonicalVectorLinearEquiv).span_eq

noncomputable def nativeEllCircularBasis (i : Fin 8) : VZ :=
  canonicalVectorLinearEquiv
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i)

theorem nativeEllCircularBasis_span_top :
    Submodule.span ℝ (Set.range nativeEllCircularBasis) = ⊤ := by
  simpa only [nativeEllCircularBasis, Module.Basis.map_apply] using
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.map
      canonicalVectorLinearEquiv).span_eq

theorem nativeEllCircularPairDerivations_span_top :
    Submodule.span ℝ
        (Set.range (fun p : Fin 8 × Fin 8 =>
          innerDerivation (nativeEllCircularBasis p.1)
            (nativeEllCircularBasis p.2))) = ⊤ := by
  exact innerDerivation_pair_span_of_span_top
    nativeEllCircularBasis nativeEllCircularBasis_span_top

theorem circular_scalarPlus_nativeE11 :
    canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
          InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.scalarPlus) =
      InfoGeometry.Algebra.ZornVectorMatrix.E11 := by
  rw [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_scalarPlus]
  rfl

theorem circular_scalarMinus_nativeE22 :
    canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
          InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.scalarMinus) =
      InfoGeometry.Algebra.ZornVectorMatrix.E22 := by
  rw [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_scalarMinus]
  rfl

theorem circular_rootPlus_nativeU (i : Fin 3) :
    canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i)) =
      InfoGeometry.Algebra.ZornVectorMatrix.U i := by
  rw [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_rootPlus]
  ext j <;>
    simp [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
      InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
      InfoGeometry.Algebra.ZornVectorMatrix.U,
      InfoGeometry.Algebra.ZornVec3.basis,
      Pi.single_apply]

theorem circular_rootMinus_nativeV (i : Fin 3) :
    canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i)) =
      InfoGeometry.Algebra.ZornVectorMatrix.V i := by
  rw [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_rootMinus]
  ext j <;>
    simp [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
      InfoGeometry.Algebra.ZornVectorMatrix.V,
      InfoGeometry.Algebra.ZornVec3.basis,
      Pi.single_apply]

theorem canonicalColorCycle_nativeCircularBasis (i : Fin 8) :
    canonicalVectorEquiv
        (canonicalColorCycle
          (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i)) =
      nativeCircularBasis (cycleFrameIndex i) := by
  rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
  rw [canonicalColorCycle_circularFrame]
  simp [nativeCircularBasis]

theorem canonicalColorReflection_nativeCircularBasis (i : Fin 8) :
    canonicalVectorEquiv
        (canonicalColorReflection
          (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i)) =
      nativeCircularBasis (reflectionFrameIndex i) := by
  rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
  rw [canonicalColorReflection_circularFrame]
  simp [nativeCircularBasis]

theorem nativeCircularPairDerivations_span_top :
    Submodule.span ℝ
        (Set.range (fun p : Fin 8 × Fin 8 =>
          innerDerivation (nativeCircularBasis p.1)
            (nativeCircularBasis p.2))) = ⊤ := by
  exact innerDerivation_pair_span_of_span_top
    nativeCircularBasis nativeCircularBasis_span_top

theorem chiralOperatorPairDerivations_span_top :
    Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          innerDerivation (chiralNativeBasis p.1)
            (chiralNativeBasis p.2))) = ⊤ := by
  exact innerDerivation_pair_span_of_span_top
    chiralNativeBasis chiralNativeBasis_span_top

theorem chiralReadoutPairDerivations_span_top :
    Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          innerDerivation (chiralReadoutBasis p.1)
            (chiralReadoutBasis p.2))) = ⊤ := by
  exact innerDerivation_pair_span_of_span_top
    chiralReadoutBasis chiralReadoutBasis_span_top

theorem chiralReadoutPairDerivations_span_eq_nativeCircularPairDerivations_span :
    Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          innerDerivation (chiralReadoutBasis p.1)
            (chiralReadoutBasis p.2))) =
      Submodule.span ℝ
        (Set.range (fun p : Fin 8 × Fin 8 =>
          innerDerivation (nativeCircularBasis p.1)
            (nativeCircularBasis p.2))) := by
  rw [chiralReadoutPairDerivations_span_top,
    nativeCircularPairDerivations_span_top]

theorem nativeCircularPair_isLeibniz
    (p : Fin 8 × Fin 8) (x y : VZ) :
    innerDerivation (nativeCircularBasis p.1) (nativeCircularBasis p.2)
        (ZornVectorMatrix.mul x y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul
          (innerDerivation (nativeCircularBasis p.1)
            (nativeCircularBasis p.2) x) y)
        (ZornVectorMatrix.mul x
          (innerDerivation (nativeCircularBasis p.1)
            (nativeCircularBasis p.2) y)) := by
  exact innerDerivation_isLeibniz
    (nativeCircularBasis p.1) (nativeCircularBasis p.2) x y

theorem chiralReadoutPair_isLeibniz
    (p : InfoGeometry.OperatorAlgebra.ChiralGenerator ×
      InfoGeometry.OperatorAlgebra.ChiralGenerator) (x y : VZ) :
    innerDerivation (chiralReadoutBasis p.1) (chiralReadoutBasis p.2)
        (ZornVectorMatrix.mul x y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul
          (innerDerivation (chiralReadoutBasis p.1)
            (chiralReadoutBasis p.2) x) y)
        (ZornVectorMatrix.mul x
          (innerDerivation (chiralReadoutBasis p.1)
            (chiralReadoutBasis p.2) y)) := by
  exact innerDerivation_isLeibniz
    (chiralReadoutBasis p.1) (chiralReadoutBasis p.2) x y

theorem chiralReadoutPair_canonical_transport
    (g h : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    vectorCanonicalLinearEquiv
        (innerDerivation (chiralReadoutBasis g) (chiralReadoutBasis h)) =
      canonicalStandardDerivationOfCanonical
        (canonicalVectorEquiv.symm (chiralReadoutBasis g))
        (canonicalVectorEquiv.symm (chiralReadoutBasis h)) := by
  exact vector_inner_to_canonical (chiralReadoutBasis g)
    (chiralReadoutBasis h)

theorem chiralStanDerivation_eq_chiralReadoutCanonicalPair
    (g h : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    chiralStanDerivation g h =
      canonicalStandardDerivationOfCanonical
        (canonicalVectorEquiv.symm (chiralReadoutBasis g))
        (canonicalVectorEquiv.symm (chiralReadoutBasis h)) := by
  rw [chiralStanDerivation,
    chiralReadoutBasis_eq_nativeCircularBasis,
    chiralReadoutBasis_eq_nativeCircularBasis,
    chiralNativeBasis, chiralNativeBasis,
    nativeCircularBasis, nativeCircularBasis]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem chiralReadoutCanonicalPair_isLeibniz
    (p : InfoGeometry.OperatorAlgebra.ChiralGenerator ×
      InfoGeometry.OperatorAlgebra.ChiralGenerator) (x y : CZ) :
    (canonicalStandardDerivationOfCanonical
        (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
        (canonicalVectorEquiv.symm (chiralReadoutBasis p.2))).1 (x * y) =
      (canonicalStandardDerivationOfCanonical
          (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
          (canonicalVectorEquiv.symm (chiralReadoutBasis p.2))).1 x * y +
        x * (canonicalStandardDerivationOfCanonical
          (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
          (canonicalVectorEquiv.symm (chiralReadoutBasis p.2))).1 y := by
  exact (canonicalStandardDerivationOfCanonical
    (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
    (canonicalVectorEquiv.symm (chiralReadoutBasis p.2))).property x y

theorem chiralReadoutCanonicalPairDerivations_span_top :
    Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          canonicalStandardDerivationOfCanonical
            (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
            (canonicalVectorEquiv.symm (chiralReadoutBasis p.2)))) = ⊤ := by
  let S : Submodule ℝ VDer :=
    Submodule.span ℝ (Set.range (fun p :
      InfoGeometry.OperatorAlgebra.ChiralGenerator ×
        InfoGeometry.OperatorAlgebra.ChiralGenerator =>
      innerDerivation (chiralReadoutBasis p.1)
        (chiralReadoutBasis p.2)))
  have hS : S = ⊤ := by
    exact chiralReadoutPairDerivations_span_top
  have hmap : S.map (vectorCanonicalLinearEquiv : VDer →ₗ[ℝ] CDer) = ⊤ := by
    rw [hS, Submodule.map_top]
    exact LinearEquiv.range _
  have himage :
      vectorCanonicalLinearEquiv ''
          (Set.range (fun p :
            InfoGeometry.OperatorAlgebra.ChiralGenerator ×
              InfoGeometry.OperatorAlgebra.ChiralGenerator =>
            innerDerivation (chiralReadoutBasis p.1)
              (chiralReadoutBasis p.2))) =
        Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          canonicalStandardDerivationOfCanonical
            (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
            (canonicalVectorEquiv.symm (chiralReadoutBasis p.2))) := by
    ext D
    constructor
    · rintro ⟨D, ⟨⟨g, h⟩, rfl⟩, rfl⟩
      exact ⟨(g, h), (chiralReadoutPair_canonical_transport g h).symm⟩
    · rintro ⟨⟨g, h⟩, rfl⟩
      exact ⟨innerDerivation (chiralReadoutBasis g)
          (chiralReadoutBasis h),
        ⟨(g, h), rfl⟩,
        chiralReadoutPair_canonical_transport g h⟩
  rw [Submodule.map_span] at hmap
  change Submodule.span ℝ
      (vectorCanonicalLinearEquiv ''
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          innerDerivation (chiralReadoutBasis p.1)
            (chiralReadoutBasis p.2)))) = ⊤ at hmap
  rw [himage] at hmap
  exact hmap

theorem chiralReadoutCanonicalPairDerivations_span_eq_standardDerivationSpan :
    Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          canonicalStandardDerivationOfCanonical
            (canonicalVectorEquiv.symm (chiralReadoutBasis p.1))
            (canonicalVectorEquiv.symm (chiralReadoutBasis p.2)))) =
      standardDerivationSpan := by
  rw [chiralReadoutCanonicalPairDerivations_span_top,
    standardDerivations_span_top]

end InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
