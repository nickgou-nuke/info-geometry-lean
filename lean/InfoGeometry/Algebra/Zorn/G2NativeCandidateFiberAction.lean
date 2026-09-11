import InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberActionReadback
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberOrbitAssembly
import InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction

/-!
# Stabilizer action on the native candidate fibre

The quotient action is defined on all native candidates.  This owner records
the stronger fact needed when the candidate is known to lie over the base
point: a stabilizer element keeps it in that fibre.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction

open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberActionReadback
open InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberOrbitAssembly
open InfoGeometry.Algebra.Zorn.G2NativePointTransitivity
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev NativeBaseCandidate :=
  {y : G2ParabolicLineCarrier.OctImF2 //
    nativeCandidateAt nativeBasePoint y}

theorem baseLineVector_nativeCandidateAt :
    nativeCandidateAt nativeBasePoint baseLineVector := by
  native_decide +revert

noncomputable def baseNativeCandidate : NativeBaseCandidate :=
  ⟨baseLineVector, baseLineVector_nativeCandidateAt⟩

theorem baseLineVector_lineSet_eq_lineZero :
    lineSet baseLineVector = lineZero.1 := by
  rfl

noncomputable def baseNativeCandidateAsCandidate : NativeCandidate :=
  ⟨baseLineVector, baseLineVector_mem_candidates⟩

theorem candidateLine_baseNativeCandidateAsCandidate :
    candidateLine baseNativeCandidateAsCandidate = lineZero := by
  apply Subtype.ext
  exact baseLineVector_lineSet_eq_lineZero

def nativeBaseCandidateAction
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    NativeBaseCandidate → NativeBaseCandidate :=
  fun y =>
    ⟨octImAction g y.1,
      nativeCandidateAt_map_of_fix g hg y.1 y.2⟩

@[simp] theorem nativeBaseCandidateAction_val
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : NativeBaseCandidate) :
    (nativeBaseCandidateAction g hg y).1 = octImAction g y.1 :=
  rfl

theorem nativeBaseCandidateAction_one (y : NativeBaseCandidate) :
    nativeBaseCandidateAction (1 : SplitOctF2Aut)
      (by
        exact InfoGeometry.Algebra.Zorn.G2NativeLineFiber.octImAction_one
          nativeBasePoint) y = y := by
  apply Subtype.ext
  change octImAction (1 : SplitOctF2Aut) y.1 = y.1
  exact InfoGeometry.Algebra.Zorn.G2NativeLineFiber.octImAction_one y.1

theorem nativeBaseCandidateAction_mul
    (g h : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (hh : octImAction h nativeBasePoint = nativeBasePoint)
    (y : NativeBaseCandidate) :
    nativeBaseCandidateAction (g * h)
      (by
        rw [octImAction_mul, hh, hg]) y =
      nativeBaseCandidateAction g hg
        (nativeBaseCandidateAction h hh y) := by
  apply Subtype.ext
  change octImAction (g * h) y.1 =
    octImAction g (octImAction h y.1)
  exact octImAction_mul g h y.1

noncomputable instance : MulAction nativePointStabilizer NativeBaseCandidate where
  smul g y :=
    nativeBaseCandidateAction g.1
      (nativePointStabilizer_fixes_base_point g.2) y
  one_smul y := by
    exact nativeBaseCandidateAction_one y
  mul_smul g h y := by
    exact nativeBaseCandidateAction_mul g.1 h.1
      (nativePointStabilizer_fixes_base_point g.2)
      (nativePointStabilizer_fixes_base_point h.2) y

theorem nativeBaseCandidateAction_surjective
    (g : nativePointStabilizer) :
    Function.Surjective (fun y : NativeBaseCandidate => g • y) := by
  intro y
  refine ⟨g⁻¹ • y, ?_⟩
  change g • (g⁻¹ • y) = y
  rw [← mul_smul]
  simp

theorem nativeBaseCandidateAction_injective
    (g : nativePointStabilizer) :
    Function.Injective (fun y : NativeBaseCandidate => g • y) := by
  intro x y hxy
  have h := congrArg (fun z : NativeBaseCandidate => g⁻¹ • z) hxy
  simpa [← mul_smul] using h

noncomputable def nativeBaseCandidateActionEquiv
    (g : nativePointStabilizer) :
    NativeBaseCandidate ≃ NativeBaseCandidate :=
  Equiv.ofBijective (fun y : NativeBaseCandidate => g • y)
    ⟨nativeBaseCandidateAction_injective g,
      nativeBaseCandidateAction_surjective g⟩

@[simp] theorem nativeBaseCandidateActionEquiv_apply
    (g : nativePointStabilizer) (y : NativeBaseCandidate) :
    nativeBaseCandidateActionEquiv g y = g • y :=
  rfl

theorem nativeBaseCandidateActionEquiv_mul
    (g h : nativePointStabilizer) :
    nativeBaseCandidateActionEquiv (g * h) =
      (nativeBaseCandidateActionEquiv h).trans
        (nativeBaseCandidateActionEquiv g) := by
  apply Equiv.ext
  intro y
  apply Subtype.ext
  simp only [nativeBaseCandidateActionEquiv_apply, Equiv.trans_apply]
  exact congrArg Subtype.val (mul_smul g h y)

theorem nativeBaseCandidateAction_inverse_apply
    (g : nativePointStabilizer) (y : NativeBaseCandidate) :
    g⁻¹ • (g • y) = y := by
  rw [← mul_smul]
  simp

theorem nativeBaseCandidateAction_left_inverse_apply
    (g : nativePointStabilizer) (y : NativeBaseCandidate) :
    g • (g⁻¹ • y) = y := by
  rw [← mul_smul]
  simp

theorem candidateLine_nativeBaseCandidateAction
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : NativeBaseCandidate) :
    candidateLine
        ⟨(nativeBaseCandidateAction g hg y).1,
          by
            simpa [candidates, kernelCandidate] using
              (nativeBaseCandidateAction g hg y).2⟩ =
      nativeLineAction g hg (candidateLine
        ⟨y.1, by simpa [candidates, kernelCandidate] using y.2⟩) := by
  apply Subtype.ext
  change lineSet (octImAction g y.1) =
    ((nativeLineFiberMap g nativeBasePoint)
      ⟨lineSet y.1, lineSet_mem_nativeLines y.1
        (by simpa [candidates, kernelCandidate] using y.2)⟩).1
  exact (nativeLineFiberMap_val_lineSet g hg y.1
    (by simpa [candidates, kernelCandidate] using y.2)).symm

theorem candidateLine_baseNativeCandidateAction
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    candidateLine
        ⟨(nativeBaseCandidateAction g hg baseNativeCandidate).1,
          by simpa [candidates, kernelCandidate] using
            (nativeBaseCandidateAction g hg baseNativeCandidate).2⟩ =
      nativeLineAction g hg lineZero := by
  simpa [baseNativeCandidateAsCandidate,
    candidateLine_baseNativeCandidateAsCandidate] using
    (candidateLine_nativeBaseCandidateAction g hg baseNativeCandidate)

theorem exists_nativeCandidate_mapping_to_line
    (L : NativeLine) :
    ∃ g : nativePointStabilizer,
      candidateLine
          ⟨(nativeBaseCandidateAction g.1
              (nativePointStabilizer_fixes_base_point g.2)
              baseNativeCandidate).1,
            by simpa [candidates, kernelCandidate] using
              (nativeBaseCandidateAction g.1
                (nativePointStabilizer_fixes_base_point g.2)
                baseNativeCandidate).2⟩ = L := by
  obtain ⟨g, hg⟩ := baseIntrinsicLine_orbit_surjective L
  refine ⟨g, ?_⟩
  exact (candidateLine_baseNativeCandidateAction g.1
    (nativePointStabilizer_fixes_base_point g.2)).trans hg

theorem nativeLineFiberMap_preimage_of_point_eq
    (g : SplitOctF2Aut)
    (q : G2ParabolicLineCarrier.OctImF2)
    (hp : octImAction g nativeBasePoint = q)
    (L : NativeLinesThroughPoint q) :
    ∃ L₀ : NativeLine,
      cast (congrArg NativeLinesThroughPoint hp)
        (nativeLineFiberMap g nativeBasePoint L₀) = L := by
  cases hp
  obtain ⟨L₀, hL₀⟩ := (nativeLineFiberMap g nativeBasePoint).surjective L
  exact ⟨L₀, hL₀⟩

theorem nativeFlagMap_baseLine_eq_of_transport
    (g : SplitOctF2Aut)
    (p : OctImIsotropicPoint)
    (hp : octImAction g nativeBasePoint = p.1)
    (L₀ : NativeLine)
    (L : NativeLinesThroughPoint p.1)
    (hL : cast (congrArg NativeLinesThroughPoint hp)
        (nativeLineFiberMap g nativeBasePoint L₀) = L) :
    nativeFlagMap g ⟨nativeBaseIsotropicPoint, L₀⟩ = ⟨p, L⟩ := by
  apply Sigma.ext_iff.mpr
  constructor
  · apply Subtype.ext
    exact hp
  · have hrec := nativeLineFamily_cast_eq_rec hp
      (nativeLineFiberMap g nativeBasePoint L₀)
    have hL' : Eq.rec (nativeLineFiberMap g nativeBasePoint L₀) hp = L := by
      rw [← hrec]
      exact hL
    simpa [nativeFlagMap] using
      (eqRec_heq hp (nativeLineFiberMap g nativeBasePoint L₀)).symm.trans
        (heq_of_eq hL')

noncomputable def nativeBaseFlag : NativeFlag :=
  ⟨nativeBaseIsotropicPoint, lineZero⟩

theorem nativeBaseFlag_fst : nativeBaseFlag.1 = nativeBaseIsotropicPoint :=
  rfl

theorem nativeFlagMap_baseFlag_fst_eq
    (g : SplitOctF2Aut)
    (p : OctImIsotropicPoint)
    (hp : octImAction g nativeBasePoint = p.1) :
    (nativeFlagMap g nativeBaseFlag).1 = p := by
  apply Subtype.ext
  change octImAction g nativeBasePoint = p.1
  exact hp

theorem nativeFlagMap_stabilizer_baseFlag
    (g : nativePointStabilizer) :
    nativeFlagMap g.1 nativeBaseFlag =
      ⟨nativeBaseIsotropicPoint,
        nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
          lineZero⟩ := by
  apply nativeFlagMap_baseLine_eq_of_transport g.1 nativeBaseIsotropicPoint
    (nativePointStabilizer_fixes_base_point g.2) lineZero
      (nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
      lineZero)
  apply Subtype.ext
  simpa [nativeLineAction] using
    (nativeRawLine_transport_val
      (nativePointStabilizer_fixes_base_point g.2)
      (nativeLineFiberMap g.1 nativeBasePoint lineZero))

theorem nativeFlag_orbit_surjective :
    Function.Surjective (fun g : SplitOctF2Aut => nativeFlagMap g nativeBaseFlag) := by
  rintro ⟨p, L⟩
  obtain ⟨g, hg⟩ := octImPointPerm_base_surjective p
  have hp : octImAction g nativeBasePoint = p.1 := by
    exact congrArg Subtype.val hg
  obtain ⟨L₀, hL₀⟩ := nativeLineFiberMap_preimage_of_point_eq g p.1 hp L
  obtain ⟨h, hh⟩ := baseIntrinsicLine_orbit_surjective L₀
  refine ⟨g * h.1, ?_⟩
  change nativeFlagMap (g * h.1) nativeBaseFlag = ⟨p, L⟩
  rw [nativeFlagMap_mul, nativeFlagMap_stabilizer_baseFlag]
  have hbase :
      nativeFlagMap h.1 nativeBaseFlag =
        ⟨nativeBaseIsotropicPoint, L₀⟩ := by
    rw [nativeFlagMap_stabilizer_baseFlag]
    apply Sigma.ext_iff.mpr
    constructor
    · rfl
    · exact heq_of_eq hh
  have hpair :
      ⟨nativeBaseIsotropicPoint,
        nativeLineAction h.1 (nativePointStabilizer_fixes_base_point h.2)
          lineZero⟩ = nativeFlagMap h.1 nativeBaseFlag := by
    simpa [hh] using hbase.symm
  have hpair' :
      ⟨nativeBaseIsotropicPoint,
        nativeLineAction h.1 (nativePointStabilizer_fixes_base_point h.2)
          lineZero⟩ = (⟨nativeBaseIsotropicPoint, L₀⟩ : NativeFlag) :=
    hpair.trans hbase
  calc
    nativeFlagMap g
        ⟨nativeBaseIsotropicPoint,
          nativeLineAction h.1 (nativePointStabilizer_fixes_base_point h.2)
            lineZero⟩ = nativeFlagMap g
        ⟨nativeBaseIsotropicPoint, L₀⟩ := by
          simpa using congrArg (fun F : NativeFlag => nativeFlagMap g F) hpair'
    _ = ⟨p, L⟩ := nativeFlagMap_baseLine_eq_of_transport g p hp L₀ L hL₀

theorem nativeCandidateAction_preserves_base_fibre
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    nativeCandidateAt nativeBasePoint
      (nativeCandidateAction g hg
        ⟨y, by simpa [candidates, kernelCandidate] using hy⟩).1 := by
  change nativeCandidateAt nativeBasePoint (octImAction g y)
  exact nativeCandidateAt_map_of_fix g hg y hy

end InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction
