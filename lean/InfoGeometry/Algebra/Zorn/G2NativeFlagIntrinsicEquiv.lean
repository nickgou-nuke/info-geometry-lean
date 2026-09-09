import InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
import InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicStructuralBridge
import InfoGeometry.Algebra.Zorn.G2NativeFlagOrbitClosure
import InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

/-!
# Native to intrinsic flag carrier equivalence and action equivariance

This module builds the canonical bijection between the native carrier
`NativeFlag := Σ p : OctImIsotropicPoint, NativeLinesThroughPoint p.1`
and the intrinsic incidence carrier
`IntrinsicFlag := Σ p : OctImIsotropicPoint, IntrinsicLine p`
using the structural point-dependent transport equivalence `nativeLineFiberEquiv p`.

Furthermore, it proves the exact full-flag action equivariance:
`nativeFlagIntrinsicEquiv (nativeFlagMap g F) = intrinsicFlagMap g (nativeFlagIntrinsicEquiv F)`
connecting the native group action to the intrinsic geometric incidence action.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicStructuralBridge
open InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
open InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeFlagOrbitClosure

/-- Canonical fiberwise equivalence between native and intrinsic lines at point `p`
    constructed structurally via group transport. -/
noncomputable def nativeLineToIntrinsicLineEquiv
    (p : OctImIsotropicPoint) :
    NativeLinesThroughPoint p.1 ≃ IntrinsicLine p :=
  nativeLineFiberEquiv p

/-- Canonical map from native lines to intrinsic lines at point `p`. -/
noncomputable def nativeLineToIntrinsicLine
    (p : OctImIsotropicPoint) :
    NativeLinesThroughPoint p.1 → IntrinsicLine p :=
  (nativeLineToIntrinsicLineEquiv p).toFun

theorem nativeLineToIntrinsicLine_injective
    (p : OctImIsotropicPoint) :
    Function.Injective (nativeLineToIntrinsicLine p) :=
  (nativeLineToIntrinsicLineEquiv p).injective

theorem nativeLineToIntrinsicLine_surjective
    (p : OctImIsotropicPoint) :
    Function.Surjective (nativeLineToIntrinsicLine p) :=
  (nativeLineToIntrinsicLineEquiv p).surjective

/-- Global equivalence between the native and intrinsic full-flag carriers. -/
noncomputable def nativeFlagIntrinsicEquiv :
    NativeFlag ≃ IntrinsicFlag :=
  Equiv.sigmaCongrRight (fun p => nativeLineToIntrinsicLineEquiv p)

theorem nativeFlagIntrinsicEquiv_injective :
    Function.Injective nativeFlagIntrinsicEquiv :=
  nativeFlagIntrinsicEquiv.injective

theorem nativeFlagIntrinsicEquiv_surjective :
    Function.Surjective nativeFlagIntrinsicEquiv :=
  nativeFlagIntrinsicEquiv.surjective

theorem nativeFlag_card_eq_intrinsicFlag_card :
    Fintype.card NativeFlag = Fintype.card IntrinsicFlag := by
  rw [Fintype.card_congr nativeFlagIntrinsicEquiv]

theorem nativeFlagIntrinsicEquiv_fst (F : NativeFlag) :
    (nativeFlagIntrinsicEquiv F).1 = F.1 :=
  rfl

theorem nativeFlagIntrinsicEquiv_snd (F : NativeFlag) :
    (nativeFlagIntrinsicEquiv F).2 = nativeLineFiberEquiv F.1 F.2 :=
  rfl

/-- THEOREM: Full flag action equivariance between native and intrinsic flag carriers. -/
theorem nativeFlagIntrinsicEquiv_action_eq
    (g : SplitOctF2Aut) (F : NativeFlag) :
    nativeFlagIntrinsicEquiv (nativeFlagMap g F) =
      intrinsicFlagMap g (nativeFlagIntrinsicEquiv F) := by
  have hfst : (nativeFlagIntrinsicEquiv (nativeFlagMap g F)).1 =
      (intrinsicFlagMap g (nativeFlagIntrinsicEquiv F)).1 := by
    change (nativeFlagMap g F).1 = octImPointPerm g (nativeFlagIntrinsicEquiv F).1
    rfl
  refine Sigma.ext hfst ?_
  have hsnd_val_left :
      ((nativeFlagIntrinsicEquiv (nativeFlagMap g F)).2).1.image Subtype.val =
        F.2.1.image (octImAction g) := by
    rw [nativeFlagIntrinsicEquiv_snd]
    rw [nativeLineFiberEquiv_val_image]
    exact nativeFlagMap_snd_val g F
  have hsnd_val_right :
      ((intrinsicFlagMap g (nativeFlagIntrinsicEquiv F)).2).1.image Subtype.val =
        F.2.1.image (octImAction g) := by
    dsimp [intrinsicFlagMap]
    rw [intrinsicLineMap_val]
    rw [zornZeroTripleMap_val_image]
    rw [show (fun v : OctImIsotropicPoint => octImAction g v.1) = (octImAction g) ∘ Subtype.val from rfl]
    rw [← Finset.image_image]
    rw [nativeFlagIntrinsicEquiv_snd]
    rw [nativeLineFiberEquiv_val_image]
  have heq_lines :
      (nativeFlagIntrinsicEquiv (nativeFlagMap g F)).2 =
        (intrinsicFlagMap g (nativeFlagIntrinsicEquiv F)).2 := by
    apply intrinsicLine_eq_of_val_image_eq
    rw [hsnd_val_left, hsnd_val_right]
  rw [heq_lines]

/-- THEOREM: The native base flag maps to the intrinsic base flag under the equivalence. -/
theorem nativeFlagIntrinsicEquiv_baseFlag :
    nativeFlagIntrinsicEquiv nativeBaseFlag = baseIntrinsicFlag := by
  have hfst : (nativeFlagIntrinsicEquiv nativeBaseFlag).1 =
      baseIntrinsicFlag.1 := by
    change nativeBaseFlag.1 = nativeBaseIsotropicPoint
    rfl
  refine Sigma.ext hfst ?_
  have hsnd_val_left :
      ((nativeFlagIntrinsicEquiv nativeBaseFlag).2).1.image Subtype.val =
        baseIntrinsicFlag.2.1.image Subtype.val := by
    rw [nativeFlagIntrinsicEquiv_snd]
    rw [nativeLineFiberEquiv_val_image]
    change lineZero.1 = baseIntrinsicLine.1.image Subtype.val
    ext x
    rw [Finset.mem_image]
    constructor
    · intro hx
      refine ⟨⟨x, nativeBaseLineWitness_points_valid x hx⟩, ?_, rfl⟩
      exact (mem_baseIntrinsicLine_iff ⟨x, nativeBaseLineWitness_points_valid x hx⟩).mpr hx
    · rintro ⟨v, hv, rfl⟩
      exact (mem_baseIntrinsicLine_iff v).mp hv
  have heq_lines :
      (nativeFlagIntrinsicEquiv nativeBaseFlag).2 =
        baseIntrinsicFlag.2 := by
    apply intrinsicLine_eq_of_val_image_eq
    exact hsnd_val_left
  rw [heq_lines]

theorem intrinsicFlag_orbit_surjective :
    Function.Surjective
      (fun g : SplitOctF2Aut => intrinsicFlagMap g baseIntrinsicFlag) := by
  intro F
  obtain ⟨N, hN⟩ := nativeFlagIntrinsicEquiv_surjective F
  obtain ⟨g, hg⟩ := nativeFlag_orbit_surjective N
  refine ⟨g, ?_⟩
  calc
    intrinsicFlagMap g baseIntrinsicFlag =
        intrinsicFlagMap g (nativeFlagIntrinsicEquiv nativeBaseFlag) := by
          rw [nativeFlagIntrinsicEquiv_baseFlag]
    _ = nativeFlagIntrinsicEquiv (nativeFlagMap g nativeBaseFlag) := by
          exact (nativeFlagIntrinsicEquiv_action_eq g nativeBaseFlag).symm
    _ = nativeFlagIntrinsicEquiv N := by exact congrArg nativeFlagIntrinsicEquiv hg
    _ = F := hN

/-- THEOREM: The G₂(2) orbit of the intrinsic base flag covers the entire 189-element IntrinsicFlag manifold. -/
theorem intrinsicFlag_orbit_eq_univ :
    MulAction.orbit SplitOctF2Aut baseIntrinsicFlag = Set.univ := by
  ext F
  simp only [Set.mem_univ, iff_true]
  obtain ⟨g, hg⟩ := intrinsicFlag_orbit_surjective F
  refine ⟨g, ?_⟩
  exact hg

end InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv
