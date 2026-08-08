import Mathlib
import InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat

/-!
# The compatible readout family as a native `TopCat` inverse limit

Restriction of stage observables induces pullback on continuous readouts.  The
compatible-family carrier is therefore the limit of the resulting direct
sequence of readout spaces.  This owner supplies the native `TopCat` cone and
its `IsLimit` property.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Clifford.Cl11TensorTower

def readoutPullbackCLM (n : ℕ) :
    (MatStage n →L[ℝ] ℝ) →L[ℝ] (MatStage (n + 1) →L[ℝ] ℝ) :=
  ContinuousLinearMap.flip
    (ContinuousLinearMap.compL ℝ (MatStage (n + 1)) (MatStage n) ℝ)
    (stageRestrictCLM n)

@[simp] theorem readoutPullbackCLM_apply
    (n : ℕ) (ρ : MatStage n →L[ℝ] ℝ) (X : MatStage (n + 1)) :
    readoutPullbackCLM n ρ X = ρ (stageRestrictCLM n X) := by
  rfl

def readoutPullbackTopCatHom (n : ℕ) :
    TopCat.of (MatStage n →L[ℝ] ℝ) ⟶
      TopCat.of (MatStage (n + 1) →L[ℝ] ℝ) :=
  TopCat.ofHom
    { toFun := readoutPullbackCLM n
      continuous_toFun := (readoutPullbackCLM n).continuous }

def readoutDiagram : ℕ ⥤ TopCat :=
  Functor.ofSequence (fun n => readoutPullbackTopCatHom n)

def readoutInverseCone : Cone readoutDiagram where
  pt := TopCat.of CompatibleContinuousReadoutFamily
  π := NatTrans.ofSequence
    (app := fun n => coordinateTopCatHom n)
    (naturality := by
      intro n
      have hmap :
          readoutDiagram.map (homOfLE (Nat.le_succ n)) =
            readoutPullbackTopCatHom n := by
        simpa [readoutDiagram] using
          (Functor.ofSequence_map_homOfLE_succ
            (f := fun n => readoutPullbackTopCatHom n) n)
      rw [hmap]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro ρ
      change ρ.1 (n + 1) = readoutPullbackCLM n (ρ.1 n)
      ext X
      change ρ.1 (n + 1) X = ρ.1 n (stageRestrictCLM n X)
      exact (compatible_apply ρ n X).symm)

def readoutInverseLimitLift (s : Cone readoutDiagram) :
    s.pt ⟶ readoutInverseCone.pt := by
  let f : s.pt → CompatibleContinuousReadoutFamily := fun x =>
    ⟨fun n => by
      change MatStage n →L[ℝ] ℝ
      exact (s.π.app n) x, by
      intro n
      ext X
      have hmap :
          readoutDiagram.map (homOfLE (Nat.le_succ n)) =
            readoutPullbackTopCatHom n := by
        simpa [readoutDiagram] using
          (Functor.ofSequence_map_homOfLE_succ
            (f := fun n => readoutPullbackTopCatHom n) n)
      have h := congrArg (fun q => q x) (s.π.naturality
        (homOfLE (Nat.le_succ n)))
      rw [hmap] at h
      have h' :
          ((s.π.app (n + 1)) x : MatStage (n + 1) →L[ℝ] ℝ) =
            readoutPullbackCLM n
              ((s.π.app n) x : MatStage n →L[ℝ] ℝ) := by
        exact h
      have h'' := congrArg
        (fun q : MatStage (n + 1) →L[ℝ] ℝ => q X) h'
      simpa [readoutPullbackCLM_apply] using h''.symm⟩
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro n
    simpa [f] using (s.π.app n).hom.continuous
  exact TopCat.ofHom
    { toFun := f
      continuous_toFun := hf }

def readoutInverseConeIsLimit : IsLimit readoutInverseCone := by
  refine IsLimit.mk readoutInverseLimitLift ?_ ?_
  · intro s n
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change (readoutInverseLimitLift s x).1 n = (s.π.app n) x
    rfl
  · intro s m hm
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    funext n
    have h := congrArg (fun q => q x) (hm n)
    change (m x).1 n = (s.π.app n) x at h
    change (m x).1 n = (s.π.app n) x
    exact h

noncomputable def compatibleReadoutInverseLimitIso :
    TopCat.of CompatibleContinuousReadoutFamily ≅
      limit readoutDiagram :=
  IsLimit.conePointUniqueUpToIso readoutInverseConeIsLimit
    (limit.isLimit readoutDiagram)

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit

end
