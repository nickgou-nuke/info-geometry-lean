import Mathlib.Tactic
import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Canonical.SplitCliffordDirectLimit

noncomputable section

namespace InfoGeometry.Spectral.Colimit

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit

/-- A concrete one-step sequential system. -/
structure SequentialSystem where
  obj : ℕ → Type*
  step : ∀ n, obj n → obj (n + 1)

namespace SequentialSystem

abbrev stage (S : SequentialSystem) (n : ℕ) : Type* := S.obj n

abbrev stepMap (S : SequentialSystem) (n : ℕ) : S.stage n → S.stage (n + 1) :=
  S.step n

/-- Iterated transition map from stage `n` to stage `n + k`. -/
def iterStep (S : SequentialSystem) (n : ℕ) : ∀ k, S.stage n → S.stage (n + k)
  | 0, x => x
  | k + 1, x => S.step (n + k) (S.iterStep n k x)

@[simp]
theorem iterStep_zero (S : SequentialSystem) (n : ℕ) (x : S.stage n) :
    S.iterStep n 0 x = x := rfl

@[simp]
theorem iterStep_succ (S : SequentialSystem) (n k : ℕ) (x : S.stage n) :
    S.iterStep n (k + 1) x = S.step (n + k) (S.iterStep n k x) := rfl

end SequentialSystem

/-- A concrete cocone over a sequential system. -/
structure Cocone (S : SequentialSystem) where
  carrier : Type*
  map : ∀ n, S.stage n → carrier
  compat : ∀ n x, map (n + 1) (S.step n x) = map n x

namespace Cocone

variable {S : SequentialSystem}

@[simp]
theorem compat_apply (K : Cocone S) (n : ℕ) (x : S.stage n) :
    K.map (n + 1) (S.step n x) = K.map n x :=
  K.compat n x

/-- Cocone maps are constant along every finite tail of the system. -/
theorem iterStep_compat (K : Cocone S) (n k : ℕ) (x : S.stage n) :
    K.map (n + k) (S.iterStep n k x) = K.map n x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact (K.compat (n + k) (S.iterStep n k x)).trans ih

end Cocone

/-- A morphism of concrete sequential systems. -/
structure SystemMap (S T : SequentialSystem) where
  map : ∀ n, S.stage n → T.stage n
  compat : ∀ n x, map (n + 1) (S.step n x) = T.step n (map n x)

namespace SystemMap

variable {R S T : SequentialSystem}

def id (S : SequentialSystem) : SystemMap S S where
  map := fun _ x => x
  compat := by intro n x; rfl

def comp (g : SystemMap S T) (f : SystemMap R S) : SystemMap R T where
  map := fun n x => g.map n (f.map n x)
  compat := by
    intro n x
    rw [f.compat n x, g.compat n (f.map n x)]

@[simp]
theorem id_apply (S : SequentialSystem) (n : ℕ) (x : S.stage n) :
    (id S).map n x = x := rfl

@[simp]
theorem comp_apply (g : SystemMap S T) (f : SystemMap R S) (n : ℕ) (x : R.stage n) :
    (g.comp f).map n x = g.map n (f.map n x) := rfl

def pullbackCocone (f : SystemMap S T) (K : Cocone T) : Cocone S where
  carrier := K.carrier
  map := fun n x => K.map n (f.map n x)
  compat := by
    intro n x
    rw [f.compat n x]
    exact K.compat n (f.map n x)

@[simp]
theorem pullbackCocone_map (f : SystemMap S T) (K : Cocone T) (n : ℕ) (x : S.stage n) :
    (f.pullbackCocone K).map n x = K.map n (f.map n x) := rfl

end SystemMap

/-- The repo-owned split Clifford tower as a concrete sequential system. -/
def SplitCliffordSystem : SequentialSystem where
  obj := SplitClNNAlg
  step := fun n x => splitCliffordStep n x

@[simp]
theorem SplitCliffordSystem_step (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordSystem.step n x = splitCliffordStep n x := rfl

/-- The existing split-Clifford direct limit is a cocone over the one-step tower. -/
def SplitCliffordInfinityCocone : Cocone SplitCliffordSystem where
  carrier := SplitCliffordInfinity
  map := fun n x =>
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
      (fun m n h => splitCliffordMap m n h) n x
  compat := by
    intro n x
    change
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) (n + 1)
          (splitCliffordStep n x)
        =
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) n x
    have h :
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) (n + 1)
            (splitCliffordMap n (n + 1) (Nat.le_succ n) x)
          =
          DirectLimit.Module.of ℝ ℕ SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) n x :=
      @DirectLimit.Module.of_f
        ℝ ℕ _ SplitClNNAlg
        (fun {i j} (_h : i ≤ j) => SplitClNNAlg i →ₐ[ℝ] SplitClNNAlg j)
        (fun m n h => splitCliffordMap m n h)
        _ _ _ _ _ _ _ _
        (i := n) (j := n + 1) (hij := Nat.le_succ n) (x := x)
    simpa [splitCliffordMap_succ] using h

abbrev SplitCliffordInclusion (n : ℕ) : SplitClNNAlg n → SplitCliffordInfinity :=
  SplitCliffordInfinityCocone.map n

@[simp]
theorem SplitCliffordInclusion_apply (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordInclusion n x =
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x := rfl

theorem SplitCliffordInclusion_step (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordInclusion (n + 1) (splitCliffordStep n x) =
      SplitCliffordInclusion n x :=
  SplitCliffordInfinityCocone.compat n x

theorem SplitCliffordInclusion_iterStep (n k : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordInclusion (n + k) (SplitCliffordSystem.iterStep n k x) =
      SplitCliffordInclusion n x :=
  SplitCliffordInfinityCocone.iterStep_compat n k x

end InfoGeometry.Spectral.Colimit
