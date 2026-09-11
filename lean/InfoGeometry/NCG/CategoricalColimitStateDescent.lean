import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Universal Categorical Colimit State Descent, GNS Towers, and KMS Flows

This module formalizes:
1. **Direct Sequential Systems of Star Algebras**: Stage algebras `Stage n`, transitions `ι_n`,
   and multi-step morphisms `ι_{n, n+k}`.
2. **Compatible State Cocones**: Normalized linear states `ω_n : Stage n → R` satisfying
   `ω_{n+1}(ι_n(x)) = ω_n(x)`.
3. **GNS Tower Isometries**: Proof that local GNS pre-Hilbert inner products embed isometrically
   across stages: `⟨ι_n(a), ι_n(b)⟩_{n+1} = ⟨a, b⟩_n`.
4. **Modular Flow Cocones & KMS Pullback**: Modular automorphism families `σ_n` intertwining with
   transitions `σ_{n+1} ∘ ι_n = ι_n ∘ σ_n` and invariant KMS boundary condition descent.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG

variable {R : Type*} [CommRing R]

/-- A direct sequential system of R-algebras with transition homomorphisms. -/
structure DirectSystem (R : Type*) [CommRing R] where
  Stage : ℕ → Type*
  [ringStage : ∀ n, Ring (Stage n)]
  [algebraStage : ∀ n, Algebra R (Stage n)]
  [starStage : ∀ n, StarRing (Stage n)]
  transition : ∀ n, Stage n →ₐ[R] Stage (n + 1)
  transition_star : ∀ n (x : Stage n), transition n (star x) = star (transition n x)

attribute [instance] DirectSystem.ringStage DirectSystem.algebraStage DirectSystem.starStage

namespace DirectSystem

variable (S : DirectSystem R)

/-- Multi-step transition map ι_{n, n+k} : Stage n →ₐ[R] Stage (n + k) -/
def transitionN (n : ℕ) : ∀ k, S.Stage n →ₐ[R] S.Stage (n + k)
  | 0 => AlgHom.id R (S.Stage n)
  | k + 1 => (S.transition (n + k)).comp (transitionN n k)

theorem transitionN_zero (n : ℕ) :
    S.transitionN n 0 = AlgHom.id R (S.Stage n) := by
  dsimp [transitionN]

theorem transitionN_one (n : ℕ) (x : S.Stage n) :
    S.transitionN n 1 x = S.transition n x := by
  dsimp [transitionN]

/-- Multi-step transition preserves star involution. -/
theorem transitionN_star (n k : ℕ) (x : S.Stage n) :
    S.transitionN n k (star x) = star (S.transitionN n k x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show S.transition (n + k) (S.transitionN n k (star x)) =
             star (S.transition (n + k) (S.transitionN n k x))
      rw [ih, S.transition_star]

theorem transitionN_mul (n k : ℕ) (x y : S.Stage n) :
    S.transitionN n k (x * y) =
      S.transitionN n k x * S.transitionN n k y := by
  exact (S.transitionN n k).map_mul x y

theorem transitionN_add (n k : ℕ) (x y : S.Stage n) :
    S.transitionN n k (x + y) =
      S.transitionN n k x + S.transitionN n k y := by
  exact (S.transitionN n k).map_add x y

theorem transitionN_smul (n k : ℕ) (r : R) (x : S.Stage n) :
    S.transitionN n k (r • x) = r • S.transitionN n k x := by
  exact _root_.map_smul (S.transitionN n k) r x

theorem transitionN_zero_element (n k : ℕ) :
    S.transitionN n k 0 = 0 := by
  exact (S.transitionN n k).map_zero

theorem transitionN_map_one (n k : ℕ) :
    S.transitionN n k 1 = 1 := by
  exact (S.transitionN n k).map_one

theorem transitionN_star_mul (n k : ℕ) (x y : S.Stage n) :
    S.transitionN n k (star x * y) =
      star (S.transitionN n k x) * S.transitionN n k y := by
  rw [S.transitionN_mul, S.transitionN_star]

/-- A compatible state cocone on the direct system:
    a family of normalized linear functionals ω_n : Stage n → R satisfying
    ω_{n+1}(ι_n(x)) = ω_n(x). -/
structure StateCocone (S : DirectSystem R) where
  state : ∀ n, S.Stage n →ₗ[R] R
  normalized : ∀ n, state n 1 = 1
  compatible : ∀ n (x : S.Stage n), state (n + 1) (S.transition n x) = state n x

namespace StateCocone

variable {S : DirectSystem R}
variable (C : StateCocone S)

/-- 🏆 THEOREM 1: Multi-step state compatibility:
    ω_{n+k}(ι_{n, n+k}(x)) = ω_n(x) -/
theorem state_transitionN (n k : ℕ) (x : S.Stage n) :
    C.state (n + k) (S.transitionN n k x) = C.state n x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show C.state (n + k + 1) (S.transition (n + k) (S.transitionN n k x)) = C.state n x
      rw [C.compatible]
      exact ih

/-- Local GNS inner product at stage n: ⟨a, b⟩_n = ω_n(b* * a) -/
def gnsInnerStage (n : ℕ) (a b : S.Stage n) : R :=
  C.state n (star b * a)

/-- 🏆 THEOREM 2: GNS Isometric Embedding across Colimit Stages:
    ⟨ι_n(a), ι_n(b)⟩_{n+1} = ⟨a, b⟩_n -/
theorem gns_transition_isometry (n : ℕ) (a b : S.Stage n) :
    C.gnsInnerStage (n + 1) (S.transition n a) (S.transition n b) =
      C.gnsInnerStage n a b := by
  dsimp [gnsInnerStage]
  have h_star : star (S.transition n b) = S.transition n (star b) :=
    (S.transition_star n b).symm
  have h_map : S.transition n (star b) * S.transition n a = S.transition n (star b * a) := by
    rw [← map_mul]
  rw [h_star, h_map, C.compatible]

/-- 🏆 THEOREM 3: Multi-step GNS Isometric Embedding:
    ⟨ι_{n, n+k}(a), ι_{n, n+k}(b)⟩_{n+k} = ⟨a, b⟩_n -/
theorem gns_transitionN_isometry (n k : ℕ) (a b : S.Stage n) :
    C.gnsInnerStage (n + k) (S.transitionN n k a) (S.transitionN n k b) =
      C.gnsInnerStage n a b := by
  dsimp [gnsInnerStage]
  have h_map : S.transitionN n k (star b) * S.transitionN n k a = S.transitionN n k (star b * a) := by
    rw [← map_mul]
  rw [← S.transitionN_star, h_map, C.state_transitionN]

end StateCocone

/-- A compatible modular automorphism flow cocone:
    a family of algebra automorphisms σ_n : Stage n ≃ₐ[R] Stage n commuting with transitions. -/
structure ModularFlowCocone (S : DirectSystem R) where
  flow : ∀ n, S.Stage n ≃ₐ[R] S.Stage n
  intertwines : ∀ n (x : S.Stage n),
    flow (n + 1) (S.transition n x) = S.transition n (flow n x)

namespace ModularFlowCocone

variable {S : DirectSystem R}
variable (M : ModularFlowCocone S)

/-- 🏆 THEOREM 4: Multi-step flow intertwining:
    σ_{n+k}(ι_{n, n+k}(x)) = ι_{n, n+k}(σ_n(x)) -/
theorem flow_transitionN (n k : ℕ) (x : S.Stage n) :
    M.flow (n + k) (S.transitionN n k x) = S.transitionN n k (M.flow n x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show M.flow (n + k + 1) (S.transition (n + k) (S.transitionN n k x)) =
             S.transition (n + k) (S.transitionN n k (M.flow n x))
      rw [M.intertwines]
      congr 1

/-- 🏆 THEOREM 5: KMS Boundary Condition Invariance across Colimit Stages:
    If ω_n(a * σ_n(b)) = ω_n(b * a) holds at stage n+1, it pulls back to stage n. -/
theorem kms_condition_transition_pullback
    (C : StateCocone S)
    (n : ℕ) (a b : S.Stage n)
    (h_kms : C.state (n + 1) (S.transition n a * M.flow (n + 1) (S.transition n b)) =
             C.state (n + 1) (S.transition n b * S.transition n a)) :
    C.state (n + 1) (S.transition n a * S.transition n (M.flow n b)) =
    C.state n (b * a) := by
  have h_map : S.transition n b * S.transition n a = S.transition n (b * a) := by
    rw [← map_mul]
  rw [← M.intertwines, h_kms, h_map, C.compatible]

/-- Multi-step KMS pullback along the iterated transition map. -/
theorem kms_condition_transitionN_pullback
    (C : StateCocone S)
    (n k : ℕ) (a b : S.Stage n)
    (h_kms :
      C.state (n + k)
          (S.transitionN n k a * M.flow (n + k) (S.transitionN n k b)) =
        C.state (n + k)
          (S.transitionN n k b * S.transitionN n k a)) :
    C.state (n + k)
        (S.transitionN n k a * S.transitionN n k (M.flow n b)) =
      C.state n (b * a) := by
  rw [← M.flow_transitionN n k b, h_kms]
  have h_map :
      S.transitionN n k b * S.transitionN n k a =
        S.transitionN n k (b * a) := by
    rw [← map_mul]
  rw [h_map, C.state_transitionN]

end ModularFlowCocone

end DirectSystem

end InfoGeometry.NCG
