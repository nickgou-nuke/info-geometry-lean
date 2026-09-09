/- SPDX-License-Identifier: Apache-2.0 -/
import Mathlib.Order.Zorn
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
import InfoGeometry.Canonical.CantorBoundaryCuntzShift

namespace InfoGeometry.Quantum.ConcreteCuntz

def CantorWord : Type := ℕ → Fin 2
def TensorBasisState : Type := CantorWord × (Fin 2 → ℝ)

def prefix0 (ω : CantorWord) : CantorWord
  | 0 => 0
  | n + 1 => ω n

def prefix1 (ω : CantorWord) : CantorWord
  | 0 => 1
  | n + 1 => ω n

def J0 (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -v 1 else v 0

theorem J0_sq (v : Fin 2 → ℝ) : J0 (J0 v) = -v := by
  ext i
  fin_cases i <;> rfl

def S_left (s : TensorBasisState) : TensorBasisState := (prefix0 s.1, s.2)
def S_right (s : TensorBasisState) : TensorBasisState := (prefix1 s.1, s.2)
def K_op (s : TensorBasisState) : TensorBasisState := (s.1, J0 s.2)

theorem prefix0_bool_transport (ω : CantorWord) :
    (fun n => InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool
      (prefix0 ω n)) =
      InfoGeometry.Canonical.CantorBoundaryCuntzShift.prefixBit false
        (fun n => InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool
          (ω n)) := by
  funext n
  cases n <;> rfl

theorem prefix1_bool_transport (ω : CantorWord) :
    (fun n => InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool
      (prefix1 ω n)) =
      InfoGeometry.Canonical.CantorBoundaryCuntzShift.prefixBit true
        (fun n => InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool
          (ω n)) := by
  funext n
  cases n <;> rfl

theorem finTwoCuntzFamily_zero_readback :
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.cantorBernoulliFin2CStarFamily.S
        (0 : Fin 2) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.vLeft := by
  rfl

theorem finTwoCuntzFamily_one_readback :
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.cantorBernoulliFin2CStarFamily.S
        (1 : Fin 2) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.vRight := by
  rfl

theorem S_left_commutes_K : S_left ∘ K_op = K_op ∘ S_left := by
  funext s
  rfl

theorem S_right_commutes_K : S_right ∘ K_op = K_op ∘ S_right := by
  funext s
  rfl

theorem prefix0_ne_prefix1 (ω₁ ω₂ : CantorWord) : prefix0 ω₁ ≠ prefix1 ω₂ := by
  intro h
  have h0 := congrFun h 0
  simpa [prefix0, prefix1] using h0

theorem prefix0_injective : Function.Injective prefix0 := by
  intro ω₁ ω₂ h
  funext n
  have := congrFun h (n + 1)
  simpa [prefix0] using this

theorem prefix1_injective : Function.Injective prefix1 := by
  intro ω₁ ω₂ h
  funext n
  have := congrFun h (n + 1)
  simpa [prefix1] using this

theorem zorn_maximal_boundary_subsystem
    (F : Set (Set TensorBasisState))
    (h_chain : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ F, ∀ s ∈ c, s ⊆ ub)
    (s0 : Set TensorBasisState) (hs0 : s0 ∈ F) :
    ∃ m, s0 ⊆ m ∧ Maximal (fun x => x ∈ F) m :=
  zorn_subset_nonempty F h_chain s0 hs0


end InfoGeometry.Quantum.ConcreteCuntz
