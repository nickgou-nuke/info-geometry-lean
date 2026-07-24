import InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface

/-!
# InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup

Finite register-subgroup interface for Fibonacci computational spaces.

For `2 * N + 2` Fibonacci anyons, the paper singles out the subgroup generated
by the first, the last, and the even braid generators.  On the computational
sector this acts locally on the corresponding qubit factors.

This file formalizes the finite combinatorial part:

* even braid-generator indices assigned to qubit positions;
* separatedness of distinct even generators;
* local bit actions on `ComputationalVector N`;
* local actions at distinct qubit positions commute;
* the corresponding block-diagonal actions have no leakage into the NC sector.

No concrete Fibonacci `B` matrix.
No conformal-block monodromy matrices.
No density/Solovay--Kitaev theorem.
No physical fault-tolerance claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup

open FiniteFibonacciComputationalSpace
open FiniteFibonacciMonodromyInterface

/-- The even braid generator acting on qubit position `k`: `b_{2(k+1)}`. -/
def evenBraidIndex {N : ℕ} (k : Fin N) : ℕ :=
  2 * (k.val + 1)

/-- The left end generator `b₁`. -/
def leftEndBraidIndex : ℕ :=
  1

/-- The right end generator `b_{2N+1}`. -/
def rightEndBraidIndex (N : ℕ) : ℕ :=
  2 * N + 1

/-- Even generator indices are really even. -/
theorem evenBraidIndex_even {N : ℕ} (k : Fin N) :
    2 ∣ evenBraidIndex k := by
  exact ⟨k.val + 1, rfl⟩

/-- Even generators for ordered distinct qubit positions are separated Artin generators. -/
theorem evenBraidIndex_separated_of_lt {N : ℕ} {k l : Fin N} (h : k.val < l.val) :
    evenBraidIndex k + 1 < evenBraidIndex l := by
  unfold evenBraidIndex
  omega

/-- The left end generator is separated from even generators not acting on the first qubit. -/
theorem leftEnd_separated_even {N : ℕ} {k : Fin N} (h : 0 < k.val) :
    leftEndBraidIndex + 1 < evenBraidIndex k := by
  unfold leftEndBraidIndex evenBraidIndex
  omega

/-- Even generators before the final qubit are separated from the right end generator. -/
theorem even_separated_rightEnd {N : ℕ} {k : Fin N} (h : k.val + 1 < N) :
    evenBraidIndex k + 1 < rightEndBraidIndex N := by
  unfold evenBraidIndex rightEndBraidIndex
  omega

/-- Apply a single-qubit Boolean operation to the first qubit. -/
def leftEndComputationalAction {N : ℕ} (k : Fin N) (r : Bool → Bool) :
    ComputationalVector N → ComputationalVector N :=
  localQubitAction k r

/-- Apply a single-qubit Boolean operation to the last qubit. -/
def rightEndComputationalAction {N : ℕ} (k : Fin N) (r : Bool → Bool) :
    ComputationalVector N → ComputationalVector N :=
  localQubitAction k r

/-- Apply a single-qubit Boolean operation at an even braid-generator position. -/
def evenComputationalAction {N : ℕ} (k : Fin N) (b : Bool → Bool) :
    ComputationalVector N → ComputationalVector N :=
  localQubitAction k b

/-- Local actions at distinct qubit positions commute. -/
theorem localQubitAction_commute {N : ℕ} {k l : Fin N} (hkl : k ≠ l)
    (f g : Bool → Bool) (α : ComputationalVector N) :
    localQubitAction k f (localQubitAction l g α) =
      localQubitAction l g (localQubitAction k f α) := by
  funext m
  by_cases hmk : m = k
  · subst hmk
    simp [localQubitAction, Function.update, hkl]
  · by_cases hml : m = l
    · subst hml
      simp [localQubitAction, Function.update, hmk]
    · simp [localQubitAction, Function.update, hmk, hml]

/-- Even computational actions at distinct qubit positions commute. -/
theorem evenComputationalAction_commute {N : ℕ} {k l : Fin N} (hkl : k ≠ l)
    (f g : Bool → Bool) (α : ComputationalVector N) :
    evenComputationalAction k f (evenComputationalAction l g α) =
      evenComputationalAction l g (evenComputationalAction k f α) :=
  localQubitAction_commute hkl f g α

/-- Block-diagonal register action for an even generator has no leakage. -/
def evenBlockAction {N : ℕ} {NC : Type*} (k : Fin N) (b : Bool → Bool)
    (onNonComputational : NC → NC) :
    FibonacciBlockLabel N NC → FibonacciBlockLabel N NC :=
  localQubitBlockAction k b onNonComputational

/-- Even block actions preserve the computational sector. -/
theorem evenBlockAction_preserves_computational {N : ℕ} {NC : Type*}
    (k : Fin N) (b : Bool → Bool) (onNonComputational : NC → NC)
    {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational (evenBlockAction k b onNonComputational x) :=
  localQubitBlockAction_preserves_computational k b onNonComputational hx

/-- Block-diagonal register action for a chosen end generator has no leakage. -/
def endBlockAction {N : ℕ} {NC : Type*} (k : Fin N) (r : Bool → Bool)
    (onNonComputational : NC → NC) :
    FibonacciBlockLabel N NC → FibonacciBlockLabel N NC :=
  localQubitBlockAction k r onNonComputational

/-- End block actions preserve the computational sector. -/
theorem endBlockAction_preserves_computational {N : ℕ} {NC : Type*}
    (k : Fin N) (r : Bool → Bool) (onNonComputational : NC → NC)
    {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational (endBlockAction k r onNonComputational x) :=
  localQubitBlockAction_preserves_computational k r onNonComputational hx

/--
A theorem-owned finite no-leakage statement for a register-subgroup generator
family presented as block-diagonal computational/NC actions.
-/
theorem registerBlockDiagonalWord_no_leakage {N : ℕ} {NC : Type*}
    (onComputational : ℕ → ComputationalVector N → ComputationalVector N)
    (onNonComputational : ℕ → NC → NC)
    (w : List ℕ) {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (braidWordAction (blockDiagonalHalfMonodromy onComputational onNonComputational) w x) :=
  blockDiagonalBraidWordAction_preserves_computational onComputational onNonComputational w hx

end InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup
