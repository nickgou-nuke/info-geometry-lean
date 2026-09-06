import InfoGeometry.Canonical.FiniteFibonacciComputationalSpace

/-!
# InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface

Finite interfaces inspired by the Fibonacci-anyon monodromy construction.

The paper constructs analytic half-monodromy matrices on conformal blocks.  This
file does not formalize those analytic continuations or matrix formulae.  Instead
it records the finite algebraic interface needed by the existing framework:

* electrons occur in multiples of three, `3 * r`;
* a half-monodromy generator family acts on an abstract finite state type;
* if the generators satisfy the two Artin rewrite identities, then the induced
  finite word action is invariant under the corresponding braid rewrites;
* if a monodromy action is block diagonal with respect to computational and
  non-computational labels, then the computational sector is invariant.

No CFT correlators.
No analytic continuation theorem.
No concrete braid matrices.
No Solovay--Kitaev or fault-tolerance claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace

/-- The allowed electron count in the `Z₃` parafermion setting: a multiple of three. -/
def electronCount (r : ℕ) : ℕ :=
  3 * r

/-- The electron count is divisible by three. -/
theorem three_dvd_electronCount (r : ℕ) :
    3 ∣ electronCount r := by
  exact ⟨r, rfl⟩

/-- A finite half-monodromy generator assignment on an abstract state type. -/
abbrev HalfMonodromy (State : Type*) :=
  ℕ → State → State

/-- Action of a finite braid word by a generator family. -/
def braidWordAction {State : Type*} (ρ : HalfMonodromy State) :
    BraidWord → State → State
  | [], x => x
  | i :: w, x => ρ i (braidWordAction ρ w x)

@[simp]
theorem braidWordAction_nil {State : Type*} (ρ : HalfMonodromy State) (x : State) :
    braidWordAction ρ [] x = x :=
  rfl

@[simp]
theorem braidWordAction_cons {State : Type*} (ρ : HalfMonodromy State)
    (i : ℕ) (w : BraidWord) (x : State) :
    braidWordAction ρ (i :: w) x = ρ i (braidWordAction ρ w x) :=
  rfl

/-- Word action sends concatenation to composition of word actions. -/
theorem braidWordAction_append {State : Type*} (ρ : HalfMonodromy State)
    (u v : BraidWord) (x : State) :
    braidWordAction ρ (u ++ v) x = braidWordAction ρ u (braidWordAction ρ v x) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [ih]

/-- Invariance under a separated Artin commutation rewrite, from a pointwise hypothesis. -/
theorem braidWordAction_commute_rewrite {State : Type*} (ρ : HalfMonodromy State)
    {i j : ℕ} (left right : BraidWord)
    (hcomm : ∀ x : State, ρ i (ρ j x) = ρ j (ρ i x))
    (x : State) :
    braidWordAction ρ (left ++ [i, j] ++ right) x =
      braidWordAction ρ (left ++ [j, i] ++ right) x := by
  repeat rw [braidWordAction_append]
  simp [hcomm]

/-- Invariance under the adjacent Artin/Yang--Baxter rewrite, from a pointwise hypothesis. -/
theorem braidWordAction_braid_rewrite {State : Type*} (ρ : HalfMonodromy State)
    (i : ℕ) (left right : BraidWord)
    (hbraid : ∀ x : State,
      ρ i (ρ (i + 1) (ρ i x)) = ρ (i + 1) (ρ i (ρ (i + 1) x)))
    (x : State) :
    braidWordAction ρ (left ++ [i, i + 1, i] ++ right) x =
      braidWordAction ρ (left ++ [i + 1, i, i + 1] ++ right) x := by
  repeat rw [braidWordAction_append]
  simp [hbraid]

/--
Electron-blind finite braid action: the electron multiplicity parameter is present
but does not enter the finite braid-word action.
-/
def electronBlindBraidAction {State : Type*} (ρ : HalfMonodromy State)
    (_r : ℕ) (w : BraidWord) (x : State) : State :=
  braidWordAction ρ w x

/-- Electron-blind actions are independent of the multiple-of-three electron count. -/
theorem electronBlindBraidAction_independent_of_r {State : Type*}
    (ρ : HalfMonodromy State) (r s : ℕ) (w : BraidWord) (x : State) :
    electronBlindBraidAction ρ r w x = electronBlindBraidAction ρ s w x :=
  rfl

/-- A block-diagonal half-monodromy generator on computational plus NC labels. -/
def blockDiagonalHalfMonodromy {N : ℕ} {NC : Type*}
    (onComputational : ℕ → ComputationalVector N → ComputationalVector N)
    (onNonComputational : ℕ → NC → NC) :
    HalfMonodromy (FibonacciBlockLabel N NC) :=
  fun i => blockDiagonalAction (onComputational i) (onNonComputational i)

/-- One block-diagonal generator preserves computational labels. -/
theorem blockDiagonalHalfMonodromy_preserves_computational {N : ℕ} {NC : Type*}
    (onComputational : ℕ → ComputationalVector N → ComputationalVector N)
    (onNonComputational : ℕ → NC → NC)
    (i : ℕ) {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (blockDiagonalHalfMonodromy onComputational onNonComputational i x) :=
  blockDiagonalAction_preserves_computational
    (onComputational i) (onNonComputational i) hx

/-- Finite no leakage for any word in block-diagonal half-monodromy generators. -/
theorem blockDiagonalBraidWordAction_preserves_computational {N : ℕ} {NC : Type*}
    (onComputational : ℕ → ComputationalVector N → ComputationalVector N)
    (onNonComputational : ℕ → NC → NC)
    (w : BraidWord) {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (braidWordAction (blockDiagonalHalfMonodromy onComputational onNonComputational) w x) := by
  induction w generalizing x with
  | nil => exact hx
  | cons i w ih =>
      exact blockDiagonalHalfMonodromy_preserves_computational
        onComputational onNonComputational i (ih hx)

/-- Electron-blind block-diagonal monodromy has finite no leakage for every `3 * r` sector. -/
theorem electronBlindBlockDiagonalAction_preserves_computational {N : ℕ} {NC : Type*}
    (onComputational : ℕ → ComputationalVector N → ComputationalVector N)
    (onNonComputational : ℕ → NC → NC)
    (r : ℕ) (w : BraidWord) {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (electronBlindBraidAction
        (blockDiagonalHalfMonodromy onComputational onNonComputational) r w x) :=
  blockDiagonalBraidWordAction_preserves_computational
    onComputational onNonComputational w hx

end InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface
