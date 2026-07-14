import InfoGeometry.Algebra.InfiniteInductiveSUSY

/-!
# InfoGeometry.Canonical.InfiniteKMSCondition

Stagewise transport for algebraic KMS boundary conditions.

This is the direct-limit companion to the repository's KMS readout modules.
It does not assert analytic continuation, modular theory in full generality,
or a Tomita-Takesaki completion theorem.  Instead, it isolates the finite-stage
induction pattern that is already used throughout the codebase:

* a bonding tower of rings;
* a flow compatible with the bonding maps;
* a state/readout compatible with the bonding maps;
* a KMS boundary identity preserved along any transported observable pair.
-/

noncomputable section

namespace InfiniteKMSCondition

open InfoGeometry.Algebra.InfiniteInductiveSUSY

universe u

section Tower

variable {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]

/--
An algebraic KMS tower.

The `flow` field is the stagewise modular action and `state` is the stagewise
readout.  Compatibility says both transport along the bonding maps.
-/
structure KMSTower where
  /-- One-step bonding maps. -/
  bond : ∀ n : ℕ, Stage n →+* Stage (n + 1)
  /-- Stagewise modular flow. -/
  flow : ∀ n : ℕ, ℝ → Stage n →+* Stage n
  /-- Stagewise state/readout. -/
  state : ∀ n : ℕ, Stage n → ℝ
  /-- Flow compatibility with the bonding maps. -/
  flow_step :
    ∀ (n : ℕ) (t : ℝ) (x : Stage n),
      bond n (flow n t x) = flow (n + 1) t (bond n x)
  /-- State compatibility with the bonding maps. -/
  state_step :
    ∀ (n : ℕ) (x : Stage n),
      state (n + 1) (bond n x) = state n x

namespace KMSTower

variable (P : KMSTower (Stage := Stage))

/--
Any transported observable family has stage-independent state readout.
-/
theorem state_image_constant
    (X : ∀ n : ℕ, Stage n)
    (hX : ∀ n : ℕ, X (n + 1) = P.bond n (X n)) :
    ∀ n : ℕ, P.state n (X n) = P.state 0 (X 0) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        P.state (n + 1) (X (n + 1))
            = P.state (n + 1) (P.bond n (X n)) := by
                rw [hX n]
        _ = P.state n (X n) := P.state_step n (X n)
        _ = P.state 0 (X 0) := ih

/--
The algebraic KMS boundary relation is preserved along every transported pair.
-/
theorem kmsBoundary_transport
    (β : ℝ)
    (A B : ∀ n : ℕ, Stage n)
    (hA : ∀ n : ℕ, A (n + 1) = P.bond n (A n))
    (hB : ∀ n : ℕ, B (n + 1) = P.bond n (B n))
    (h0 : P.state 0 (A 0 * P.flow 0 β (B 0)) = P.state 0 (B 0 * A 0)) :
    ∀ n : ℕ,
      P.state n (A n * P.flow n β (B n)) = P.state n (B n * A n) := by
  intro n
  have hLeftStep :
      ∀ n : ℕ,
        (fun n : ℕ => A n * P.flow n β (B n)) (n + 1) =
          P.bond n ((fun n : ℕ => A n * P.flow n β (B n)) n) := by
    intro n
    change A (n + 1) * P.flow (n + 1) β (B (n + 1)) =
      P.bond n (A n * P.flow n β (B n))
    rw [hA n, hB n, ← P.flow_step n β (B n), ← map_mul]
  have hRightStep :
      ∀ n : ℕ,
        (fun n : ℕ => B n * A n) (n + 1) =
          P.bond n ((fun n : ℕ => B n * A n) n) := by
    intro n
    change B (n + 1) * A (n + 1) = P.bond n (B n * A n)
    rw [hB n, hA n, ← map_mul]
  have hLeft :
      ∀ n : ℕ, P.state n (A n * P.flow n β (B n)) = P.state 0 (A 0 * P.flow 0 β (B 0)) :=
    P.state_image_constant (fun n : ℕ => A n * P.flow n β (B n)) hLeftStep
  have hRight :
      ∀ n : ℕ, P.state n (B n * A n) = P.state 0 (B 0 * A 0) :=
    P.state_image_constant (fun n : ℕ => B n * A n) hRightStep
  calc
    P.state n (A n * P.flow n β (B n)) = P.state 0 (A 0 * P.flow 0 β (B 0)) := hLeft n
    _ = P.state 0 (B 0 * A 0) := h0
    _ = P.state n (B n * A n) := (hRight n).symm

/--
The transported left-hand observable has stage-independent state readout.
-/
theorem kmsLeft_state_image_constant
    (β : ℝ)
    (A B : ∀ n : ℕ, Stage n)
    (hA : ∀ n : ℕ, A (n + 1) = P.bond n (A n))
    (hB : ∀ n : ℕ, B (n + 1) = P.bond n (B n)) :
    ∀ n : ℕ,
      P.state n (A n * P.flow n β (B n)) = P.state 0 (A 0 * P.flow 0 β (B 0)) := by
  have hLeftStep :
      ∀ n : ℕ,
        (fun n : ℕ => A n * P.flow n β (B n)) (n + 1) =
          P.bond n ((fun n : ℕ => A n * P.flow n β (B n)) n) := by
    intro n
    change A (n + 1) * P.flow (n + 1) β (B (n + 1)) =
      P.bond n (A n * P.flow n β (B n))
    rw [hA n, hB n, ← P.flow_step n β (B n), ← map_mul]
  exact P.state_image_constant (fun n : ℕ => A n * P.flow n β (B n)) hLeftStep

/--
The transported right-hand observable has stage-independent state readout.
-/
theorem kmsRight_state_image_constant
    (A B : ∀ n : ℕ, Stage n)
    (hA : ∀ n : ℕ, A (n + 1) = P.bond n (A n))
    (hB : ∀ n : ℕ, B (n + 1) = P.bond n (B n)) :
    ∀ n : ℕ,
      P.state n (B n * A n) = P.state 0 (B 0 * A 0) := by
  have hRightStep :
      ∀ n : ℕ,
        (fun n : ℕ => B n * A n) (n + 1) =
          P.bond n ((fun n : ℕ => B n * A n) n) := by
    intro n
    change B (n + 1) * A (n + 1) = P.bond n (B n * A n)
    rw [hB n, hA n, ← map_mul]
  exact P.state_image_constant (fun n : ℕ => B n * A n) hRightStep

end KMSTower

end Tower

end InfiniteKMSCondition
