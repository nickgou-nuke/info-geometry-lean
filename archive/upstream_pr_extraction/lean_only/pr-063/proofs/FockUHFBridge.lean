import Mathlib

/-!
# Finite Fock Factors as UHF Cylinder Observables

This bridge places the finite prime-Fock supertrace into the diagonal UHF/MASA
inductive colimit.

At stage `n`, a finite graded Fock determinant

`Z_gr,n = ∏ᵢ (1 - xᵢ)`

is represented as the constant diagonal observable on binary words of length
`n`.  The UHF embedding keeps the cylinder value fixed, while adding a new
prime mode multiplies by the local factor `1 - x`.
-/

noncomputable section

namespace FockUHFBridge

/-- Binary words of length `n`. -/
abbrev BitWord (n : ℕ) : Type :=
  Fin n → Bool

/-- Diagonal finite-dimensional algebra at stage `n`. -/
abbrev DiagAlg (n : ℕ) : Type :=
  BitWord n → ℂ

/-- Cantor boundary of the diagonal UHF algebra. -/
abbrev CantorBoundary : Type :=
  ℕ → Bool

/-- Prefix a word of length `n+1` down to length `n`. -/
def prefixSucc (n : ℕ) (w : BitWord (n + 1)) : BitWord n :=
  fun i => w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- UHF diagonal connecting map: duplicate over the newly added bit. -/
def diagEmbedSucc (n : ℕ) : DiagAlg n → DiagAlg (n + 1) :=
  fun f w => f (prefixSucc n w)

/-- Restrict a boundary point to its first `n` bits. -/
def boundaryPrefix (n : ℕ) (b : CantorBoundary) : BitWord n :=
  fun i => b i.1

/-- Finite-cylinder realization of a stage-`n` diagonal observable. -/
def cylinder (n : ℕ) (f : DiagAlg n) : CantorBoundary → ℂ :=
  fun b => f (boundaryPrefix n b)

theorem boundaryPrefix_succ_eq_prefixSucc
    (n : ℕ) (b : CantorBoundary) :
    prefixSucc n (boundaryPrefix (n + 1) b) = boundaryPrefix n b := by
  ext i
  rfl

/-- Cylinder maps are compatible with the UHF connecting maps. -/
theorem cylinder_compatible_succ (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  ext b
  simp [cylinder, diagEmbedSucc, boundaryPrefix_succ_eq_prefixSucc]

theorem cylinder_one (n : ℕ) :
    cylinder n 1 = (1 : CantorBoundary → ℂ) := by
  ext b
  rfl

/-- Finite-cylinder functions: the concrete diagonal UHF inductive colimit. -/
def CylinderColimit : Set (CantorBoundary → ℂ) :=
  Set.range (fun p : Sigma DiagAlg => cylinder p.1 p.2)

theorem cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder n f ∈ CylinderColimit := by
  exact ⟨⟨n, f⟩, rfl⟩

/-- Constant diagonal stage observable. -/
def constantStageObservable (n : ℕ) (z : ℂ) : DiagAlg n :=
  fun _ => z

/-- Local graded fermion factor: empty minus occupied. -/
def gradedFermionLocal (x : ℂ) : ℂ :=
  1 - x

/-- Local boson factor, encoded as the reciprocal determinant. -/
def bosonLocal (x : ℂ) : ℂ :=
  (1 - x)⁻¹

/-- Finite graded Fock supertrace over a cutoff list of weights. -/
def gradedFockSupertrace (xs : List ℂ) : ℂ :=
  xs.map gradedFermionLocal |>.prod

/-- Finite bosonic reciprocal determinant over a cutoff list of weights. -/
def bosonicFockDeterminant (xs : List ℂ) : ℂ :=
  xs.map bosonLocal |>.prod

/-- Finite cutoff cancellation over a list of nonsingular local weights. -/
theorem finite_boson_cancels_graded
    (xs : List ℂ) (hxs : ∀ x ∈ xs, x ≠ 1) :
    bosonicFockDeterminant xs * gradedFockSupertrace xs = 1 := by
  induction xs with
  | nil =>
      simp [bosonicFockDeterminant, gradedFockSupertrace]
  | cons x xs ih =>
      have hx : x ≠ 1 := hxs x (by simp)
      have htail : ∀ y ∈ xs, y ≠ 1 := by
        intro y hy
        apply hxs
        exact List.mem_cons_of_mem x hy
      calc
        bosonicFockDeterminant (x :: xs) * gradedFockSupertrace (x :: xs)
            =
          ((1 - x)⁻¹ * bosonicFockDeterminant xs) *
            ((1 - x) * gradedFockSupertrace xs) := by
              rfl
        _ =
          ((1 - x)⁻¹ * (1 - x)) *
            (bosonicFockDeterminant xs * gradedFockSupertrace xs) := by
              ring
        _ = 1 * 1 := by
              rw [ih htail]
              exact congrArg (fun a => a * 1) (by
                have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
                simp [hden])
        _ = 1 := by ring

/-- Finite graded Fock factor as a constant diagonal UHF observable. -/
def gradedFockStageObservable (xs : List ℂ) :
    DiagAlg xs.length :=
  constantStageObservable xs.length (gradedFockSupertrace xs)

/-- Finite bosonic reciprocal determinant as a constant diagonal UHF observable. -/
def bosonicFockStageObservable (xs : List ℂ) :
    DiagAlg xs.length :=
  constantStageObservable xs.length (bosonicFockDeterminant xs)

/-- The graded Fock stage observable is a finite-cylinder colimit element. -/
theorem gradedFockStage_mem_colimit (xs : List ℂ) :
    cylinder xs.length (gradedFockStageObservable xs) ∈ CylinderColimit := by
  exact cylinder_mem_colimit xs.length (gradedFockStageObservable xs)

/-- Same for the bosonic reciprocal determinant. -/
theorem bosonicFockStage_mem_colimit (xs : List ℂ) :
    cylinder xs.length (bosonicFockStageObservable xs) ∈ CylinderColimit := by
  exact cylinder_mem_colimit xs.length (bosonicFockStageObservable xs)

/-- UHF embedding keeps a finite Fock factor as the same cylinder observable. -/
theorem gradedFockStage_embed_same_cylinder (xs : List ℂ) :
    cylinder (xs.length + 1)
        (diagEmbedSucc xs.length (gradedFockStageObservable xs))
      =
    cylinder xs.length (gradedFockStageObservable xs) := by
  exact cylinder_compatible_succ xs.length (gradedFockStageObservable xs)

/-- Adding a new prime mode multiplies the graded factor by `1 - x`. -/
theorem gradedFockSupertrace_snoc (xs : List ℂ) (x : ℂ) :
    gradedFockSupertrace (xs ++ [x]) =
      gradedFockSupertrace xs * (1 - x) := by
  induction xs with
  | nil =>
      simp [gradedFockSupertrace, gradedFermionLocal]
  | cons y ys ih =>
      simp [gradedFockSupertrace, gradedFermionLocal]
      ring

/-- The one-step prime update as multiplication by a local constant observable. -/
theorem gradedFockStage_add_prime
    (xs : List ℂ) (x : ℂ) :
    cylinder ((xs ++ [x]).length) (gradedFockStageObservable (xs ++ [x]))
      =
    cylinder (xs.length + 1)
      (diagEmbedSucc xs.length (gradedFockStageObservable xs) *
        constantStageObservable (xs.length + 1) (1 - x)) := by
  ext b
  simp [gradedFockStageObservable, constantStageObservable,
    cylinder, diagEmbedSucc, gradedFockSupertrace_snoc]

/-- Bosonic and graded stage observables cancel pointwise under the finite hypothesis. -/
theorem fock_stage_cancellation_observable
    (xs : List ℂ) (hxs : ∀ x ∈ xs, x ≠ 1) :
    bosonicFockStageObservable xs * gradedFockStageObservable xs =
      (1 : DiagAlg xs.length) := by
  ext w
  simp [bosonicFockStageObservable, gradedFockStageObservable,
    constantStageObservable, finite_boson_cancels_graded xs hxs]

/-- The same cancellation as a cylinder function on the UHF boundary. -/
theorem fock_stage_cancellation_cylinder
    (xs : List ℂ) (hxs : ∀ x ∈ xs, x ≠ 1) :
    cylinder xs.length
        (bosonicFockStageObservable xs * gradedFockStageObservable xs)
      =
    (1 : CantorBoundary → ℂ) := by
  rw [fock_stage_cancellation_observable xs hxs]
  exact cylinder_one xs.length

end FockUHFBridge

end noncomputable section
