import Mathlib.Tactic

/-!
# Finite inductive superclosure lemmas

This file proves finite local-to-global preservation of supergraded closure
relations along a typed inductive chain of ring homomorphisms.

It is deliberately finite-stage only: no colimit, completion, extra data
carrier, or analytic limit claim is introduced.
-/

namespace InfoGeometry.Algebra.InductiveSuperClosureLemmas

universe u

/-- Super-anticommutator in a multiplicative additive carrier. -/
def anticommutator {A : Type u} [Mul A] [Add A] (x y : A) : A :=
  x * y + y * x

/-- Ring homomorphisms preserve the super-anticommutator. -/
theorem map_anticommutator
    {A B : Type u} [Semiring A] [Semiring B]
    (f : A →+* B) (x y : A) :
    f (anticommutator x y) = anticommutator (f x) (f y) := by
  simp [anticommutator]

/-- Ring homomorphisms preserve square-zero operators. -/
theorem ringHom_preserves_square_zero
    {A B : Type u} [Semiring A] [Semiring B]
    (f : A →+* B) {Q : A}
    (hQ : Q * Q = 0) :
    f Q * f Q = 0 := by
  rw [← map_mul, hQ, map_zero]

/-- Ring homomorphisms preserve fixed power-zero laws. -/
theorem ringHom_preserves_pow_zero
    {A B : Type u} [Semiring A] [Semiring B]
    (f : A →+* B) {Q : A} (k : Nat)
    (hQ : Q ^ k = 0) :
    f Q ^ k = 0 := by
  rw [← map_pow, hQ, map_zero]

/-- Ring homomorphisms preserve idempotents. -/
theorem ringHom_preserves_idempotent
    {A B : Type u} [Semiring A] [Semiring B]
    (f : A →+* B) {P : A}
    (hP : P * P = P) :
    f P * f P = f P := by
  rw [← map_mul, hP]

/-- Ring homomorphisms transport an anticommutator identity exactly. -/
theorem ringHom_map_anticommutator
    {A B : Type u} [Semiring A] [Semiring B]
    (f : A →+* B) {Q R Z : A}
    (hQR : anticommutator Q R = Z) :
    anticommutator (f Q) (f R) = f Z := by
  rw [← map_anticommutator f Q R, hQR]

/-- Finite-stage superbracket transport along a bonding homomorphism. -/
theorem finite_stage_superbracket_transport
    {A B : Type u} [Semiring A] [Semiring B]
    (bond : A →+* B) {Q R Z : A}
    (hQR : anticommutator Q R = Z) :
    anticommutator (bond Q) (bond R) = bond Z :=
  ringHom_map_anticommutator bond hQR

/-- Centrality on the source transports to centrality on the image. -/
theorem finite_stage_centrality_on_image
    {A B : Type u} [Semiring A] [Semiring B]
    (bond : A →+* B) {Z X : A}
    (hZX : Commute Z X) :
    Commute (bond Z) (bond X) :=
  hZX.map bond

/-- A commuting Cartan family remains commuting after finite-stage transport. -/
theorem finite_cartan_commuting_family_transport
    {A B : Type u} {ι : Type*} [Semiring A] [Semiring B]
    (bond : A →+* B) (H : ι → A)
    (hH : ∀ i j, Commute (H i) (H j)) :
    ∀ i j, Commute (bond (H i)) (bond (H j)) := by
  intro i j
  exact finite_stage_centrality_on_image bond (hH i j)

section Chain

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]

/--
Square-zero transport along a typed inductive chain.

If `Q₀² = 0` and `Q` is transported by every bonding homomorphism, then
`Qₙ² = 0` at every finite stage.
-/
theorem squareZero_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q : ∀ n : Nat, Stage n)
    (h0 : Q 0 * Q 0 = 0)
    (hQ : ∀ n, bond n (Q n) = Q (n + 1)) :
    ∀ n : Nat, Q n * Q n = 0 := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      rw [← hQ n]
      exact ringHom_preserves_square_zero (bond n) ih

/--
Fixed power-zero transport along a typed inductive chain.

If `Q₀^k = 0` and `Q` is transported by every bonding homomorphism, then
`Qₙ^k = 0` at every finite stage.
-/
theorem powZero_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q : ∀ n : Nat, Stage n)
    (k : Nat)
    (h0 : Q 0 ^ k = 0)
    (hQ : ∀ n, bond n (Q n) = Q (n + 1)) :
    ∀ n : Nat, Q n ^ k = 0 := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      rw [← hQ n]
      exact ringHom_preserves_pow_zero (bond n) k ih

/--
Idempotent transport along a typed inductive chain.

If `P₀² = P₀` and `P` is transported by every bonding homomorphism, then
`Pₙ² = Pₙ` at every finite stage.
-/
theorem idempotent_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (P : ∀ n : Nat, Stage n)
    (h0 : P 0 * P 0 = P 0)
    (hP : ∀ n, bond n (P n) = P (n + 1)) :
    ∀ n : Nat, P n * P n = P n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      rw [← hP n]
      exact ringHom_preserves_idempotent (bond n) ih

/--
Commutation transport along a typed inductive chain.

If `Z₀` commutes with `X₀` and both elements are transported by every bonding
homomorphism, then `Zₙ` commutes with `Xₙ` at every finite stage.
-/
theorem commute_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Z X : ∀ n : Nat, Stage n)
    (h0 : Commute (Z 0) (X 0))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1))
    (hX : ∀ n, bond n (X n) = X (n + 1)) :
    ∀ n : Nat, Commute (Z n) (X n) := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      rw [← hZ n, ← hX n]
      exact ih.map (bond n)

/--
A commuting family transported along a typed inductive chain remains commuting
at every finite stage.
-/
theorem commutingFamily_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    {ι : Type*} (H : ∀ n : Nat, ι → Stage n)
    (h0 : ∀ i j, Commute (H 0 i) (H 0 j))
    (hH : ∀ n i, bond n (H n i) = H (n + 1) i) :
    ∀ n i j, Commute (H n i) (H n j) := by
  intro n i j
  exact commute_all bond
    (fun n => H n i) (fun n => H n j)
    (h0 i j) (fun n => hH n i) (fun n => hH n j) n

/--
Fixed-point transport for a compatible family of stage endomorphisms.

If `θ₀ X₀ = X₀`, `X` is transported by the bonds, and `θ` commutes with the
bonds, then `θₙ Xₙ = Xₙ` at every finite stage.
-/
theorem endomorphism_fixed_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (θ : ∀ n : Nat, Stage n →+* Stage n)
    (X : ∀ n : Nat, Stage n)
    (hθ : ∀ n (x : Stage n), θ (n + 1) (bond n x) = bond n (θ n x))
    (h0 : θ 0 (X 0) = X 0)
    (hX : ∀ n, bond n (X n) = X (n + 1)) :
    ∀ n : Nat, θ n (X n) = X n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      calc
        θ (n + 1) (X (n + 1))
            = θ (n + 1) (bond n (X n)) := by rw [hX n]
        _ = bond n (θ n (X n)) := hθ n (X n)
        _ = bond n (X n) := by rw [ih]
        _ = X (n + 1) := hX n

/--
Neg-fixed-point transport for a compatible family of stage endomorphisms.

This is the finite algebraic grading rule for odd elements:
if `θ₀ X₀ = -X₀`, the transported representatives remain neg-fixed at every
finite stage.
-/
theorem endomorphism_neg_fixed_all
    {RingStage : Nat → Type u} [∀ n : Nat, Ring (RingStage n)]
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (θ : ∀ n : Nat, RingStage n →+* RingStage n)
    (X : ∀ n : Nat, RingStage n)
    (hθ : ∀ n (x : RingStage n), θ (n + 1) (bond n x) = bond n (θ n x))
    (h0 : θ 0 (X 0) = -X 0)
    (hX : ∀ n, bond n (X n) = X (n + 1)) :
    ∀ n : Nat, θ n (X n) = -X n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      calc
        θ (n + 1) (X (n + 1))
            = θ (n + 1) (bond n (X n)) := by rw [hX n]
        _ = bond n (θ n (X n)) := hθ n (X n)
        _ = bond n (-X n) := by rw [ih]
        _ = -bond n (X n) := by rw [map_neg]
        _ = -X (n + 1) := by rw [hX n]

/-- Stagewise single-supercharge closure: `{Qₙ,Qₙ}=Hₙ+Zₙ`. -/
def SuperClosureAt
    (Q H Z : ∀ n : Nat, Stage n) (n : Nat) : Prop :=
  anticommutator (Q n) (Q n) = H n + Z n

/--
One-step preservation of single-supercharge closure along a bonding ring
homomorphism preserving the named generators.
-/
theorem superClosure_step
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q H Z : ∀ n : Nat, Stage n)
    (n : Nat)
    (hQ : bond n (Q n) = Q (n + 1))
    (hH : bond n (H n) = H (n + 1))
    (hZ : bond n (Z n) = Z (n + 1))
    (h : SuperClosureAt Q H Z n) :
    SuperClosureAt Q H Z (n + 1) := by
  unfold SuperClosureAt at h ⊢
  rw [← hQ, ← hH, ← hZ]
  calc
    anticommutator (bond n (Q n)) (bond n (Q n))
        = bond n (anticommutator (Q n) (Q n)) := by
          exact (map_anticommutator (bond n) (Q n) (Q n)).symm
    _ = bond n (H n + Z n) := by
          rw [h]
    _ = bond n (H n) + bond n (Z n) := by
          simp

/--
Finite induction theorem for single-supercharge closure along a typed
inductive system.
-/
theorem superClosure_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q H Z : ∀ n : Nat, Stage n)
    (h0 : SuperClosureAt Q H Z 0)
    (hQ : ∀ n, bond n (Q n) = Q (n + 1))
    (hH : ∀ n, bond n (H n) = H (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat, SuperClosureAt Q H Z n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      exact superClosure_step bond Q H Z n (hQ n) (hH n) (hZ n) ih

/-- Mixed odd-odd closure: `{Q⁽ᴬ⁾ₙ,Q⁽ᴮ⁾ₙ}=Kₙ+Zₙ`. -/
def MixedSuperClosureAt
    (QA QB K Z : ∀ n : Nat, Stage n) (n : Nat) : Prop :=
  anticommutator (QA n) (QB n) = K n + Z n

/--
One-step preservation of mixed odd-odd closure along a bonding ring homomorphism
preserving the named generators.
-/
theorem mixedSuperClosure_step
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (QA QB K Z : ∀ n : Nat, Stage n)
    (n : Nat)
    (hQA : bond n (QA n) = QA (n + 1))
    (hQB : bond n (QB n) = QB (n + 1))
    (hK : bond n (K n) = K (n + 1))
    (hZ : bond n (Z n) = Z (n + 1))
    (h : MixedSuperClosureAt QA QB K Z n) :
    MixedSuperClosureAt QA QB K Z (n + 1) := by
  unfold MixedSuperClosureAt at h ⊢
  rw [← hQA, ← hQB, ← hK, ← hZ]
  calc
    anticommutator (bond n (QA n)) (bond n (QB n))
        = bond n (anticommutator (QA n) (QB n)) := by
          exact (map_anticommutator (bond n) (QA n) (QB n)).symm
    _ = bond n (K n + Z n) := by
          rw [h]
    _ = bond n (K n) + bond n (Z n) := by
          simp

/--
Finite induction theorem for mixed odd-odd closure along a typed inductive
system.
-/
theorem mixedSuperClosure_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (QA QB K Z : ∀ n : Nat, Stage n)
    (h0 : MixedSuperClosureAt QA QB K Z 0)
    (hQA : ∀ n, bond n (QA n) = QA (n + 1))
    (hQB : ∀ n, bond n (QB n) = QB (n + 1))
    (hK : ∀ n, bond n (K n) = K (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat, MixedSuperClosureAt QA QB K Z n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      exact mixedSuperClosure_step bond QA QB K Z n
        (hQA n) (hQB n) (hK n) (hZ n) ih

end Chain

end InfoGeometry.Algebra.InductiveSuperClosureLemmas
