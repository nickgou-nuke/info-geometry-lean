import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable section

namespace FibAnyonTrueHexagon

inductive FibLabel where
| I
| tau
deriving DecidableEq, Fintype

open FibLabel

variable {K : Type*} [CommRing K]

/--
Algebraic coefficient data for the Fibonacci theory.

The element `zeta` satisfies the tenth cyclotomic polynomial

`Φ₁₀(zeta) = zeta⁴ - zeta³ + zeta² - zeta + 1 = 0`.

Consequently `zeta⁵ = -1` and `zeta¹⁰ = 1`.  The Fibonacci parameter is

`tau = zeta² - zeta³`,

and `sqrtTau` is a chosen square root of `tau`.
-/
structure FibonacciCyclotomicData (K : Type*) [CommRing K] where
zeta : K
sqrtTau : K
cyclotomic :
zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1 = 0
sqrtTau_sq :
sqrtTau ^ 2 = zeta ^ 2 - zeta ^ 3

def goldenTau (D : FibonacciCyclotomicData K) : K :=
D.zeta ^ 2 - D.zeta ^ 3

lemma zeta_pow_five (D : FibonacciCyclotomicData K) :
D.zeta ^ 5 = -1 := by
  linear_combination (D.zeta + 1) * D.cyclotomic

lemma zeta_pow_ten (D : FibonacciCyclotomicData K) :
D.zeta ^ 10 = 1 := by
  calc
    D.zeta ^ 10 = (D.zeta ^ 5) ^ 2 := by ring
    _ = (-1 : K) ^ 2 := by rw [zeta_pow_five D]
    _ = 1 := by ring

lemma goldenTau_quadratic (D : FibonacciCyclotomicData K) :
goldenTau D * goldenTau D + goldenTau D = 1 := by
  unfold goldenTau
  linear_combination (D.zeta ^ 2 - D.zeta - 1) * D.cyclotomic

lemma sqrtTau_sq_eq_goldenTau (D : FibonacciCyclotomicData K) :
D.sqrtTau ^ 2 = goldenTau D := by
  exact D.sqrtTau_sq

lemma vacuum_phase_inverse (D : FibonacciCyclotomicData K) :
D.zeta ^ 6 * D.zeta ^ 4 = 1 := by
  calc
    D.zeta ^ 6 * D.zeta ^ 4 = D.zeta ^ 10 := by ring
    _ = 1 := zeta_pow_ten D

lemma tau_phase_inverse (D : FibonacciCyclotomicData K) :
D.zeta ^ 3 * D.zeta ^ 7 = 1 := by
  calc
    D.zeta ^ 3 * D.zeta ^ 7 = D.zeta ^ 10 := by ring
    _ = 1 := zeta_pow_ten D

/--
The multiplicity-free Fibonacci fusion coefficient.
-/
def fusionAllowed : FibLabel → FibLabel → FibLabel → Bool
| I, I, I => true
| I, tau, tau => true
| tau, I, tau => true
| tau, tau, I => true
| tau, tau, tau => true
| _, _, _ => false

/--
The Fibonacci associator coefficients over the cyclotomic coefficient ring.

The convention is

`FibF D a b c d e f = [Fᵃᵇᶜ_d]ₑ_f`.
-/
def FibF
(D : FibonacciCyclotomicData K)
(a b c d e f : FibLabel) : K :=
match
fusionAllowed a b e &&
fusionAllowed e c d &&
fusionAllowed b c f &&
fusionAllowed a f d with
| false => 0
| true =>
match a, b, c, d, e, f with
| tau, tau, tau, tau, I, I => goldenTau D
| tau, tau, tau, tau, I, tau => D.sqrtTau
| tau, tau, tau, tau, tau, I => D.sqrtTau
| tau, tau, tau, tau, tau, tau => -goldenTau D
| _, _, _, _, _, _ => 1

/--
The positive Fibonacci braiding coefficients.

With `zeta` a root of `Φ₁₀`, these are

`R¹_{ττ} = zeta⁶` and `Rᵗᵃᵘ_{ττ} = zeta³`.
-/
def FibR
(D : FibonacciCyclotomicData K) :
FibLabel → FibLabel → FibLabel → K
| I, I, I => 1
| I, tau, tau => 1
| tau, I, tau => 1
| tau, tau, I => D.zeta ^ 6
| tau, tau, tau => D.zeta ^ 3
| _, _, _ => 0

/--
The algebraic inverses of the Fibonacci braiding coefficients.

They are represented without division by

`(R¹_{ττ})⁻¹ = zeta⁴` and
`(Rᵗᵃᵘ_{ττ})⁻¹ = zeta⁷`.
-/
def FibRInv
(D : FibonacciCyclotomicData K) :
FibLabel → FibLabel → FibLabel → K
| I, I, I => 1
| I, tau, tau => 1
| tau, I, tau => 1
| tau, tau, I => D.zeta ^ 4
| tau, tau, tau => D.zeta ^ 7
| _, _, _ => 0

/--
The positive multiplicity-free hexagon path

`Rᵃᶜ_e · [Fᵃᶜᵇ_d]ₑ_g · Rᵇᶜ_g`.
-/
def forwardHexagonLHS
(D : FibonacciCyclotomicData K)
(a b c d e g : FibLabel) : K :=
FibR D a c e *
FibF D a c b d e g *
FibR D b c g

/--
The alternative positive hexagon path, contracted over the intermediate
fusion channel `f`.
-/
def forwardHexagonRHS
(D : FibonacciCyclotomicData K)
(a b c d e g : FibLabel) : K :=
FibF D c a b d e I *
FibR D I c d *
FibF D a b c d I g
+
FibF D c a b d e tau *
FibR D tau c d *
FibF D a b c d tau g

/--
The negative multiplicity-free hexagon path.
-/
def reverseHexagonLHS
(D : FibonacciCyclotomicData K)
(a b c d e g : FibLabel) : K :=
FibRInv D a c e *
FibF D a c b d e g *
FibRInv D b c g

/--
The alternative negative hexagon path, contracted over the intermediate
fusion channel `f`.
-/
def reverseHexagonRHS
(D : FibonacciCyclotomicData K)
(a b c d e g : FibLabel) : K :=
FibF D c a b d e I *
FibRInv D I c d *
FibF D a b c d I g
+
FibF D c a b d e tau *
FibRInv D tau c d *
FibF D a b c d tau g

def ForwardHexagonIdentity
(D : FibonacciCyclotomicData K) : Prop :=
∀ a b c d e g : FibLabel,
forwardHexagonLHS D a b c d e g =
forwardHexagonRHS D a b c d e g

def ReverseHexagonIdentity
(D : FibonacciCyclotomicData K) : Prop :=
∀ a b c d e g : FibLabel,
reverseHexagonLHS D a b c d e g =
reverseHexagonRHS D a b c d e g

def TrueHexagonIdentity
(D : FibonacciCyclotomicData K) : Prop :=
ForwardHexagonIdentity D ∧ ReverseHexagonIdentity D

lemma forward_hexagon_vacuum_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 6 * goldenTau D * D.zeta ^ 6 =
goldenTau D * goldenTau D +
D.sqrtTau * D.zeta ^ 3 * D.sqrtTau := by
  have h_sq : D.sqrtTau * D.zeta ^ 3 * D.sqrtTau = D.zeta ^ 3 * goldenTau D := by
    calc D.sqrtTau * D.zeta ^ 3 * D.sqrtTau = D.zeta ^ 3 * (D.sqrtTau ^ 2) := by ring
    _ = D.zeta ^ 3 * goldenTau D := by rw [sqrtTau_sq_eq_goldenTau]
  rw [h_sq]
  unfold goldenTau
  linear_combination (-D.zeta ^ 11 + D.zeta ^ 9 + D.zeta ^ 6 - D.zeta ^ 4) * D.cyclotomic

lemma forward_hexagon_mixed_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 6 * D.sqrtTau * D.zeta ^ 3 =
goldenTau D * D.sqrtTau +
D.sqrtTau * D.zeta ^ 3 * (-goldenTau D) := by
  have h : D.zeta ^ 6 * D.sqrtTau * D.zeta ^ 3 - (goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 3 * (-goldenTau D)) =
           D.sqrtTau * (D.zeta ^ 9 - goldenTau D + D.zeta ^ 3 * goldenTau D) := by ring
  have h_inside : D.zeta ^ 9 - goldenTau D + D.zeta ^ 3 * goldenTau D = 0 := by
    unfold goldenTau
    linear_combination (D.zeta ^ 5 + D.zeta ^ 4 - D.zeta ^ 2) * D.cyclotomic
  calc D.zeta ^ 6 * D.sqrtTau * D.zeta ^ 3 = D.sqrtTau * (D.zeta ^ 9 - goldenTau D + D.zeta ^ 3 * goldenTau D) + (goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 3 * (-goldenTau D)) := by ring
  _ = D.sqrtTau * 0 + (goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 3 * (-goldenTau D)) := by rw [h_inside]
  _ = goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 3 * (-goldenTau D) := by ring

lemma forward_hexagon_tau_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 3 * (-goldenTau D) * D.zeta ^ 3 =
D.sqrtTau * D.sqrtTau +
(-goldenTau D) * D.zeta ^ 3 * (-goldenTau D) := by
  have h_sq : D.sqrtTau * D.sqrtTau = goldenTau D := by
    calc D.sqrtTau * D.sqrtTau = D.sqrtTau ^ 2 := by ring
    _ = goldenTau D := sqrtTau_sq_eq_goldenTau D
  rw [h_sq]
  unfold goldenTau
  linear_combination (D.zeta ^ 4 - D.zeta ^ 2) * D.cyclotomic

lemma reverse_hexagon_total_vacuum_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 7 * D.zeta ^ 7 = D.zeta ^ 4 := by
  linear_combination (D.zeta ^ 10 + D.zeta ^ 9 - D.zeta ^ 5 - D.zeta ^ 4) * D.cyclotomic

lemma reverse_hexagon_vacuum_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 4 * goldenTau D * D.zeta ^ 4 =
goldenTau D * goldenTau D +
D.sqrtTau * D.zeta ^ 7 * D.sqrtTau := by
  have h_sq : D.sqrtTau * D.zeta ^ 7 * D.sqrtTau = D.zeta ^ 7 * goldenTau D := by
    calc D.sqrtTau * D.zeta ^ 7 * D.sqrtTau = D.zeta ^ 7 * (D.sqrtTau ^ 2) := by ring
    _ = D.zeta ^ 7 * goldenTau D := by rw [sqrtTau_sq_eq_goldenTau]
  rw [h_sq]
  unfold goldenTau
  linear_combination (-D.zeta ^ 7 + D.zeta ^ 6 + D.zeta ^ 5 - D.zeta ^ 4) * D.cyclotomic

lemma reverse_hexagon_mixed_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 4 * D.sqrtTau * D.zeta ^ 7 =
goldenTau D * D.sqrtTau +
D.sqrtTau * D.zeta ^ 7 * (-goldenTau D) := by
  have h : D.zeta ^ 4 * D.sqrtTau * D.zeta ^ 7 - (goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 7 * (-goldenTau D)) =
           D.sqrtTau * (D.zeta ^ 11 - goldenTau D + D.zeta ^ 7 * goldenTau D) := by ring
  have h_inside : D.zeta ^ 11 - goldenTau D + D.zeta ^ 7 * goldenTau D = 0 := by
    unfold goldenTau
    linear_combination (D.zeta ^ 7 + D.zeta ^ 4 - D.zeta ^ 2) * D.cyclotomic
  calc D.zeta ^ 4 * D.sqrtTau * D.zeta ^ 7 = D.sqrtTau * (D.zeta ^ 11 - goldenTau D + D.zeta ^ 7 * goldenTau D) + (goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 7 * (-goldenTau D)) := by ring
  _ = D.sqrtTau * 0 + (goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 7 * (-goldenTau D)) := by rw [h_inside]
  _ = goldenTau D * D.sqrtTau + D.sqrtTau * D.zeta ^ 7 * (-goldenTau D) := by ring

lemma reverse_hexagon_tau_channel
(D : FibonacciCyclotomicData K) :
D.zeta ^ 7 * (-goldenTau D) * D.zeta ^ 7 =
D.sqrtTau * D.sqrtTau +
(-goldenTau D) * D.zeta ^ 7 * (-goldenTau D) := by
  have h_sq : D.sqrtTau * D.sqrtTau = goldenTau D := by
    calc D.sqrtTau * D.sqrtTau = D.sqrtTau ^ 2 := by ring
    _ = goldenTau D := sqrtTau_sq_eq_goldenTau D
  rw [h_sq]
  unfold goldenTau
  linear_combination (D.zeta ^ 13 - D.zeta ^ 11 - D.zeta ^ 9 + D.zeta ^ 7 + D.zeta ^ 4 - D.zeta ^ 2) * D.cyclotomic


lemma forward_hexagon_mixed_channel_mirror
(D : FibonacciCyclotomicData K) :
D.zeta ^ 3 * D.sqrtTau * D.zeta ^ 6 =
D.sqrtTau * goldenTau D +
(-goldenTau D) * D.zeta ^ 3 * D.sqrtTau := by
  calc
  D.zeta ^ 3 * D.sqrtTau * D.zeta ^ 6 =
  D.zeta ^ 6 * D.sqrtTau * D.zeta ^ 3 := by ring
  _ =
  goldenTau D * D.sqrtTau +
  D.sqrtTau * D.zeta ^ 3 * (-goldenTau D) :=
  forward_hexagon_mixed_channel D
  _ =
  D.sqrtTau * goldenTau D +
  (-goldenTau D) * D.zeta ^ 3 * D.sqrtTau := by ring

lemma reverse_hexagon_mixed_channel_mirror
(D : FibonacciCyclotomicData K) :
D.zeta ^ 7 * D.sqrtTau * D.zeta ^ 4 =
D.sqrtTau * goldenTau D +
(-goldenTau D) * D.zeta ^ 7 * D.sqrtTau := by
  calc
  D.zeta ^ 7 * D.sqrtTau * D.zeta ^ 4 =
  D.zeta ^ 4 * D.sqrtTau * D.zeta ^ 7 := by ring
  _ =
  goldenTau D * D.sqrtTau +
  D.sqrtTau * D.zeta ^ 7 * (-goldenTau D) :=
  reverse_hexagon_mixed_channel D
  _ =
  D.sqrtTau * goldenTau D +
  (-goldenTau D) * D.zeta ^ 7 * D.sqrtTau := by ring

lemma forward_hexagon_branch_tau_tau_tau_tau_I_I
(D : FibonacciCyclotomicData K) :
forwardHexagonLHS D tau tau tau tau I I =
forwardHexagonRHS D tau tau tau tau I I := by
  simpa [
  forwardHexagonLHS,
  forwardHexagonRHS,
  FibF,
  FibR,
  fusionAllowed
  ] using forward_hexagon_vacuum_channel D

lemma forward_hexagon_branch_tau_tau_tau_tau_I_tau
(D : FibonacciCyclotomicData K) :
forwardHexagonLHS D tau tau tau tau I tau =
forwardHexagonRHS D tau tau tau tau I tau := by
  simpa [
  forwardHexagonLHS,
  forwardHexagonRHS,
  FibF,
  FibR,
  fusionAllowed
  ] using forward_hexagon_mixed_channel D

lemma forward_hexagon_branch_tau_tau_tau_tau_tau_I
(D : FibonacciCyclotomicData K) :
forwardHexagonLHS D tau tau tau tau tau I =
forwardHexagonRHS D tau tau tau tau tau I := by
  simpa [
  forwardHexagonLHS,
  forwardHexagonRHS,
  FibF,
  FibR,
  fusionAllowed
  ] using forward_hexagon_mixed_channel_mirror D

lemma forward_hexagon_branch_tau_tau_tau_tau_tau_tau
(D : FibonacciCyclotomicData K) :
forwardHexagonLHS D tau tau tau tau tau tau =
forwardHexagonRHS D tau tau tau tau tau tau := by
  simpa [
  forwardHexagonLHS,
  forwardHexagonRHS,
  FibF,
  FibR,
  fusionAllowed
  ] using forward_hexagon_tau_channel D

lemma reverse_hexagon_branch_tau_tau_tau_I_tau_tau
(D : FibonacciCyclotomicData K) :
reverseHexagonLHS D tau tau tau I tau tau =
reverseHexagonRHS D tau tau tau I tau tau := by
  simpa [
  reverseHexagonLHS,
  reverseHexagonRHS,
  FibF,
  FibRInv,
  fusionAllowed
  ] using reverse_hexagon_total_vacuum_channel D

lemma reverse_hexagon_branch_tau_tau_tau_tau_I_I
(D : FibonacciCyclotomicData K) :
reverseHexagonLHS D tau tau tau tau I I =
reverseHexagonRHS D tau tau tau tau I I := by
  simpa [
  reverseHexagonLHS,
  reverseHexagonRHS,
  FibF,
  FibRInv,
  fusionAllowed
  ] using reverse_hexagon_vacuum_channel D

lemma reverse_hexagon_branch_tau_tau_tau_tau_I_tau
(D : FibonacciCyclotomicData K) :
reverseHexagonLHS D tau tau tau tau I tau =
reverseHexagonRHS D tau tau tau tau I tau := by
  simpa [
  reverseHexagonLHS,
  reverseHexagonRHS,
  FibF,
  FibRInv,
  fusionAllowed
  ] using reverse_hexagon_mixed_channel D

lemma reverse_hexagon_branch_tau_tau_tau_tau_tau_I
(D : FibonacciCyclotomicData K) :
reverseHexagonLHS D tau tau tau tau tau I =
reverseHexagonRHS D tau tau tau tau tau I := by
  simpa [
  reverseHexagonLHS,
  reverseHexagonRHS,
  FibF,
  FibRInv,
  fusionAllowed
  ] using reverse_hexagon_mixed_channel_mirror D

lemma reverse_hexagon_branch_tau_tau_tau_tau_tau_tau
(D : FibonacciCyclotomicData K) :
reverseHexagonLHS D tau tau tau tau tau tau =
reverseHexagonRHS D tau tau tau tau tau tau := by
  simpa [
  reverseHexagonLHS,
  reverseHexagonRHS,
  FibF,
  FibRInv,
  fusionAllowed
  ] using reverse_hexagon_tau_channel D

theorem fib_anyons_true_forward_hexagon
(D : FibonacciCyclotomicData K) :
ForwardHexagonIdentity D := by
  intro a b c d e g
  cases a <;>
  cases b <;>
  cases c <;>
  cases d <;>
  cases e <;>
  cases g
  all_goals
  first
  | exact forward_hexagon_branch_tau_tau_tau_tau_I_I D
  | exact forward_hexagon_branch_tau_tau_tau_tau_I_tau D
  | exact forward_hexagon_branch_tau_tau_tau_tau_tau_I D
  | exact forward_hexagon_branch_tau_tau_tau_tau_tau_tau D
  | simp [
  forwardHexagonLHS,
  forwardHexagonRHS,
  FibF,
  FibR,
  fusionAllowed
  ] <;> ring

theorem fib_anyons_true_reverse_hexagon
(D : FibonacciCyclotomicData K) :
ReverseHexagonIdentity D := by
  intro a b c d e g
  cases a <;>
  cases b <;>
  cases c <;>
  cases d <;>
  cases e <;>
  cases g
  all_goals
  first
  | exact reverse_hexagon_branch_tau_tau_tau_I_tau_tau D
  | exact reverse_hexagon_branch_tau_tau_tau_tau_I_I D
  | exact reverse_hexagon_branch_tau_tau_tau_tau_I_tau D
  | exact reverse_hexagon_branch_tau_tau_tau_tau_tau_I D
  | exact reverse_hexagon_branch_tau_tau_tau_tau_tau_tau D
  | simp [
  reverseHexagonLHS,
  reverseHexagonRHS,
  FibF,
  FibRInv,
  fusionAllowed
  ] <;> ring

theorem fib_anyons_true_hexagon
(D : FibonacciCyclotomicData K) :
TrueHexagonIdentity D := by
  exact
  ⟨fib_anyons_true_forward_hexagon D,
  fib_anyons_true_reverse_hexagon D⟩

end FibAnyonTrueHexagon
