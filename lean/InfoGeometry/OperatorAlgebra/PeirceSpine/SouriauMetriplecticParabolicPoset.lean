/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Ring

/-!
# Souriau–Metriplectic–Parabolic Super-Grassmannian Poset (`𝔖𝔊₁ ≺ ⋯ ≺ 𝔖𝔊₈`)

This module formalizes the canonical noncommutative operator-algebra poset unifying
Souriau's symplectic/coadjoint mechanics, Brockett's double-commutator dissipation,
the DeWitt–Peirce para-Kähler Clifford core, moving-frame Euler/Coriolis/centrifugal
accelerations, chiral Cartan–MacDowell–Mansouri spin-wave curvature/torsion splitting,
quotiented tensor exterior calculus with Amari `α`-connection curvature and Bruhat
projector renormalization, three-horizon log-radial modular Weyl scaling `H = P₁ - P₂`,
and the 5-graded `3 × 3` parabolic Maurer–Cartan tower with `24 = 4!` Lagrange
grade projectors and `(ℤ/24ℤ)ˣ` Galois exponent-2 closure.

All declarations are formulated over an arbitrary associative (noncommutative) ring `B`
(`[Ring B]`), with choice-free cyclic trace functionals `CyclicTrace B M` valued in any
additive commutative group `[AddCommGroup M]`.

## Causal Poset Architecture (`𝔖𝔊₁ ≺ 𝔖𝔊₂ ≺ 𝔖𝔊₃ ≺ 𝔖𝔊₄ ≺ 𝔖𝔊₅ ≺ 𝔖𝔊₆ ≺ 𝔖𝔊₇ ≺ 𝔖𝔊₈`)

* `SG1` (`node1_lie_jordan_and_parakahler_clifford_core`):
  Noncommutative Lie–Jordan decomposition, para-Kähler reflection `S_P = 2P - 1`,
  and split-quaternion Clifford squares `Φ² = V`, `J² = -V`, `Σ² = V²`.
* `SG2` (`node2_souriau_brockett_trace_foliation_and_twin_bimodule`):
  Choice-free cyclic trace pairing `CyclicTrace B M`, twin bimodule `[L_a, R_b] = 0`,
  modular Laplacian `δ_K² = L_{K²} + R_{K²} - 2 C_K`, Souriau on-leaf orthogonality,
  Brockett cross-leaf dissipation, and centrifugal self-adjointness.
* `SG3` (`node3_moving_frame_euler_coriolis_centrifugal_and_aporia`):
  Second-order Leibniz defect `2 D(X) D(Y)` and moving-frame acceleration split into
  bare `D²`, Euler `[DΩ, X]`, Coriolis `2[Ω, DX]`, and centrifugal `[Ω, [Ω, X]]`.
* `SG4` (`node4_rotating_ball_parabolic_entropy_well_and_dewitt_lock`):
  DeWitt–Souriau–Brockett lock (`Ω = Σ`, `ρ = Φ`, `G = J`), radial gravity vs. Coriolis
  balance `-[Φ, [Φ, J]] + 2[Σ, Φ] = 0`, centrifugal vs. well balance
  `[Σ, [Σ, Φ]] + V[J, [J, Φ]] = 0`, and cubic Bruhat tail `2 P̂_± - 2 Ψ₁ = ∓[Σ, Φ]`.
* `SG5` (`node5_cartan_macdowell_mansouri_spin_wave_split_parity_and_gauge`):
  Forward/backward spin-wave curvatures `F(ω ± e)`, MacDowell–Mansouri sum, Cartan
  torsion difference, chiral parity mirror `S F(ω + e) S = F(ω - e)`, and non-abelian
  gauge covariance `∇_{ω'}(e') = g ∇_ω(e) g⁻¹`.
* `SG6` (`node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure`):
  Quotiented tensor exterior differentials `d_±² = 0`, graded Leibniz rule, `Cl(1,1)`
  anticommutation `{d_sum, d_diff} = 0`, Amari `α`-curvature `(d_sum + α d_diff)²(Z) = (1 - α²)[V, Z]`,
  Weitzenböck cross-derivative `d_diff(d_sum(Σ)) = 4 V²`, and Bruhat cure `2 P̂_± = 2 Ψ₁ ± d_±(Σ)`.
* `SG7` (`node7_log_radial_modular_time_and_five_graded_weyl_invariance`):
  Three orthogonal horizons `1 = P₁ + P₀ + P₂`, tripotent modular generator `H = P₁ - P₂` (`H³ = H`),
  expanding lightlike shells `[H, N_{±1}] = ±N_{±1}`, `[H, N_{±1}²] = ±2 N_{±1}²`,
  and Weyl scale invariance `[H, V_{1,2}] = [H, Σ_{1,2}] = 0`.
* `SG8` (`node8_parabolic_maurer_cartan_tower_24_projectors_and_galois`):
  5-graded `3 × 3` `ParabolicOp B` algebra, quintic Weyl annihilator `D⁵ - 5 D³ + 4 D = 0`,
  quartic chiral parity formula `3 S_par X S_par = 3 X - 8 D² X + 2 D⁴ X`, unipotent
  Maurer–Cartan dressing `g⁻¹ H g = H + θ_W`, flat cocycle `d_Q θ_Q + θ_Q² = 0`,
  `24 = 4!` Lagrange grade projectors, and `(ℤ/24ℤ)ˣ` Galois exponent-2 closure.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine

universe u v
variable {B : Type u} [Ring B]

/-! ### Causal Poset Indexing (`𝔖𝔊₁ ≺ ⋯ ≺ 𝔖𝔊₈`) -/

/-- The 8-node causal poset of the Souriau–Metriplectic–Parabolic synthesis. -/
inductive SouriauParabolicNode : Type
  | SG1_LieJordanParaKahlerCore
  | SG2_SouriauBrockettTwinBimodule
  | SG3_MovingFrameEulerCoriolisCentrifugal
  | SG4_RotatingBallParabolicEntropyWell
  | SG5_CartanMacDowellMansouriSpinWave
  | SG6_QuotientedExteriorAmariAlphaBruhat
  | SG7_LogRadialModularWeylHorizon
  | SG8_ParabolicMaurerCartan24Galois
  deriving DecidableEq, Repr

instance : Inhabited SouriauParabolicNode := ⟨.SG1_LieJordanParaKahlerCore⟩

/-- Monotone rank embedding `𝔖𝔊_k ↦ k` defining the partial order on `SouriauParabolicNode`. -/
def SouriauParabolicNode.rank : SouriauParabolicNode → ℕ
  | .SG1_LieJordanParaKahlerCore => 1
  | .SG2_SouriauBrockettTwinBimodule => 2
  | .SG3_MovingFrameEulerCoriolisCentrifugal => 3
  | .SG4_RotatingBallParabolicEntropyWell => 4
  | .SG5_CartanMacDowellMansouriSpinWave => 5
  | .SG6_QuotientedExteriorAmariAlphaBruhat => 6
  | .SG7_LogRadialModularWeylHorizon => 7
  | .SG8_ParabolicMaurerCartan24Galois => 8

instance : PartialOrder SouriauParabolicNode where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    revert hab hba; cases a <;> cases b <;> decide

/-! ### Primitive Definitions: Peirce Twin Waves & Exterior Differentials -/

/-- Chiral reflection `S_P = 2P - 1 = P - (1 - P)`. -/
def S_P (P : B) : B := P + P - 1

/-- Forward off-diagonal Peirce wave `N_+ = P X (1 - P)`. -/
def N_plus (P X : B) : B := P * X * (1 - P)

/-- Backward off-diagonal Peirce wave `N_- = (1 - P) Y P`. -/
def N_minus (P Y : B) : B := (1 - P) * Y * P

/-- Symmetric cross-leaf velocity / solder form `Φ = N_+ + N_-`. -/
def Phi_v (P X Y : B) : B := N_plus P X + N_minus P Y

/-- Skew on-leaf Maurer–Cartan generator `J = N_+ - N_-`. -/
def J_mc (P X Y : B) : B := N_plus P X - N_minus P Y

/-- Upper sheet quadratic operator `Q_+ = N_+ N_-`. -/
def Q_pos (P X Y : B) : B := N_plus P X * N_minus P Y

/-- Lower sheet quadratic operator `Q_- = N_- N_+`. -/
def Q_neg (P X Y : B) : B := N_minus P Y * N_plus P X

/-- Positive-sheet Jordan metric `V = {N_+, N_-} = Q_+ + Q_-`. -/
def V_met (P X Y : B) : B := Q_pos P X Y + Q_neg P X Y

/-- Bi-Lagrangian spin-vorticity curvature `Σ = [N_+, N_-] = Q_+ - Q_-`. -/
def Sigma_sp (P X Y : B) : B := Q_pos P X Y - Q_neg P X Y

/-- Chiral grading involution conjugation `Z ↦ S_P Z S_P`. -/
def chiralConj (P Z : B) : B := S_P P * Z * S_P P

/-- Forward graded exterior differential `d_+(Z) = N_+ Z - (S_P Z S_P) N_+`. -/
def d_plus (P X Z : B) : B := N_plus P X * Z - chiralConj P Z * N_plus P X

/-- Backward graded exterior differential `d_-(Z) = N_- Z - (S_P Z S_P) N_-`. -/
def d_minus (P Y Z : B) : B := N_minus P Y * Z - chiralConj P Z * N_minus P Y

/-- Symmetric exterior differential `d_sum = d_+ + d_-`. -/
def d_sum (P X Y Z : B) : B := d_plus P X Z + d_minus P Y Z

/-- Skew exterior differential `d_diff = d_+ - d_-`. -/
def d_diff (P X Y Z : B) : B := d_plus P X Z - d_minus P Y Z

/-- Amari `α`-connection exterior differential `d_α(Z) = d_sum(Z) + α d_diff(Z)`. -/
def d_alpha (P X Y α Z : B) : B := d_sum P X Y Z + α * d_diff P X Y Z

/-- Degree-2 truncated Schrieffer–Wolff / Bruhat projector `Ψ₁ = P + Φ - Σ`. -/
def Psi1 (P X Y : B) : B := P + Phi_v P X Y - Sigma_sp P X Y

/-- Exact degree-3 forward Bruhat projector `P̂_+ = Ψ₁ - V N_+`. -/
def P_hat_plus (P X Y : B) : B := Psi1 P X Y - V_met P X Y * N_plus P X

/-- Exact degree-3 backward Bruhat projector `P̂_- = Ψ₁ - V N_-`. -/
def P_hat_minus (P X Y : B) : B := Psi1 P X Y - V_met P X Y * N_minus P Y

/-- Exact degree-3 forward Bruhat reflection `Ŝ_+ = 2 P̂_+ - 1`. -/
def S_hat_plus (P X Y : B) : B :=
  S_P P + 2 • Phi_v P X Y - 2 • Sigma_sp P X Y + d_plus P X (Sigma_sp P X Y)

/-- Exact degree-3 backward Bruhat reflection `Ŝ_- = 2 P̂_- - 1`. -/
def S_hat_minus (P X Y : B) : B :=
  S_P P + 2 • Phi_v P X Y - 2 • Sigma_sp P X Y - d_minus P Y (Sigma_sp P X Y)

/-! ### Structural Peirce Reduction Lemmas (Keeping `S_P`, `N_plus`, `N_minus` Atomic) -/

theorem proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

macro "peirce_base_nf" hP:ident : tactic =>
  `(tactic| (
    try simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
                   mul_assoc, $hP:ident, proj_idem $hP:ident, mul_zero, zero_mul]
    try abel))

theorem S_P_sq {P : B} (hP : P * P = P) : S_P P * S_P P = 1 := by
  dsimp only [S_P]; peirce_base_nf hP

theorem S_P_sq_assoc {P : B} (hP : P * P = P) (Z : B) : S_P P * (S_P P * Z) = Z := by
  rw [← mul_assoc, S_P_sq hP, one_mul]

theorem N_plus_sq {P : B} (hP : P * P = P) (X : B) : N_plus P X * N_plus P X = 0 := by
  dsimp only [N_plus]; peirce_base_nf hP

theorem N_plus_sq_assoc {P : B} (hP : P * P = P) (X Z : B) :
    N_plus P X * (N_plus P X * Z) = 0 := by
  rw [← mul_assoc, N_plus_sq hP X, zero_mul]

theorem N_minus_sq {P : B} (hP : P * P = P) (Y : B) : N_minus P Y * N_minus P Y = 0 := by
  dsimp only [N_minus]; peirce_base_nf hP

theorem N_minus_sq_assoc {P : B} (hP : P * P = P) (Y Z : B) :
    N_minus P Y * (N_minus P Y * Z) = 0 := by
  rw [← mul_assoc, N_minus_sq hP Y, zero_mul]

theorem P_mul_N_plus {P : B} (hP : P * P = P) (X : B) : P * N_plus P X = N_plus P X := by
  dsimp only [N_plus]; peirce_base_nf hP

theorem P_mul_N_plus_assoc {P : B} (hP : P * P = P) (X Z : B) :
    P * (N_plus P X * Z) = N_plus P X * Z := by
  rw [← mul_assoc, P_mul_N_plus hP X]

theorem N_plus_mul_P {P : B} (hP : P * P = P) (X : B) : N_plus P X * P = 0 := by
  dsimp only [N_plus]; peirce_base_nf hP

theorem N_plus_mul_P_assoc {P : B} (hP : P * P = P) (X Z : B) :
    N_plus P X * (P * Z) = 0 := by
  rw [← mul_assoc, N_plus_mul_P hP X, zero_mul]

theorem P_mul_N_minus {P : B} (hP : P * P = P) (Y : B) : P * N_minus P Y = 0 := by
  dsimp only [N_minus]; peirce_base_nf hP

theorem P_mul_N_minus_assoc {P : B} (hP : P * P = P) (Y Z : B) :
    P * (N_minus P Y * Z) = 0 := by
  rw [← mul_assoc, P_mul_N_minus hP Y, zero_mul]

theorem N_minus_mul_P {P : B} (hP : P * P = P) (Y : B) : N_minus P Y * P = N_minus P Y := by
  dsimp only [N_minus]; peirce_base_nf hP

theorem N_minus_mul_P_assoc {P : B} (hP : P * P = P) (Y Z : B) :
    N_minus P Y * (P * Z) = N_minus P Y * Z := by
  rw [← mul_assoc, N_minus_mul_P hP Y]

theorem S_P_mul_N_plus {P : B} (hP : P * P = P) (X : B) : S_P P * N_plus P X = N_plus P X := by
  unfold S_P; simp only [add_mul, sub_mul, one_mul, P_mul_N_plus hP]; abel

theorem S_P_mul_N_plus_assoc {P : B} (hP : P * P = P) (X Z : B) :
    S_P P * (N_plus P X * Z) = N_plus P X * Z := by
  rw [← mul_assoc, S_P_mul_N_plus hP X]

theorem N_plus_mul_S_P {P : B} (hP : P * P = P) (X : B) : N_plus P X * S_P P = - N_plus P X := by
  unfold S_P; simp only [mul_add, mul_sub, mul_one, N_plus_mul_P hP]; abel

theorem N_plus_mul_S_P_assoc {P : B} (hP : P * P = P) (X Z : B) :
    N_plus P X * (S_P P * Z) = - (N_plus P X * Z) := by
  rw [← mul_assoc, N_plus_mul_S_P hP X, neg_mul]

theorem S_P_mul_N_minus {P : B} (hP : P * P = P) (Y : B) : S_P P * N_minus P Y = - N_minus P Y := by
  unfold S_P; simp only [add_mul, sub_mul, one_mul, P_mul_N_minus hP]; abel

theorem S_P_mul_N_minus_assoc {P : B} (hP : P * P = P) (Y Z : B) :
    S_P P * (N_minus P Y * Z) = - (N_minus P Y * Z) := by
  rw [← mul_assoc, S_P_mul_N_minus hP Y, neg_mul]

theorem N_minus_mul_S_P {P : B} (hP : P * P = P) (Y : B) : N_minus P Y * S_P P = N_minus P Y := by
  unfold S_P; simp only [mul_add, mul_sub, mul_one, N_minus_mul_P hP]; abel

theorem N_minus_mul_S_P_assoc {P : B} (hP : P * P = P) (Y Z : B) :
    N_minus P Y * (S_P P * Z) = N_minus P Y * Z := by
  rw [← mul_assoc, N_minus_mul_S_P hP Y]

/-- Normal-form tactic for atomic Peirce corner expressions (`S_P`, `N_plus`, `N_minus`). -/
macro "atomic_peirce_nf" hP:ident : tactic =>
  `(tactic| (
    try simp only [smul_add, smul_sub, two_nsmul,
      add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      neg_mul, mul_neg, mul_assoc,
      $hP:ident, proj_idem $hP:ident,
      S_P_sq $hP:ident, S_P_sq_assoc $hP:ident,
      N_plus_sq $hP:ident, N_plus_sq_assoc $hP:ident,
      N_minus_sq $hP:ident, N_minus_sq_assoc $hP:ident,
      P_mul_N_plus $hP:ident, P_mul_N_plus_assoc $hP:ident,
      N_plus_mul_P $hP:ident, N_plus_mul_P_assoc $hP:ident,
      P_mul_N_minus $hP:ident, P_mul_N_minus_assoc $hP:ident,
      N_minus_mul_P $hP:ident, N_minus_mul_P_assoc $hP:ident,
      S_P_mul_N_plus $hP:ident, S_P_mul_N_plus_assoc $hP:ident,
      N_plus_mul_S_P $hP:ident, N_plus_mul_S_P_assoc $hP:ident,
      S_P_mul_N_minus $hP:ident, S_P_mul_N_minus_assoc $hP:ident,
      N_minus_mul_S_P $hP:ident, N_minus_mul_S_P_assoc $hP:ident,
      mul_zero, zero_mul]
    <;> abel))

/-! ### Node `𝔖𝔊₁`: Noncommutative Lie–Jordan Cut & Para-Kähler Split-Quaternion Core -/

/-- **Node `𝔖𝔊₁`**: Noncommutative Lie–Jordan binary cut `2XY = [X,Y] + {X,Y}`, Jacobi and
Poisson–Jordan identities, para-Kähler bi-Lagrangian lock `Σ = S_P V = V S_P`, and
split-quaternion Clifford squares `Φ² = V`, `J² = -V`, `Σ² = V²`. -/
theorem node1_lie_jordan_and_parakahler_clifford_core
    (P X Y Z : B) (hP : P * P = P) :
    let sp := S_P P
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    comm X Y + anticomm X Y = 2 • (X * Y) ∧
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
    comm X (anticomm Y Z) = anticomm (comm X Y) Z + anticomm Y (comm X Z) ∧
    sp * sp = 1 ∧ s = sp * v ∧ s = v * sp ∧ v = sp * s ∧
    ph * ph = v ∧ j * j = - v ∧ s * s = v * v ∧
    comm v ph = 0 ∧ comm v j = 0 ∧ comm v s = 0 ∧
    anticomm ph j = 0 ∧ anticomm s ph = 0 ∧ anticomm s j = 0 := by
  refine ⟨?_, ?_, ?_, S_P_sq hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    atomic_peirce_nf hP

/-! ### Node `𝔖𝔊₂`: Choice-Free Cyclic Trace Foliation & Twin Bimodule Modular Flow -/

/-- Choice-free cyclic trace functional `τ : B →+ M` on a noncommutative ring `B` valued
in an additive commutative group `M`, satisfying `τ(x * y) = τ(y * x)`. -/
structure CyclicTrace (B : Type u) (M : Type v) [Ring B] [AddCommGroup M] where
  tr : B →+ M
  cyclic : ∀ x y : B, tr (x * y) = tr (y * x)

instance {M : Type v} [AddCommGroup M] : Inhabited (CyclicTrace B M) :=
  ⟨{ tr := 0, cyclic := fun _ _ => rfl }⟩

/-- Trace pairing `(X, Y) ↦ τ(X * Y)` associated to a cyclic trace `τ`. -/
def tracePairing {M : Type v} [AddCommGroup M] (τ : CyclicTrace B M) (X Y : B) : M :=
  τ.tr (X * Y)

theorem trace_comm_zero {M : Type v} [AddCommGroup M] (τ : CyclicTrace B M) (X Y : B) :
    τ.tr (comm X Y) = 0 := by
  unfold comm
  rw [map_sub, τ.cyclic X Y, sub_self]

/-- Souriau rotational coadjoint flow `[Ω, ρ]`. -/
def souriauRotational (Ω ρ : B) : B := comm Ω ρ

/-- Brockett irrotational double-commutator flow `[ρ, [ρ, G]]`. -/
def brockettIrrotational (G ρ : B) : B := comm ρ (comm ρ G)

/-- Combined Souriau–Brockett metriplectic vector field `[Ω, ρ] + [ρ, [ρ, G]]`. -/
def metriplecticFlow (Ω G ρ : B) : B := souriauRotational Ω ρ + brockettIrrotational G ρ

/-- Left multiplication operator `L_a(x) = a * x`. -/
def leftMul (a x : B) : B := a * x

/-- Right multiplication operator `R_b(x) = x * b`. -/
def rightMul (b x : B) : B := x * b

/-- Modular derivation `δ_K(x) = K * x - x * K`. -/
def modularDeriv (K x : B) : B := leftMul K x - rightMul K x

/-- Twin-sheet cross-correlation superoperator `C_K(x) = K * x * K`. -/
def twinCrossCorrelation (K x : B) : B := leftMul K (rightMul K x)

/-- **Node `𝔖𝔊₂`**: Choice-free cyclic trace foliation, twin bimodule commutativity
`[L_a, R_b] = 0`, modular Laplacian decomposition `δ_K² = L_{K²} + R_{K²} - 2 C_K`,
Souriau on-leaf orthogonality to the centralizer `Z(ρ)`, weak metriplectic duality,
and centrifugal self-adjointness. -/
theorem node2_souriau_brockett_trace_foliation_and_twin_bimodule
    {M : Type v} [AddCommGroup M] (τ : CyclicTrace B M)
    (K a b x Ω G ρ H Z : B) (hZ : comm ρ Z = 0) :
    leftMul a (rightMul b x) = rightMul b (leftMul a x) ∧
    modularDeriv K (modularDeriv K x) =
      leftMul (K * K) x + rightMul (K * K) x - 2 • twinCrossCorrelation K x ∧
    tracePairing τ (souriauRotational Ω ρ) Z = 0 ∧
    tracePairing τ (souriauRotational Ω ρ) ρ = 0 ∧
    tracePairing τ (metriplecticFlow Ω G ρ) H =
      tracePairing τ Ω (comm ρ H) - tracePairing τ (comm ρ G) (comm ρ H) ∧
    tracePairing τ (comm Ω (comm Ω x)) H = tracePairing τ x (comm Ω (comm Ω H)) := by
  have h_rot : ∀ U : B,
      tracePairing τ (souriauRotational Ω ρ) U = tracePairing τ Ω (comm ρ U) := by
    intro U
    unfold tracePairing souriauRotational
    have h_decomp : comm Ω ρ * U = comm (Ω * U) ρ + Ω * comm ρ U := by
      unfold comm; noncomm_ring
    rw [h_decomp, map_add, trace_comm_zero τ (Ω * U) ρ, zero_add]
  have h_irr : ∀ R U V : B,
      tracePairing τ (comm R (comm R U)) V = - tracePairing τ (comm R U) (comm R V) := by
    intro R U V
    unfold tracePairing
    have h_decomp : comm R (comm R U) * V = comm R (comm R U * V) - comm R U * comm R V := by
      unfold comm; noncomm_ring
    rw [h_decomp, map_sub, trace_comm_zero τ R (comm R U * V), zero_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [leftMul, rightMul]; noncomm_ring
  · dsimp only [modularDeriv, twinCrossCorrelation, leftMul, rightMul]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  · rw [h_rot Z, hZ]; unfold tracePairing; rw [mul_zero, map_zero]
  · rw [h_rot ρ]; unfold tracePairing comm; rw [sub_self, mul_zero, map_zero]
  · unfold metriplecticFlow brockettIrrotational
    have h_add : tracePairing τ (souriauRotational Ω ρ + comm ρ (comm ρ G)) H =
        tracePairing τ (souriauRotational Ω ρ) H + tracePairing τ (comm ρ (comm ρ G)) H := by
      unfold tracePairing; rw [add_mul, map_add]
    rw [h_add, h_rot H, h_irr ρ G H, ← sub_eq_add_neg]
  · have h_symm : tracePairing τ x (comm Ω (comm Ω H)) = tracePairing τ (comm Ω (comm Ω H)) x := by
      unfold tracePairing; exact τ.cyclic x (comm Ω (comm Ω H))
    rw [h_symm, h_irr Ω x H, h_irr Ω H x]
    unfold tracePairing
    rw [τ.cyclic (comm Ω x) (comm Ω H)]

/-! ### Node `𝔖𝔊₃`: Moving-Frame Derivations, Euler, Coriolis & Centrifugal Acceleration -/

/-- Ring derivation `D : B → B` satisfying additivity, subtraction, and the Leibniz rule. -/
structure OpDerivation (B : Type u) [Ring B] where
  toFun    : B → B
  map_add' : ∀ X Y, toFun (X + Y) = toFun X + toFun Y
  map_sub' : ∀ X Y, toFun (X - Y) = toFun X - toFun Y
  leibniz' : ∀ X Y, toFun (X * Y) = toFun X * Y + X * toFun Y

instance : Inhabited (OpDerivation B) :=
  ⟨{ toFun := fun _ => 0
     map_add' := fun _ _ => by simp
     map_sub' := fun _ _ => by simp
     leibniz' := fun _ _ => by simp }⟩

theorem OpDerivation.map_zero (D : OpDerivation B) : D.toFun 0 = 0 := by
  have h := D.map_sub' 0 0
  simpa [sub_self] using h

theorem OpDerivation.map_neg (D : OpDerivation B) (X : B) : D.toFun (-X) = - D.toFun X := by
  have h := D.map_sub' 0 X
  rw [zero_sub, D.map_zero, zero_sub] at h
  exact h

theorem OpDerivation.map_one (D : OpDerivation B) : D.toFun 1 = 0 := by
  have h := D.leibniz' 1 1; rw [mul_one] at h
  calc D.toFun 1 = (D.toFun 1 * 1 + 1 * D.toFun 1) - D.toFun 1 := by noncomm_ring
    _ = D.toFun 1 - D.toFun 1 := by rw [← h]
    _ = 0 := sub_self _

theorem OpDerivation.map_units_inv (D : OpDerivation B) (g : Bˣ) :
    D.toFun (↑g⁻¹ : B) = - (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by
  have h1 : D.toFun ((g : B) * (↑g⁻¹ : B)) = 0 := by rw [Units.mul_inv, D.map_one]
  rw [D.leibniz'] at h1
  calc D.toFun (↑g⁻¹ : B)
      = (↑g⁻¹ : B) * ((g : B) * D.toFun (↑g⁻¹ : B)) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (↑g⁻¹ : B) * ((D.toFun (g : B) * (↑g⁻¹ : B) + (g : B) * D.toFun (↑g⁻¹ : B)) -
          D.toFun (g : B) * (↑g⁻¹ : B)) := by noncomm_ring
    _ = (↑g⁻¹ : B) * (0 - D.toFun (g : B) * (↑g⁻¹ : B)) := by rw [h1]
    _ = - (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by noncomm_ring

/-- Rotating covariant derivative `∇_Ω X = D(X) + [Ω, X]`. -/
def rotatingCovariantDeriv (D : OpDerivation B) (Ω X : B) : B := D.toFun X + comm Ω X

/-- **Node `𝔖𝔊₃`**: Second-order Leibniz defect `2 D(X) D(Y)` and moving-frame acceleration
decomposition `∇_Ω² X = D²X + [DΩ, X] + 2[Ω, DX] + [Ω, [Ω, X]]`. -/
theorem node3_moving_frame_euler_coriolis_centrifugal_and_aporia
    (D : OpDerivation B) (Ω X Y : B) :
    D.toFun (D.toFun (X * Y)) - (D.toFun (D.toFun X) * Y + X * D.toFun (D.toFun Y)) =
      2 • (D.toFun X * D.toFun Y) ∧
    rotatingCovariantDeriv D Ω (rotatingCovariantDeriv D Ω X) =
      D.toFun (D.toFun X) + comm (D.toFun Ω) X +
        2 • comm Ω (D.toFun X) + comm Ω (comm Ω X) := by
  refine ⟨?_, ?_⟩
  · rw [D.leibniz', D.map_add', D.leibniz', D.leibniz']
    abel
  · unfold rotatingCovariantDeriv comm
    rw [D.map_add', D.map_sub', D.leibniz', D.leibniz']
    simp only [add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
    abel

/-! ### Node `𝔖𝔊₄`: Rotating Ball in the Parabolic Entropy Well & DeWitt Metriplectic Lock -/

/-- **Node `𝔖𝔊₄`**: The Rotating Ball in the Parabolic Entropy Well & DeWitt Metriplectic Lock
(`Ω = Σ`, `ρ = Φ`, `G = J`):
1. Coriolis velocity `[Σ, Φ] = 2 V J` vs. radial gravity pull `-[Φ, [Φ, J]] = -4 V J` (`-4VJ + 2(2VJ) = 0`),
2. Outward centrifugal `[Σ, [Σ, Φ]] = 4 V² Φ` vs. inward well pull `V[J, [J, Φ]] = -4 V² Φ`,
3. Degree-3 Bruhat projector tail `2 P̂_+ - 2 Ψ₁ = -[Σ, Φ]` and `2 P̂_- - 2 Ψ₁ = +[Σ, Φ]`. -/
theorem node4_rotating_ball_parabolic_entropy_well_and_dewitt_lock
    (P X Y : B) (hP : P * P = P) :
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    comm s ph = 2 • (v * j) ∧
    - comm ph (comm ph j) = - (4 • (v * j)) ∧
    - comm ph (comm ph j) + 2 • comm s ph = 0 ∧
    comm s (comm s ph) = 4 • (v * v * ph) ∧
    v * comm j (comm j ph) = - (4 • (v * v * ph)) ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 ∧
    2 • P_hat_plus P X Y - 2 • Psi1 P X Y = d_plus P X s ∧
    2 • P_hat_minus P X Y - 2 • Psi1 P X Y = - d_minus P Y s ∧
    2 • P_hat_minus P X Y - 2 • P_hat_plus P X Y = comm s ph := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [P_hat_plus, P_hat_minus, Psi1, Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg,
                d_plus, d_minus, chiralConj, comm]
    atomic_peirce_nf hP

/-! ### Node `𝔖𝔊₅`: Cartan–MacDowell–Mansouri Spin-Wave Split, Parity Mirror & Gauge Covariance -/

/-- Non-abelian curvature 2-form `F_{12}(ω) = D₁(ω₂) - D₂(ω₁) + [ω₁, ω₂]`. -/
def curvature2Form (D1 D2 : OpDerivation B) (ω1 ω2 : B) : B :=
  D1.toFun ω2 - D2.toFun ω1 + comm ω1 ω2

/-- Cartan torsion 2-form `T_{12}(ω, e) = D₁(e₂) - D₂(e₁) + [ω₁, e₂] - [ω₂, e₁]`. -/
def torsion2Form (D1 D2 : OpDerivation B) (ω1 ω2 e1 e2 : B) : B :=
  D1.toFun e2 - D2.toFun e1 + comm ω1 e2 - comm ω2 e1

/-- Non-abelian gauge transformation of connection `ω' = g ω g⁻¹ - D(g) g⁻¹`. -/
def gaugeTransformConn (D : OpDerivation B) (g : Bˣ) (ω : B) : B :=
  (g : B) * ω * (↑g⁻¹ : B) - D.toFun (g : B) * (↑g⁻¹ : B)

/-- Adjoint gauge transformation of frame / vielbein `e' = g e g⁻¹`. -/
def gaugeTransformFrame (g : Bˣ) (e : B) : B :=
  (g : B) * e * (↑g⁻¹ : B)

/-- Adjoint covariant derivative `∇^ad_ω(e) = D(e) + [ω, e]`. -/
def adjointCovariantDeriv (D : OpDerivation B) (ω e : B) : B :=
  D.toFun e + comm ω e

/-- **Node `𝔖𝔊₅`**: Chiral Cartan–MacDowell–Mansouri spin-wave curvature/torsion split,
chiral parity reflection `S F_{12}(ω + e) S = F_{12}(ω - e)`, and non-abelian gauge covariance
`∇^ad_{ω'}(e') = g ∇^ad_ω(e) g⁻¹`. -/
theorem node5_cartan_macdowell_mansouri_spin_wave_split_parity_and_gauge
    (D D1 D2 : OpDerivation B) (g : Bˣ) (S ω ω1 ω2 e e1 e2 : B)
    (hS2 : S * S = 1)
    (hDS1 : ∀ Z, D1.toFun (S * Z * S) = S * D1.toFun Z * S)
    (hDS2 : ∀ Z, D2.toFun (S * Z * S) = S * D2.toFun Z * S)
    (hω1 : S * ω1 * S = ω1) (hω2 : S * ω2 * S = ω2)
    (he1 : S * e1 * S = -e1) (he2 : S * e2 * S = -e2) :
    let F_pos := curvature2Form D1 D2 (ω1 + e1) (ω2 + e2)
    let F_neg := curvature2Form D1 D2 (ω1 - e1) (ω2 - e2)
    F_pos + F_neg = 2 • curvature2Form D1 D2 ω1 ω2 + 2 • comm e1 e2 ∧
    F_pos - F_neg = 2 • torsion2Form D1 D2 ω1 ω2 e1 e2 ∧
    S * F_pos * S = F_neg ∧
    adjointCovariantDeriv D (gaugeTransformConn D g ω) (gaugeTransformFrame g e) =
      gaugeTransformFrame g (adjointCovariantDeriv D ω e) := by
  have hS_inv : ∀ U V : B, (S * U * S) * (S * V * S) = S * (U * V) * S := by
    intro U V
    calc (S * U * S) * (S * V * S)
        = S * U * (S * S) * V * S := by noncomm_ring
      _ = S * (U * V) * S := by rw [hS2]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [curvature2Form, comm]
    rw [D1.map_add', D2.map_add', D1.map_sub', D2.map_sub']
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    abel
  · dsimp only [curvature2Form, torsion2Form, comm]
    rw [D1.map_add', D2.map_add', D1.map_sub', D2.map_sub']
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    abel
  · dsimp only [curvature2Form, comm]
    have h1 : S * D1.toFun (ω2 + e2) * S = D1.toFun (ω2 - e2) := by
      rw [← hDS1 (ω2 + e2)]
      have h_in : S * (ω2 + e2) * S = ω2 - e2 := by
        calc S * (ω2 + e2) * S = S * ω2 * S + S * e2 * S := by noncomm_ring
          _ = ω2 - e2 := by rw [hω2, he2]; abel
      rw [h_in]
    have h2 : S * D2.toFun (ω1 + e1) * S = D2.toFun (ω1 - e1) := by
      rw [← hDS2 (ω1 + e1)]
      have h_in : S * (ω1 + e1) * S = ω1 - e1 := by
        calc S * (ω1 + e1) * S = S * ω1 * S + S * e1 * S := by noncomm_ring
          _ = ω1 - e1 := by rw [hω1, he1]; abel
      rw [h_in]
    have h3 : S * ((ω1 + e1) * (ω2 + e2)) * S = (ω1 - e1) * (ω2 - e2) := by
      rw [← hS_inv (ω1 + e1) (ω2 + e2)]
      have ha : S * (ω1 + e1) * S = ω1 - e1 := by
        calc S * (ω1 + e1) * S = S * ω1 * S + S * e1 * S := by noncomm_ring
          _ = ω1 - e1 := by rw [hω1, he1]; abel
      have hb : S * (ω2 + e2) * S = ω2 - e2 := by
        calc S * (ω2 + e2) * S = S * ω2 * S + S * e2 * S := by noncomm_ring
          _ = ω2 - e2 := by rw [hω2, he2]; abel
      rw [ha, hb]
    have h4 : S * ((ω2 + e2) * (ω1 + e1)) * S = (ω2 - e2) * (ω1 - e1) := by
      rw [← hS_inv (ω2 + e2) (ω1 + e1)]
      have ha : S * (ω1 + e1) * S = ω1 - e1 := by
        calc S * (ω1 + e1) * S = S * ω1 * S + S * e1 * S := by noncomm_ring
          _ = ω1 - e1 := by rw [hω1, he1]; abel
      have hb : S * (ω2 + e2) * S = ω2 - e2 := by
        calc S * (ω2 + e2) * S = S * ω2 * S + S * e2 * S := by noncomm_ring
          _ = ω2 - e2 := by rw [hω2, he2]; abel
      rw [hb, ha]
    calc S * (D1.toFun (ω2 + e2) - D2.toFun (ω1 + e1) +
              ((ω1 + e1) * (ω2 + e2) - (ω2 + e2) * (ω1 + e1))) * S
        = S * D1.toFun (ω2 + e2) * S - S * D2.toFun (ω1 + e1) * S +
          (S * ((ω1 + e1) * (ω2 + e2)) * S - S * ((ω2 + e2) * (ω1 + e1)) * S) := by noncomm_ring
      _ = D1.toFun (ω2 - e2) - D2.toFun (ω1 - e1) +
          ((ω1 - e1) * (ω2 - e2) - (ω2 - e2) * (ω1 - e1)) := by rw [h1, h2, h3, h4]
  · unfold adjointCovariantDeriv gaugeTransformConn gaugeTransformFrame comm
    rw [D.leibniz', D.leibniz', D.map_units_inv g]
    calc (D.toFun (g : B) * e + (g : B) * D.toFun e) * (↑g⁻¹ : B) +
          (g : B) * e * (- (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B)) +
         (((g : B) * ω * (↑g⁻¹ : B) - D.toFun (g : B) * (↑g⁻¹ : B)) * ((g : B) * e * (↑g⁻¹ : B)) -
          ((g : B) * e * (↑g⁻¹ : B)) * ((g : B) * ω * (↑g⁻¹ : B) - D.toFun (g : B) * (↑g⁻¹ : B)))
      _ = (g : B) * D.toFun e * (↑g⁻¹ : B) +
          (g : B) * ω * ((↑g⁻¹ : B) * (g : B)) * e * (↑g⁻¹ : B) -
          D.toFun (g : B) * ((↑g⁻¹ : B) * (g : B)) * e * (↑g⁻¹ : B) -
          (g : B) * e * ((↑g⁻¹ : B) * (g : B)) * ω * (↑g⁻¹ : B) +
          D.toFun (g : B) * e * (↑g⁻¹ : B) := by noncomm_ring
      _ = (g : B) * (D.toFun e + (ω * e - e * ω)) * (↑g⁻¹ : B) := by
          rw [Units.inv_mul]; noncomm_ring

/-! ### Node `𝔖𝔊₆`: Quotiented Tensor Exterior Calculus, Amari `α`-Curvature & Bruhat Cure -/

/-- **Node `𝔖𝔊₆`**: Intrinsic square-zero differentials `d_±² = 0`, graded Leibniz rule,
metric genesis `d_+(N_-) = V`, metric closure `d_±(V) = 0`, `Cl(1,1)` anticommutation
`{d_sum, d_diff} = 0`, Weitzenböck cross-derivative `d_diff(d_sum(Σ)) = 4 V²`,
universal Amari `α`-connection curvature `(d_sum + α d_diff)²(Z) = (1 - α²)[V, Z]`,
and exterior Bruhat renormalization `2 P̂_+ = 2 Ψ₁ + d_+(Σ)`. -/
theorem node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure
    (P X Y α Z Z1 Z2 : B) (hP : P * P = P) (hα : ∀ W : B, α * W = W * α) :
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    d_plus P X (d_plus P X Z) = 0 ∧
    d_minus P Y (d_minus P Y Z) = 0 ∧
    d_plus P X (Z1 * Z2) = d_plus P X Z1 * Z2 + chiralConj P Z1 * d_plus P X Z2 ∧
    d_plus P X (N_minus P Y) = v ∧
    d_plus P X v = 0 ∧ d_minus P Y v = 0 ∧
    d_sum P X Y s = - (2 • (v * j)) ∧
    d_diff P X Y s = - (2 • (v * ph)) ∧
    d_sum P X Y (d_diff P X Y Z) + d_diff P X Y (d_sum P X Y Z) = 0 ∧
    d_diff P X Y (d_sum P X Y s) = 4 • (v * v) ∧
    d_alpha P X Y α (d_alpha P X Y α Z) = (1 - α * α) * comm v Z ∧
    2 • P_hat_plus P X Y = 2 • Psi1 P X Y + d_plus P X s ∧
    P_hat_plus P X Y * P_hat_plus P X Y = P_hat_plus P X Y ∧
    S_hat_plus P X Y * S_hat_plus P X Y = 1 ∧
    S_hat_minus P X Y - S_hat_plus P X Y = - d_sum P X Y s := by
  have h_lin_plus : ∀ W : B, d_plus P X (α * W) = α * d_plus P X W := by
    intro W; unfold d_plus chiralConj
    calc N_plus P X * (α * W) - S_P P * (α * W) * S_P P * N_plus P X
        = (N_plus P X * α) * W - (S_P P * α) * W * S_P P * N_plus P X := by noncomm_ring
      _ = (α * N_plus P X) * W - (α * S_P P) * W * S_P P * N_plus P X := by
          rw [← hα (N_plus P X), ← hα (S_P P)]
      _ = α * (N_plus P X * W - S_P P * W * S_P P * N_plus P X) := by noncomm_ring
  have h_lin_minus : ∀ W : B, d_minus P Y (α * W) = α * d_minus P Y W := by
    intro W; unfold d_minus chiralConj
    calc N_minus P Y * (α * W) - S_P P * (α * W) * S_P P * N_minus P Y
        = (N_minus P Y * α) * W - (S_P P * α) * W * S_P P * N_minus P Y := by noncomm_ring
      _ = (α * N_minus P Y) * W - (α * S_P P) * W * S_P P * N_minus P Y := by
          rw [← hα (N_minus P Y), ← hα (S_P P)]
      _ = α * (N_minus P Y * W - S_P P * W * S_P P * N_minus P Y) := by noncomm_ring
  have h_lin_sum : ∀ W : B, d_sum P X Y (α * W) = α * d_sum P X Y W := by
    intro W; unfold d_sum; rw [h_lin_plus, h_lin_minus, ← mul_add]
  have h_lin_diff : ∀ W : B, d_diff P X Y (α * W) = α * d_diff P X Y W := by
    intro W; unfold d_diff; rw [h_lin_plus, h_lin_minus, ← mul_sub]
  have h_add_s : ∀ U W : B, d_sum P X Y (U + W) = d_sum P X Y U + d_sum P X Y W := by
    intro U W; unfold d_sum d_plus d_minus chiralConj; noncomm_ring
  have h_add_d : ∀ U W : B, d_diff P X Y (U + W) = d_diff P X Y U + d_diff P X Y W := by
    intro U W; unfold d_diff d_plus d_minus chiralConj; noncomm_ring
  have h_anti : d_sum P X Y (d_diff P X Y Z) + d_diff P X Y (d_sum P X Y Z) = 0 := by
    dsimp only [d_sum, d_diff, d_plus, d_minus, chiralConj]; atomic_peirce_nf hP
  have h_sq_s : d_sum P X Y (d_sum P X Y Z) = comm (V_met P X Y) Z := by
    dsimp only [d_sum, d_plus, d_minus, chiralConj, V_met, Q_pos, Q_neg, comm]; atomic_peirce_nf hP
  have h_sq_d : d_diff P X Y (d_diff P X Y Z) = - comm (V_met P X Y) Z := by
    dsimp only [d_diff, d_plus, d_minus, chiralConj, V_met, Q_pos, Q_neg, comm]; atomic_peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_anti, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [d_plus, chiralConj]; atomic_peirce_nf hP
  · dsimp only [d_minus, chiralConj]; atomic_peirce_nf hP
  · dsimp only [d_plus, chiralConj]; atomic_peirce_nf hP
  · dsimp only [d_plus, chiralConj, V_met, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [d_plus, chiralConj, V_met, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [d_minus, chiralConj, V_met, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [d_sum, d_plus, d_minus, chiralConj, J_mc, V_met, Sigma_sp, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [d_diff, d_plus, d_minus, chiralConj, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [d_sum, d_diff, d_plus, d_minus, chiralConj, V_met, Sigma_sp, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [d_alpha]
    rw [h_add_s, h_add_d, h_lin_sum, h_lin_diff]
    calc d_sum P X Y (d_sum P X Y Z) + α * d_sum P X Y (d_diff P X Y Z) +
         α * (d_diff P X Y (d_sum P X Y Z) + α * d_diff P X Y (d_diff P X Y Z))
      _ = d_sum P X Y (d_sum P X Y Z) +
          α * (d_sum P X Y (d_diff P X Y Z) + d_diff P X Y (d_sum P X Y Z)) +
          (α * α) * d_diff P X Y (d_diff P X Y Z) := by simp only [mul_add, mul_assoc]; abel
      _ = (1 - α * α) * comm (V_met P X Y) Z := by
          rw [h_anti, mul_zero, add_zero, h_sq_s, h_sq_d]
          simp only [sub_mul, one_mul, mul_neg]; abel
  · dsimp only [P_hat_plus, Psi1, d_plus, chiralConj, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [P_hat_plus, Psi1, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [S_hat_plus, d_plus, chiralConj, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]; atomic_peirce_nf hP
  · dsimp only [S_hat_plus, S_hat_minus, d_sum]; abel

/-! ### Node `𝔖𝔊₇`: Log-Radial Modular Time (`H = P₁ - P₂`) & 5-Graded Weyl Scale Invariance -/

theorem comm_mul_leibniz (A B_op C_op : B) :
    comm A (B_op * C_op) = comm A B_op * C_op + B_op * comm A C_op := by
  unfold comm; noncomm_ring

theorem comm_add_right (A B_op C_op : B) :
    comm A (B_op + C_op) = comm A B_op + comm A C_op := by
  unfold comm; noncomm_ring

theorem comm_sub_right (A B_op C_op : B) :
    comm A (B_op - C_op) = comm A B_op - comm A C_op := by
  unfold comm; noncomm_ring

macro "parabolic_idem_nf" h1:ident h2:ident h12:ident h21:ident
    h1':ident h2':ident h12':ident h21':ident : tactic =>
  `(tactic| (
    try simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc,
                   $h1:ident, $h2:ident, $h12:ident, $h21:ident,
                   $h1':ident, $h2':ident, $h12':ident, $h21':ident,
                   mul_zero, zero_mul]
    abel))

/-- **Node `𝔖𝔊₇`**: Three orthogonal horizons `1 = P₁ + P₀ + P₂`, tripotent modular Weyl
generator `H = P₁ - P₂` (`H³ = H`), expanding lightlike shells `[H, N_{±1}] = ±N_{±1}`
and `[H, N_{±1}²] = ±2 N_{±1}²` (`N_{±1}³ = 0`), and Weyl scale invariance
`[H, V₁] = [H, Σ₁] = [H, V₂] = [H, Σ₂] = 0`. -/
theorem node7_log_radial_modular_time_and_five_graded_weyl_invariance
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0  := 1 - P1 - P2
    let H   := P1 - P2
    let Np1 := P1 * X * P0 + P0 * X * P2
    let Nm1 := P0 * Y * P1 + P2 * Y * P0
    let Np2 := Np1 * Np1
    let Nm2 := Nm1 * Nm1
    let V1  := anticomm Np1 Nm1
    let S1  := comm Np1 Nm1
    let V2  := anticomm Np2 Nm2
    let S2  := comm Np2 Nm2
    P0 * P0 = P0 ∧ H * (H * H) = H ∧
    Np2 = P1 * X * P0 * X * P2 ∧ Np1 * Np2 = 0 ∧
    comm H Np1 = Np1 ∧ comm H Nm1 = - Nm1 ∧
    comm H Np2 = 2 • Np2 ∧ comm H Nm2 = - (2 • Nm2) ∧
    comm H V1 = 0 ∧ comm H S1 = 0 ∧ comm H V2 = 0 ∧ comm H S2 = 0 := by
  intro P0 H Np1 Nm1 Np2 Nm2 V1 S1 V2 S2
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have hP0_sq : P0 * P0 = P0 := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hH_cub : H * (H * H) = H := by
    dsimp only [H]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hNp2_eq : Np2 = P1 * X * P0 * X * P2 := by
    dsimp only [Np2, Np1, P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hNp3_zero : Np1 * Np2 = 0 := by
    rw [hNp2_eq]; dsimp only [Np1, P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_comm_p1 : comm H Np1 = Np1 := by
    dsimp only [H, Np1, P0, comm]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_comm_m1 : comm H Nm1 = - Nm1 := by
    dsimp only [H, Nm1, P0, comm]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_comm_p2 : comm H Np2 = 2 • Np2 := by
    dsimp only [Np2]
    rw [comm_mul_leibniz H Np1 Np1, h_comm_p1]
    abel
  have h_comm_m2 : comm H Nm2 = - (2 • Nm2) := by
    dsimp only [Nm2]
    rw [comm_mul_leibniz H Nm1 Nm1, h_comm_m1]
    simp only [neg_mul, mul_neg]
    abel
  have h_V1 : comm H V1 = 0 := by
    change comm H (Np1 * Nm1 + Nm1 * Np1) = 0
    rw [comm_add_right, comm_mul_leibniz H Np1 Nm1, comm_mul_leibniz H Nm1 Np1, h_comm_p1, h_comm_m1]
    simp only [neg_mul, mul_neg]
    abel
  refine ⟨hP0_sq, hH_cub, hNp2_eq, hNp3_zero, h_comm_p1, h_comm_m1, h_comm_p2, h_comm_m2,
          h_V1, ?_, ?_, ?_⟩
  · change comm H (Np1 * Nm1 - Nm1 * Np1) = 0
    rw [comm_sub_right, comm_mul_leibniz H Np1 Nm1, comm_mul_leibniz H Nm1 Np1, h_comm_p1, h_comm_m1]
    simp only [neg_mul, mul_neg]
    abel
  · change comm H (Np2 * Nm2 + Nm2 * Np2) = 0
    rw [comm_add_right, comm_mul_leibniz H Np2 Nm2, comm_mul_leibniz H Nm2 Np2, h_comm_p2, h_comm_m2]
    simp only [two_nsmul, add_mul, mul_add, neg_mul, mul_neg]
    abel
  · change comm H (Np2 * Nm2 - Nm2 * Np2) = 0
    rw [comm_sub_right, comm_mul_leibniz H Np2 Nm2, comm_mul_leibniz H Nm2 Np2, h_comm_p2, h_comm_m2]
    simp only [two_nsmul, add_mul, mul_add, neg_mul, mul_neg]
    abel

/-! ### Node `𝔖𝔊₈`: 5-Graded Parabolic Maurer–Cartan Tower, `24 = 4!` Projectors & Galois Closure -/

/-- The `3 × 3` 5-graded Super-Grassmannian / parabolic operator algebra over `B`. -/
@[ext]
structure ParabolicOp (B : Type u) where
  a00 : B
  a01 : B
  a02 : B
  a10 : B
  a11 : B
  a12 : B
  a20 : B
  a21 : B
  a22 : B

namespace ParabolicOp

instance : Zero (ParabolicOp B) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
instance : One  (ParabolicOp B) := ⟨⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩⟩
instance : Inhabited (ParabolicOp B) := ⟨0⟩

instance : Add (ParabolicOp B) := ⟨fun X Y =>
  ⟨X.a00 + Y.a00, X.a01 + Y.a01, X.a02 + Y.a02,
   X.a10 + Y.a10, X.a11 + Y.a11, X.a12 + Y.a12,
   X.a20 + Y.a20, X.a21 + Y.a21, X.a22 + Y.a22⟩⟩

instance : Sub (ParabolicOp B) := ⟨fun X Y =>
  ⟨X.a00 - Y.a00, X.a01 - Y.a01, X.a02 - Y.a02,
   X.a10 - Y.a10, X.a11 - Y.a11, X.a12 - Y.a12,
   X.a20 - Y.a20, X.a21 - Y.a21, X.a22 - Y.a22⟩⟩

instance : Neg (ParabolicOp B) := ⟨fun X =>
  ⟨-X.a00, -X.a01, -X.a02, -X.a10, -X.a11, -X.a12, -X.a20, -X.a21, -X.a22⟩⟩

instance : Mul (ParabolicOp B) := ⟨fun X Y =>
  ⟨X.a00 * Y.a00 + X.a01 * Y.a10 + X.a02 * Y.a20,
   X.a00 * Y.a01 + X.a01 * Y.a11 + X.a02 * Y.a21,
   X.a00 * Y.a02 + X.a01 * Y.a12 + X.a02 * Y.a22,
   X.a10 * Y.a00 + X.a11 * Y.a10 + X.a12 * Y.a20,
   X.a10 * Y.a01 + X.a11 * Y.a11 + X.a12 * Y.a21,
   X.a10 * Y.a02 + X.a11 * Y.a12 + X.a12 * Y.a22,
   X.a20 * Y.a00 + X.a21 * Y.a10 + X.a22 * Y.a20,
   X.a20 * Y.a01 + X.a21 * Y.a11 + X.a22 * Y.a21,
   X.a20 * Y.a02 + X.a21 * Y.a12 + X.a22 * Y.a22⟩⟩

@[simp] theorem zero_mk : (0 : ParabolicOp B) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem one_mk  : (1 : ParabolicOp B) = ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ := rfl
@[simp] theorem add_mk (X Y : ParabolicOp B) :
    X + Y = ⟨X.a00 + Y.a00, X.a01 + Y.a01, X.a02 + Y.a02,
             X.a10 + Y.a10, X.a11 + Y.a11, X.a12 + Y.a12,
             X.a20 + Y.a20, X.a21 + Y.a21, X.a22 + Y.a22⟩ := rfl
@[simp] theorem sub_mk (X Y : ParabolicOp B) :
    X - Y = ⟨X.a00 - Y.a00, X.a01 - Y.a01, X.a02 - Y.a02,
             X.a10 - Y.a10, X.a11 - Y.a11, X.a12 - Y.a12,
             X.a20 - Y.a20, X.a21 - Y.a21, X.a22 - Y.a22⟩ := rfl
@[simp] theorem neg_mk (X : ParabolicOp B) :
    -X = ⟨-X.a00, -X.a01, -X.a02, -X.a10, -X.a11, -X.a12, -X.a20, -X.a21, -X.a22⟩ := rfl
@[simp] theorem mul_mk (X Y : ParabolicOp B) :
    X * Y = ⟨X.a00 * Y.a00 + X.a01 * Y.a10 + X.a02 * Y.a20,
             X.a00 * Y.a01 + X.a01 * Y.a11 + X.a02 * Y.a21,
             X.a00 * Y.a02 + X.a01 * Y.a12 + X.a02 * Y.a22,
             X.a10 * Y.a00 + X.a11 * Y.a10 + X.a12 * Y.a20,
             X.a10 * Y.a01 + X.a11 * Y.a11 + X.a12 * Y.a21,
             X.a10 * Y.a02 + X.a11 * Y.a12 + X.a12 * Y.a22,
             X.a20 * Y.a00 + X.a21 * Y.a10 + X.a22 * Y.a20,
             X.a20 * Y.a01 + X.a21 * Y.a11 + X.a22 * Y.a21,
             X.a20 * Y.a02 + X.a21 * Y.a12 + X.a22 * Y.a22⟩ := rfl

/-- Integer scalar multiplication on `ParabolicOp B`. -/
def smulZ (c : ℤ) (X : ParabolicOp B) : ParabolicOp B :=
  ⟨c • X.a00, c • X.a01, c • X.a02,
   c • X.a10, c • X.a11, c • X.a12,
   c • X.a20, c • X.a21, c • X.a22⟩

/-- Commutator in `ParabolicOp B`. -/
def pComm (X Y : ParabolicOp B) : ParabolicOp B := X * Y - Y * X

/-- Grade `-2` projection. -/
def gradeNeg2 (X : ParabolicOp B) : ParabolicOp B := ⟨0, 0, 0, 0, 0, 0, X.a20, 0, 0⟩
/-- Grade `-1` projection. -/
def gradeNeg1 (X : ParabolicOp B) : ParabolicOp B := ⟨0, 0, 0, X.a10, 0, 0, 0, X.a21, 0⟩
/-- Grade `0` projection. -/
def gradeZero (X : ParabolicOp B) : ParabolicOp B := ⟨X.a00, 0, 0, 0, X.a11, 0, 0, 0, X.a22⟩
/-- Grade `+1` projection. -/
def gradePos1 (X : ParabolicOp B) : ParabolicOp B := ⟨0, X.a01, 0, 0, 0, X.a12, 0, 0, 0⟩
/-- Grade `+2` projection. -/
def gradePos2 (X : ParabolicOp B) : ParabolicOp B := ⟨0, 0, X.a02, 0, 0, 0, 0, 0, 0⟩

/-- Internal Weyl grading generator `H = diag(1, 0, -1)`. -/
def weylH : ParabolicOp B := ⟨1, 0, 0, 0, 0, 0, 0, 0, -1⟩
/-- Horizon idempotent `P_hor = H² = diag(1, 0, 1)`. -/
def P_hor : ParabolicOp B := (weylH : ParabolicOp B) * weylH
/-- Parabolic chiral grading involution `S_par = 2 H² - 1 = diag(1, -1, 1)`. -/
def S_par : ParabolicOp B := (P_hor : ParabolicOp B) + P_hor - 1

/-- Adjoint Weyl derivation `D(X) = [H, X]` and its powers `D² .. D⁵`. -/
def D  (X : ParabolicOp B) : ParabolicOp B := pComm weylH X
def D2 (X : ParabolicOp B) : ParabolicOp B := D (D X)
def D3 (X : ParabolicOp B) : ParabolicOp B := D (D2 X)
def D4 (X : ParabolicOp B) : ParabolicOp B := D (D3 X)
def D5 (X : ParabolicOp B) : ParabolicOp B := D (D4 X)

/-- Nilpotent contact differential `d_Q(C, Z) = [gradePos2 C, Z]`. -/
def d_Q (C Z : ParabolicOp B) : ParabolicOp B := pComm (gradePos2 C) Z

/-- The five `24 = 4!` Lagrange interpolation polynomials in `D = ad_H`. -/
def Poly24_0    (X : ParabolicOp B) : ParabolicOp B := smulZ 6 (D4 X) - smulZ 30 (D2 X) + smulZ 24 X
def Poly24_pos1 (X : ParabolicOp B) : ParabolicOp B := - smulZ 4 (D4 X) - smulZ 4 (D3 X) + smulZ 16 (D2 X) + smulZ 16 (D X)
def Poly24_neg1 (X : ParabolicOp B) : ParabolicOp B := - smulZ 4 (D4 X) + smulZ 4 (D3 X) + smulZ 16 (D2 X) - smulZ 16 (D X)
def Poly24_pos2 (X : ParabolicOp B) : ParabolicOp B := D4 X + smulZ 2 (D3 X) - D2 X - smulZ 2 (D X)
def Poly24_neg2 (X : ParabolicOp B) : ParabolicOp B := D4 X - smulZ 2 (D3 X) - D2 X + smulZ 2 (D X)

theorem S_par_eq : (S_par : ParabolicOp B) = ⟨1, 0, 0, 0, -1, 0, 0, 0, 1⟩ := by
  dsimp only [S_par, P_hor, weylH]
  simp only [mul_mk, add_mk, sub_mk, one_mk]
  ext <;> dsimp <;> noncomm_ring

theorem D_eq (X : ParabolicOp B) :
    D X = ⟨0, X.a01, (2 : ℤ) • X.a02,
           -X.a10, 0, X.a12,
           (-2 : ℤ) • X.a20, -X.a21, 0⟩ := by
  dsimp only [D, pComm, weylH]
  simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

theorem D2_eq (X : ParabolicOp B) :
    D2 X = ⟨0, X.a01, (4 : ℤ) • X.a02,
            X.a10, 0, X.a12,
            (4 : ℤ) • X.a20, X.a21, 0⟩ := by
  unfold D2; rw [D_eq (D X), D_eq X]
  ext <;> dsimp <;> abel

theorem D3_eq (X : ParabolicOp B) :
    D3 X = ⟨0, X.a01, (8 : ℤ) • X.a02,
            -X.a10, 0, X.a12,
            (-8 : ℤ) • X.a20, -X.a21, 0⟩ := by
  unfold D3; rw [D_eq (D2 X), D2_eq X]
  ext <;> dsimp <;> abel

theorem D4_eq (X : ParabolicOp B) :
    D4 X = ⟨0, X.a01, (16 : ℤ) • X.a02,
            X.a10, 0, X.a12,
            (16 : ℤ) • X.a20, X.a21, 0⟩ := by
  unfold D4; rw [D_eq (D3 X), D3_eq X]
  ext <;> dsimp <;> abel

theorem D5_eq (X : ParabolicOp B) :
    D5 X = ⟨0, X.a01, (32 : ℤ) • X.a02,
            -X.a10, 0, X.a12,
            (-32 : ℤ) • X.a20, -X.a21, 0⟩ := by
  unfold D5; rw [D_eq (D4 X), D4_eq X]
  ext <;> dsimp <;> abel

theorem Poly24_0_eq (X : ParabolicOp B) : Poly24_0 X = smulZ 24 (gradeZero X) := by
  unfold Poly24_0; rw [D4_eq, D2_eq]
  dsimp only [smulZ, gradeZero]
  simp only [sub_mk, add_mk]
  ext <;> dsimp <;> abel

theorem Poly24_pos1_eq (X : ParabolicOp B) : Poly24_pos1 X = smulZ 24 (gradePos1 X) := by
  unfold Poly24_pos1; rw [D4_eq, D3_eq, D2_eq, D_eq]
  dsimp only [smulZ, gradePos1]
  simp only [neg_mk, sub_mk, add_mk]
  ext <;> dsimp <;> abel

theorem Poly24_neg1_eq (X : ParabolicOp B) : Poly24_neg1 X = smulZ 24 (gradeNeg1 X) := by
  unfold Poly24_neg1; rw [D4_eq, D3_eq, D2_eq, D_eq]
  dsimp only [smulZ, gradeNeg1]
  simp only [neg_mk, sub_mk, add_mk]
  ext <;> dsimp <;> abel

theorem Poly24_pos2_eq (X : ParabolicOp B) : Poly24_pos2 X = smulZ 24 (gradePos2 X) := by
  unfold Poly24_pos2; rw [D4_eq, D3_eq, D2_eq, D_eq]
  dsimp only [smulZ, gradePos2]
  simp only [sub_mk, add_mk]
  ext <;> dsimp <;> abel

theorem Poly24_neg2_eq (X : ParabolicOp B) : Poly24_neg2 X = smulZ 24 (gradeNeg2 X) := by
  unfold Poly24_neg2; rw [D4_eq, D3_eq, D2_eq, D_eq]
  dsimp only [smulZ, gradeNeg2]
  simp only [sub_mk, add_mk]
  ext <;> dsimp <;> abel

/-- **Node `𝔖𝔊₈`**: 5-graded parabolic Maurer–Cartan tower, quintic Weyl annihilator
`D⁵ - 5 D³ + 4 D = 0`, quartic chiral parity formula `3 S_par X S_par = 3 X - 8 D²X + 2 D⁴X`,
unipotent Maurer–Cartan Galois dressing `g⁻¹ H g = H + θ_W`, flat cocycle `d_Q θ_Q + θ_Q² = 0`,
complete `24 = 4!` orthogonal spectral resolution, and `(ℤ/24ℤ)ˣ` Galois exponent-2 closure. -/
theorem node8_parabolic_maurer_cartan_tower_24_projectors_and_galois
    (X C : ParabolicOp B) :
    let N     := gradePos1 X + gradePos2 X
    let g     := 1 + N
    let g_inv := 1 - N + N * N
    let θ_W   := g_inv * D g
    let θ_Q   := g_inv * d_Q C g
    D5 X - smulZ 5 (D3 X) + smulZ 4 (D X) = 0 ∧
    smulZ 3 (S_par * X * S_par) = smulZ 3 X - smulZ 8 (D2 X) + smulZ 2 (D4 X) ∧
    g * g_inv = 1 ∧
    θ_W = gradePos1 X + (gradePos2 X + gradePos2 X - gradePos1 X * gradePos1 X) ∧
    g_inv * weylH * g = weylH + θ_W ∧
    d_Q C θ_Q + θ_Q * θ_Q = 0 ∧
    Poly24_neg2 X + Poly24_neg1 X + Poly24_0 X + Poly24_pos1 X + Poly24_pos2 X = smulZ 24 X ∧
    Poly24_0    (Poly24_0 X)    = smulZ 24 (Poly24_0 X) ∧
    Poly24_pos1 (Poly24_pos1 X) = smulZ 24 (Poly24_pos1 X) ∧
    Poly24_pos2 (Poly24_pos2 X) = smulZ 24 (Poly24_pos2 X) ∧
    Poly24_0 (Poly24_pos1 X) = 0 ∧ Poly24_pos1 (Poly24_pos2 X) = 0 ∧
    ((1 * 1) % 24 = 1 ∧ (5 * 5) % 24 = 1 ∧ (7 * 7) % 24 = 1 ∧ (11 * 11) % 24 = 1 ∧
     (13 * 13) % 24 = 1 ∧ (17 * 17) % 24 = 1 ∧ (19 * 19) % 24 = 1 ∧ (23 * 23) % 24 = 1) := by
  intro N g g_inv θ_W θ_Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [D5_eq, D3_eq, D_eq]
    dsimp only [smulZ]; simp only [sub_mk, add_mk, zero_mk]
    ext <;> dsimp <;> abel
  · rw [S_par_eq, D2_eq, D4_eq]
    dsimp only [smulZ]; simp only [mul_mk, sub_mk, add_mk]
    ext <;> dsimp <;> noncomm_ring
  · dsimp only [g, g_inv, N, gradePos1, gradePos2]
    simp only [add_mk, sub_mk, mul_mk, one_mk]
    ext <;> dsimp <;> noncomm_ring
  · dsimp only [θ_W, g_inv, g, N]
    rw [D_eq]
    dsimp only [gradePos1, gradePos2]
    simp only [add_mk, sub_mk, mul_mk, one_mk]
    ext <;> dsimp <;> noncomm_ring
  · dsimp only [θ_W, g_inv, g, N]
    rw [D_eq]
    dsimp only [weylH, gradePos1, gradePos2]
    simp only [add_mk, sub_mk, mul_mk, one_mk]
    ext <;> dsimp <;> noncomm_ring
  · dsimp only [θ_Q, g_inv, g, N, d_Q, pComm, gradePos1, gradePos2]
    simp only [add_mk, sub_mk, mul_mk, one_mk, zero_mk]
    ext <;> dsimp <;> noncomm_ring
  · rw [Poly24_neg2_eq, Poly24_neg1_eq, Poly24_0_eq, Poly24_pos1_eq, Poly24_pos2_eq]
    dsimp only [smulZ, gradeNeg2, gradeNeg1, gradeZero, gradePos1, gradePos2]
    simp only [add_mk]
    ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_0 X), Poly24_0_eq X]
    dsimp only [smulZ, gradeZero]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradePos1]; ext <;> dsimp <;> abel
  · rw [Poly24_pos2_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradePos2]; ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradeZero, gradePos1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradePos1, gradePos2, zero_mk]; ext <;> dsimp <;> abel

end ParabolicOp

end InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
