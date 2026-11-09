/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset

/-!
# Wheeler Single-Commutator Ladder, Forgotten Physics Archetypes (1870–1988),
# Decadic Resolvent Crystal, Vieta Braid Anomaly & SUSY Spectral Triple Poset (`𝔗𝔓₁ ≺ ⋯ ≺ 𝔗𝔓₁₄`)

This module formalizes the single-commutator power ladder `J¹ … J⁶ … J²⁴` of `J = [P, X]`
for an idempotent `P² = P` in an arbitrary associative (noncommutative) ring `B` (`[Ring B]`),
unifying:
1. **Nodes `𝔗𝔓₁–𝔗𝔓₄`**: Peirce (1870) nilpotents, Schrödinger (1930) *Zitterbewegung*,
   Fock–Ivanenko (1929) line element, Narasimhan–Ramanan (1961) projector metric,
   Born (1938) reciprocity, and Nomizu (1954) associative product/commutator flip
   `Φ_X Φ_Y = -J_X J_Y`, triple-commutator Riemann tensor, and 1st Bianchi identity.
2. **Nodes `𝔗𝔓₅–𝔗𝔓₆`**: Bloch (1958) / Schrieffer–Wolff (1966) / Foldy–Wouthuysen (1950)
   exact degree-3 decoupled projectors `P̂_±`, inverse decoupling `G_±⁻¹ P̂_± G_± = P`,
   and Sato (1981) Grassmannian Lax flow `[P, P̂_±] = [-Φ G_±⁻¹, P̂_±] = J ∓ V Φ`.
3. **Nodes `𝔗𝔓₇–𝔗𝔓₁₀`**: Madelung–Bohm (1927/52) quantum potential well, Israel–Unruh–Sewell
   (1976/82) intrinsic horizon modular Hamiltonian `K_Unruh = V - 2 V P = -Σ`, the universal
   `1 : 1 : 2` Tomita–Sakharov twin-vacuum partition, and the Penrose–Tanaka–Finkelstein
   two-bit XOR ambitwistor flag `H = P - Q` (`H³ = H`) with `24 = 4!` contact shells.
4. **Node `𝔗𝔓₁₁` (Decadic Resolvent Crystal)**: Sheet-Gramian factorizations of `1 ± V` and
   `1 ± Σ`, the 4-way Bott factorization diamond of `1 - J⁴`, telescoping `J¹ … J⁷` ladders,
   and real noncommutative cyclotomic factorization of `1 - J²⁴` via `Φ₂₄(J) = J⁸ - J⁴ + 1`.
5. **Node `𝔗𝔓₁₂` (Hendecadic/Dodecadic Vieta Scattering Anomaly)**: Causal root reordering
   `(1 - J)(1 - Φ)(1 + J)(1 + Φ) = 1 + 2Σ + V² + 2V(J + Φ)` and spin-dilaton bracket
   `[Σ, J + Φ] = 2V(J + Φ)`.
6. **Nodes `𝔗𝔓₁₃–𝔗𝔓₁₄` (Tridecadic SUSY Fermion Genesis & Tessaradecadic Connes Spectral Triple)**:
   Supercharges `Q = J + Φ = 2 N_+` and `Q̄ = J - Φ = -2 N_-` (`Q² = Q̄² = 0`, `{Q, Q̄} = -4V`,
   `[Q, Q̄] = -4Σ`, `[Σ, Q] = 2VQ`, `[Σ, Q̄] = -2VQ̄`) and Connes spectral triple `(D = Φ, γ₅ = S_P)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset

universe u
variable {B : Type u} [Ring B]

/-! ### Causal Poset Indexing (`𝔗𝔓₁ ≺ ⋯ ≺ 𝔗𝔓₁₄`) -/

/-- The 14-node causal poset of the Wheeler Single-Commutator & Historical Physics synthesis. -/
inductive WheelerHistoricalNode : Type
  | HP1_PeirceSchrodingerZitterbewegung
  | HP2_NarasimhanRamananMetricSpin
  | HP3_BornNomizuProductFlipRiemann
  | HP4_ZitterbewegungSectionalCurvature
  | HP5_BlochSchriefferWolffFoldyWouthuysen
  | HP6_SatoGrassmannianLaxFlow
  | HP7_IsraelUnruhIntrinsicModularWell
  | HP8_TomitaSakharov112Partition
  | HP9_PenroseTanakaFinkelsteinTwoBitFlag
  | HP10_TwoFacesQuantumAndGravity
  | HP11_DecadicResolventCrystalJ24
  | HP12_VietaCausalScatteringBraidAnomaly
  | HP13_TridecadicSusyFermionGenesis
  | HP14_TessaradecadicConnesSpectralTriple
  deriving DecidableEq, Repr

instance : Inhabited WheelerHistoricalNode := ⟨.HP1_PeirceSchrodingerZitterbewegung⟩

/-- Monotone rank embedding `𝔗𝔓_k ↦ k`. -/
def WheelerHistoricalNode.rank : WheelerHistoricalNode → ℕ
  | .HP1_PeirceSchrodingerZitterbewegung => 1
  | .HP2_NarasimhanRamananMetricSpin => 2
  | .HP3_BornNomizuProductFlipRiemann => 3
  | .HP4_ZitterbewegungSectionalCurvature => 4
  | .HP5_BlochSchriefferWolffFoldyWouthuysen => 5
  | .HP6_SatoGrassmannianLaxFlow => 6
  | .HP7_IsraelUnruhIntrinsicModularWell => 7
  | .HP8_TomitaSakharov112Partition => 8
  | .HP9_PenroseTanakaFinkelsteinTwoBitFlag => 9
  | .HP10_TwoFacesQuantumAndGravity => 10
  | .HP11_DecadicResolventCrystalJ24 => 11
  | .HP12_VietaCausalScatteringBraidAnomaly => 12
  | .HP13_TridecadicSusyFermionGenesis => 13
  | .HP14_TessaradecadicConnesSpectralTriple => 14

instance : PartialOrder WheelerHistoricalNode where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    revert hab hba; cases a <;> cases b <;> decide

/-! ### Single-Commutator Primitives (`J = [P, X]`, `Φ = [P, [P, X]]`) -/

/-- First commutator `J₁(P, X) = [P, X]`. -/
def J_1 (P X : B) : B := comm P X

/-- Double commutator `Φ₁(P, X) = [P, [P, X]]`. -/
def Phi_1 (P X : B) : B := comm P (comm P X)

/-- Single-operator forward corner `N_+(P, X) = P [P, X] = P X (1 - P)`. -/
def N_plus_1 (P X : B) : B := P * J_1 P X

/-- Single-operator backward corner `N_-(P, X) = -[P, X] P = (1 - P) X P`. -/
def N_minus_1 (P X : B) : B := - (J_1 P X * P)

/-- Upper sheet Gramian `Q_+(P, X) = N_+ N_-`. -/
def Q_pos_1 (P X : B) : B := N_plus_1 P X * N_minus_1 P X

/-- Lower sheet Gramian `Q_-(P, X) = N_- N_+`. -/
def Q_neg_1 (P X : B) : B := N_minus_1 P X * N_plus_1 P X

/-- Single-commutator metric `V₁(P, X) = -[P, X]²`. -/
def V_1 (P X : B) : B := - (J_1 P X * J_1 P X)

/-- Single-commutator spin curvature `Σ₁(P, X) = [P, X] [P, [P, X]]`. -/
def Sigma_1 (P X : B) : B := J_1 P X * Phi_1 P X

/-- Forward Bruhat / Foldy–Wouthuysen gauge `G_+(P, X) = (1 - P J)(1 - J P)`. -/
def G_plus_1 (P X : B) : B := (1 - P * J_1 P X) * (1 - J_1 P X * P)

/-- Inverse forward Bruhat gauge `G_+⁻¹(P, X) = (1 + J P)(1 + P J)`. -/
def G_plus_inv_1 (P X : B) : B := (1 + J_1 P X * P) * (1 + P * J_1 P X)

/-- Backward Bruhat / Foldy–Wouthuysen gauge `G_-(P, X) = (1 - J P)(1 - P J)`. -/
def G_minus_1 (P X : B) : B := (1 - J_1 P X * P) * (1 - P * J_1 P X)

/-- Inverse backward Bruhat gauge `G_-⁻¹(P, X) = (1 + P J)(1 + J P)`. -/
def G_minus_inv_1 (P X : B) : B := (1 + P * J_1 P X) * (1 + J_1 P X * P)

/-- Exact degree-3 forward interacting projector `P̂_+(P, X) = P + Φ - Σ + P J³`. -/
def P_hat_plus_1 (P X : B) : B :=
  P + Phi_1 P X - Sigma_1 P X + P * (J_1 P X * J_1 P X * J_1 P X)

/-- Exact degree-3 backward interacting projector `P̂_-(P, X) = P + Φ - Σ - J³ P`. -/
def P_hat_minus_1 (P X : B) : B :=
  P + Phi_1 P X - Sigma_1 P X - (J_1 P X * J_1 P X * J_1 P X) * P

/-- Nomizu reductive triple-commutator Riemann tensor `R(X, Y)Z = -[[Φ_X, Φ_Y], Z]`. -/
def NomizuRiemann (P X Y Z : B) : B :=
  - comm (comm (Phi_1 P X) (Phi_1 P Y)) Z

/-- Intrinsic Unruh–Sewell horizon modular Hamiltonian `K_Unruh = V - 2 V P`. -/
def K_Unruh (P X : B) : B := V_1 P X - (V_1 P X + V_1 P X) * P

/-- Single-operator forward exterior differential `d_{+1}(P, X, Z)`. -/
def d_plus_1 (P X Z : B) : B := N_plus_1 P X * Z - chiralConj P Z * N_plus_1 P X

/-- Single-operator backward exterior differential `d_{-1}(P, X, Z)`. -/
def d_minus_1 (P X Z : B) : B := N_minus_1 P X * Z - chiralConj P Z * N_minus_1 P X

/-- Adjoint powers `ad_H^k(Z)` for a 2-bit tripotent generator `H = P - Q`. -/
def adH  (H Z : B) : B := H * Z - Z * H
def adH2 (H Z : B) : B := adH H (adH H Z)
def adH3 (H Z : B) : B := adH H (adH2 H Z)
def adH4 (H Z : B) : B := adH H (adH3 H Z)
def adH5 (H Z : B) : B := adH H (adH4 H Z)

/-- Grade `+2` and `-2` Lagrange projectors `Poly24_±2(H, Z)`. -/
def Poly24_pos2 (H Z : B) : B := adH4 H Z + 2 • adH3 H Z - adH2 H Z - 2 • adH H Z
def Poly24_neg2 (H Z : B) : B := adH4 H Z - 2 • adH3 H Z - adH2 H Z + 2 • adH H Z

/-- 24th cyclotomic polynomial `Φ₂₄(J) = J⁸ - J⁴ + 1`. -/
def Phi24_Op (J : B) : B :=
  let J2 := J * J
  let J4 := J2 * J2
  let J8 := J4 * J4
  J8 - J4 + 1

/-- Nilpotent lightcone / SUSY supercharge `Q = J + Φ`. -/
def Q_susy (P X : B) : B := J_1 P X + Phi_1 P X

/-- Conjugate nilpotent lightcone / SUSY supercharge `Q̄ = J - Φ`. -/
def Q_bar_susy (P X : B) : B := J_1 P X - Phi_1 P X

/-! ### Bridge Lemmas: Single-Commutator to Atomic Peirce Corners -/

theorem N_plus_1_eq {P : B} (hP : P * P = P) (X : B) : N_plus_1 P X = N_plus P X := by
  dsimp only [N_plus_1, J_1, N_plus, comm]; peirce_base_nf hP

theorem N_minus_1_eq {P : B} (hP : P * P = P) (X : B) : N_minus_1 P X = N_minus P X := by
  dsimp only [N_minus_1, J_1, N_minus, comm]; peirce_base_nf hP

theorem J_1_eq (P X : B) : J_1 P X = J_mc P X X := by
  dsimp only [J_1, J_mc, N_plus, N_minus, comm]
  simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
  abel

theorem Phi_1_eq {P : B} (hP : P * P = P) (X : B) : Phi_1 P X = Phi_v P X X := by
  dsimp only [Phi_1, Phi_v, N_plus, N_minus, comm]; peirce_base_nf hP

theorem V_1_eq {P : B} (hP : P * P = P) (X : B) : V_1 P X = V_met P X X := by
  unfold V_1
  rw [J_1_eq P X]
  dsimp only [J_mc, V_met, Q_pos, Q_neg]
  amari_peirce_nf hP

theorem Sigma_1_eq {P : B} (hP : P * P = P) (X : B) : Sigma_1 P X = Sigma_sp P X X := by
  unfold Sigma_1
  rw [J_1_eq P X, Phi_1_eq hP X]
  dsimp only [J_mc, Phi_v, Sigma_sp, Q_pos, Q_neg]
  amari_peirce_nf hP

/-! ### Nodes `𝔗𝔓₁–𝔗𝔓₄`: Peirce, Schrödinger, Narasimhan–Ramanan, Born & Nomizu -/

/-- **Theorem 1 (`𝔗𝔓₁–𝔗𝔓₄` — Peirce, Schrödinger, Narasimhan–Ramanan, Born & Nomizu Synthesis)**:
1. Peirce (1870) nilpotents `(P J)² = (J P)² = 0`, Schrödinger (1930) *Zitterbewegung*
   `[P, J] = Φ`, `[P, Φ] = J`, and Born (1938) reciprocity `S_P Φ = J`, `S_P J = Φ`,
2. Narasimhan–Ramanan (1961) universal projector metric `Φ² = V = -J²` and `Σ² = V² = J⁴`,
3. Universal associative product flip `Φ_X * Φ_Y = -(J_X * J_Y)`, cross-orthogonality
   `J_X * Φ_Y + Φ_X * J_Y = 0`, Nomizu (1954) commutator flip `[Φ_X, Φ_Y] = -[J_X, J_Y]`,
   triple-bracket Riemann tensor `R(X, Y)Φ_Z = [[J_X, J_Y], Φ_Z]`, and 1st Bianchi identity,
4. Single-operator sectional curvature reduction at `Y = [P, X]` yielding the Coriolis
   and centrifugal forces. -/
theorem peirce_schrodinger_nomizu_narasimhan_ramanan_synthesis
    (P X Y Z : B) (hP : P * P = P) :
    let sp  := S_P P
    let jX  := J_1 P X
    let jY  := J_1 P Y
    let phX := Phi_1 P X
    let phY := Phi_1 P Y
    let phZ := Phi_1 P Z
    let vX  := V_1 P X
    let sX  := Sigma_1 P X
    let jX4 := (jX * jX) * (jX * jX)
    (P * jX) * (P * jX) = 0 ∧
    (jX * P) * (jX * P) = 0 ∧
    comm P jX  = phX ∧
    comm P phX = jX ∧
    sp * phX   = jX ∧
    sp * jX    = phX ∧
    phX * phX  = vX ∧
    sX * sX    = jX4 ∧
    vX * vX    = jX4 ∧
    phX * phY  = - (jX * jY) ∧
    jX * phY + phX * jY = 0 ∧
    comm phX phY = - comm jX jY ∧
    NomizuRiemann P X Y phZ = comm (comm jX jY) phZ ∧
    NomizuRiemann P X Y phZ + NomizuRiemann P Y Z phX + NomizuRiemann P Z X phY = 0 ∧
    comm (comm jX phX) phX = (4 : ℕ) • (vX * jX) ∧
    vX * comm (comm jX phX) jX = (4 : ℕ) • (jX4 * phX) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try dsimp only [NomizuRiemann]
    try rw [J_1_eq P X]
    try rw [J_1_eq P Y]
    try rw [Phi_1_eq hP X]
    try rw [Phi_1_eq hP Y]
    try rw [Phi_1_eq hP Z]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-! ### Nodes `𝔗𝔓₅–𝔗𝔓₆`: Bloch / Schrieffer–Wolff / Foldy–Wouthuysen & Sato Lax Flow -/

/-- **Theorem 2 (`𝔗𝔓₅–𝔗𝔓₆` — Bloch, Schrieffer–Wolff, Foldy–Wouthuysen & Sato Lax Flow)**:
1. Exact degree-3 interacting projectors `G_± P G_±⁻¹ = P̂_±`, inverse decoupling
   `G_±⁻¹ P̂_± G_± = P`, and metric gauge invariance `G_+ V G_+⁻¹ = V`,
2. Cubic and sextic commutator invariants `P̂_- - P̂_+ = -J³` and
   `{P̂_+, P̂_-} - (P̂_+ + P̂_-) = -J⁶`,
3. Sato (1981) Grassmannian Lax flow `[P, P̂_±] = [-Φ G_±⁻¹, P̂_±]`, with
   `[P, P̂_+] = J + P J³`, `[P, P̂_-] = J + J³ P`, and `[P, P̂_-] - [P, P̂_+] = V Φ`,
4. Complete `J¹ … J⁶` power ladder `[P, J³] = -V Φ`, `[P, J⁵] = J⁴ Φ`, and
   Weitzenböck `[d_+, d_-](Σ) = 4 J⁴`. -/
theorem bloch_schrieffer_wolff_bruhat_and_sato_lax_flow
    (P X : B) (hP : P * P = P) :
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    let j2  := j * j
    let j3  := j2 * j
    let j4  := j2 * j2
    let j5  := j4 * j
    let j6  := j3 * j3
    let Gp  := G_plus_1 P X
    let GpI := G_plus_inv_1 P X
    let Gm  := G_minus_1 P X
    let GmI := G_minus_inv_1 P X
    let Php := P_hat_plus_1 P X
    let Phm := P_hat_minus_1 P X
    Gp * GpI = 1 ∧ Gm * GmI = 1 ∧
    Gm - Gp = s ∧
    Gp * P * GpI = Php ∧ Gm * P * GmI = Phm ∧
    GpI * Php * Gp = P ∧ GmI * Phm * Gm = P ∧
    Gp * v * GpI = v ∧
    Php * Php = Php ∧ Phm * Phm = Phm ∧
    Phm - Php = - j3 ∧
    anticomm Php Phm - (Php + Phm) = - j6 ∧
    comm P Php = comm (- ph * GpI) Php ∧
    comm P Phm = comm (- ph * GmI) Phm ∧
    comm P Php = j + P * j3 ∧
    comm P Phm = j + j3 * P ∧
    comm P Phm - comm P Php = v * ph ∧
    comm P j3 = - (v * ph) ∧
    comm P j5 = j4 * ph ∧
    d_plus_1 P X (d_minus_1 P X s) - d_minus_1 P X (d_plus_1 P X s) = 4 • j4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try dsimp only [P_hat_plus_1, P_hat_minus_1, G_plus_1, G_plus_inv_1, G_minus_1, G_minus_inv_1,
                    d_plus_1, d_minus_1, chiralConj]
    try rw [N_plus_1_eq hP X]
    try rw [N_minus_1_eq hP X]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    amari_peirce_nf hP

/-! ### Nodes `𝔗𝔓₇–𝔗𝔓₁₀`: Israel–Unruh Modular Well, `1:1:2` Sakharov Partition & Penrose–Tanaka Flags -/

macro "xor_idem_nf" hP:ident hQ:ident hPQ:ident proj_P:ident proj_Q:ident comm_QP:ident : tactic =>
  `(tactic| (
    try simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
                   neg_mul, mul_neg, mul_assoc,
                   $hP:ident, $hQ:ident, $hPQ:ident,
                   $proj_P:ident, $proj_Q:ident, $comm_QP:ident,
                   mul_zero, zero_mul]
    try abel))

theorem tripotent_quintic_adH {H : B} (hH : H * (H * H) = H) (Z : B) :
    adH5 H Z - 5 • adH3 H Z + 4 • adH H Z = 0 := by
  have hH' : ∀ W : B, H * (H * (H * W)) = H * W := fun W => by
    calc H * (H * (H * W))
      _ = (H * (H * H)) * W := by simp only [mul_assoc]
      _ = H * W             := by rw [hH]
  dsimp only [adH5, adH4, adH3, adH2, adH]
  simp only [sub_mul, mul_sub, mul_assoc, hH, hH']
  abel

theorem Poly24_pos2_add (H A B_op : B) :
    Poly24_pos2 H (A + B_op) = Poly24_pos2 H A + Poly24_pos2 H B_op := by
  dsimp only [Poly24_pos2, adH4, adH3, adH2, adH]; noncomm_ring

theorem Poly24_pos2_sub (H A B_op : B) :
    Poly24_pos2 H (A - B_op) = Poly24_pos2 H A - Poly24_pos2 H B_op := by
  dsimp only [Poly24_pos2, adH4, adH3, adH2, adH]; noncomm_ring

theorem Poly24_neg2_add (H A B_op : B) :
    Poly24_neg2 H (A + B_op) = Poly24_neg2 H A + Poly24_neg2 H B_op := by
  dsimp only [Poly24_neg2, adH4, adH3, adH2, adH]; noncomm_ring

theorem Poly24_neg2_sub (H A B_op : B) :
    Poly24_neg2 H (A - B_op) = Poly24_neg2 H A - Poly24_neg2 H B_op := by
  dsimp only [Poly24_neg2, adH4, adH3, adH2, adH]; noncomm_ring

theorem Poly24_on_grade_pos2 {H U : B} (hL : H * U = U) (hR : U * H = -U) :
    Poly24_pos2 H U = 24 • U ∧ Poly24_neg2 H U = 0 := by
  have h1 : adH H U = U + U := by unfold adH; rw [hL, hR]; abel
  have h2 : adH2 H U = (U + U) + (U + U) := by
    unfold adH2; rw [h1]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  have h3 : adH3 H U = ((U + U) + (U + U)) + ((U + U) + (U + U)) := by
    unfold adH3; rw [h2]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  have h4 : adH4 H U =
      (((U + U) + (U + U)) + ((U + U) + (U + U))) +
      (((U + U) + (U + U)) + ((U + U) + (U + U))) := by
    unfold adH4; rw [h3]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  refine ⟨?_, ?_⟩
  · unfold Poly24_pos2; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_neg2; rw [h1, h2, h3, h4]; abel

theorem Poly24_on_grade_neg2 {H U : B} (hL : H * U = -U) (hR : U * H = U) :
    Poly24_pos2 H U = 0 ∧ Poly24_neg2 H U = 24 • U := by
  have h1 : adH H U = - (U + U) := by unfold adH; rw [hL, hR]; abel
  have h2 : adH2 H U = (U + U) + (U + U) := by
    unfold adH2; rw [h1]; unfold adH
    simp only [mul_neg, neg_mul, mul_add, add_mul, hL, hR]; abel
  have h3 : adH3 H U = - (((U + U) + (U + U)) + ((U + U) + (U + U))) := by
    unfold adH3; rw [h2]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  have h4 : adH4 H U =
      (((U + U) + (U + U)) + ((U + U) + (U + U))) +
      (((U + U) + (U + U)) + ((U + U) + (U + U))) := by
    unfold adH4; rw [h3]; unfold adH
    simp only [mul_neg, neg_mul, mul_add, add_mul, hL, hR]; abel
  refine ⟨?_, ?_⟩
  · unfold Poly24_pos2; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_neg2; rw [h1, h2, h3, h4]; abel

theorem Poly24_on_grade_zero {H U : B} (h0 : adH H U = 0) :
    Poly24_pos2 H U = 0 ∧ Poly24_neg2 H U = 0 := by
  have h00 : adH H (0 : B) = 0 := by unfold adH; simp
  have h2 : adH2 H U = 0 := by unfold adH2; rw [h0, h00]
  have h3 : adH3 H U = 0 := by unfold adH3; rw [h2, h00]
  have h4 : adH4 H U = 0 := by unfold adH4; rw [h3, h00]
  refine ⟨?_, ?_⟩
  · unfold Poly24_pos2; rw [h0, h2, h3, h4]; abel
  · unfold Poly24_neg2; rw [h0, h2, h3, h4]; abel

/-- **Theorem 3 (`𝔗𝔓₇–𝔗𝔓₁₀` — Israel–Unruh Modular Well, `1:1:2` Sakharov Partition & 2-Bit Flag)**:
1. Intrinsic Unruh–Sewell horizon modular Hamiltonian `K_Unruh = V - 2 V P = -Σ` and
   exact cancellation `[K_Unruh, [K_Unruh, Φ]] + V [J, [J, Φ]] = 0`,
2. Universal `1 : 1 : 2` Tomita–Sakharov twin-vacuum partition:
   `Σ² Φ = V² Φ` (Left `1/4`), `Φ Σ² = V² Φ` (Right `1/4`), `-2(Σ Φ Σ) = 2 V² Φ` (Twin `1/2`),
   summing to `[Σ, [Σ, Φ]] = 4 V² Φ`,
3. Penrose (1967) ambitwistor flag & Tanaka (1970) / Finkelstein (1969) 5-graded prolongation
   from two commuting bits `P, Q` (`H = P - Q`, `H³ = H`), populating grade `±2` contact shells
   `Poly24_±2(H, V_XOR) = -24 P_{1,2} X P₀ X P_{2,1}`. -/
theorem unruh_modular_well_sakharov_1_1_2_and_penrose_tanaka_flags
    (P Q X Z : B)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Q * P = P * Q) :
    let j     := J_1 P X
    let ph    := Phi_1 P X
    let v     := V_1 P X
    let s     := Sigma_1 P X
    let K     := K_Unruh P X
    let P1    := P * (1 - Q)
    let P2    := (1 - P) * Q
    let H     := P - Q
    let P_hor := H * H
    let P0    := 1 - P_hor
    let V_XOR := d_plus_1 P_hor X (N_minus P_hor X)
    K = - s ∧
    comm K ph = 2 • (j * j * j) ∧
    comm K (comm K ph) = comm s (comm s ph) ∧
    comm K (comm K ph) + v * comm j (comm j ph) = 0 ∧
    (s * s) * ph = (v * v) * ph ∧
    ph * (s * s) = (v * v) * ph ∧
    - ((2 : ℕ) • (s * ph * s)) = (2 : ℕ) • ((v * v) * ph) ∧
    (s * s) * ph + ph * (s * s) - 2 • (s * ph * s) = comm s (comm s ph) ∧
    H * (H * H) = H ∧
    adH5 H Z - 5 • adH3 H Z + 4 • adH H Z = 0 ∧
    d_plus_1 P_hor X (d_plus_1 P_hor X Z) = 0 ∧
    Poly24_pos2 H V_XOR = 24 • (P1 * X * P0 * X * P2) ∧
    Poly24_neg2 H V_XOR = 24 • (P2 * X * P0 * X * P1) := by
  intro j ph v s K P1 P2 H P_hor P0 V_XOR
  have proj_P  : ∀ W : B, P * (P * W) = P * W       := fun W => by rw [← mul_assoc, hP]
  have proj_Q  : ∀ W : B, Q * (Q * W) = Q * W       := fun W => by rw [← mul_assoc, hQ]
  have comm_QP : ∀ W : B, Q * (P * W) = P * (Q * W) := fun W => by rw [← mul_assoc, hPQ, mul_assoc]
  have hH_cub : H * (H * H) = H := by
    dsimp only [H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hP_hor_idem : P_hor * P_hor = P_hor := by
    dsimp only [P_hor, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hP_hor' : ∀ W : B, P_hor * (P_hor * W) = P_hor * W := fun W => by
    rw [← mul_assoc, hP_hor_idem]
  have hP0_idem : P0 * P0 = P0 := by
    dsimp only [P0]; peirce_base_nf hP_hor_idem
  have hP0' : ∀ W : B, P0 * (P0 * W) = P0 * W := fun W => by
    rw [← mul_assoc, hP0_idem]
  have hP_hor_eq : P_hor = P1 + P2 := by
    dsimp only [P_hor, H, P1, P2]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hd2_xor : d_plus_1 P_hor X (d_plus_1 P_hor X Z) = 0 := by
    dsimp only [d_plus_1]
    rw [N_plus_1_eq hP_hor_idem X]
    exact (node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure
      P_hor X X 0 Z Z Z hP_hor_idem (fun _ => by simp)).1
  have hV_step1 : V_met P_hor X X = P_hor * X * P0 * X * P_hor + P0 * X * P_hor * X * P0 := by
    dsimp only [V_met, Q_pos, Q_neg, N_plus, N_minus]
    change P_hor * X * P0 * (P0 * X * P_hor) + P0 * X * P_hor * (P_hor * X * P0) = _
    simp only [mul_assoc, hP0', hP_hor']
  have hV_step2 : P_hor * X * P0 * X * P_hor =
      P1 * X * P0 * X * P1 + P2 * X * P0 * X * P2 + P1 * X * P0 * X * P2 + P2 * X * P0 * X * P1 := by
    rw [hP_hor_eq]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  have hV_xor_eq :
      V_XOR = (P1 * X * P0 * X * P1 + P2 * X * P0 * X * P2 + P0 * X * P_hor * X * P0) +
              P1 * X * P0 * X * P2 + P2 * X * P0 * X * P1 := by
    dsimp only [V_XOR, d_plus_1]
    rw [N_plus_1_eq hP_hor_idem X]
    have h_gen := (node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure
      P_hor X X 0 Z Z Z hP_hor_idem (fun _ => by simp)).2.2.2.1
    dsimp only [d_plus] at h_gen
    rw [h_gen, hV_step1, hV_step2]
    abel
  set U0 := P1 * X * P0 * X * P1 + P2 * X * P0 * X * P2 + P0 * X * P_hor * X * P0
  set Up := P1 * X * P0 * X * P2
  set Um := P2 * X * P0 * X * P1
  have hU0 : adH H U0 = 0 := by
    dsimp only [U0, adH, P_hor, P0, P1, P2, H]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUp_L : H * Up = Up := by
    dsimp only [Up, P0, P_hor, P1, P2, H]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUp_R : Up * H = -Up := by
    dsimp only [Up, P0, P_hor, P1, P2, H]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUm_L : H * Um = -Um := by
    dsimp only [Um, P0, P_hor, P1, P2, H]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUm_R : Um * H = Um := by
    dsimp only [Um, P0, P_hor, P1, P2, H]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have h_pos2 : Poly24_pos2 H V_XOR = 24 • Up := by
    rw [hV_xor_eq, Poly24_pos2_add, Poly24_pos2_add,
        (Poly24_on_grade_zero hU0).1,
        (Poly24_on_grade_pos2 hUp_L hUp_R).1,
        (Poly24_on_grade_neg2 hUm_L hUm_R).1]
    abel
  have h_neg2 : Poly24_neg2 H V_XOR = 24 • Um := by
    rw [hV_xor_eq, Poly24_neg2_add, Poly24_neg2_add,
        (Poly24_on_grade_zero hU0).2,
        (Poly24_on_grade_pos2 hUp_L hUp_R).2,
        (Poly24_on_grade_neg2 hUm_L hUm_R).2]
    abel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hH_cub, tripotent_quintic_adH hH_cub Z,
          hd2_xor, h_pos2, h_neg2⟩ <;>
  · dsimp only [K, K_Unruh, j, ph, v, s]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-! ### Nodes `𝔗𝔓₁₁–𝔗𝔓₁₄`: Decadic Resolvent Crystal, Vieta Scattering, SUSY & Spectral Triple -/

/-- **Theorem 4 (`𝔗𝔓₁₁` — Decadic Resolvent Crystal, Bott Diamond & `1 - J²⁴` Cyclotomic Closure)**:
1. Sheet-Gramian factorizations `(1 - Q_+)(1 - Q_-) = 1 - V`, `(1 - Q_+)(1 + Q_-) = 1 - Σ`,
2. Four-way Bott factorization diamond `(1 - J)(1 + J)(1 - Φ)(1 + Φ) = (1 - V)(1 + V) = (1 - Σ)(1 + Σ) = 1 - J⁴`,
3. Telescoping resolvent ladders `(1 + J²)(1 - J² + J⁴) = 1 + J⁶ = 1 - V³` and
   `(1 + J²)(J - J³ + J⁵) = J + J⁷`,
4. Real noncommutative cyclotomic factorization of `1 - J²⁴` via `Φ₂₄(J) = J⁸ - J⁴ + 1`. -/
theorem decadic_resolvent_crystal_bott_diamond_and_J24_factorization
    (P X : B) (hP : P * P = P) :
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    let qp  := Q_pos_1 P X
    let qm  := Q_neg_1 P X
    let j2  := j * j
    let j3  := j2 * j
    let j4  := j2 * j2
    let j5  := j4 * j
    let j6  := j3 * j3
    let j7  := j6 * j
    let j8  := j4 * j4
    let j12 := j8 * j4
    let j24 := j12 * j12
    (1 - qp) * (1 - qm) = 1 - v ∧
    (1 + qp) * (1 + qm) = 1 + v ∧
    (1 - qp) * (1 + qm) = 1 - s ∧
    (1 + qp) * (1 - qm) = 1 + s ∧
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) = 1 - j4 ∧
    (1 - v) * (1 + v) = 1 - j4 ∧
    (1 - s) * (1 + s) = 1 - j4 ∧
    (1 - qp) * (1 + qp) * (1 - qm) * (1 + qm) = 1 - j4 ∧
    (1 + j2) * (1 - j2 + j4) = 1 + j6 ∧
    (1 + j2) * (j - j3 + j5) = j + j7 ∧
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) *
      (1 + j4) * Phi24_Op j = 1 - j24 := by
  have h_bott : (1 - J_1 P X) * (1 + J_1 P X) * (1 - Phi_1 P X) * (1 + Phi_1 P X) =
      1 - (J_1 P X * J_1 P X) * (J_1 P X * J_1 P X) := by
    rw [J_1_eq P X, Phi_1_eq hP X]
    dsimp only [Phi_v, J_mc]
    amari_peirce_nf hP
  set j := J_1 P X
  set ph := Phi_1 P X
  set j2 := j * j
  set j4 := j2 * j2
  set j8 := j4 * j4
  set j12 := j8 * j4
  set j24 := j12 * j12
  have h_12_minus : (1 - j4) * (1 + j4 + j8) = 1 - j12 := by
    dsimp [j12, j8, j4, j2]
    simp only [sub_mul, mul_add, one_mul, mul_one, mul_assoc]; abel
  have h_12_plus : (1 + j4) * Phi24_Op j = 1 + j12 := by
    dsimp [Phi24_Op, j12, j8, j4, j2]
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, mul_assoc]; abel
  have h_24 : (1 - j12) * (1 + j12) = 1 - j24 := by
    dsimp [j24]
    simp only [sub_mul, mul_add, one_mul, mul_one]; abel
  refine ⟨?_, ?_, ?_, ?_, h_bott, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q_pos_1, Q_neg_1]
    rw [N_plus_1_eq hP X, N_minus_1_eq hP X, V_1_eq hP X]
    dsimp only [V_met, Q_pos, Q_neg]; amari_peirce_nf hP
  · dsimp only [Q_pos_1, Q_neg_1]
    rw [N_plus_1_eq hP X, N_minus_1_eq hP X, V_1_eq hP X]
    dsimp only [V_met, Q_pos, Q_neg]; amari_peirce_nf hP
  · dsimp only [Q_pos_1, Q_neg_1]
    rw [N_plus_1_eq hP X, N_minus_1_eq hP X, Sigma_1_eq hP X]
    dsimp only [Sigma_sp, Q_pos, Q_neg]; amari_peirce_nf hP
  · dsimp only [Q_pos_1, Q_neg_1]
    rw [N_plus_1_eq hP X, N_minus_1_eq hP X, Sigma_1_eq hP X]
    dsimp only [Sigma_sp, Q_pos, Q_neg]; amari_peirce_nf hP
  · dsimp only [V_1, j4, j2, j]; amari_peirce_nf hP
  · dsimp only [j4, j2, j]
    rw [J_1_eq P X, Sigma_1_eq hP X]
    dsimp only [J_mc, Sigma_sp, Q_pos, Q_neg]; amari_peirce_nf hP
  · dsimp only [Q_pos_1, Q_neg_1, j4, j2, j]
    rw [N_plus_1_eq hP X, N_minus_1_eq hP X, J_1_eq P X]
    dsimp only [J_mc]; amari_peirce_nf hP
  · dsimp only [j4, j2, j]; amari_peirce_nf hP
  · dsimp only [j4, j2, j]; amari_peirce_nf hP
  · calc (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) * (1 + j4) * Phi24_Op j
      _ = ((1 - j4) * (1 + j4 + j8)) * ((1 + j4) * Phi24_Op j) := by
          rw [h_bott]; simp only [mul_assoc]
      _ = (1 - j12) * (1 + j12) := by rw [h_12_minus, h_12_plus]
      _ = 1 - j24               := h_24

/-- **Theorem 5 (`𝔗𝔓₁₂–𝔗𝔓₁₄` — Vieta Causal Scattering Braid Anomaly, SUSY Fermion Genesis & Connes Spectral Triple)**:
1. Causal Vieta scattering braid anomaly:
   `(1 - J)(1 - Φ) = 1 + Σ - Q`, `(1 + J)(1 + Φ) = 1 + Σ + Q`, and
   `(1 - J)(1 - Φ)(1 + J)(1 + Φ) = 1 + 2 • Σ + V² + 2 • (V * Q)`,
2. Tridecadic `N = 1` SUSY fermion genesis (`Q = J + Φ = 2 N_+`, `Q̄ = J - Φ = -2 N_-`):
   `Q² = Q̄² = 0`, `{Q, Q̄} = -4 V`, `[Q, Q̄] = -4 Σ`, `[Σ, Q] = 2 V Q`, `[Σ, Q̄] = -2 V Q̄`,
3. Tessaradecadic Connes spectral triple (`D = Φ`, `γ₅ = S_P`):
   `γ₅² = 1`, `{D, γ₅} = 0`, `D² = V`, `2 N_+ = D + γ₅ D`, and `2 N_- = D - γ₅ D`. -/
theorem vieta_scattering_susy_fermion_genesis_and_spectral_triple
    (P X : B) (hP : P * P = P) :
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    let np  := N_plus P X
    let nm  := N_minus P X
    let q   := Q_susy P X
    let qb  := Q_bar_susy P X
    let γ5  := S_P P
    let R1  := 1 - j
    let R2  := 1 + j
    let R3  := 1 - ph
    let R4  := 1 + ph
    -- 1. Causal Vieta Scattering & Braid Anomaly:
    R1 * R3 = 1 + s - q ∧
    R2 * R4 = 1 + s + q ∧
    (R1 * R3) * (R2 * R4) = 1 + 2 • s + v * v + 2 • (v * q) ∧
    -- 2. Tridecadic SUSY Fermion Genesis:
    q * q = 0 ∧
    qb * qb = 0 ∧
    anticomm q qb = - (4 • v) ∧
    comm q qb = - (4 • s) ∧
    comm s q = 2 • (v * q) ∧
    comm s qb = - (2 • (v * qb)) ∧
    -- 3. Tessaradecadic Fermion-First Unmasking & Connes Spectral Triple:
    q = 2 • np ∧
    qb = - (2 • nm) ∧
    γ5 * γ5 = 1 ∧
    anticomm ph γ5 = 0 ∧
    ph * ph = v ∧
    2 • np = ph + γ5 * ph ∧
    2 • nm = ph - γ5 * ph := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, S_P_sq hP, ?_, ?_, ?_, ?_⟩ <;>
  · try dsimp only [Q_susy, Q_bar_susy]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    amari_peirce_nf hP

/-- **Master Poset Chain (`𝔗𝔓₁ ≺ ⋯ ≺ 𝔗𝔓₁₄`)**: Strict causal ordering of the 14-node
Wheeler single-commutator historical physics poset. -/
theorem master_wheeler_single_commutator_historical_poset_coagulation :
    WheelerHistoricalNode.HP1_PeirceSchrodingerZitterbewegung < .HP2_NarasimhanRamananMetricSpin ∧
    WheelerHistoricalNode.HP2_NarasimhanRamananMetricSpin < .HP3_BornNomizuProductFlipRiemann ∧
    WheelerHistoricalNode.HP3_BornNomizuProductFlipRiemann < .HP4_ZitterbewegungSectionalCurvature ∧
    WheelerHistoricalNode.HP4_ZitterbewegungSectionalCurvature < .HP5_BlochSchriefferWolffFoldyWouthuysen ∧
    WheelerHistoricalNode.HP5_BlochSchriefferWolffFoldyWouthuysen < .HP6_SatoGrassmannianLaxFlow ∧
    WheelerHistoricalNode.HP6_SatoGrassmannianLaxFlow < .HP7_IsraelUnruhIntrinsicModularWell ∧
    WheelerHistoricalNode.HP7_IsraelUnruhIntrinsicModularWell < .HP8_TomitaSakharov112Partition ∧
    WheelerHistoricalNode.HP8_TomitaSakharov112Partition < .HP9_PenroseTanakaFinkelsteinTwoBitFlag ∧
    WheelerHistoricalNode.HP9_PenroseTanakaFinkelsteinTwoBitFlag < .HP10_TwoFacesQuantumAndGravity ∧
    WheelerHistoricalNode.HP10_TwoFacesQuantumAndGravity < .HP11_DecadicResolventCrystalJ24 ∧
    WheelerHistoricalNode.HP11_DecadicResolventCrystalJ24 < .HP12_VietaCausalScatteringBraidAnomaly ∧
    WheelerHistoricalNode.HP12_VietaCausalScatteringBraidAnomaly < .HP13_TridecadicSusyFermionGenesis ∧
    WheelerHistoricalNode.HP13_TridecadicSusyFermionGenesis < .HP14_TessaradecadicConnesSpectralTriple := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · change WheelerHistoricalNode.rank _ < WheelerHistoricalNode.rank _
    decide

end InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset
