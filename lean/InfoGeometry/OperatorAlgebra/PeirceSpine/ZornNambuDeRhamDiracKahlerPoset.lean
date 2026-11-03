/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Non-Commutative Zorn–Nambu, Operator De Rham–Dirac–Kähler, & Malik–Thome DMP–MPD Poset

This module provides a 100% kernel-verified formalization in Lean 4 (native Mathlib) of the
Batch 3 mathematical archetypes (`Stages ZND₁, ZND₂, ZND₃`), operating strictly over
non-commutative rings (`[Ring R]`, `[StarRing R]`, `[Ring B]`, `[StarRing B]`) without
scalar, diagonal, or commuting surrogates:

## Stage ZND₁: Zorn Tetraktys `γ₅`, Four-Pillar Rosetta Stone, & Baryon–Chromomagnetic Poset
* **`ZS_G1` (`tetraktys_gamma5_threefold_origin`)**: Threefold origin of `γ₅ = e_L - e_R` from
  the Dyad, single-channel particle-hole commutator `[E_x⁺, E_x⁻]`, and Triadic Weyl product
  `(W_x * W_y) * W_z = -W_x * (W_y * W_z)`.
* **`ZS_G2` (`tetraktys_klein_four_group_identities`)**: The Klein Four-Group
  `K₄ = {Id, L_{γ₅}, R_{γ₅}, Ad_{γ₅}}` (`ℤ₂ × ℤ₂` bimodule grading).
* **`ZS_G3` (`tetraktys_walsh_hadamard_peirce_projectors`)**: The `4 × 4` Walsh–Hadamard
  projector decomposition isolating the 4 Tetraktys rows with weight `4`.
* **`ZS_G4` (`tetraktys_mass_protection_and_chiral_charge_duality`)**: Linearized mass operator
  `2 M_lin(X) = {γ₅, X}` and chiral triplet charge `2 Q_chiral(X) = [γ₅, X]`.
* **`ZS_G5` (`tetraktys_hodge_inversion_dihedral_duality`)**: Dihedral `D₄` commutation and
  anticommutation between `γ₅` and upside-down Tetraktys Hodge inversion `⋆_{K₄}`.
* **`ZS_R1..R8` (Universal Four-Pillar Rosetta Stone over `[Ring R]` & `[StarRing R]`)**:
  Right/left Hurwitz–Zorn composition norms, supertrace zero-point commutator, full 4-sector
  Moufang–Norm associator = Nambu 3-bracket, Kantor–Allison self-triple product on Weyl
  reflections, partial vs. total tensor involution `totalConj = star ⊗ bar`, and pure imaginary
  Dirac octonion `conj D_+ = -D_+` packaging both Gauss and Ampère operators.
* **`ZS_A1..A4` (`universal_alternating_gamma5_associator_chain`, `universal_tetraktys_spine_unification`,
  `archetype_A88_zorn_tetraktys_diquark_baryon_and_chromomagnetic_anomaly`,
  `archetype_A89_baryon_parity_partner_pure_quark_vacuum_and_cyclic_jacobi`,
  `universal_three_channel_projector_purification`)**: Alternating `γ₅` associator chain,
  unification of `(V, Φ, J, Σ)` with `[γ₅, Φ, Φ]`, diquark exterior wedge, baryon singlet
  determinant, non-Abelian chromomagnetic anomaly, chiral baryon parity partner, pure-quark
  cubic vacuum condensation, 3-flavour cyclic Jacobi–Baryon identity, and the `(2/3, -1/3)`
  3-channel projector purification `2 Σ_RR(X) - Σ_LL(X) = 3 (e_L * X)`.

## Stage ZND₂: Universal `[Ring R]` 3D Operator-Valued De Rham Complex & Dirac–Kähler Poset
* **`DK_1` (`frechet_commutator_leibniz_bridge`)**: Non-commutative Fréchet directional
  derivative bridge `[p, X * Y] = frechetBilinear X Y [p, X] [p, Y]` and
  `[p, X³] = frechetCube X [p, X]`.
* **`DK_2` (`hodge_duality_of_generalized_div_and_curl`)**: Hodge duality between `extCurl` (`d_∇`)
  and `extDiv` (`-δ_∇`) via `hodgeStar` across all four exterior grades `Ω⁰ ⊕ Ω¹ ⊕ Ω² ⊕ Ω³`.
* **`DK_3` (`graded_leibniz_rule_for_operator_forms`)**: Graded Leibniz derivation rule
  `d_∇(ω^(k) ∧ η) = (d_∇ ω^(k)) ∧ η + (-1)^k ω^(k) ∧ (d_∇ η)` for `k = 0` (`+1`) and `k = 1` (`-1`).
* **`DK_4` (`interior_leibniz_rule_for_generalized_div`)**: Interior Leibniz rule
  `Div_ad(φ A) = (Grad_ad φ) · A + φ * (Div_ad A)`.
* **`DK_5` (`curvature_square_of_extCurl_and_hodge_laplacian`)**: Non-Abelian curvature
  obstructions `d_∇²` and `Div_∇²` and the Weitzenböck–Hodge Laplacian across all grades `k = 0..3`.
* **`DK_6` (`bv_second_order_convective_rule_for_extDiv`)**: Second-order Batalin–Vilkovisky
  (BV) convective rule for `extDiv(A ∧ C)` on two 1-forms.
* **`DK_7` (`dirac_kaehler_square_three_channel_decomposition`)**: Three-channel square of the
  Dirac–Kähler operator `D_DK² = d_∇² + Div_∇² - Δ_Hodge`.
* **`DK_8` (`de_rham_pontryagin_chain_from_temporal_connection`)**: Three-step De Rham–Pontryagin
  chain `d_∇¹(α) = -E`, `d_∇²(α) = -[α, B]`, `d_∇³(α) = E ·_ad B` and differential Bianchi commutation.
* **`DK_9` (`zorn_clifford_to_de_rham_wedge_bridge`)**: Exact bridge between non-associative
  Zorn multiplication and the `ℤ`-graded De Rham wedge product.

## Stage ZND₃: Operator Pell Equation, Dual Chiral `γ⁵`, Malik–Thome DMP–MPD, & Star-Algebra QGT
* **`MT_1` (`archetype_A81_operator_pell_equation_and_wavelet_scaling`)**: Non-commutative
  operator Pell equation `S_P² - D_P² = 4 V_P`, wavelet two-scale dilation, and cubic Newton–Raphson
  idempotent defect factorization.
* **`MT_2` (`archetype_A83_metriplectic_weak_measurement_duality`)**: Metriplectic weak-measurement
  decomposition, exact vanishing of cross-helicity weak values, and Aharonov–Albert–Vaidman
  amplification theorem.
* **`MT_3` (`archetype_A86_tetraktys_dirac_clifford_and_chiral_gamma5_duality`,
  `archetype_A87_tetraktys_clifford_casimir_and_internal_projector_duality`)**: Dual Chiral `γ⁵`
  (`S_P = 2P - 1` vs. `Σ = J * Φ`), complete `4 × 4` Clifford `Cl_{1,1}(V)` table, Casimir
  dispersion, and internal orthogonal Weyl projectors `V ± Σ = 2 Q_±`.
* **`MT_4` (`campbell_meyer_drazin_equations`, `malik_thome_dmp_characterization`,
  `superoperator_drazin_is_the_tetraktys`, `monad_sandwich_is_drazin_inverse_and_master_mp_decomposition`,
  `malik_thome_walsh_hadamard_gamma5_dictionary`, `nilpotent_transient_inverted_by_shadow_ground_row4`,
  `malik_thome_commutator_direct_qgt_and_metric_extraction`,
  `malik_thome_pure_commutator_tetraktys_sixfold_generator`,
  `bipartite_token_context_attention_quantum_structure`,
  `transformer_residual_self_attention_and_qkv_transfer_duality`)**: Complete Campbell–Meyer /
  Malik–Thome DMP–MPD Tetraktys synthesis and Bipartite Attention QGT duality.
* **`MT_5` (`jordan_fundamental_moufang_identity`, `bracket_grade_plus1_generates_grade_plus2`,
  `grade_plus2_terminates`, `kantor_triple_lands_in_grade_plus1`)**: Jordan fundamental Moufang
  identity and 3-idempotent 5-grading (`g_{-2} ⊕ g_{-1} ⊕ g_0 ⊕ g_{+1} ⊕ g_{+2}`).
* **`MT_6` (`peirce_star_algebra_geometry`, `grassmannian_variation_norm`)**: `[StarRing B]`
  Hermitian symmetry of `Φ` and `V`, skew-Hermitian `J` and `Σ`, and intrinsic Fubini–Study
  Grassmannian tangent norm `-(dP)² = V = N_+ N_+⋆ + N_+⋆ N_+`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset

universe u

-- ============================================================================
-- STAGE ZND₁ & ZND₂ CARRIERS: 3-Vector Operator Space & Zorn Split-Octonions
-- ============================================================================

/-- 3-component vector with entries in an arbitrary non-commutative ring `R`. -/
@[ext]
structure Vec3 (R : Type u) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Vec3
variable {R : Type u} [Ring R]

@[simp] def zero : Vec3 R := ⟨0, 0, 0⟩
@[simp] def add (u v : Vec3 R) : Vec3 R := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
@[simp] def neg (u : Vec3 R)   : Vec3 R := ⟨-u.x, -u.y, -u.z⟩
@[simp] def sub (u v : Vec3 R) : Vec3 R := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

instance instZero : Zero (Vec3 R) := ⟨zero⟩
instance instAdd : Add (Vec3 R)  := ⟨add⟩
instance instNeg : Neg (Vec3 R)  := ⟨neg⟩
instance instSub : Sub (Vec3 R)  := ⟨sub⟩

@[simp] lemma zero_x : (0 : Vec3 R).x = 0 := rfl
@[simp] lemma zero_y : (0 : Vec3 R).y = 0 := rfl
@[simp] lemma zero_z : (0 : Vec3 R).z = 0 := rfl
@[simp] lemma add_x (u v : Vec3 R) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : Vec3 R) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : Vec3 R) : (u + v).z = u.z + v.z := rfl
@[simp] lemma neg_x (u : Vec3 R) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : Vec3 R) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : Vec3 R) : (-u).z = -u.z := rfl
@[simp] lemma sub_x (u v : Vec3 R) : (u - v).x = u.x - v.x := rfl
@[simp] lemma sub_y (u v : Vec3 R) : (u - v).y = u.y - v.y := rfl
@[simp] lemma sub_z (u v : Vec3 R) : (u - v).z = u.z - v.z := rfl

@[simp] def smulLeft (a : R) (u : Vec3 R) : Vec3 R := ⟨a * u.x, a * u.y, a * u.z⟩
@[simp] def smulRight (u : Vec3 R) (d : R) : Vec3 R := ⟨u.x * d, u.y * d, u.z * d⟩
@[simp] def dot (u v : Vec3 R) : R := u.x * v.x + u.y * v.y + u.z * v.z

@[simp] def cross (u v : Vec3 R) : Vec3 R :=
  ⟨ u.y * v.z - u.z * v.y,
    u.z * v.x - u.x * v.z,
    u.x * v.y - u.y * v.x ⟩

@[simp] def commOp (p a : R) : R := p * a - a * p

@[simp] def commVec (a : R) (u : Vec3 R) : Vec3 R :=
  smulLeft a u - smulRight u a

@[simp] def adjointGrad (p : Vec3 R) (φ : R) : Vec3 R :=
  ⟨commOp p.x φ, commOp p.y φ, commOp p.z φ⟩

@[simp] def adjointDiv (p v : Vec3 R) : R :=
  dot p v - dot v p

@[simp] def adjointCurl (p v : Vec3 R) : Vec3 R :=
  cross p v + cross v p

@[simp] def nambu3 (u : Vec3 R) : R :=
  dot u (cross u u)

@[simp] def convectiveLeft (p A C : Vec3 R) : Vec3 R :=
  let act (ci : R) : R :=
    A.x * commOp p.x ci + A.y * commOp p.y ci + A.z * commOp p.z ci
  ⟨act C.x, act C.y, act C.z⟩

@[simp] def convectiveRight (p A C : Vec3 R) : Vec3 R :=
  let act (ai : R) : R :=
    commOp p.x ai * C.x + commOp p.y ai * C.y + commOp p.z ai * C.z
  ⟨act A.x, act A.y, act A.z⟩

@[simp] def bochnerScalar (p : Vec3 R) (φ : R) : R :=
  commOp p.x (commOp p.x φ) + commOp p.y (commOp p.y φ) + commOp p.z (commOp p.z φ)

@[simp] def bochnerVec (p V : Vec3 R) : Vec3 R :=
  ⟨bochnerScalar p V.x, bochnerScalar p V.y, bochnerScalar p V.z⟩

@[simp] def starVec [Star R] (u : Vec3 R) : Vec3 R :=
  ⟨star u.x, star u.y, star u.z⟩

@[simp] def channelX (u : Vec3 R) : Vec3 R := ⟨u.x, 0, 0⟩
@[simp] def channelY (u : Vec3 R) : Vec3 R := ⟨0, u.y, 0⟩
@[simp] def channelZ (u : Vec3 R) : Vec3 R := ⟨0, 0, u.z⟩

@[simp] def eX : Vec3 R := ⟨1, 0, 0⟩
@[simp] def eY : Vec3 R := ⟨0, 1, 0⟩
@[simp] def eZ : Vec3 R := ⟨0, 0, 1⟩

end Vec3

-- ============================================================================
-- STAGE ZND₁: Zorn Tetraktys `γ₅`, Four-Pillar Rosetta Stone, & Baryon Poset
-- ============================================================================

/-- The 4-sector Zorn split-octonion matrix `ZornMatrix R` over `[Ring R]`. -/
@[ext]
structure ZornMatrix (R : Type u) where
  a : R
  u : Vec3 R
  v : Vec3 R
  d : R
  deriving DecidableEq, Repr, Inhabited

namespace ZornMatrix
variable {R : Type u} [Ring R]

@[simp] def zero : ZornMatrix R := ⟨0, 0, 0, 0⟩
@[simp] def one  : ZornMatrix R := ⟨1, 0, 0, 1⟩
@[simp] def add (X Y : ZornMatrix R) : ZornMatrix R := ⟨X.a + Y.a, X.u + Y.u, X.v + Y.v, X.d + Y.d⟩
@[simp] def neg (X : ZornMatrix R)   : ZornMatrix R := ⟨-X.a, -X.u, -X.v, -X.d⟩
@[simp] def sub (X Y : ZornMatrix R) : ZornMatrix R := ⟨X.a - Y.a, X.u - Y.u, X.v - Y.v, X.d - Y.d⟩

instance instZero : Zero (ZornMatrix R) := ⟨zero⟩
instance instOne : One (ZornMatrix R)  := ⟨one⟩
instance instAdd : Add (ZornMatrix R)  := ⟨add⟩
instance instNeg : Neg (ZornMatrix R)  := ⟨neg⟩
instance instSub : Sub (ZornMatrix R)  := ⟨sub⟩

@[simp] def mul (X Y : ZornMatrix R) : ZornMatrix R where
  a := X.a * Y.a + Vec3.dot X.u Y.v
  u := Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d - Vec3.cross X.v Y.v
  v := Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v + Vec3.cross X.u Y.u
  d := Vec3.dot X.v Y.u + X.d * Y.d

instance instMul : Mul (ZornMatrix R) := ⟨mul⟩

@[simp] lemma zero_a : (0 : ZornMatrix R).a = 0 := rfl
@[simp] lemma zero_u : (0 : ZornMatrix R).u = 0 := rfl
@[simp] lemma zero_v : (0 : ZornMatrix R).v = 0 := rfl
@[simp] lemma zero_d : (0 : ZornMatrix R).d = 0 := rfl
@[simp] lemma one_a  : (1 : ZornMatrix R).a = 1 := rfl
@[simp] lemma one_u  : (1 : ZornMatrix R).u = 0 := rfl
@[simp] lemma one_v  : (1 : ZornMatrix R).v = 0 := rfl
@[simp] lemma one_d  : (1 : ZornMatrix R).d = 1 := rfl
@[simp] lemma add_a (X Y : ZornMatrix R) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma add_u (X Y : ZornMatrix R) : (X + Y).u = X.u + Y.u := rfl
@[simp] lemma add_v (X Y : ZornMatrix R) : (X + Y).v = X.v + Y.v := rfl
@[simp] lemma add_d (X Y : ZornMatrix R) : (X + Y).d = X.d + Y.d := rfl
@[simp] lemma neg_a (X : ZornMatrix R) : (-X).a = -X.a := rfl
@[simp] lemma neg_u (X : ZornMatrix R) : (-X).u = -X.u := rfl
@[simp] lemma neg_v (X : ZornMatrix R) : (-X).v = -X.v := rfl
@[simp] lemma neg_d (X : ZornMatrix R) : (-X).d = -X.d := rfl
@[simp] lemma sub_a (X Y : ZornMatrix R) : (X - Y).a = X.a - Y.a := rfl
@[simp] lemma sub_u (X Y : ZornMatrix R) : (X - Y).u = X.u - Y.u := rfl
@[simp] lemma sub_v (X Y : ZornMatrix R) : (X - Y).v = X.v - Y.v := rfl
@[simp] lemma sub_d (X Y : ZornMatrix R) : (X - Y).d = X.d - Y.d := rfl
@[simp] lemma mul_def (X Y : ZornMatrix R) : X * Y = mul X Y := rfl

@[simp] def eL : ZornMatrix R := ⟨1, 0, 0, 0⟩
@[simp] def eR : ZornMatrix R := ⟨0, 0, 0, 1⟩
@[simp] def gamma5 : ZornMatrix R := ⟨1, 0, 0, -1⟩

@[simp] def Ex_plus  : ZornMatrix R := ⟨0, ⟨1, 0, 0⟩, 0, 0⟩
@[simp] def Ex_minus : ZornMatrix R := ⟨0, 0, ⟨1, 0, 0⟩, 0⟩

@[simp] def Wx : ZornMatrix R := ⟨0, ⟨1, 0, 0⟩, ⟨1, 0, 0⟩, 0⟩
@[simp] def Wy : ZornMatrix R := ⟨0, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩, 0⟩
@[simp] def Wz : ZornMatrix R := ⟨0, ⟨0, 0, 1⟩, ⟨0, 0, 1⟩, 0⟩

@[simp] def leftG5 (X : ZornMatrix R) : ZornMatrix R := gamma5 * X
@[simp] def rightG5 (X : ZornMatrix R) : ZornMatrix R := X * gamma5
@[simp] def adG5 (X : ZornMatrix R) : ZornMatrix R := (gamma5 * X) * gamma5

@[simp] def hadamardRow1 (X : ZornMatrix R) : ZornMatrix R :=
  X + leftG5 X + rightG5 X + adG5 X
@[simp] def hadamardRow2 (X : ZornMatrix R) : ZornMatrix R :=
  X + leftG5 X - rightG5 X - adG5 X
@[simp] def hadamardRow3 (X : ZornMatrix R) : ZornMatrix R :=
  X - leftG5 X + rightG5 X - adG5 X
@[simp] def hadamardRow4 (X : ZornMatrix R) : ZornMatrix R :=
  X - leftG5 X - rightG5 X + adG5 X

@[simp] def massLin (X : ZornMatrix R) : ZornMatrix R := eL * X + X * eL - X
@[simp] def chargeChiral (X : ZornMatrix R) : ZornMatrix R := eL * X - X * eL
@[simp] def hodgeSwap (X : ZornMatrix R) : ZornMatrix R := ⟨X.d, X.v, X.u, X.a⟩

@[simp] def associator (X Y Z : ZornMatrix R) : ZornMatrix R := (X * Y) * Z - X * (Y * Z)
@[simp] def cubicAssociator (X : ZornMatrix R) : ZornMatrix R := associator X X X
@[simp] def commZorn (X Y : ZornMatrix R) : ZornMatrix R := X * Y - Y * X
@[simp] def anticommZorn (X Y : ZornMatrix R) : ZornMatrix R := X * Y + Y * X

@[simp] def psiPlus (u : Vec3 R) : ZornMatrix R := ⟨0, u, 0, 0⟩
@[simp] def psiMinus (v : Vec3 R) : ZornMatrix R := ⟨0, 0, v, 0⟩
@[simp] def psiOffDiag (u v : Vec3 R) : ZornMatrix R := ⟨0, u, v, 0⟩
@[simp] def zornJ (u v : Vec3 R) : ZornMatrix R := ⟨0, u, -v, 0⟩
@[simp] def zornV (u v : Vec3 R) : ZornMatrix R :=
  psiPlus u * psiMinus v + psiMinus v * psiPlus u
@[simp] def zornSig (u v : Vec3 R) : ZornMatrix R :=
  psiPlus u * psiMinus v - psiMinus v * psiPlus u

@[simp] def sigmaLL (X : ZornMatrix R) : ZornMatrix R :=
  psiPlus Vec3.eX * (psiMinus Vec3.eX * X) +
  psiPlus Vec3.eY * (psiMinus Vec3.eY * X) +
  psiPlus Vec3.eZ * (psiMinus Vec3.eZ * X)

@[simp] def sigmaRR (X : ZornMatrix R) : ZornMatrix R :=
  (X * psiPlus Vec3.eX) * psiMinus Vec3.eX +
  (X * psiPlus Vec3.eY) * psiMinus Vec3.eY +
  (X * psiPlus Vec3.eZ) * psiMinus Vec3.eZ

macro "zorn_ring" : tactic =>
  `(tactic| (
    (try ext) <;>
    (simp only [zero_a, zero_u, zero_v, zero_d, one_a, one_u, one_v, one_d,
                add_a, add_u, add_v, add_d, neg_a, neg_u, neg_v, neg_d,
                sub_a, sub_u, sub_v, sub_d, mul_def, mul,
                eL, eR, gamma5, Ex_plus, Ex_minus, Wx, Wy, Wz,
                leftG5, rightG5, adG5,
                hadamardRow1, hadamardRow2, hadamardRow3, hadamardRow4,
                massLin, chargeChiral, hodgeSwap,
                associator, cubicAssociator, commZorn, anticommZorn,
                psiPlus, psiMinus, psiOffDiag, zornJ, zornV, zornSig,
                sigmaLL, sigmaRR,
                Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
                Vec3.add_x, Vec3.add_y, Vec3.add_z,
                Vec3.neg_x, Vec3.neg_y, Vec3.neg_z,
                Vec3.sub_x, Vec3.sub_y, Vec3.sub_z,
                Vec3.smulLeft, Vec3.smulRight, Vec3.dot, Vec3.cross,
                Vec3.commOp, Vec3.commVec, Vec3.adjointGrad,
                Vec3.adjointDiv, Vec3.adjointCurl, Vec3.nambu3,
                Vec3.convectiveLeft, Vec3.convectiveRight,
                Vec3.bochnerScalar, Vec3.bochnerVec,
                Vec3.channelX, Vec3.channelY, Vec3.channelZ,
                Vec3.eX, Vec3.eY, Vec3.eZ,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_zero, neg_neg, neg_add_rev, neg_sub, sub_neg_eq_add,
                neg_mul, mul_neg, add_mul, mul_add, sub_mul, mul_sub, mul_assoc];
     try abel)))

/-- **Theorem ZS_G1 (`tetraktys_gamma5_threefold_origin`):**
Over ANY `[Ring R]`, `γ₅` is simultaneously the Dyad difference `e_L - e_R`,
the single-channel nilpotent commutator `[E_x⁺, E_x⁻]`, and the Triadic Weyl product
`W_x * (W_y * W_z) = -((W_x * W_y) * W_z) = γ₅`. -/
theorem tetraktys_gamma5_threefold_origin :
    (gamma5 : ZornMatrix R) = eL - eR ∧
    (gamma5 : ZornMatrix R) * gamma5 = 1 ∧
    (Ex_plus : ZornMatrix R) * Ex_minus - Ex_minus * Ex_plus = gamma5 ∧
    ((Wx : ZornMatrix R) * Wy) * Wz = -gamma5 ∧
    (Wx : ZornMatrix R) * (Wy * Wz) = gamma5 := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_G2 (`tetraktys_klein_four_group_identities`):**
In the Zorn Tetraktys, `leftG5`, `rightG5`, and `adG5` form an exact commutative
`ℤ₂ × ℤ₂` Klein four-group. -/
theorem tetraktys_klein_four_group_identities (X : ZornMatrix R) :
    leftG5 (leftG5 X)   = X ∧
    rightG5 (rightG5 X) = X ∧
    adG5 (adG5 X)       = X ∧
    leftG5 (rightG5 X)  = adG5 X ∧
    rightG5 (leftG5 X)  = adG5 X := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_G3 (`tetraktys_walsh_hadamard_peirce_projectors`):**
Applying the `4 × 4` Walsh–Hadamard matrix `H₄` to `(X, γ₅ X, X γ₅, γ₅ X γ₅)` isolates
each of the 4 rows of the Tetraktys (`a`, `u`, `v`, `d`) and reconstructs `4 X` upon summation. -/
theorem tetraktys_walsh_hadamard_peirce_projectors (X : ZornMatrix R) :
    let fourA := X.a + X.a + X.a + X.a
    let fourU := X.u + X.u + X.u + X.u
    let fourV := X.v + X.v + X.v + X.v
    let fourD := X.d + X.d + X.d + X.d
    hadamardRow1 X = ⟨fourA, 0, 0, 0⟩ ∧
    hadamardRow2 X = ⟨0, fourU, 0, 0⟩ ∧
    hadamardRow3 X = ⟨0, 0, fourV, 0⟩ ∧
    hadamardRow4 X = ⟨0, 0, 0, fourD⟩ ∧
    hadamardRow1 X + hadamardRow2 X + hadamardRow3 X + hadamardRow4 X =
      X + X + X + X := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_G4 (`tetraktys_mass_protection_and_chiral_charge_duality`):**
Twice the linearized mass operator `2 M_lin(X)` is `{γ₅, X} = ⟨2a, 0, 0, -2d⟩`,
and twice the chiral charge operator `2 Q_chiral(X)` is `[γ₅, X] = ⟨0, 2u, -2v, 0⟩`. -/
theorem tetraktys_mass_protection_and_chiral_charge_duality (X : ZornMatrix R) :
    leftG5 X + rightG5 X = massLin X + massLin X ∧
    leftG5 X + rightG5 X = ⟨X.a + X.a, 0, 0, -(X.d + X.d)⟩ ∧
    leftG5 X - rightG5 X = chargeChiral X + chargeChiral X ∧
    leftG5 X - rightG5 X = ⟨0, X.u + X.u, -(X.v + X.v), 0⟩ := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_G5 (`tetraktys_hodge_inversion_dihedral_duality`):**
Upside-down Tetraktys Hodge inversion `hodgeSwap` anticommutes with `leftG5` and `rightG5`
and commutes with Bose–Fermi parity `adG5`. -/
theorem tetraktys_hodge_inversion_dihedral_duality (X : ZornMatrix R) :
    hodgeSwap (leftG5 X)  = -leftG5 (hodgeSwap X) ∧
    hodgeSwap (rightG5 X) = -rightG5 (hodgeSwap X) ∧
    hodgeSwap (adG5 X)    =  adG5 (hodgeSwap X) := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_A1 (`universal_alternating_gamma5_associator_chain`):**
For ANY `[Ring R]` and ANY `X, Y : ZornMatrix R`:
1. `[γ₅, X, Y] = ⟨0, 2(v_X × v_Y), 2(u_X × u_Y), 0⟩`.
2. `[X, γ₅, Y] = ⟨0, -2(v_X × v_Y), -2(u_X × u_Y), 0⟩ = -[γ₅, X, Y] = -[X, Y, γ₅]`.
3. `[X, Y, γ₅] = ⟨0, 2(v_X × v_Y), 2(u_X × u_Y), 0⟩`. -/
theorem universal_alternating_gamma5_associator_chain (X Y : ZornMatrix R) :
    let vu := Vec3.cross X.v Y.v
    let uv := Vec3.cross X.u Y.u
    associator gamma5 X Y = ⟨0, vu + vu, uv + uv, 0⟩ ∧
    associator X gamma5 Y = ⟨0, -(vu + vu), -(uv + uv), 0⟩ ∧
    associator X Y gamma5 = ⟨0, vu + vu, uv + uv, 0⟩ ∧
    associator gamma5 X Y + associator X gamma5 Y + associator X Y gamma5 =
      ⟨0, vu + vu, uv + uv, 0⟩ := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_A2 (`universal_tetraktys_spine_unification`):**
Unification of the associative Peirce Tetraktys `(V, Φ, J, Σ)` with the non-associative
Zorn split-octonion associator `[γ₅, Φ, Φ]`. -/
theorem universal_tetraktys_spine_unification (u v : Vec3 R) :
    let Phi := psiOffDiag u v
    let J   := zornJ u v
    let V   := zornV u v
    let Sig := zornSig u v
    let bu  := Vec3.cross u u
    let bv  := Vec3.cross v v
    commZorn gamma5 Phi = J + J ∧
    commZorn gamma5 J   = Phi + Phi ∧
    (gamma5 : ZornMatrix R) * V = Sig ∧
    (gamma5 : ZornMatrix R) * Sig = V ∧
    J * Phi = Sig + ⟨0, bv, bu, 0⟩ ∧
    Phi * Phi = V + ⟨0, -bv, bu, 0⟩ ∧
    J * J     = -V + ⟨0, -bv, bu, 0⟩ ∧
    associator gamma5 Phi Phi = ⟨0, bv + bv, bu + bu, 0⟩ ∧
    associator Phi gamma5 Phi = ⟨0, -(bv + bv), -(bu + bu), 0⟩ := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring,
          by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_A3 (`archetype_A88_zorn_tetraktys_diquark_baryon_and_chromomagnetic_anomaly`):**
1. Pure Quark Diquark Exterior Wedge `psiPlus q₁ * psiPlus q₂ = psiMinus (q₁ × q₂)`.
2. Baryon Singlet Determinant `[psiPlus q₁, psiPlus q₂, psiPlus q₃] = ⟨-det, 0, 0, +det⟩`.
3. Non-Abelian Chromomagnetic Anomaly on `Φ²`, `J²`, and `J * Φ`. -/
theorem archetype_A88_zorn_tetraktys_diquark_baryon_and_chromomagnetic_anomaly
    (q₁ q₂ q₃ u v : Vec3 R) :
    let detQ := Vec3.dot (Vec3.cross q₁ q₂) q₃
    let Phi  := psiOffDiag u v
    let J    := zornJ u v
    let V    := zornV u v
    let Sig  := zornSig u v
    let bu   := Vec3.cross u u
    let bv   := Vec3.cross v v
    psiPlus q₁ * psiPlus q₂ = psiMinus (Vec3.cross q₁ q₂) ∧
    psiMinus q₁ * psiMinus q₂ = psiPlus (-Vec3.cross q₁ q₂) ∧
    (psiPlus q₁ * psiPlus q₂) * psiPlus q₃ = ⟨0, 0, 0, detQ⟩ ∧
    psiPlus q₁ * (psiPlus q₂ * psiPlus q₃) = ⟨detQ, 0, 0, 0⟩ ∧
    associator (psiPlus q₁) (psiPlus q₂) (psiPlus q₃) = ⟨-detQ, 0, 0, detQ⟩ ∧
    Phi * Phi + J * J = ⟨0, -(bv + bv), bu + bu, 0⟩ ∧
    Phi * Phi - J * J = V + V ∧
    J * Phi - Phi * J = Sig + Sig ∧
    J * Phi + Phi * J = ⟨0, bv + bv, bu + bu, 0⟩ := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring,
          by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

/-- **Theorem ZS_A4 (`archetype_A89_baryon_parity_partner_pure_quark_vacuum_and_cyclic_jacobi`):**
1. Chiral Baryon Parity Partner `((psiPlus q₁ * psiPlus q₂) * psiPlus q₃) + psiPlus q₁ * (psiPlus q₂ * psiPlus q₃) = ⟨det, 0, 0, det⟩`.
2. Pure-Quark 3rd-Order Vacuum Condensation `[psiPlus u, psiPlus u, psiPlus u] = -nambu3(u) * γ₅`.
3. Universal 3-Flavour Cyclic Jacobi–Baryon Identity over any non-commutative `[Ring R]`.
4. The `(2/3, -1/3)` 3-Channel Projector Purification Law `2 Σ_RR(X) - Σ_LL(X) = 3 (e_L * X)`. -/
theorem archetype_A89_baryon_parity_partner_pure_quark_vacuum_and_cyclic_jacobi
    (q₁ q₂ q₃ u : Vec3 R) (X : ZornMatrix R) :
    let det123 := Vec3.dot (Vec3.cross q₁ q₂) q₃
    let det231 := Vec3.dot (Vec3.cross q₂ q₃) q₁
    let det312 := Vec3.dot (Vec3.cross q₃ q₁) q₂
    let c123   := Vec3.dot q₁ (Vec3.cross q₂ q₃)
    let c231   := Vec3.dot q₂ (Vec3.cross q₃ q₁)
    let c312   := Vec3.dot q₃ (Vec3.cross q₁ q₂)
    ((psiPlus q₁ * psiPlus q₂) * psiPlus q₃) + (psiPlus q₁ * (psiPlus q₂ * psiPlus q₃)) =
      ⟨det123, 0, 0, det123⟩ ∧
    ((psiPlus u * psiPlus u) * psiPlus u) = ⟨0, 0, 0, Vec3.nambu3 u⟩ ∧
    (psiPlus u * (psiPlus u * psiPlus u)) = ⟨Vec3.nambu3 u, 0, 0, 0⟩ ∧
    cubicAssociator (psiPlus u) = ⟨-Vec3.nambu3 u, 0, 0, Vec3.nambu3 u⟩ ∧
    associator (psiPlus q₁) (psiPlus q₂) (psiPlus q₃) +
    associator (psiPlus q₂) (psiPlus q₃) (psiPlus q₁) +
    associator (psiPlus q₃) (psiPlus q₁) (psiPlus q₂) =
      ⟨-(det123 + det231 + det312), 0, 0, c123 + c231 + c312⟩ ∧
    (sigmaRR X + sigmaRR X) - sigmaLL X = (eL * X) + (eL * X) + (eL * X) := by
  refine ⟨by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring, by zorn_ring⟩

end ZornMatrix

-- ============================================================================
-- UNIVERSAL FOUR-PILLAR ROSETTA STONE (`ZornNC R` with `conj` & `totalConj`)
-- ============================================================================

/-- Non-Commutative Zorn–Kantor Structurable Algebra `ZornNC R` (using `-dot` Hurwitz convention). -/
@[ext]
structure ZornNC (R : Type u) where
  α : R
  x : Vec3 R
  y : Vec3 R
  β : R
  deriving DecidableEq, Repr, Inhabited

namespace ZornNC
variable {R : Type u} [Ring R]

@[simp] def zero   : ZornNC R := ⟨0, 0, 0, 0⟩
@[simp] def one    : ZornNC R := ⟨1, 0, 0, 1⟩
@[simp] def gamma5 : ZornNC R := ⟨1, 0, 0, -1⟩
@[simp] def add (A B : ZornNC R) : ZornNC R := ⟨A.α + B.α, A.x + B.x, A.y + B.y, A.β + B.β⟩
@[simp] def neg (A : ZornNC R)   : ZornNC R := ⟨-A.α, -A.x, -A.y, -A.β⟩
@[simp] def sub (A B : ZornNC R) : ZornNC R := ⟨A.α - B.α, A.x - B.x, A.y - B.y, A.β - B.β⟩

instance instZero : Zero (ZornNC R) := ⟨zero⟩
instance instOne : One (ZornNC R)  := ⟨one⟩
instance instAdd : Add (ZornNC R)  := ⟨add⟩
instance instNeg : Neg (ZornNC R)  := ⟨neg⟩
instance instSub : Sub (ZornNC R)  := ⟨sub⟩

@[simp] def mul (A B : ZornNC R) : ZornNC R where
  α := A.α * B.α - Vec3.dot A.x B.y
  x := Vec3.smulLeft A.α B.x + Vec3.smulRight A.x B.β + Vec3.cross A.y B.y
  y := Vec3.smulLeft A.β B.y + Vec3.smulRight A.y B.α + Vec3.cross A.x B.x
  β := A.β * B.β - Vec3.dot A.y B.x

instance instMul : Mul (ZornNC R) := ⟨mul⟩

@[simp] lemma zero_α : (0 : ZornNC R).α = 0 := rfl
@[simp] lemma zero_x : (0 : ZornNC R).x = 0 := rfl
@[simp] lemma zero_y : (0 : ZornNC R).y = 0 := rfl
@[simp] lemma zero_β : (0 : ZornNC R).β = 0 := rfl
@[simp] lemma one_α  : (1 : ZornNC R).α = 1 := rfl
@[simp] lemma one_x  : (1 : ZornNC R).x = 0 := rfl
@[simp] lemma one_y  : (1 : ZornNC R).y = 0 := rfl
@[simp] lemma one_β  : (1 : ZornNC R).β = 1 := rfl
@[simp] lemma add_α (A B : ZornNC R) : (A + B).α = A.α + B.α := rfl
@[simp] lemma add_x (A B : ZornNC R) : (A + B).x = A.x + B.x := rfl
@[simp] lemma add_y (A B : ZornNC R) : (A + B).y = A.y + B.y := rfl
@[simp] lemma add_β (A B : ZornNC R) : (A + B).β = A.β + B.β := rfl
@[simp] lemma neg_α (A : ZornNC R) : (-A).α = -A.α := rfl
@[simp] lemma neg_x (A : ZornNC R) : (-A).x = -A.x := rfl
@[simp] lemma neg_y (A : ZornNC R) : (-A).y = -A.y := rfl
@[simp] lemma neg_β (A : ZornNC R) : (-A).β = -A.β := rfl
@[simp] lemma sub_α (A B : ZornNC R) : (A - B).α = A.α - B.α := rfl
@[simp] lemma sub_x (A B : ZornNC R) : (A - B).x = A.x - B.x := rfl
@[simp] lemma sub_y (A B : ZornNC R) : (A - B).y = A.y - B.y := rfl
@[simp] lemma sub_β (A B : ZornNC R) : (A - B).β = A.β - B.β := rfl
@[simp] lemma mul_def (A B : ZornNC R) : A * B = mul A B := rfl

@[simp] def commZorn (A B : ZornNC R) : ZornNC R := A * B - B * A
@[simp] def anticommZorn (A B : ZornNC R) : ZornNC R := A * B + B * A
@[simp] def associator (A B C : ZornNC R) : ZornNC R := (A * B) * C - A * (B * C)
@[simp] def superTrace (X : ZornNC R) : R := X.α - X.β

@[simp] def conj (X : ZornNC R) : ZornNC R := ⟨X.β, -X.x, -X.y, X.α⟩

@[simp] def totalConj [Star R] (X : ZornNC R) : ZornNC R :=
  ⟨star X.β, -Vec3.starVec X.x, -Vec3.starVec X.y, star X.α⟩

@[simp] def normRight (X : ZornNC R) : ZornNC R := X * conj X
@[simp] def normLeft (X : ZornNC R) : ZornNC R := conj X * X

@[simp] def kantorTriple (X Y Z : ZornNC R) : ZornNC R :=
  (X * conj Y) * Z + (Z * conj Y) * X - (Z * conj X) * Y

@[simp] def psiCov (α : R) (p : Vec3 R) : ZornNC R := ⟨α, p, p, α⟩
@[simp] def diracPlus (α : R) (p : Vec3 R) : ZornNC R := ⟨α, p, -p, -α⟩
@[simp] def diracMinus (α : R) (p : Vec3 R) : ZornNC R := ⟨α, -p, p, -α⟩
@[simp] def weyl1 : ZornNC R := ⟨0, ⟨1, 0, 0⟩, ⟨-1, 0, 0⟩, 0⟩

macro "zorn_nc_ring" : tactic =>
  `(tactic| (
    (try ext) <;>
    (simp only [zero_α, zero_x, zero_y, zero_β, one_α, one_x, one_y, one_β,
                add_α, add_x, add_y, add_β, neg_α, neg_x, neg_y, neg_β,
                sub_α, sub_x, sub_y, sub_β, mul_def, mul, gamma5,
                commZorn, anticommZorn, associator, superTrace,
                conj, normRight, normLeft, kantorTriple,
                psiCov, diracPlus, diracMinus, weyl1,
                Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
                Vec3.add_x, Vec3.add_y, Vec3.add_z,
                Vec3.neg_x, Vec3.neg_y, Vec3.neg_z,
                Vec3.sub_x, Vec3.sub_y, Vec3.sub_z,
                Vec3.smulLeft, Vec3.smulRight, Vec3.dot, Vec3.cross,
                Vec3.commOp, Vec3.commVec, Vec3.adjointDiv, Vec3.adjointCurl, Vec3.nambu3,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_zero, neg_neg, neg_add_rev, neg_sub, sub_neg_eq_add,
                neg_mul, mul_neg, add_mul, mul_add, sub_mul, mul_sub, mul_assoc];
     try abel)))

/-- **Theorem ZS_R1..R5 (Universal Four-Pillar Rosetta Stone over `[Ring R]`):**
1. Right Hurwitz–Zorn Norm `normRight (psiCov α p) = ⟨lap, -(E + B), -(E + B), lap⟩`.
2. Supertrace Zero-Point Commutator `superTrace (normRight X) = [α, β] + (x ·_ad y)`.
3. Full 4-Sector Moufang–Norm Associator `[X, conj X, X]_diag = ∓(nambu3 x - nambu3 y)`.
4. Kantor–Allison Self-Triple Product on Weyl Reflections `{W₁, W₁, W₁} = -W₁`.
5. Left Hurwitz–Zorn Norm `normLeft (psiCov α p)` & Pure Chromoelectric Commutator `[Ψ, conj Ψ] = -2 E`. -/
theorem universal_rosetta_stone_hurwitz_nambu_kantor (α : R) (p : Vec3 R) (X : ZornNC R) :
    let E   := Vec3.commVec α p
    let B   := Vec3.cross p p
    let lap := α * α + Vec3.dot p p
    let netNambu := Vec3.nambu3 X.x - Vec3.nambu3 X.y
    normRight (psiCov α p) = ⟨lap, -(E + B), -(E + B), lap⟩ ∧
    superTrace (normRight X) = (X.α * X.β - X.β * X.α) + Vec3.adjointDiv X.x X.y ∧
    (associator X (conj X) X).α = -netNambu ∧
    (associator X (conj X) X).β =  netNambu ∧
    conj (weyl1 : ZornNC R) = -weyl1 ∧
    normRight (weyl1 : ZornNC R) = -1 ∧
    kantorTriple (weyl1 : ZornNC R) weyl1 weyl1 = -weyl1 ∧
    normLeft (psiCov α p) = ⟨lap, E - B, E - B, lap⟩ ∧
    commZorn (psiCov α p) (conj (psiCov α p)) = ⟨0, -(E + E), -(E + E), 0⟩ ∧
    conj (psiCov α p * psiCov α p) - (conj (psiCov α p) * conj (psiCov α p)) =
      ⟨0, -(B + B), -(B + B), 0⟩ := by
  refine ⟨by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring,
          by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring⟩

/-- **Theorem ZS_R6 (`universal_total_tensor_involution_is_anti_automorphism`):**
Over ANY `[Ring R] [StarRing R]`, the Total Tensor Involution `totalConj = star ⊗ bar`
satisfies `totalConj (X * Y) = totalConj Y * totalConj X` identically for all `X, Y : ZornNC R`. -/
theorem universal_total_tensor_involution_is_anti_automorphism [StarRing R] (X Y : ZornNC R) :
    totalConj (X * Y) = totalConj Y * totalConj X := by
  ext <;>
  · simp only [totalConj, mul_def, mul, Vec3.starVec,
               Vec3.add_x, Vec3.add_y, Vec3.add_z,
               Vec3.neg_x, Vec3.neg_y, Vec3.neg_z,
               Vec3.smulLeft, Vec3.smulRight, Vec3.dot, Vec3.cross,
               star_sub, star_add, star_mul,
               neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add]
    abel

/-- **Theorem ZS_R7_R8 (`universal_chiral_factorization_and_dirac_gauss_ampere`):**
Chiral `γ₅` factorization `D_+ = γ₅ * Ψ_cov`, `D_- = Ψ_cov * γ₅`, pure imaginary octonion
property `conj D_+ = -D_+`, and unified conjugate-twisted Gauss–Ampère extraction
`conj D_+ * F_+ - F_+ * D_+ = ⟨G_gauss, -J_amp, J_amp, -G_gauss⟩`. -/
theorem universal_chiral_factorization_and_dirac_gauss_ampere (α : R) (p : Vec3 R) :
    let Ψ   := psiCov α p
    let D_p := diracPlus α p
    let D_m := diracMinus α p
    let E   := Vec3.commVec α p
    let B   := Vec3.cross p p
    let F_p : ZornNC R := ⟨0, B + E, B + E, 0⟩
    let G_gauss := Vec3.adjointDiv p E
    let J_amp   := Vec3.commVec α E - Vec3.adjointCurl p B
    D_p = gamma5 * Ψ ∧
    D_m = Ψ * gamma5 ∧
    conj D_p = -D_p ∧
    normRight D_p = -(D_p * D_p) ∧
    conj D_p * F_p - F_p * D_p = ⟨G_gauss, -J_amp, J_amp, -G_gauss⟩ := by
  refine ⟨by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring, by zorn_nc_ring⟩

end ZornNC

-- ============================================================================
-- STAGE ZND₂: Universal `[Ring R]` 3D Operator-Valued De Rham & Dirac–Kähler Poset
-- ============================================================================

/-- The Zorn De Rham Exterior Complex `ZornForms R` (`Ω•(R) = Ω⁰ ⊕ Ω¹ ⊕ Ω² ⊕ Ω³`) over `[Ring R]`. -/
@[ext]
structure ZornForms (R : Type u) where
  ω0 : R
  ω1 : Vec3 R
  ω2 : Vec3 R
  ω3 : R
  deriving DecidableEq, Repr, Inhabited

namespace ZornForms
variable {R : Type u} [Ring R]

@[simp] def zero : ZornForms R := ⟨0, 0, 0, 0⟩
@[simp] def add (A B : ZornForms R) : ZornForms R :=
  ⟨A.ω0 + B.ω0, A.ω1 + B.ω1, A.ω2 + B.ω2, A.ω3 + B.ω3⟩
@[simp] def neg (A : ZornForms R) : ZornForms R :=
  ⟨-A.ω0, -A.ω1, -A.ω2, -A.ω3⟩
@[simp] def sub (A B : ZornForms R) : ZornForms R :=
  ⟨A.ω0 - B.ω0, A.ω1 - B.ω1, A.ω2 - B.ω2, A.ω3 - B.ω3⟩

instance instZero : Zero (ZornForms R) := ⟨zero⟩
instance instAdd : Add (ZornForms R)  := ⟨add⟩
instance instNeg : Neg (ZornForms R)  := ⟨neg⟩
instance instSub : Sub (ZornForms R)  := ⟨sub⟩

@[simp] lemma zero_ω0 : (0 : ZornForms R).ω0 = 0 := rfl
@[simp] lemma zero_ω1 : (0 : ZornForms R).ω1 = 0 := rfl
@[simp] lemma zero_ω2 : (0 : ZornForms R).ω2 = 0 := rfl
@[simp] lemma zero_ω3 : (0 : ZornForms R).ω3 = 0 := rfl
@[simp] lemma add_ω0 (A B : ZornForms R) : (A + B).ω0 = A.ω0 + B.ω0 := rfl
@[simp] lemma add_ω1 (A B : ZornForms R) : (A + B).ω1 = A.ω1 + B.ω1 := rfl
@[simp] lemma add_ω2 (A B : ZornForms R) : (A + B).ω2 = A.ω2 + B.ω2 := rfl
@[simp] lemma add_ω3 (A B : ZornForms R) : (A + B).ω3 = A.ω3 + B.ω3 := rfl
@[simp] lemma neg_ω0 (A : ZornForms R) : (-A).ω0 = -A.ω0 := rfl
@[simp] lemma neg_ω1 (A : ZornForms R) : (-A).ω1 = -A.ω1 := rfl
@[simp] lemma neg_ω2 (A : ZornForms R) : (-A).ω2 = -A.ω2 := rfl
@[simp] lemma neg_ω3 (A : ZornForms R) : (-A).ω3 = -A.ω3 := rfl
@[simp] lemma sub_ω0 (A B : ZornForms R) : (A - B).ω0 = A.ω0 - B.ω0 := rfl
@[simp] lemma sub_ω1 (A B : ZornForms R) : (A - B).ω1 = A.ω1 - B.ω1 := rfl
@[simp] lemma sub_ω2 (A B : ZornForms R) : (A - B).ω2 = A.ω2 - B.ω2 := rfl
@[simp] lemma sub_ω3 (A B : ZornForms R) : (A - B).ω3 = A.ω3 - B.ω3 := rfl

/-- Non-commutative Fréchet directional derivative of bilinear product `F(X, Y) = X * Y`. -/
@[simp] def frechetBilinear (X Y dX dY : R) : R := dX * Y + X * dY

/-- Non-commutative Fréchet directional derivative of cubic monomial `F(X) = X³`. -/
@[simp] def frechetCube (X dX : R) : R := (dX * X) * X + (X * dX) * X + (X * X) * dX

/-- Graded Exterior Wedge Product `ω ∧ η` on `Ω•(R)`. -/
@[simp] def wedge (A B : ZornForms R) : ZornForms R where
  ω0 := A.ω0 * B.ω0
  ω1 := Vec3.smulLeft A.ω0 B.ω1 + Vec3.smulRight A.ω1 B.ω0
  ω2 := Vec3.smulLeft A.ω0 B.ω2 + Vec3.smulRight A.ω2 B.ω0 + Vec3.cross A.ω1 B.ω1
  ω3 := A.ω0 * B.ω3 + A.ω3 * B.ω0 + Vec3.dot A.ω1 B.ω2 + Vec3.dot A.ω2 B.ω1

/-- Non-Associative Zorn Split-Octonion Product on `ZornForms R`. -/
@[simp] def zornMul (A B : ZornForms R) : ZornForms R where
  ω0 := A.ω0 * B.ω0 - Vec3.dot A.ω1 B.ω2
  ω1 := Vec3.smulLeft A.ω0 B.ω1 + Vec3.smulRight A.ω1 B.ω3 + Vec3.cross A.ω2 B.ω2
  ω2 := Vec3.smulLeft A.ω3 B.ω2 + Vec3.smulRight A.ω2 B.ω0 + Vec3.cross A.ω1 B.ω1
  ω3 := A.ω3 * B.ω3 - Vec3.dot A.ω2 B.ω1

/-- Euclidean Hodge Star Operator `⋆ : Ω^k(R) → Ω^{3-k}(R)`. -/
@[simp] def hodgeStar (ω : ZornForms R) : ZornForms R := ⟨ω.ω3, ω.ω2, ω.ω1, ω.ω0⟩

/-- Generalized Curl / Covariant Exterior Derivative `d_∇ : Ω^k(R) → Ω^{k+1}(R)`. -/
@[simp] def extCurl (p : Vec3 R) (ω : ZornForms R) : ZornForms R where
  ω0 := 0
  ω1 := Vec3.adjointGrad p ω.ω0
  ω2 := Vec3.adjointCurl p ω.ω1
  ω3 := Vec3.adjointDiv  p ω.ω2

/-- Generalized Div / Negative Codifferential `Div_∇ = -δ_∇ : Ω^k(R) → Ω^{k-1}(R)`. -/
@[simp] def extDiv (p : Vec3 R) (ω : ZornForms R) : ZornForms R where
  ω0 := Vec3.adjointDiv  p ω.ω1
  ω1 := -Vec3.adjointCurl p ω.ω2
  ω2 := Vec3.adjointGrad p ω.ω3
  ω3 := 0

/-- Covariant Codifferential `δ_∇ = -Div_∇ : Ω^k(R) → Ω^{k-1}(R)`. -/
@[simp] def codiff (p : Vec3 R) (ω : ZornForms R) : ZornForms R := -extDiv p ω

/-- Unified Dirac–Kähler Operator `D_DK = d_∇ - δ_∇ = extCurl + extDiv`. -/
@[simp] def diracKaehler (p : Vec3 R) (ω : ZornForms R) : ZornForms R :=
  extCurl p ω + extDiv p ω

/-- Covariant Hodge–de Rham Laplacian `Δ_Hodge = d_∇ δ_∇ + δ_∇ d_∇`. -/
@[simp] def hodgeLaplacian (p : Vec3 R) (ω : ZornForms R) : ZornForms R :=
  extCurl p (codiff p ω) + codiff p (extCurl p ω)

@[simp] def form0 (φ : R) : ZornForms R := ⟨φ, 0, 0, 0⟩
@[simp] def form1 (A : Vec3 R) : ZornForms R := ⟨0, A, 0, 0⟩
@[simp] def form2 (B : Vec3 R) : ZornForms R := ⟨0, 0, B, 0⟩

macro "zorn_forms_ring" : tactic =>
  `(tactic| (
    (try ext) <;>
    (simp only [zero_ω0, zero_ω1, zero_ω2, zero_ω3,
                add_ω0, add_ω1, add_ω2, add_ω3,
                neg_ω0, neg_ω1, neg_ω2, neg_ω3,
                sub_ω0, sub_ω1, sub_ω2, sub_ω3,
                frechetBilinear, frechetCube,
                wedge, zornMul, hodgeStar, extCurl, extDiv, codiff,
                diracKaehler, hodgeLaplacian, form0, form1, form2,
                Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
                Vec3.add_x, Vec3.add_y, Vec3.add_z,
                Vec3.neg_x, Vec3.neg_y, Vec3.neg_z,
                Vec3.sub_x, Vec3.sub_y, Vec3.sub_z,
                Vec3.smulLeft, Vec3.smulRight, Vec3.dot, Vec3.cross,
                Vec3.commOp, Vec3.commVec, Vec3.adjointGrad,
                Vec3.adjointDiv, Vec3.adjointCurl,
                Vec3.convectiveLeft, Vec3.convectiveRight,
                Vec3.bochnerScalar, Vec3.bochnerVec,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_zero, neg_neg, neg_add_rev, neg_sub, sub_neg_eq_add,
                neg_mul, mul_neg, add_mul, mul_add, sub_mul, mul_sub, mul_assoc];
     try abel)))

/-- **Theorem DK_1 (`frechet_commutator_leibniz_bridge`):**
Over ANY `[Ring R]`, the commutator derivation `[p, F(X)]` equals the non-commutative Fréchet
directional derivative `DF(X)[[p, X]]` on bilinear (`X * Y`) and cubic (`X³`) polynomials. -/
theorem frechet_commutator_leibniz_bridge (p X Y : R) :
    let dX := Vec3.commOp p X
    let dY := Vec3.commOp p Y
    Vec3.commOp p (X * Y) = frechetBilinear X Y dX dY ∧
    Vec3.commOp p ((X * X) * X) = frechetCube X dX := by
  refine ⟨by zorn_forms_ring, by zorn_forms_ring⟩

/-- **Theorem DK_2 (`hodge_duality_of_generalized_div_and_curl`):**
Over ANY `[Ring R]`, `⋆ d_∇ ⋆` reproduces the components of `extDiv` across all 4 grades
(with the graded sign `-1` on 2-forms). -/
theorem hodge_duality_of_generalized_div_and_curl (p : Vec3 R) (ω : ZornForms R) :
    let dualD := hodgeStar (extCurl p (hodgeStar ω))
    let divW  := extDiv p ω
    dualD.ω0 = divW.ω0 ∧
    dualD.ω1 = -divW.ω1 ∧
    dualD.ω2 = divW.ω2 ∧
    dualD.ω3 = divW.ω3 := by
  refine ⟨by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring⟩

/-- **Theorem DK_3 (`graded_leibniz_rule_for_operator_forms`):**
Over ANY `[Ring R]`, `d_∇(ω^(k) ∧ η) = (d_∇ ω^(k)) ∧ η + (-1)^k ω^(k) ∧ (d_∇ η)`
for `k = 0` (`+1` sign) and `k = 1` (`-1` sign: `Div_ad(A × C) = (Curl_ad A)·C - A·(Curl_ad C)`). -/
theorem graded_leibniz_rule_for_operator_forms (p A C : Vec3 R) (φ : R) :
    extCurl p (wedge (form0 φ) (form1 A)) =
      wedge (extCurl p (form0 φ)) (form1 A) + wedge (form0 φ) (extCurl p (form1 A)) ∧
    extCurl p (wedge (form1 A) (form1 C)) =
      wedge (extCurl p (form1 A)) (form1 C) - wedge (form1 A) (extCurl p (form1 C)) ∧
    Vec3.adjointDiv p (Vec3.cross A C) =
      Vec3.dot (Vec3.adjointCurl p A) C - Vec3.dot A (Vec3.adjointCurl p C) := by
  refine ⟨by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring⟩

/-- **Theorem DK_4 (`interior_leibniz_rule_for_generalized_div`):**
Over ANY `[Ring R]`, `Div_ad(φ A) = (Grad_ad φ) · A + φ * (Div_ad A)`. -/
theorem interior_leibniz_rule_for_generalized_div (p A : Vec3 R) (φ : R) :
    (extDiv p (wedge (form0 φ) (form1 A))).ω0 =
      Vec3.dot (Vec3.adjointGrad p φ) A + φ * Vec3.adjointDiv p A := by
  zorn_forms_ring

/-- **Theorem DK_5 (`curvature_square_of_extCurl_and_hodge_laplacian`):**
Over ANY `[Ring R]`, `d_∇²` and `Div_∇²` act by the chromomagnetic curvature `B = p × p`,
and `hodgeLaplacian = d_∇ δ_∇ + δ_∇ d_∇` equals `-Δ_Bochner` plus the Weitzenböck magnetic
curvature twist `B ×_ad ·` on `Ω¹` and `Ω²`. -/
theorem curvature_square_of_extCurl_and_hodge_laplacian (p : Vec3 R) (ω : ZornForms R) :
    let B  := Vec3.cross p p
    let d2 := extCurl p (extCurl p ω)
    let v2 := extDiv  p (extDiv  p ω)
    let lapHodge := hodgeLaplacian p ω
    d2.ω0 = 0 ∧
    d2.ω1 = 0 ∧
    d2.ω2 = Vec3.adjointGrad B ω.ω0 ∧
    d2.ω3 = Vec3.adjointDiv B ω.ω1 ∧
    v2.ω0 = -Vec3.adjointDiv B ω.ω2 ∧
    v2.ω1 = -Vec3.adjointGrad B ω.ω3 ∧
    v2.ω2 = 0 ∧
    v2.ω3 = 0 ∧
    lapHodge.ω0 = -Vec3.bochnerScalar p ω.ω0 ∧
    lapHodge.ω1 = -Vec3.bochnerVec p ω.ω1 + Vec3.adjointCurl B ω.ω1 ∧
    lapHodge.ω2 = -Vec3.bochnerVec p ω.ω2 + Vec3.adjointCurl B ω.ω2 ∧
    lapHodge.ω3 = -Vec3.bochnerScalar p ω.ω3 := by
  refine ⟨by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring,
          by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring,
          by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring⟩

/-- **Theorem DK_6 (`bv_second_order_convective_rule_for_extDiv`):**
Over ANY `[Ring R]`, the second-order Batalin–Vilkovisky operator `extDiv` on `form1 A ∧ form1 C`
equals `(Div_ad A) C - A (Div_ad C)` plus the BV convective antibracket defect
`(A · ∇_ad) C - (∇_ad A) · C`. -/
theorem bv_second_order_convective_rule_for_extDiv (p A C : Vec3 R) :
    let divTerm := Vec3.smulLeft (Vec3.adjointDiv p A) C - Vec3.smulRight A (Vec3.adjointDiv p C)
    let bvConvectiveDefect := Vec3.convectiveLeft p A C - Vec3.convectiveRight p A C
    (extDiv p (wedge (form1 A) (form1 C))).ω1 = divTerm + bvConvectiveDefect := by
  zorn_forms_ring

/-- **Theorem DK_7 (`dirac_kaehler_square_three_channel_decomposition`):**
Over ANY `[Ring R]`, squaring `diracKaehler = extCurl + extDiv` decomposes into the
3 orthogonal grade-shift channels `d_∇² + Div_∇² - Δ_Hodge`. -/
theorem dirac_kaehler_square_three_channel_decomposition (p : Vec3 R) (ω : ZornForms R) :
    diracKaehler p (diracKaehler p ω) =
      (extCurl p (extCurl p ω) + extDiv p (extDiv p ω)) - hodgeLaplacian p ω := by
  zorn_forms_ring

/-- **Theorem DK_8 (`de_rham_pontryagin_chain_from_temporal_connection`):**
Over ANY `[Ring R]`, iterating `extCurl p` on `form0 α` generates `-E` at step 1,
`-[α, B]` at step 2, and the 4th-order Pontryagin 3-form `E ·_ad B` at step 3,
and satisfies the differential Bianchi commutation `(d_∇ ∘ d_∇²)(φ) = (d_∇² ∘ d_∇)(φ)`. -/
theorem de_rham_pontryagin_chain_from_temporal_connection (p : Vec3 R) (α φ : R) :
    let E  := Vec3.commVec α p
    let B  := Vec3.cross p p
    let d1 := extCurl p (form0 α)
    let d2 := extCurl p d1
    let d3 := extCurl p d2
    d1 = ⟨0, -E, 0, 0⟩ ∧
    d2 = ⟨0, 0, -Vec3.commVec α B, 0⟩ ∧
    d3 = ⟨0, 0, 0, Vec3.adjointDiv E B⟩ ∧
    (extCurl p (extCurl p (extCurl p (form0 φ)))).ω3 =
      Vec3.adjointDiv B (Vec3.adjointGrad p φ) := by
  refine ⟨by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring⟩

/-- **Theorem DK_9 (`zorn_clifford_to_de_rham_wedge_bridge`):**
Exact bridge between non-associative Zorn multiplication `zornMul` and the De Rham `wedge` product. -/
theorem zorn_clifford_to_de_rham_wedge_bridge (A C : Vec3 R) :
    (zornMul (form1 A) (form1 C)).ω2 = (wedge (form1 A) (form1 C)).ω2 ∧
    (zornMul (form1 A) (form2 C)).ω0 = -(wedge (form1 A) (form2 C)).ω3 ∧
    (zornMul (form2 C) (form1 A)).ω3 = -(wedge (form2 C) (form1 A)).ω3 := by
  refine ⟨by zorn_forms_ring, by zorn_forms_ring, by zorn_forms_ring⟩

end ZornForms

-- ============================================================================
-- STAGE ZND₃: Operator Pell Equation, Dual Chiral `γ⁵`, Malik–Thome DMP–MPD, & QGT
-- ============================================================================

section PeirceOperatorSpine

variable {B : Type*} [Ring B]

def comm (X Y : B) : B := X * Y - Y * X
def anticomm (X Y : B) : B := X * Y + Y * X
def assocDefect (X Y Z : B) : B := X * Y * Z - Y * X * Z

def invS (P : B) : B := P - (1 - P)
def idempDefect (P : B) : B := P * P - P

def secPP (P X : B) : B := P * X * P
def secPM (P X : B) : B := P * X * (1 - P)
def secMP (P X : B) : B := (1 - P) * X * P
def secMM (P X : B) : B := (1 - P) * X * (1 - P)

def conePlus (P A : B) : B := P * A * (1 - P)
def coneMinus (P C : B) : B := (1 - P) * C * P

def genPhi (P A C : B) : B := conePlus P A + coneMinus P C
def genJ   (P A C : B) : B := conePlus P A - coneMinus P C
def genV   (P A C : B) : B := anticomm (conePlus P A) (coneMinus P C)
def genSig (P A C : B) : B := comm (conePlus P A) (coneMinus P C)

def qgtPlus  (P A C : B) : B := conePlus P A * coneMinus P C
def qgtMinus (P A C : B) : B := coneMinus P C * conePlus P A

def coreOp (P X : B) : B := secPP P X + secMM P X
def offOp  (P X : B) : B := secPM P X + secMP P X

def twoOp   (X : B) : B := X + X
def threeOp (X : B) : B := X + X + X
def fourOp  (X : B) : B := X + X + X + X
def eightOp (X : B) : B := fourOp X + fourOp X

def newtonStep (P : B) : B := threeOp (P * P) - twoOp (P * P * P)
def pellScale (P : B) : B := (1 : B) + fourOp (idempDefect P)

def weakNum (P A X : B) : B := (1 - P) * X * conePlus P A
def weakDen (P A C : B) : B := qgtMinus P A C
def weakRem (P A C X : B) : B := secMP P X * qgtPlus P A C - qgtMinus P A C * secMP P X

/-- **Coordinate-Free Drazin Core-Nilpotent Resolution (`DrazinResolution M P C N B_d`)**:
Over any non-commutative ring `B`, an operator `M : B` has an index-`≤ 2` Drazin resolution
with spectral idempotent `P`, invertible core `C` (with Drazin inverse `B_d`), and square-zero
nilpotent transient `N` when:
- `P * P = P` (spectral idempotent),
- `M = C + N` with `P * C = C`, `C * P = C`, `P * N = 0`, `N * P = 0`, `N * N = 0`,
- `B_d * P = B_d`, `P * B_d = B_d`, `C * B_d = P`, and `B_d * C = P`. -/
structure DrazinResolution (M P C N B_d : B) : Prop where
  idem : P * P = P
  decomp : M = C + N
  core_left : P * C = C
  core_right : C * P = C
  nil_left : P * N = 0
  nil_right : N * P = 0
  nil_sq : N * N = 0
  drazin_left : P * B_d = B_d
  drazin_right : B_d * P = B_d
  core_inv_right : C * B_d = P
  core_inv_left : B_d * C = P

/-- Constructive inhabitant witness for `DrazinResolution` (`0` in any ring `B`). -/
theorem drazinResolution_zero_witness :
    DrazinResolution (0 : B) 0 0 0 0 :=
  { idem := mul_zero 0
    decomp := (add_zero 0).symm
    core_left := mul_zero 0
    core_right := mul_zero 0
    nil_left := mul_zero 0
    nil_right := mul_zero 0
    nil_sq := mul_zero 0
    drazin_left := mul_zero 0
    drazin_right := mul_zero 0
    core_inv_right := mul_zero 0
    core_inv_left := mul_zero 0 }

end PeirceOperatorSpine

/-- **Penrose Four Equations (`IsMoorePenrose M Mdag`)** in any `StarRing B`. -/
structure IsMoorePenrose {B : Type*} [Ring B] [Star B] (M Mdag : B) : Prop where
  penrose1 : M * Mdag * M = M
  penrose2 : Mdag * M * Mdag = Mdag
  penrose3 : star (M * Mdag) = M * Mdag
  penrose4 : star (Mdag * M) = Mdag * M

/-- Constructive inhabitant witness for `IsMoorePenrose` (`0` in any `StarRing B`). -/
theorem isMoorePenrose_zero_witness {B : Type*} [Ring B] [StarRing B] :
    IsMoorePenrose (0 : B) 0 :=
  { penrose1 := mul_zero (0 * 0)
    penrose2 := mul_zero (0 * 0)
    penrose3 := by
      calc
        star ((0 : B) * 0) = star (0 : B) := by rw [zero_mul]
        _ = 0 := star_zero B
        _ = (0 : B) * 0 := by rw [zero_mul]
    penrose4 := by
      calc
        star ((0 : B) * 0) = star (0 : B) := by rw [zero_mul]
        _ = 0 := star_zero B
        _ = (0 : B) * 0 := by rw [zero_mul] }

section PeirceOperatorSpine

variable {B : Type*} [Ring B]

/-- The Malik–Thome DMP inverse `T_DMP = M^D M M† = B_d M M†` and dual MPD inverse
`T_MPD = M† M M^D = M† M B_d`. -/
def dmpOp (B_d M Mdag : B) : B := B_d * M * Mdag
def mpdOp (B_d M Mdag : B) : B := Mdag * M * B_d

/-- The Row-4 Shadow Reflexive Inverse `S_{--} = M† - T_DMP - T_MPD + B_d = (1 - P) M† (1 - P)`. -/
def row4ShadowOp (B_d M Mdag : B) : B := Mdag - dmpOp B_d M Mdag - mpdOp B_d M Mdag + B_d

/-- Bipartite Token–Context Two-Point Correlation `C(M†) = P M† (1 - P) M† P + (1 - P) M† P M† (1 - P)`. -/
def twoPointCorrelation (P X : B) : B :=
  secPM P X * secMP P X + secMP P X * secPM P X

def hadamardPP (S X : B) : B := X + S * X + X * S + S * X * S
def hadamardPM (S X : B) : B := X + S * X - X * S - S * X * S
def hadamardMP (S X : B) : B := X - S * X + X * S - S * X * S
def hadamardMM (S X : B) : B := X - S * X - X * S + S * X * S

def grade0 (E₁ E₂ E₃ X : B) : B := E₁ * X * E₁ + E₂ * X * E₂ + E₃ * X * E₃
def gradePlus1 (E₁ E₂ E₃ X : B) : B := E₁ * X * E₂ + E₂ * X * E₃
def gradeMinus1 (E₁ E₂ E₃ X : B) : B := E₂ * X * E₁ + E₃ * X * E₂
def gradePlus2 (E₁ E₃ X : B) : B := E₁ * X * E₃
def gradeMinus2 (E₁ E₃ X : B) : B := E₃ * X * E₁

lemma P_assoc {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

macro "peirce_abel_znd3" hP:ident : tactic =>
  `(tactic| (
    simp only [dmpOp, mpdOp, row4ShadowOp, twoPointCorrelation,
               hadamardPP, hadamardPM, hadamardMP, hadamardMM,
               grade0, gradePlus1, gradeMinus1, gradePlus2, gradeMinus2,
               weakNum, weakDen, weakRem, newtonStep, pellScale, idempDefect,
               coreOp, offOp, secPP, secPM, secMP, secMM,
               qgtPlus, qgtMinus, genPhi, genJ, genV, genSig,
               invS, comm, anticomm, assocDefect, conePlus, coneMinus,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               zsmul_add, zsmul_sub, sub_self, mul_zero, zero_mul, add_zero, zero_add,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

set_option linter.unusedSimpArgs false in
/-- **Theorem MT_1 (`archetype_A81_operator_pell_equation_and_wavelet_scaling`):**
For ANY element `P : B` in ANY non-commutative ring `B` (without assuming `P * P = P`!):
1. `invS P * invS P = pellScale P = 1 + 4 (P² - P)` and `invS P * invS P - 4 (P² - P) = 1`.
2. `comm P (invS P) = 0`.
3. Wavelet Two-Scale Dilation: `(1 + invS P)² + (1 - invS P)² = 4 (1 + 2 (P² - P))`,
   `(1 + invS P)² - (1 - invS P)² = 8 P - 4`, and
   `(1 + invS P) * (1 - invS P) = -4 (P² - P)`.
4. Cubic Newton–Raphson Idempotent Defect Factorization:
   `idempDefect (3 P² - 2 P³) = (P² - P)² * (4 (P² - P) - 3)`. -/
theorem archetype_A81_operator_pell_equation_and_wavelet_scaling (P : B) :
    invS P * invS P = pellScale P ∧
    invS P * invS P - fourOp (idempDefect P) = (1 : B) ∧
    comm P (invS P) = (0 : B) ∧
    (1 + invS P) * (1 + invS P) + (1 - invS P) * (1 - invS P) =
      fourOp ((1 : B) + twoOp (idempDefect P)) ∧
    (1 + invS P) * (1 + invS P) - (1 - invS P) * (1 - invS P) =
      eightOp P - fourOp (1 : B) ∧
    (1 + invS P) * (1 - invS P) = -fourOp (idempDefect P) ∧
    (1 - invS P) * (1 + invS P) = -fourOp (idempDefect P) ∧
    idempDefect (newtonStep P) =
      (idempDefect P * idempDefect P) * (fourOp (idempDefect P) - threeOp (1 : B)) ∧
    invS (newtonStep P) * invS (newtonStep P) - (1 : B) =
      fourOp ((idempDefect P * idempDefect P) * (fourOp (idempDefect P) - threeOp (1 : B))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [twoOp, threeOp, fourOp, eightOp,
               newtonStep, pellScale, idempDefect, invS, comm,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               sub_self, mul_zero, zero_mul, add_zero, zero_add,
               mul_assoc]
    try abel

/-- **Theorem MT_2 (`archetype_A83_metriplectic_weak_measurement_duality`):**
For ANY binary idempotent `P * P = P` and ANY `A, C, X : B`:
1. Metriplectic Weak-Measurement Decomposition:
   `(1 - P) X P + [N_-, P X P] + [(1 - P) X (1 - P), N_+] = (1 - P) X P + N_- X P - P A (1 - P) X (1 - P)`.
2. Exact Vanishing of Cross-Helicity Weak Values:
   `(1 - P) N_+ N_+ = 0` and `P N_- N_- = 0`.
3. Exact Weak-Value Eigenvalue Laws on `V`, `Σ`, `Q_+`, `Q_-`.
4. Non-Commutative Aharonov–Albert–Vaidman Weak-Value Amplification Theorem:
   `weakNum P A X * coneMinus P C = weakDen P A C * secMP P X + weakRem P A C X`. -/
theorem archetype_A83_metriplectic_weak_measurement_duality
    {P : B} (hP : P * P = P) (A C X : B) :
    weakNum P A X = secMP P X * conePlus P A ∧
    weakNum P A (conePlus P A) = 0 ∧
    P * (coneMinus P C) * (coneMinus P C) = 0 ∧
    weakNum P A (genV P A C) = weakDen P A C * conePlus P A ∧
    weakNum P A (genSig P A C) = weakDen P A C * conePlus P A ∧
    weakNum P A (qgtPlus P A C) = weakDen P A C * conePlus P A ∧
    weakNum P A (qgtMinus P A C) = 0 ∧
    weakNum P A X * coneMinus P C = weakDen P A C * secMP P X + weakRem P A C X ∧
    coneMinus P C * weakNum P A X = weakDen P A C * secPP P X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_znd3 hP

/-- **Theorem MT_3a (`archetype_A86_tetraktys_dirac_clifford_and_chiral_gamma5_duality`):**
Dual Chiral `γ⁵` Theorem (`S_P = 2P - 1` vs. `Σ = J * Φ`), Internal `γ⁵` multiplication table,
and External/Internal Weyl Chiral Projectors. -/
theorem archetype_A86_tetraktys_dirac_clifford_and_chiral_gamma5_duality
    {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    genSig P A C = invS P * genV P A C ∧
    invS P * genSig P A C = genV P A C ∧
    anticomm (invS P) (genPhi P A C) = 0 ∧
    anticomm (invS P) (genJ P A C) = 0 ∧
    anticomm (genSig P A C) (genPhi P A C) = 0 ∧
    anticomm (genSig P A C) (genJ P A C) = 0 ∧
    comm (invS P) (genV P A C) = 0 ∧
    comm (genSig P A C) (genV P A C) = 0 ∧
    genSig P A C * genPhi P A C = genV P A C * genJ P A C ∧
    genSig P A C * genJ P A C = genV P A C * genPhi P A C ∧
    genSig P A C * conePlus P A = genV P A C * conePlus P A ∧
    genSig P A C * coneMinus P C = -(genV P A C * coneMinus P C) ∧
    (1 + invS P) * genPhi P A C = (2 : ℤ) • conePlus P A ∧
    (1 - invS P) * genPhi P A C = (2 : ℤ) • coneMinus P C ∧
    (1 + invS P) * genV P A C = (2 : ℤ) • qgtPlus P A C ∧
    (1 - invS P) * genV P A C = (2 : ℤ) • qgtMinus P A C ∧
    (genV P A C - genSig P A C) * (genPhi P A C + genJ P A C) = 0 ∧
    (genV P A C + genSig P A C) * (genPhi P A C - genJ P A C) = 0 ∧
    (genV P A C + genSig P A C) * (genPhi P A C + genJ P A C) =
      (4 : ℤ) • (genV P A C * conePlus P A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_znd3 hP

/-- **Theorem MT_3b (`archetype_A87_tetraktys_clifford_casimir_and_internal_projector_duality`):**
Complete `Cl_{1,1}(V)` multiplication table, Casimir dispersion (`Φ² + J² = 0`, `V² = Σ²`),
orthogonal internal projector algebra (`(V ± Σ)² = 2V(V ± Σ)`, `(V + Σ)(V - Σ) = 0`),
cubic Dirac eigenvalue laws (`Φ³ = V Φ`, `J³ = -V J`), and commutator/anticommutator Hodge duality. -/
theorem archetype_A87_tetraktys_clifford_casimir_and_internal_projector_duality
    {P : B} (hP : P * P = P) (A C : B) :
    let SP  := invS P
    let Np  := conePlus P A
    let Nm  := coneMinus P C
    let Phi := genPhi P A C
    let J   := genJ P A C
    let V   := genV P A C
    let Sig := genSig P A C
    comm V Np = 0 ∧
    comm V Nm = 0 ∧
    comm V Phi = 0 ∧
    comm V J = 0 ∧
    comm V Sig = 0 ∧
    Phi * Phi = V ∧
    J * J = -V ∧
    anticomm Phi J = 0 ∧
    comm J Phi = (2 : ℤ) • Sig ∧
    Phi * Phi + J * J = 0 ∧
    Phi * Phi - J * J = (2 : ℤ) • V ∧
    Sig * Sig = V * V ∧
    V * V - Sig * Sig = 0 ∧
    Phi * Phi * Phi = V * Phi ∧
    J * J * J = -(V * J) ∧
    (V + Sig) * (V - Sig) = 0 ∧
    (V - Sig) * (V + Sig) = 0 ∧
    (V + Sig) * (V + Sig) = (2 : ℤ) • (V * (V + Sig)) ∧
    (V - Sig) * (V - Sig) = (2 : ℤ) • (V * (V - Sig)) ∧
    anticomm SP V = (2 : ℤ) • Sig ∧
    anticomm SP Sig = (2 : ℤ) • V ∧
    comm SP Phi = (2 : ℤ) • J ∧
    comm SP J = (2 : ℤ) • Phi ∧
    comm Sig Phi = (2 : ℤ) • (V * J) ∧
    comm Sig J = (2 : ℤ) • (V * Phi) ∧
    SP * V * SP = V ∧
    SP * Sig * SP = Sig ∧
    SP * Phi * SP = -Phi ∧
    SP * J * SP = -J := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_znd3 hP

/-- **Theorem MT_4a (`campbell_meyer_drazin_equations`, `malik_thome_dmp_characterization`,
`superoperator_drazin_is_the_tetraktys`):**
Over ANY non-commutative ring `B`, let `DrazinResolution M P C N B_d` hold:
1. Campbell–Meyer Drazin inverse equations for `(M, B_d)` (`M² B_d = M P = C`, `B_d M B_d = B_d`,
   `M B_d = B_d M = P`, `M³ B_d = M²`, `M - M² B_d = N` with `N² = 0`).
2. Malik–Thome DMP (`T_DMP = B_d M M† = P M† = B_d + N_+`) and MPD (`T_MPD = M† M B_d = M† P = B_d + N_-`)
   characterization: `T_DMP M T_DMP = T_DMP`, `M T_DMP M = M (P M†) M`, `T_DMP M = P M† M`,
   `M T_DMP = C M†`.
3. Superoperator Drazin inverse is the Tetraktys core projector (`ad_P³ = ad_P`,
   `ad_P²(coreOp P X) = 0`, `ad_P²(offOp P X) = offOp P X`). -/
theorem campbell_meyer_drazin_and_superoperator_tetraktys
    {M P C N B_d : B} (hD : DrazinResolution M P C N B_d) (Mdag X : B) :
    -- 1. Campbell–Meyer Drazin Equations:
    M * B_d = P ∧
    B_d * M = P ∧
    B_d * M * B_d = B_d ∧
    M * M * B_d = C ∧
    M * M * M * B_d = M * M ∧
    M - M * M * B_d = N ∧
    (M - M * M * B_d) * (M - M * M * B_d) = 0 ∧
    -- 2. Malik–Thome DMP & MPD Projector Reduction:
    dmpOp B_d M Mdag = P * Mdag ∧
    mpdOp B_d M Mdag = Mdag * P ∧
    P * dmpOp B_d M Mdag = dmpOp B_d M Mdag ∧
    mpdOp B_d M Mdag * P = mpdOp B_d M Mdag ∧
    -- 3. Superoperator Drazin Equations (`ad_P³ = ad_P`):
    comm P (comm P (comm P X)) = comm P X ∧
    comm P (comm P (coreOp P X)) = 0 ∧
    comm P (comm P (offOp P X))  = offOp P X := by
  rcases hD with ⟨hP, hM, hCL, hCR, hNL, hNR, hN2, hDL, hDR, hCIR, hCIL⟩
  have hNBd : N * B_d = 0 := by
    calc N * B_d = N * (P * B_d) := by rw [hDL]
      _ = (N * P) * B_d := by rw [← mul_assoc]
      _ = 0 := by rw [hNR, zero_mul]
  have hBdN : B_d * N = 0 := by
    calc B_d * N = (B_d * P) * N := by rw [hDR]
      _ = B_d * (P * N) := by rw [mul_assoc]
      _ = 0 := by rw [hNL, mul_zero]
  have hCN : C * N = 0 := by
    calc C * N = (C * P) * N := by rw [hCR]
      _ = C * (P * N) := by rw [mul_assoc]
      _ = 0 := by rw [hNL, mul_zero]
  have hNC : N * C = 0 := by
    calc N * C = N * (P * C) := by rw [hCL]
      _ = (N * P) * C := by rw [← mul_assoc]
      _ = 0 := by rw [hNR, zero_mul]
  have hMBd : M * B_d = P := by
    rw [hM, add_mul, hCIR, hNBd, add_zero]
  have hBdM : B_d * M = P := by
    rw [hM, mul_add, hCIL, hBdN, add_zero]
  have hBdMBd : B_d * M * B_d = B_d := by
    rw [hBdM, hDL]
  have hM2 : M * M = C * C := by
    rw [hM, add_mul, mul_add, mul_add, hCN, hNC, hN2, add_zero, add_zero, add_zero]
  have hM2Bd : M * M * B_d = C := by
    rw [mul_assoc, hMBd, hM, add_mul, hCR, hNR, add_zero]
  have hM3Bd : M * M * M * B_d = M * M := by
    calc M * M * M * B_d = M * (M * M * B_d) := by simp only [mul_assoc]
      _ = M * C := by rw [hM2Bd]
      _ = (C + N) * C := by rw [hM]
      _ = C * C := by rw [add_mul, hNC, add_zero]
      _ = M * M := hM2.symm
  have hMN : M - M * M * B_d = N := by
    rw [hM2Bd, hM, add_sub_cancel_left]
  refine ⟨hMBd, hBdM, hBdMBd, hM2Bd, hM3Bd, hMN, by rw [hMN, hN2],
          by simp only [dmpOp, hBdM],
          by simp only [mpdOp, mul_assoc, hMBd],
          by simp only [dmpOp, hBdM, ← mul_assoc, hP],
          by simp only [mpdOp, mul_assoc, hMBd, hP],
          by peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP⟩

/-- **Theorem MT_4b (`monad_sandwich_is_drazin_inverse_and_master_mp_decomposition`,
`nilpotent_transient_inverted_by_shadow_ground_row4`):**
Let `DrazinResolution M P C N B_d` hold and let `Mdag : B` satisfy the core–nilpotent
block compatibility `P * Mdag * P = B_d` (Monad Sandwich IS the Drazin inverse!) and
`N * Mdag * N = N` (Penrose 1st equation on the nilpotent block `(1 - P)`). Then:
1. `T_DMP = B_d + N_+` (`N_+ = P M† (1 - P)`) and `T_MPD = B_d + N_-` (`N_- = (1 - P) M† P`).
2. `T_DMP * C * T_MPD = B_d` and `P * T_DMP * P = P * T_MPD * P = P * M† * P = B_d`.
3. Master MP Decomposition: `M† = T_DMP + T_MPD - B_d + S_{--} = B_d + S_{--} + Φ`, where
   `S_{--} = row4ShadowOp B_d M Mdag = (1 - P) M† (1 - P)` and `Φ = genPhi P Mdag Mdag`.
4. Row-4 Shadow Reflexive Inversion of the Nilpotent Transient `N`:
   `N * S_{--} * N = N`, `C * S_{--} = 0`, `S_{--} * C = 0`, `B_d * S_{--} = 0`, `S_{--} * B_d = 0`. -/
theorem monad_sandwich_master_mp_and_row4_nilpotent_inversion
    {M P C N B_d Mdag : B} (hD : DrazinResolution M P C N B_d)
    (hMonad : P * Mdag * P = B_d)
    (hNilMP : N * Mdag * N = N) :
    let N_p  := conePlus P Mdag
    let N_m  := coneMinus P Mdag
    let Phi  := genPhi P Mdag Mdag
    let T_d  := dmpOp B_d M Mdag
    let T_m  := mpdOp B_d M Mdag
    let S_mm := row4ShadowOp B_d M Mdag
    -- 1. Explicit Peirce Expansions of `T_DMP`, `T_MPD`, and `S_{--}`:
    T_d = B_d + N_p ∧
    T_m = B_d + N_m ∧
    S_mm = secMM P Mdag ∧
    Mdag = B_d + S_mm + Phi ∧
    -- 2. Monad Sandwich Identities (`T_DMP * C * T_MPD = B_d`):
    P * T_d * P = B_d ∧
    P * T_m * P = B_d ∧
    T_d * C * T_m = B_d ∧
    -- 3. Row-4 Shadow Reflexive Inversion of the Nilpotent Transient `N`:
    N * S_mm * N = N ∧
    (N * S_mm) * (N * S_mm) = N * S_mm ∧
    (S_mm * N) * (S_mm * N) = S_mm * N ∧
    C * S_mm = 0 ∧
    S_mm * C = 0 ∧
    B_d * S_mm = 0 ∧
    S_mm * B_d = 0 := by
  have hCM := campbell_meyer_drazin_and_superoperator_tetraktys hD Mdag (0 : B)
  have hMBd : M * B_d = P := hCM.1
  have hBdM : B_d * M = P := hCM.2.1
  rcases hD with ⟨hP, hM, hCL, hCR, hNL, hNR, hN2, hDL, hDR, hCIR, hCIL⟩
  have hTd : dmpOp B_d M Mdag = B_d + conePlus P Mdag := by
    calc dmpOp B_d M Mdag = P * Mdag := by simp only [dmpOp, hBdM]
      _ = P * Mdag * P + conePlus P Mdag := by peirce_abel_znd3 hP
      _ = B_d + conePlus P Mdag := by rw [hMonad]
  have hTm : mpdOp B_d M Mdag = B_d + coneMinus P Mdag := by
    calc mpdOp B_d M Mdag = Mdag * P := by simp only [mpdOp, mul_assoc, hMBd]
      _ = P * Mdag * P + coneMinus P Mdag := by peirce_abel_znd3 hP
      _ = B_d + coneMinus P Mdag := by rw [hMonad]
  have hSmm : row4ShadowOp B_d M Mdag = secMM P Mdag := by
    calc row4ShadowOp B_d M Mdag
        = Mdag - (P * Mdag) - (Mdag * P) + P * Mdag * P := by
          simp only [row4ShadowOp, dmpOp, mpdOp, mul_assoc, hBdM, hMBd, hMonad]
      _ = secMM P Mdag := by peirce_abel_znd3 hP
  have hMdagDecomp : Mdag = B_d + row4ShadowOp B_d M Mdag + genPhi P Mdag Mdag := by
    rw [hSmm, ← hMonad]
    peirce_abel_znd3 hP
  have hPTdP : P * dmpOp B_d M Mdag * P = B_d := by
    calc P * dmpOp B_d M Mdag * P = P * (P * Mdag) * P := by simp only [dmpOp, hBdM]
      _ = P * Mdag * P := by peirce_abel_znd3 hP
      _ = B_d := hMonad
  have hPTmP : P * mpdOp B_d M Mdag * P = B_d := by
    calc P * mpdOp B_d M Mdag * P = P * (Mdag * P) * P := by simp only [mpdOp, mul_assoc, hMBd]
      _ = P * Mdag * P := by peirce_abel_znd3 hP
      _ = B_d := hMonad
  have hNSmmN : N * row4ShadowOp B_d M Mdag * N = N := by
    rw [hSmm]
    have hN1P : N * (1 - P) = N := by
      rw [mul_sub, mul_one, hNR, sub_zero]
    have h1PN : (1 - P) * N = N := by
      rw [sub_mul, one_mul, hNL, sub_zero]
    calc N * secMM P Mdag * N
        = (N * (1 - P)) * Mdag * ((1 - P) * N) := by
          simp only [secMM, mul_assoc]
      _ = N * Mdag * N := by rw [hN1P, h1PN]
      _ = N := hNilMP
  have hNSmmIdem : (N * row4ShadowOp B_d M Mdag) * (N * row4ShadowOp B_d M Mdag) = N * row4ShadowOp B_d M Mdag := by
    calc (N * row4ShadowOp B_d M Mdag) * (N * row4ShadowOp B_d M Mdag)
        = (N * row4ShadowOp B_d M Mdag * N) * row4ShadowOp B_d M Mdag := by simp only [mul_assoc]
      _ = N * row4ShadowOp B_d M Mdag := by rw [hNSmmN]
  have hSmmNIdem : (row4ShadowOp B_d M Mdag * N) * (row4ShadowOp B_d M Mdag * N) = row4ShadowOp B_d M Mdag * N := by
    calc (row4ShadowOp B_d M Mdag * N) * (row4ShadowOp B_d M Mdag * N)
        = row4ShadowOp B_d M Mdag * (N * row4ShadowOp B_d M Mdag * N) := by simp only [mul_assoc]
      _ = row4ShadowOp B_d M Mdag * N := by rw [hNSmmN]
  have hCSmm : C * row4ShadowOp B_d M Mdag = 0 := by
    rw [hSmm, ← hCR]
    peirce_abel_znd3 hP
  have hSmmC : row4ShadowOp B_d M Mdag * C = 0 := by
    rw [hSmm, ← hCL]
    peirce_abel_znd3 hP
  have hBdSmm : B_d * row4ShadowOp B_d M Mdag = 0 := by
    rw [hSmm, ← hDR]
    peirce_abel_znd3 hP
  have hSmmBd : row4ShadowOp B_d M Mdag * B_d = 0 := by
    rw [hSmm, ← hDL]
    peirce_abel_znd3 hP
  have hTdCTm : dmpOp B_d M Mdag * C * mpdOp B_d M Mdag = B_d := by
    have hTdP : dmpOp B_d M Mdag = P * Mdag := by simp only [dmpOp, hBdM]
    have hTmP : mpdOp B_d M Mdag = Mdag * P := by simp only [mpdOp, mul_assoc, hMBd]
    calc dmpOp B_d M Mdag * C * mpdOp B_d M Mdag
        = ((P * Mdag * P) * C) * (P * Mdag * P) := by
          rw [hTdP, hTmP, ← hCL, ← hCR]
          peirce_abel_znd3 hP
      _ = (B_d * C) * B_d := by rw [hMonad]
      _ = B_d := by rw [hCIL, hDL]
  exact ⟨hTd, hTm, hSmm, hMdagDecomp, hPTdP, hPTmP, hTdCTm,
         hNSmmN, hNSmmIdem, hSmmNIdem, hCSmm, hSmmC, hBdSmm, hSmmBd⟩

/-- **Theorem MT_4c (`malik_thome_walsh_hadamard_gamma5_dictionary`,
`malik_thome_commutator_direct_qgt_and_metric_extraction`,
`malik_thome_pure_commutator_tetraktys_sixfold_generator`,
`bipartite_token_context_two_point_correlation_is_fubini_study_metric`,
`transformer_self_attention_is_malik_thome_duality`):**
1. Walsh–Hadamard `γ⁵ = 2P - 1` Dictionary (`hadamardPP`, `hadamardPM`, `hadamardMP`, `hadamardMM`).
2. Sixfold Pure Commutator Tetraktys Generator from `(P, T_DMP, T_MPD)` (`Δ_+ = [P, T_DMP] = N_+`,
   `Δ_- = [T_MPD, P] = N_-`, `Δ_+ + Δ_- = Φ`, `Δ_+ - Δ_- = J`, `{Δ_+, Δ_-} = V`, `[Δ_+, Δ_-] = Σ`).
3. Firth's Contextual Hypothesis (`twoPointCorrelation P Mdag = genV P Mdag Mdag`).
4. Transformer Residual + Self-Attention Decomposition:
   `T_DMP * T_MPD = B_d * B_d + qgtPlus P Mdag Mdag`, and the unnormalized attention score
   satisfies `qgtPlus P Mdag Mdag * N_+ = N_+ * qgtMinus P Mdag Mdag = genV P Mdag Mdag * N_+`. -/
theorem malik_thome_commutator_bipartite_attention_and_transformer_duality
    {M P C N B_d Mdag : B} (hD : DrazinResolution M P C N B_d)
    (hMonad : P * Mdag * P = B_d) (X : B) :
    let S   := invS P
    let N_p := conePlus P Mdag
    let N_m := coneMinus P Mdag
    let Phi := genPhi P Mdag Mdag
    let J   := genJ P Mdag Mdag
    let V   := genV P Mdag Mdag
    let Sig := genSig P Mdag Mdag
    let Q_p := qgtPlus P Mdag Mdag
    let Q_m := qgtMinus P Mdag Mdag
    let T_d := dmpOp B_d M Mdag
    let T_m := mpdOp B_d M Mdag
    -- 1. Walsh–Hadamard `γ⁵` Dictionary:
    hadamardPP S X = (4 : ℤ) • secPP P X ∧
    hadamardPM S X = (4 : ℤ) • secPM P X ∧
    hadamardMP S X = (4 : ℤ) • secMP P X ∧
    hadamardMM S X = (4 : ℤ) • secMM P X ∧
    -- 2. Sixfold Pure Commutator Tetraktys Generator from `(P, T_DMP, T_MPD)`:
    comm P T_d = N_p ∧
    comm T_m P = N_m ∧
    comm P T_d + comm T_m P = Phi ∧
    comm P T_d - comm T_m P = J ∧
    anticomm (comm P T_d) (comm T_m P) = V ∧
    comm (comm P T_d) (comm T_m P) = Sig ∧
    -- 3. Firth's Contextual Hypothesis (`C(M†) = V`):
    twoPointCorrelation P Mdag = V ∧
    -- 4. Transformer Residual (`B_d²`) + Self-Attention (`Q_+`) Decomposition:
    T_d * T_m = B_d * B_d + Q_p ∧
    Q_p * N_p = N_p * Q_m ∧
    Q_p * N_p = V * N_p := by
  have hCM := campbell_meyer_drazin_and_superoperator_tetraktys hD Mdag X
  have hMBd : M * B_d = P := hCM.1
  have hBdM : B_d * M = P := hCM.2.1
  rcases hD with ⟨hP, hM, hCL, hCR, hNL, hNR, hN2, hDL, hDR, hCIR, hCIL⟩
  have hTdP : dmpOp B_d M Mdag = P * Mdag := by simp only [dmpOp, hBdM]
  have hTmP : mpdOp B_d M Mdag = Mdag * P := by simp only [mpdOp, mul_assoc, hMBd]
  have hTdTm : dmpOp B_d M Mdag * mpdOp B_d M Mdag = B_d * B_d + qgtPlus P Mdag Mdag := by
    calc dmpOp B_d M Mdag * mpdOp B_d M Mdag
        = (P * Mdag) * (Mdag * P) := by rw [hTdP, hTmP]
      _ = (P * Mdag * P) * (P * Mdag * P) + qgtPlus P Mdag Mdag := by peirce_abel_znd3 hP
      _ = B_d * B_d + qgtPlus P Mdag Mdag := by rw [hMonad]
  refine ⟨by peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP,
          by rw [hTdP]; peirce_abel_znd3 hP,
          by rw [hTmP]; peirce_abel_znd3 hP,
          by rw [hTdP, hTmP]; peirce_abel_znd3 hP,
          by rw [hTdP, hTmP]; peirce_abel_znd3 hP,
          by rw [hTdP, hTmP]; peirce_abel_znd3 hP,
          by rw [hTdP, hTmP]; peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP,
          hTdTm,
          by peirce_abel_znd3 hP,
          by peirce_abel_znd3 hP⟩

set_option linter.unusedSimpArgs false in
/-- **Theorem MT_5 (`jordan_fundamental_identity_and_peirce_idempotent`,
`moufang_identities_and_malcev_identity_in_associative_ring`,
`three_idempotent_nine_sector_kantor_koecher_tits_five_grading`):**
1. Fundamental McCrimmon Quadratic Jordan Identity `U_{U_X(Y)} = U_X ∘ U_Y ∘ U_X`, where `U_X(Y) = X Y X`,
   and Jordan–Moufang identities `X (Y (X Z)) = ((X Y) X) Z`, `((Z X) Y) X = Z (X (Y X))`,
   `(X Y) (Z X) = (X (Y Z)) X`.
2. Nine-Sector Kantor–Koecher–Tits 5-Grading (`g_{-2} ⊕ g_{-1} ⊕ g_0 ⊕ g_{+1} ⊕ g_{+2}`) for any
   three orthogonal idempotents `E₁, E₂, E₃ : B` summing to `1`:
   - `X = gradeMinus2 + gradeMinus1 + grade0 + gradePlus1 + gradePlus2`,
   - `[g_0, g_k] ⊆ g_k`, `[g_{+1}, g_{+1}] ⊆ g_{+2}`, `[g_{-1}, g_{-1}] ⊆ g_{-2}`,
   - `[g_{+2}, g_{+1}] = 0`, `[g_{+2}, g_{+2}] = 0`, `[g_{-2}, g_{-1}] = 0`, `[g_{-2}, g_{-2}] = 0`. -/
theorem jordan_moufang_and_three_idempotent_five_grading
    {E₁ E₂ E₃ : B}
    (h11 : E₁ * E₁ = E₁) (h22 : E₂ * E₂ = E₂) (h33 : E₃ * E₃ = E₃)
    (h12 : E₁ * E₂ = 0) (h21 : E₂ * E₁ = 0)
    (h13 : E₁ * E₃ = 0) (h31 : E₃ * E₁ = 0)
    (h23 : E₂ * E₃ = 0) (h32 : E₃ * E₂ = 0)
    (hSum : E₁ + E₂ + E₃ = 1) (X Y Z : B) :
    -- 1. McCrimmon Quadratic Jordan & Moufang Identities:
    (X * Y * X) * Z * (X * Y * X) = X * (Y * (X * Z * X) * Y) * X ∧
    X * (Y * (X * Z)) = ((X * Y) * X) * Z ∧
    ((Z * X) * Y) * X = Z * (X * (Y * X)) ∧
    (X * Y) * (Z * X) = (X * (Y * Z)) * X ∧
    -- 2. Kantor–Koecher–Tits 5-Grading Completeness & Lie Bracket Grading Laws:
    gradeMinus2 E₁ E₃ X + gradeMinus1 E₁ E₂ E₃ X + grade0 E₁ E₂ E₃ X +
      gradePlus1 E₁ E₂ E₃ X + gradePlus2 E₁ E₃ X = X ∧
    gradePlus1 E₁ E₂ E₃ X * gradePlus1 E₁ E₂ E₃ Y =
      E₁ * X * E₂ * Y * E₃ ∧
    gradeMinus1 E₁ E₂ E₃ X * gradeMinus1 E₁ E₂ E₃ Y =
      E₃ * X * E₂ * Y * E₁ ∧
    comm (gradePlus2 E₁ E₃ X) (gradePlus1 E₁ E₂ E₃ Y) = 0 ∧
    comm (gradePlus2 E₁ E₃ X) (gradePlus2 E₁ E₃ Y) = 0 ∧
    comm (gradeMinus2 E₁ E₃ X) (gradeMinus1 E₁ E₂ E₃ Y) = 0 ∧
    comm (gradeMinus2 E₁ E₃ X) (gradeMinus2 E₁ E₃ Y) = 0 := by
  have h11' : ∀ W : B, E₁ * (E₁ * W) = E₁ * W := fun W => by rw [← mul_assoc, h11]
  have h22' : ∀ W : B, E₂ * (E₂ * W) = E₂ * W := fun W => by rw [← mul_assoc, h22]
  have h33' : ∀ W : B, E₃ * (E₃ * W) = E₃ * W := fun W => by rw [← mul_assoc, h33]
  have h12' : ∀ W : B, E₁ * (E₂ * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W : B, E₂ * (E₁ * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have h13' : ∀ W : B, E₁ * (E₃ * W) = 0 := fun W => by rw [← mul_assoc, h13, zero_mul]
  have h31' : ∀ W : B, E₃ * (E₁ * W) = 0 := fun W => by rw [← mul_assoc, h31, zero_mul]
  have h23' : ∀ W : B, E₂ * (E₃ * W) = 0 := fun W => by rw [← mul_assoc, h23, zero_mul]
  have h32' : ∀ W : B, E₃ * (E₂ * W) = 0 := fun W => by rw [← mul_assoc, h32, zero_mul]
  have hCompl : gradeMinus2 E₁ E₃ X + gradeMinus1 E₁ E₂ E₃ X + grade0 E₁ E₂ E₃ X +
      gradePlus1 E₁ E₂ E₃ X + gradePlus2 E₁ E₃ X = X := by
    calc gradeMinus2 E₁ E₃ X + gradeMinus1 E₁ E₂ E₃ X + grade0 E₁ E₂ E₃ X +
          gradePlus1 E₁ E₂ E₃ X + gradePlus2 E₁ E₃ X
        = (E₁ + E₂ + E₃) * X * (E₁ + E₂ + E₃) := by
          simp only [grade0, gradePlus1, gradeMinus1, gradePlus2, gradeMinus2,
                     add_mul, mul_add, mul_assoc]
          abel
      _ = 1 * X * 1 := by rw [hSum]
      _ = X := by rw [one_mul, mul_one]
  refine ⟨by simp only [mul_assoc],
          by simp only [mul_assoc],
          by simp only [mul_assoc],
          by simp only [mul_assoc],
          hCompl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [grade0, gradePlus1, gradeMinus1, gradePlus2, gradeMinus2, comm,
               add_mul, mul_add, sub_mul, mul_sub, mul_assoc,
               h11, h22, h33, h12, h21, h13, h31, h23, h32,
               h11', h22', h33', h12', h21', h13', h31', h23', h32',
               mul_zero, zero_mul, add_zero, zero_add, sub_self]

/-- **Theorem MT_6 (`peirce_star_algebra_geometry_and_grassmannian_variation_norm`):**
Over ANY non-commutative `StarRing B`, let `P * P = P` with `star P = P` (Hermitian projector)
and `star X = X` (Hermitian observable):
1. `(N_+)⋆ = (P X (1 - P))⋆ = (1 - P) X P = N_-` and `(N_-)⋆ = N_+`.
2. `Φ⋆ = Φ` (Hermitian field), `J⋆ = -J` (anti-Hermitian current), `V⋆ = V` (positive-semidefinite
   Gramian Fubini–Study metric `N_+ N_+⋆ + N_+⋆ N_+`), and `Σ⋆ = Σ` (Hermitian Berry curvature).
3. Grassmannian Tangent Variation Norm (`δP = J = [P, Φ]`):
   `(δP)⋆ * (δP) = J⋆ * J = -J² = V = N_+ N_+⋆ + N_+⋆ N_+`. -/
theorem peirce_star_algebra_geometry_and_grassmannian_variation_norm
    [StarRing B] {P X : B} (hP : P * P = P) (hPs : star P = P) (hXs : star X = X) :
    let N_p := conePlus P X
    let N_m := coneMinus P X
    let Phi := genPhi P X X
    let J   := genJ P X X
    let V   := genV P X X
    let Sig := genSig P X X
    star N_p = N_m ∧
    star N_m = N_p ∧
    star Phi = Phi ∧
    star J   = -J ∧
    star V   = V ∧
    star Sig = Sig ∧
    V = N_p * star N_p + star N_p * N_p ∧
    Sig = N_p * star N_p - star N_p * N_p ∧
    comm P Phi = J ∧
    star J * J = V := by
  have h1Ps : star (1 - P) = 1 - P := by
    rw [star_sub, star_one, hPs]
  have hNp : star (conePlus P X) = coneMinus P X := by
    simp only [conePlus, coneMinus, star_mul, h1Ps, hPs, hXs, mul_assoc]
  have hNm : star (coneMinus P X) = conePlus P X := by
    simp only [conePlus, coneMinus, star_mul, h1Ps, hPs, hXs, mul_assoc]
  have hPhi : star (genPhi P X X) = genPhi P X X := by
    simp only [genPhi, star_add, hNp, hNm]
    abel
  have hJ : star (genJ P X X) = -genJ P X X := by
    simp only [genJ, star_sub, hNp, hNm]
    abel
  have hV : star (genV P X X) = genV P X X := by
    simp only [genV, anticomm, star_add, star_mul, hNp, hNm]
    try abel
  have hSig : star (genSig P X X) = genSig P X X := by
    simp only [genSig, comm, star_sub, star_mul, hNp, hNm]
    try abel
  have hVGram : genV P X X = conePlus P X * star (conePlus P X) + star (conePlus P X) * conePlus P X := by
    simp only [genV, anticomm, hNp]
  have hSigGram : genSig P X X = conePlus P X * star (conePlus P X) - star (conePlus P X) * conePlus P X := by
    simp only [genSig, comm, hNp]
  have hComm : comm P (genPhi P X X) = genJ P X X := by
    peirce_abel_znd3 hP
  have hJJ : star (genJ P X X) * genJ P X X = genV P X X := by
    rw [hJ]
    peirce_abel_znd3 hP
  exact ⟨hNp, hNm, hPhi, hJ, hV, hSig, hVGram, hSigGram, hComm, hJJ⟩

/-- The scaled `sl₂` Quadratic Casimir Operator `C₂(N, M, H) = H² + 2(N M + M N) = H² + 2V`
over any non-commutative ring `B` (avoiding division by `2`). -/
def casimir2 (N M H : B) : B := H * H + twoOp (N * M + M * N)

set_option linter.unusedSimpArgs false in
/-- **Theorem MT_7 (`nilpotent_first_sl2_casimir_invariants_and_projector_precipitation`):**
Over ANY non-commutative ring `B`:
1. **Nilpotent-First Precipitation of Orthogonal Projector Sheets (`𝔭₀ → 𝔭₁ → 𝔭₂ → 𝔭₃`)**:
   Given a von Neumann regular nilpotent pair `(N, M)` satisfying `N * N = 0`, `M * M = 0`,
   `N * M * N = N`, and `M * N * M = M`, define the emergent sheets `P := N * M`, `Q := M * N`,
   the grading friction `H := N * M - M * N = P - Q`, the metric `V := N * M + M * N = P + Q`,
   the integrative bridge `Φ := N + M`, and the skew current `J := N - M`. Then:
   - `P * P = P`, `Q * Q = Q`, `P * Q = 0`, `Q * P = 0` (mutually orthogonal idempotent sheets),
   - `Φ * Φ = V`, `J * J = -V`, `anticomm Φ J = 0` (split-Clifford algebra `Cl_{1,1}` over `V`),
   - `comm H N = twoOp N`, `comm H M = -twoOp M`, `comm N M = H` (exact `sl₂` triple!).
2. **`sl₂` Casimir Centrality & Parabolic Metric Law (`V = ½(C₂ - H²)`)**:
   For the `sl₂` triple `(N, M, H)` generated by `(N, M)`:
   - `H * H = V` and `casimir2 N M H = threeOp V`,
   - `comm (casimir2 N M H) H = 0`, `comm (casimir2 N M H) N = 0`, `comm (casimir2 N M H) M = 0`
     (the Quadratic Casimir `C₂` is an exact central invariant of the non-commutative flow!),
   - `casimir2 N M H - H * H = twoOp V` (the metric `2V` is the complementary difference
     between the central Casimir invariant `C₂` and `H²`). -/
theorem nilpotent_first_sl2_casimir_invariants_and_projector_precipitation
    {N M : B} (hN2 : N * N = 0) (hM2 : M * M = 0)
    (hNMN : N * M * N = N) (hMNM : M * N * M = M) :
    let P   := N * M
    let Q   := M * N
    let H   := N * M - M * N
    let V   := N * M + M * N
    let Phi := N + M
    let J   := N - M
    let C2  := casimir2 N M H
    -- 1. Emergent Projector Sheets (`P := N M`, `Q := M N`):
    P * P = P ∧
    Q * Q = Q ∧
    P * Q = 0 ∧
    Q * P = 0 ∧
    -- 2. Split-Clifford Algebra `Cl_{1,1}` (`Φ² = +V`, `J² = -V`, `{Φ, J} = 0`):
    Phi * Phi = V ∧
    J * J = -V ∧
    anticomm Phi J = 0 ∧
    -- 3. Exact `sl₂` Lie Triple (`[H, N] = 2N`, `[H, M] = -2M`, `[N, M] = H`):
    comm H N = twoOp N ∧
    comm H M = -twoOp M ∧
    comm N M = H ∧
    -- 4. Quadratic Casimir Centrality & Parabolic Metric Law:
    H * H = V ∧
    C2 = threeOp V ∧
    C2 - H * H = twoOp V ∧
    comm C2 H = 0 ∧
    comm C2 N = 0 ∧
    comm C2 M = 0 := by
  have hNMN_r : N * (M * N) = N := by rw [← mul_assoc, hNMN]
  have hMNM_r : M * (N * M) = M := by rw [← mul_assoc, hMNM]
  have hNMN' : ∀ W : B, N * (M * (N * W)) = N * W := fun W => by
    calc N * (M * (N * W)) = (N * M * N) * W := by simp only [mul_assoc]
      _ = N * W := by rw [hNMN]
  have hMNM' : ∀ W : B, M * (N * (M * W)) = M * W := fun W => by
    calc M * (N * (M * W)) = (M * N * M) * W := by simp only [mul_assoc]
      _ = M * W := by rw [hMNM]
  have hN2' : ∀ W : B, N * (N * W) = 0 := fun W => by rw [← mul_assoc, hN2, zero_mul]
  have hM2' : ∀ W : B, M * (M * W) = 0 := fun W => by rw [← mul_assoc, hM2, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [twoOp, threeOp, casimir2, comm, anticomm,
               add_mul, mul_add, sub_mul, mul_sub,
               mul_assoc, hN2, hM2, hNMN, hMNM, hNMN_r, hMNM_r, hN2', hM2', hNMN', hMNM',
               mul_zero, zero_mul, add_zero, zero_add, sub_self]
    try abel

set_option linter.unusedSimpArgs false in
/-- **Theorem MT_8 (`universal_sl2_casimir_centrality_any_index`):**
Over ANY non-commutative ring `B` and for ANY nilpotency order `n ≥ 2` (without assuming `N² = 0`!),
let `(N, M, H)` be any `sl₂` triple satisfying:
- `H * N - N * H = twoOp N`,
- `H * M - M * H = -twoOp M`,
- `N * M - M * N = H`.
Then:
1. Both projector sheets `P_N = N * M` and `Q_N = M * N` commute with the internal clock `H`:
   `comm H (N * M) = 0`, `comm H (M * N) = 0`, and `comm H (anticomm N M) = 0`.
2. The scaled Quadratic Casimir `C₂ = casimir2 N M H = H² + 2(N M + M N)` is a **strict central
   invariant** of the `sl₂` representation:
   `comm (casimir2 N M H) H = 0`, `comm (casimir2 N M H) N = 0`, `comm (casimir2 N M H) M = 0`.
3. **Parabolic Metric Law**: Twice the metric operator `{N, M} = N * M + M * N` is the
   complementary difference between the central Casimir invariant `C₂` and `H²`:
   `twoOp (anticomm N M) = casimir2 N M H - H * H`. -/
theorem universal_sl2_casimir_centrality_any_index
    {N M H : B}
    (hHN : comm H N = twoOp N)
    (hHM : comm H M = -twoOp M)
    (hNM : comm N M = H) :
    let V  := anticomm N M
    let C2 := casimir2 N M H
    comm H (N * M) = 0 ∧
    comm H (M * N) = 0 ∧
    comm H V = 0 ∧
    comm C2 H = 0 ∧
    comm C2 N = 0 ∧
    comm C2 M = 0 ∧
    twoOp V = C2 - H * H := by
  have hHN_eq : H * N = N * H + twoOp N := by
    calc H * N = comm H N + N * H := by simp only [comm]; abel
      _ = N * H + twoOp N := by rw [hHN]; abel
  have hHM_eq : H * M = M * H - twoOp M := by
    calc H * M = comm H M + M * H := by simp only [comm]; abel
      _ = M * H - twoOp M := by rw [hHM]; abel
  have hNM_eq : N * M = M * N + H := by
    calc N * M = comm N M + M * N := by simp only [comm]; abel
      _ = M * N + H := by rw [hNM]; abel
  have hMN_eq : M * N = N * M - H := by
    calc M * N = (M * N + H) - H := by abel
      _ = N * M - H := by rw [← hNM_eq]
  have hH_NM : comm H (N * M) = 0 := by
    calc comm H (N * M)
        = (H * N) * M - N * (H * M) + (N * (H * M) - N * (M * H)) := by
          simp only [comm, mul_assoc]; abel
      _ = (N * H + twoOp N) * M - N * (M * H) := by
          rw [hHN_eq]; abel
      _ = N * (H * M) + twoOp N * M - N * (M * H) := by
          simp only [add_mul, mul_assoc]
      _ = N * (M * H - twoOp M) + twoOp N * M - N * (M * H) := by
          rw [hHM_eq]
      _ = 0 := by
          simp only [twoOp, add_mul, mul_add, mul_sub, mul_assoc]; abel
  have hH_MN : comm H (M * N) = 0 := by
    calc comm H (M * N)
        = (H * M) * N - M * (N * H) := by
          simp only [comm, mul_assoc]
      _ = (M * H - twoOp M) * N - M * (N * H) := by
          rw [hHM_eq]
      _ = M * (H * N) - twoOp M * N - M * (N * H) := by
          simp only [sub_mul, mul_assoc]
      _ = M * (N * H + twoOp N) - twoOp M * N - M * (N * H) := by
          rw [hHN_eq]
      _ = 0 := by
          simp only [twoOp, add_mul, mul_add, mul_assoc]; abel
  have hH_V : comm H (anticomm N M) = 0 := by
    calc comm H (anticomm N M)
        = comm H (N * M) + comm H (M * N) := by
          simp only [comm, anticomm, mul_add, add_mul]; abel
      _ = 0 := by rw [hH_NM, hH_MN, add_zero]
  have hC2_H : comm (casimir2 N M H) H = 0 := by
    calc comm (casimir2 N M H) H
        = -twoOp (comm H (anticomm N M)) := by
          simp only [twoOp, casimir2, comm, anticomm, add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
          abel
      _ = 0 := by rw [hH_V]; simp only [twoOp, add_zero, neg_zero]
  have hH2_N : H * H * N - N * (H * H) = fourOp (N * H) + fourOp N := by
    calc H * H * N - N * (H * H)
        = H * (H * N) - N * (H * H) := by simp only [mul_assoc]
      _ = H * (N * H + twoOp N) - N * (H * H) := by rw [hHN_eq]
      _ = (H * N) * H + twoOp (H * N) - N * (H * H) := by
          simp only [twoOp, mul_add, mul_assoc]
      _ = (N * H + twoOp N) * H + twoOp (N * H + twoOp N) - N * (H * H) := by
          rw [hHN_eq]
      _ = fourOp (N * H) + fourOp N := by
          simp only [twoOp, fourOp, add_mul, mul_add, mul_assoc]
          abel
  have hV_N : (N * M + M * N) * N - N * (N * M + M * N) = -twoOp (N * H) - twoOp N := by
    have hMN_N : (M * N) * N = N * (M * N) - H * N := by
      calc (M * N) * N = (N * M - H) * N := by rw [hMN_eq]
        _ = N * (M * N) - H * N := by simp only [sub_mul, mul_assoc]
    have hN_NM : N * (N * M) = N * (M * N) + N * H := by
      calc N * (N * M) = N * (M * N + H) := by rw [hNM_eq]
        _ = N * (M * N) + N * H := by simp only [mul_add]
    calc (N * M + M * N) * N - N * (N * M + M * N)
        = N * (M * N) + (M * N) * N - (N * (N * M) + N * (M * N)) := by
          simp only [add_mul, mul_add, mul_assoc]
      _ = N * (M * N) + (N * (M * N) - H * N) - ((N * (M * N) + N * H) + N * (M * N)) := by
          rw [hMN_N, hN_NM]
      _ = -(H * N) - N * H := by abel
      _ = -(N * H + twoOp N) - N * H := by rw [hHN_eq]
      _ = -twoOp (N * H) - twoOp N := by simp only [twoOp]; abel
  have hC2_N : comm (casimir2 N M H) N = 0 := by
    calc comm (casimir2 N M H) N
        = (H * H * N - N * (H * H)) + twoOp ((N * M + M * N) * N - N * (N * M + M * N)) := by
          simp only [twoOp, casimir2, comm, add_mul, mul_add, mul_assoc]; abel
      _ = (fourOp (N * H) + fourOp N) + twoOp (-twoOp (N * H) - twoOp N) := by
          rw [hH2_N, hV_N]
      _ = 0 := by simp only [twoOp, fourOp]; abel
  have hH2_M : H * H * M - M * (H * H) = -fourOp (M * H) + fourOp M := by
    calc H * H * M - M * (H * H)
        = H * (H * M) - M * (H * H) := by simp only [mul_assoc]
      _ = H * (M * H - twoOp M) - M * (H * H) := by rw [hHM_eq]
      _ = (H * M) * H - twoOp (H * M) - M * (H * H) := by
          simp only [twoOp, mul_sub, mul_add, mul_assoc]
      _ = (M * H - twoOp M) * H - twoOp (M * H - twoOp M) - M * (H * H) := by
          rw [hHM_eq]
      _ = -fourOp (M * H) + fourOp M := by
          simp only [twoOp, fourOp, sub_mul, add_mul, mul_assoc]
          abel
  have hV_M : (N * M + M * N) * M - M * (N * M + M * N) = twoOp (M * H) - twoOp M := by
    have hNM_M : (N * M) * M = M * (N * M) + H * M := by
      calc (N * M) * M = (M * N + H) * M := by rw [hNM_eq]
        _ = M * (N * M) + H * M := by simp only [add_mul, mul_assoc]
    have hM_MN : M * (M * N) = M * (N * M) - M * H := by
      calc M * (M * N) = M * (N * M - H) := by rw [hMN_eq]
        _ = M * (N * M) - M * H := by simp only [mul_sub]
    calc (N * M + M * N) * M - M * (N * M + M * N)
        = (N * M) * M + M * (N * M) - (M * (N * M) + M * (M * N)) := by
          simp only [add_mul, mul_add, mul_assoc]
      _ = (M * (N * M) + H * M) + M * (N * M) - (M * (N * M) + (M * (N * M) - M * H)) := by
          rw [hNM_M, hM_MN]
      _ = H * M + M * H := by abel
      _ = (M * H - twoOp M) + M * H := by rw [hHM_eq]
      _ = twoOp (M * H) - twoOp M := by simp only [twoOp]; abel
  have hC2_M : comm (casimir2 N M H) M = 0 := by
    calc comm (casimir2 N M H) M
        = (H * H * M - M * (H * H)) + twoOp ((N * M + M * N) * M - M * (N * M + M * N)) := by
          simp only [twoOp, casimir2, comm, add_mul, mul_add, mul_assoc]; abel
      _ = (-fourOp (M * H) + fourOp M) + twoOp (twoOp (M * H) - twoOp M) := by
          rw [hH2_M, hV_M]
      _ = 0 := by simp only [twoOp, fourOp]; abel
  have hParab : twoOp (anticomm N M) = casimir2 N M H - H * H := by
    simp only [casimir2, anticomm]; abel
  exact ⟨hH_NM, hH_MN, hH_V, hC2_H, hC2_N, hC2_M, hParab⟩

end PeirceOperatorSpine

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
