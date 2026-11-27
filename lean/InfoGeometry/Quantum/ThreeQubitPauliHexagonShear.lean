/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.TwoQubitPauliGeometry
import InfoGeometry.Algebra.Zorn.G2HexagonIncidence
import InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
import InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
import InfoGeometry.Algebra.SplitE8RootSystem
import InfoGeometry.Algebra.H3ZornE7RootSystem
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.CubicJordanOs
import InfoGeometry.Algebra.CubicJordanOsExtensions
import InfoGeometry.Algebra.CubicJordanPeirce
import InfoGeometry.Algebra.Generations
import InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge
import InfoGeometry.Lie.SplitOctonionEllCircularCAR
import InfoGeometry.Physics.QCDCanonicalComplexZornBridge
import InfoGeometry.Canonical.FiniteParaKahler
import InfoGeometry.Canonical.PlabicDiracKrein
import InfoGeometry.Canonical.FinitePlabicKasteleyn
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

/-!
# Three-Qubit Pauli Hexagon, Symplectic Transvections, `E₈`/`E₇` Branching, `ℂ ⊗ 𝕆ₛ` CAR & Kasteleyn–Dirac

This module formalizes the kernel-checked algebraic and matrix-operator structures for
Features `D1`, `D2`, `D4`, `D6`, `G1`, `G2`, `G4`, `G5`, `H1`, `H2`, `H4`, `H6`, and `I3`
by directly importing and extending the repository's existing owners:

1. **D1 (`Label3`, `Operator3`, `pauli3`, `OctImIsotropicPoint`, `HexPoint`)**:
   Genuine `8 × 8` noncommutative matrix realization of 3-qubit Pauli words on
   `(ZMod 2 × ZMod 2) × ZMod 2` (specializing to `ℂ⁸` for `R = ℂ`), commutation characterization
   `Commute (pauli3 v) (pauli3 w) ↔ symplectic3 v w = 0`, constructive bijections
   `octImIsotropicEquivNonzeroLabel3` and `hexPointEquivNonzeroLabel3`, and proof that
   `ZornZeroRelated u v` implies `symplectic3 = 0` and commuting `pauli3` operators, plus
   vector-addition closedness of `zornZeroTriples`.
   *(Note: `G2ParabolicIncidenceCertificate.incidence` and `casPointEnum` use distinct `Fin 63`
   vertex numberings, so line-commutation preservation is proved on the native `OctImIsotropicPoint`
   / `zornZeroTriples` carrier rather than raw `parabolicIncidenceData.linePoints`.)*
2. **D2 & D4 (`Sp(6, 𝔽₂)` symplectic transvections)**:
   Transvections `transvectionVec a x := x + sympForm6 x a • a` and matrices
   `transvectionMat a := 1 + vecMulVec a (J6.mulVec a)`, proving `(T_a - 1)^2 = 0`, `T_a^2 = 1`,
   `T_a.det = 1`, symplectic invariance `T_aᵀ * J6 * T_a = J6`, `pauli3` commutation
   preservation, non-triviality for `a ≠ 0`, and line-fixation / line-commutation preservation.
3. **D6 & I3 (`E₈ ⊃ G₂ × F₄` and `E₇` rank-7 partition)**:
   Direct linkage to `NativeTitsE8Carrier`, `MagicSquareTitsBracket.SplitE8Lie`,
   `SplitE8RootSystem` (`248 = 14 + 52 + 182`, `182 = 7 * 26`, `240 = 12 + 48 + 180`, 5-sector
   partition `6 + 18 + 24 + 48 + 144 = 240`), and `H3ZornTKKLieAlgebra` / `H3ZornE7RootSystem`
   (`133 = 7 + 126 = 7 * (1 + 5 + 13) = 7 + 35 + 91` with ratios `1/19, 5/19, 13/19`).
4. **G1, G2, G4, G5 (`𝕆ₛ`, `ℂ ⊗ 𝕆ₛ` Peirce CAR, `J₃(𝕆ₛ)`, `D_{X,Y}`)**:
   Re-exports `SplitOctonionEllCircularCAR`, bridges `(ℂ ⊗[ℝ] ZornMatrix ℝ) ≃ₗ[ℂ] ZornMatrix ℂ`,
   establishes complexified Peirce CAR `{a_i, a_j†} = δ_{ij} • 1` and left-operator CAR
   `{L_{a_i}, L_{a_j†}} = δ_{ij} • id`, links `AlbertMatrix.e₁, e₂, e₃` (`CubicJordanOs`,
   avoiding `CubicJordanPeirce.peirceE₃`), `e_sum_one`, `freudenthal_identityZ`,
   `penrose_global_closure`, `Algebra.Generations`, `directCanonicalStanDerMap_apply_normal_form`,
   `splitThreeBracket_derivation`, and proves `zorn_peirce_associator_udu`.
5. **H1, H2, H4, H6 (Para-Dolbeault, Kasteleyn–Dirac `D_χ`, Pfaffian–Determinant)**:
   Finite algebraic Para-Dolbeault bigrading (`d_+^2 = 0`, `d_-^2 = 0`, `{d_+, d_-} = 0`,
   chiral Hodge–Dirac anticommutation with `Γ` and concrete `Fin 2 × Fin 2 → ℝ` witness),
   Kasteleyn–Dirac Gram trace equality `Tr(Kᴴ K) = Tr(K Kᴴ)`, Krein supertrace vanishing,
   index `dim ker K - dim ker Kᴴ = N_circ - N_bullet`, and `det (fromBlocks 0 K (-Kᵀ) 0) = (det K)^2`.

### Excluded Transcript Claims (Audited Separately in M5)
- `D3` (`T06:357-362, 401`, `T10:971-974`, `T57:4602`): Incompatible `S_dil` definitions on
  `ℂ⁶³` (column norm `1/√3` vs unitarity claim, `ω₁₂` conflict `e^{iπ/6}` vs `e^{iπ/12}`).
- `D4` (`T06:377`): Claimed `e^{i2π/3}` triple-product Pauli phase; refuted below by
  `pauli3_product_phase_pm_one` (`±1 ≠ exp(2πi/3)`).
- `D5` (`T06:385-394`, `T10:977-986`): Unproved Jordan-block count claim on the `21`-dim rep.
- `T39:3080–3084`: Non-nilpotent candidate `(-e₂ + i e₅)/2` (`a₁² = -1/2 ≠ 0`, `{a₁, a₁†} = 0`);
  replaced by the genuine split-octonion Peirce CAR in `ZornMatrix ℂ`.
- `T41:3301` & `T41:3323`: Incorrect sign/coefficient in `D_{X,Y}(Z)` and `1/2` associator factor;
  verified instead against `directCanonicalStanDerMap_apply_normal_form` (`[[x,y],z] - 3[x,y,z]`)
  and `zorn_peirce_associator_udu` (coefficient `1`).
- `T42:3574` & `T42:3513`: Typographical `sTr_K(D_χ)` for `sTr_K(D_χ^2)` and uncontracted
  octonionic square formula.
- `T44:3767` & `T44:3775`: Singular odd-block Berezinian `Ber(0, K†; K, 0)` and Amplituhedron
  volume identification.
- `T66:5197`, `T68:5286–5291`, `T71:5496–5533`: `dim(H(2)) = 133` typo, inconsistent `E₇`
  `35`-dim nilradical / `91`-dim Levi claim, and cosmological density numerology (`Ω_b, Ω_DM, Ω_Λ`).
-/

namespace InfoGeometry.Quantum.ThreeQubitPauliHexagonShear

open Matrix
open scoped BigOperators Kronecker TensorProduct ComplexOrder

/-! ## Section D1: 3-Qubit Pauli Carrier `𝒫₃`, `OctImIsotropicPoint`, and `HexPoint` -/

section ThreeQubitPauli

open InfoGeometry.Quantum.BinaryWeyl
open InfoGeometry.Projective.BinarySymplectic
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates

private abbrev SplitOctF2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2
private abbrev mulF2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
private abbrev zeroF2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero
private abbrev addF2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
private abbrev dot3F2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.dot3
private abbrev cross0F2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross0
private abbrev cross1F2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross1
private abbrev cross2F2 := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross2

/-- Six-bit label `((x₁, z₁), ((x₂, z₂), (x₃, z₃)))` for 3-qubit Pauli words. -/
abbrev Label3 := (Bit × Bit) × (Bit × Bit) × (Bit × Bit)

/-- The `8 × 8` matrix carrier acting on `(ZMod 2 × ZMod 2) × ZMod 2` (specializing to `ℂ⁸`). -/
abbrev Operator3 (R : Type*) :=
  Matrix ((ZMod 2 × ZMod 2) × ZMod 2) ((ZMod 2 × ZMod 2) × ZMod 2) R

theorem finrank_label3 : Module.finrank Bit Label3 = 6 := by
  simp [Label3]

theorem card_nonzero_label3 : Fintype.card {v : Label3 // v ≠ 0} = 63 := by
  decide

/-- Ordered 3-qubit binary Weyl word `(X^{a₁} Z^{b₁}) ⊗ (X^{a₂} Z^{b₂}) ⊗ (X^{a₃} Z^{b₃})`. -/
def pauli3 {R : Type*} [CommRing R] (v : Label3) : Operator3 R :=
  (word v.1.1 v.1.2 ⊗ₖ word v.2.1.1 v.2.1.2) ⊗ₖ word v.2.2.1 v.2.2.2

/-- Multiplication cocycle for 3-qubit Pauli words. -/
def cocycle3 (v w : Label3) : Bit :=
  v.1.2 * w.1.1 + v.2.1.2 * w.2.1.1 + v.2.2.2 * w.2.2.1

/-- Alternating `F₂`-symplectic pairing on `Label3`. -/
def symplectic3 (v w : Label3) : Bit :=
  cocycle3 v w + cocycle3 w v

@[simp] theorem label3_add_self (v : Label3) : v + v = 0 := by
  apply Prod.ext
  · apply Prod.ext <;> exact CharTwo.add_self_eq_zero _
  · apply Prod.ext <;> apply Prod.ext <;> exact CharTwo.add_self_eq_zero _

@[simp] theorem pauli3_zero {R : Type*} [CommRing R] :
    pauli3 (R := R) 0 = 1 := by
  simp [pauli3]

theorem pauli3_mul {R : Type*} [CommRing R] (v w : Label3) :
    pauli3 (R := R) v * pauli3 w = phase (R := R) (cocycle3 v w) • pauli3 (v + w) := by
  simp only [pauli3, ← Matrix.mul_kronecker_mul, word_mul,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← phase_add]
  congr 2
  · simp only [cocycle3]
    ring

theorem pauli3_mul_self {R : Type*} [CommRing R] (v : Label3) :
    pauli3 (R := R) v * pauli3 v = phase (R := R) (cocycle3 v v) • (1 : Operator3 R) := by
  rw [pauli3_mul, label3_add_self, pauli3_zero]

theorem pauli3_mul_inverse {R : Type*} [CommRing R] (v : Label3) :
    pauli3 (R := R) v * (phase (R := R) (cocycle3 v v) • pauli3 v) = 1 := by
  rw [mul_smul_comm, pauli3_mul_self, smul_smul, phase_mul_self, one_smul]

theorem pauli3_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (v : Label3) :
    pauli3 (R := R) v ≠ 0 := by
  intro h
  have hi := pauli3_mul_inverse (R := R) v
  rw [h, zero_mul] at hi
  exact zero_ne_one hi

theorem smul_pauli3_injective {R : Type*} [CommRing R] (v : Label3) :
    Function.Injective (fun r : R => r • pauli3 (R := R) v) := by
  intro r s h
  have hi := congrArg (fun A : Operator3 R => A *
    (phase (R := R) (cocycle3 v v) • pauli3 v)) h
  simp only [smul_mul_assoc, pauli3_mul_inverse] at hi
  have he := congrArg (fun A : Operator3 R => A ((0, 0), 0) ((0, 0), 0)) hi
  simpa using he

theorem pauli3_phase_commutation {R : Type*} [CommRing R] (v w : Label3) :
    pauli3 (R := R) v * pauli3 w =
      phase (R := R) (symplectic3 v w) • (pauli3 w * pauli3 v) := by
  rw [pauli3_mul, pauli3_mul, smul_smul, ← phase_add, add_comm w v]
  congr 2
  simp only [symplectic3]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem pauli3_commute_iff {R : Type*} [CommRing R] [CharZero R] (v w : Label3) :
    Commute (pauli3 (R := R) v) (pauli3 w) ↔ symplectic3 v w = 0 := by
  change pauli3 (R := R) v * pauli3 w = pauli3 w * pauli3 v ↔ _
  rw [pauli3_mul, pauli3_mul, add_comm w v]
  constructor
  · intro h
    have hc := phase_injective (smul_pauli3_injective (v + w) h)
    simp [symplectic3, hc]
  · intro h
    have hc : cocycle3 v w = cocycle3 w v := CharTwo.add_eq_zero.mp h
    rw [hc]

theorem pauli3_line_product {R : Type*} [CommRing R] (v w : Label3) :
    pauli3 (R := R) v * pauli3 w * pauli3 (v + w) =
      phase (R := R) (cocycle3 v w + cocycle3 (v + w) (v + w)) • (1 : Operator3 R) := by
  rw [pauli3_mul, smul_mul_assoc, pauli3_mul_self, smul_smul, ← phase_add]

/-- Every binary Weyl phase over `ℂ` lies in `{±1}` and cannot equal `exp(2πi/3)`,
refuting the `T06:377` triple-product phase claim. -/
theorem pauli3_product_phase_pm_one (t : Bit) :
    (phase (R := ℂ) t = 1 ∨ phase (R := ℂ) t = -1) ∧
      phase (R := ℂ) t ≠ Complex.exp (2 * Real.pi * Complex.I / 3) := by
  have him : (Complex.exp (2 * Real.pi * Complex.I / 3)).im ≠ 0 := by
    have hmul : (2 * Real.pi * Complex.I / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hmul, Complex.exp_ofReal_mul_I_im]
    have hpos : 0 < Real.sin (2 * Real.pi / 3) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    exact ne_of_gt hpos
  have hpm : phase (R := ℂ) t = 1 ∨ phase (R := ℂ) t = -1 := by
    fin_cases t
    · left; exact phase_zero
    · right; exact phase_one
  refine ⟨hpm, ?_⟩
  intro heq
  rcases hpm with h1 | hneg
  · rw [h1] at heq
    have := congrArg Complex.im heq
    simp at this
    exact him this.symm
  · rw [hneg] at heq
    have := congrArg Complex.im heq
    simp at this
    exact him this.symm

/-- Projection from 7-coordinate `OctImF2` to 6-coordinate `Label3`. -/
def octImToLabel3 (v : OctImF2) : Label3 :=
  ((v 0, v 3), ((v 1, v 4), (v 2, v 5)))

/-- Lifting `Label3` to the unique isotropic `OctImF2` vector with quadratic 7th coordinate. -/
def label3ToOctIm (l : Label3) : OctImF2
  | 0 => l.1.1
  | 1 => l.2.1.1
  | 2 => l.2.2.1
  | 3 => l.1.2
  | 4 => l.2.1.2
  | 5 => l.2.2.2
  | 6 => l.1.1 * l.1.2 + l.2.1.1 * l.2.1.2 + l.2.2.1 * l.2.2.2

theorem octImToLabel3_label3ToOctIm (l : Label3) :
    octImToLabel3 (label3ToOctIm l) = l := by
  rcases l with ⟨⟨x0, y0⟩, ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩⟩
  rfl

theorem label3ToOctIm_splitQuad (l : Label3) :
    splitQuad (label3ToOctIm l) = 0 := by
  dsimp [splitQuad, label3ToOctIm]
  rw [pow_two]
  ring_nf
  simp

theorem label3ToOctIm_octImToLabel3 {v : OctImF2} (hv : splitQuad v = 0) :
    label3ToOctIm (octImToLabel3 v) = v := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · dsimp [label3ToOctIm, octImToLabel3]
    have hsq : v 0 * v 3 + v 1 * v 4 + v 2 * v 5 + (v 6) ^ 2 = 0 := hv
    have hv6 : (v 6) ^ 2 = v 6 := by
      rcases bit_eq_zero_or_one (v 6) with h | h <;> simp [h]
    rw [hv6] at hsq
    exact CharTwo.add_eq_zero.mp hsq

/-- Constructive bijection between isotropic imaginary split octonions over `𝔽₂`
and nonzero 3-qubit Pauli labels. -/
def octImIsotropicEquivNonzeroLabel3 :
    OctImIsotropicPoint ≃ {v : Label3 // v ≠ 0} where
  toFun u := ⟨octImToLabel3 u.1, by
    intro h0
    apply u.2.2
    rw [← label3ToOctIm_octImToLabel3 u.2.1, h0]
    funext i
    fin_cases i <;> decide⟩
  invFun l := ⟨label3ToOctIm l.1, label3ToOctIm_splitQuad l.1, by
    intro h0
    apply l.2
    rw [← octImToLabel3_label3ToOctIm l.1, h0]
    rfl⟩
  left_inv u := by
    apply Subtype.ext
    exact label3ToOctIm_octImToLabel3 u.2.1
  right_inv l := by
    apply Subtype.ext
    exact octImToLabel3_label3ToOctIm l.1

/-- Cardinality-63 bijection from `G2HexagonIncidence.HexPoint` (`casPointEnum`)
to nonzero 3-qubit Pauli labels. -/
noncomputable def hexPointEquivNonzeroLabel3 :
    HexPoint ≃ {v : Label3 // v ≠ 0} :=
  casPointEnum.trans octImIsotropicEquivNonzeroLabel3

private theorem boolToZMod_zModToBool_mul (a b : ZMod 2) :
    boolToZMod (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul2
      (zModToBool a) (zModToBool b)) = a * b := by
  fin_cases a <;> fin_cases b <;> rfl

private theorem boolToZMod_zModToBool_add (a b : ZMod 2) :
    boolToZMod (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2
      (zModToBool a) (zModToBool b)) = a + b := by
  fin_cases a <;> fin_cases b <;> rfl

private theorem boolToZMod_injective : Function.Injective boolToZMod := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolToZMod]

/-- Native split-Zorn orthogonality `ZornZeroRelated u v` forces the 6D binary
symplectic form of `octImToLabel3 u.1` and `octImToLabel3 v.1` to vanish. -/
theorem zornZeroRelated_implies_symplectic3_zero {u v : OctImIsotropicPoint}
    (h : ZornZeroRelated u v) :
    symplectic3 (octImToLabel3 u.1) (octImToLabel3 v.1) = 0 := by
  have ha := congrArg (fun z => boolToZMod z.a) h.2.1
  have hb := congrArg (fun z => boolToZMod z.b) h.2.1
  dsimp [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul, embed, octImToImaginary,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.dot3,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero] at ha hb
  simp only [boolToZMod_add2, boolToZMod_mul2, boolToZMod_zModToBool] at ha hb
  change u.1 6 * v.1 6 + (u.1 0 * v.1 3 + (u.1 1 * v.1 4 + u.1 2 * v.1 5)) = 0 at ha
  change u.1 6 * v.1 6 + (u.1 3 * v.1 0 + (u.1 4 * v.1 1 + u.1 5 * v.1 2)) = 0 at hb
  have hsum := congrArg₂ (· + ·) ha hb
  rw [add_zero] at hsum
  have hcancel :
      (u.1 6 * v.1 6 + (u.1 0 * v.1 3 + (u.1 1 * v.1 4 + u.1 2 * v.1 5))) +
        (u.1 6 * v.1 6 + (u.1 3 * v.1 0 + (u.1 4 * v.1 1 + u.1 5 * v.1 2))) =
      symplectic3 (octImToLabel3 u.1) (octImToLabel3 v.1) := by
    simp only [symplectic3, cocycle3, octImToLabel3]
    ring_nf
    simp [show (2 : Bit) = 0 by decide]
  rw [← hcancel]
  exact hsum

/-- Every `ZornZeroRelated` edge in the native `G₂(2)` split-octonion incidence lifts
to a commuting pair of `8 × 8` 3-qubit Pauli matrices over `ℂ`. -/
theorem zornZeroRelated_implies_pauli3_commute {u v : OctImIsotropicPoint}
    (h : ZornZeroRelated u v) :
    Commute (pauli3 (R := ℂ) (octImToLabel3 u.1))
      (pauli3 (R := ℂ) (octImToLabel3 v.1)) :=
  (pauli3_commute_iff (R := ℂ) _ _).mpr (zornZeroRelated_implies_symplectic3_zero h)

private theorem zModToBool_add_eq_xor (a b : Bit) :
    zModToBool (a + b) = xor (zModToBool a) (zModToBool b) := by
  revert a b
  decide

private theorem embed_add_of_symplectic3_zero (u v : OctImIsotropicPoint) :
    embed (u.1 + v.1) = addF2 (embed u.1) (embed v.1) := by
  apply InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2.ext <;>
    simp [embed, octImToImaginary, addF2,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      zModToBool_add_eq_xor]

private theorem zorn_isotropic_mul_self (u : OctImIsotropicPoint) :
    mulF2 (embed u.1) (embed u.1) = zeroF2 := by
  have hsplit : u.1 6 = u.1 0 * u.1 3 + u.1 1 * u.1 4 + u.1 2 * u.1 5 := by
    have := u.2.1
    dsimp [splitQuad] at this
    have hv6 : (u.1 6) ^ 2 = u.1 6 := by
      rcases bit_eq_zero_or_one (u.1 6) with h | h <;> simp [h]
    rw [hv6] at this
    exact (CharTwo.add_eq_zero.mp this).symm
  apply InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2.ext <;>
    apply boolToZMod_injective <;>
    dsimp [mulF2, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul, embed, octImToImaginary,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.dot3,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross0,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross1,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross2,
      zeroF2, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero] <;>
    simp only [boolToZMod_add2, boolToZMod_mul2, boolToZMod_zModToBool]
  · rw [hsplit]; ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · rw [hsplit]; ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl
  · ring_nf; simp [show (2 : Bit) = 0 by decide]; rfl

private theorem zorn_mul_add_left (X Y Z : SplitOctF2) :
    mulF2 X (addF2 Y Z) = addF2 (mulF2 X Y) (mulF2 X Z) := by
  apply InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2.ext <;>
    apply boolToZMod_injective <;>
    dsimp [mulF2, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul,
      addF2, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.dot3,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross0,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross1,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross2] <;>
    simp only [boolToZMod_add2, boolToZMod_mul2, boolToZMod_xor] <;>
    ring

private theorem zorn_mul_add_right (X Y Z : SplitOctF2) :
    mulF2 (addF2 X Y) Z = addF2 (mulF2 X Z) (mulF2 Y Z) := by
  apply InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2.ext <;>
    apply boolToZMod_injective <;>
    dsimp [mulF2, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul,
      addF2, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.dot3,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross0,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross1,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.cross2] <;>
    simp only [boolToZMod_add2, boolToZMod_mul2, boolToZMod_xor] <;>
    ring

/-- Every `ZornZeroRelated` pair `u, v` extends to an isotropic third point `u + v`
forming a closed `zornZeroTriple` `{u, v, u + v}` whose `Label3` coordinates add. -/
theorem zornZeroRelated_forms_triple {u v : OctImIsotropicPoint}
    (huv : ZornZeroRelated u v) :
    ∃ w : OctImIsotropicPoint,
      w.1 = u.1 + v.1 ∧
      octImToLabel3 w.1 = octImToLabel3 u.1 + octImToLabel3 v.1 ∧
      ZornZeroRelated u w ∧
      ZornZeroRelated v w ∧
      ({u, v, w} : Finset OctImIsotropicPoint) ∈ zornZeroTriples := by
  have hsymp := zornZeroRelated_implies_symplectic3_zero huv
  have hsplit : splitQuad (u.1 + v.1) = 0 := by
    have hcalc : splitQuad (u.1 + v.1) =
        splitQuad u.1 + splitQuad v.1 + symplectic3 (octImToLabel3 u.1) (octImToLabel3 v.1) := by
      simp only [splitQuad, symplectic3, cocycle3, octImToLabel3, Pi.add_apply]
      ring_nf
      simp [show (2 : Bit) = 0 by decide]
    rw [hcalc, u.2.1, v.2.1, hsymp]
    rfl
  have hne0 : u.1 + v.1 ≠ 0 := by
    intro h0
    apply huv.1
    have := congrArg (fun x => x + v.1) h0
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at this
    exact this
  let w : OctImIsotropicPoint := ⟨u.1 + v.1, hsplit, hne0⟩
  have huw_ne : u.1 ≠ w.1 := by
    intro h
    apply v.2.2
    have := congrArg (fun x => u.1 + x) h
    dsimp [w] at this
    rw [CharTwo.add_self_eq_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
    exact this.symm
  have hvw_ne : v.1 ≠ w.1 := by
    intro h
    apply u.2.2
    have := congrArg (fun x => x + v.1) h
    dsimp [w] at this
    rw [CharTwo.add_self_eq_zero, add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
    exact this.symm
  have huv21 : mulF2 (embed u.1) (embed v.1) = zeroF2 := huv.2.1
  have huv22 : mulF2 (embed v.1) (embed u.1) = zeroF2 := huv.2.2
  have huw_mul : mulF2 (embed u.1) (embed w.1) = zeroF2 := by
    change mulF2 (embed u.1) (embed (u.1 + v.1)) = zeroF2
    rw [embed_add_of_symplectic3_zero, zorn_mul_add_left,
      zorn_isotropic_mul_self u, huv21]
    exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero_add zeroF2
  have hwu_mul : mulF2 (embed w.1) (embed u.1) = zeroF2 := by
    change mulF2 (embed (u.1 + v.1)) (embed u.1) = zeroF2
    rw [embed_add_of_symplectic3_zero, zorn_mul_add_right,
      zorn_isotropic_mul_self u, huv22]
    exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero_add zeroF2
  have hvw_mul : mulF2 (embed v.1) (embed w.1) = zeroF2 := by
    change mulF2 (embed v.1) (embed (u.1 + v.1)) = zeroF2
    rw [embed_add_of_symplectic3_zero, zorn_mul_add_left,
      huv22, zorn_isotropic_mul_self v]
    exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero_add zeroF2
  have hwv_mul : mulF2 (embed w.1) (embed v.1) = zeroF2 := by
    change mulF2 (embed (u.1 + v.1)) (embed v.1) = zeroF2
    rw [embed_add_of_symplectic3_zero, zorn_mul_add_right,
      huv21, zorn_isotropic_mul_self v]
    exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero_add zeroF2
  have hrel_uw : ZornZeroRelated u w := ⟨huw_ne, huw_mul, hwu_mul⟩
  have hrel_vw : ZornZeroRelated v w := ⟨hvw_ne, hvw_mul, hwv_mul⟩
  have hu_ne_v : u ≠ v := fun h => huv.1 (congrArg Subtype.val h)
  have hu_ne_w : u ≠ w := fun h => huw_ne (congrArg Subtype.val h)
  have hv_ne_w : v ≠ w := fun h => hvw_ne (congrArg Subtype.val h)
  have hcard : ({u, v, w} : Finset OctImIsotropicPoint).card = 3 :=
    Finset.card_eq_three.mpr ⟨u, v, w, hu_ne_v, hu_ne_w, hv_ne_w, rfl⟩
  have htriple : zornZeroTriple ({u, v, w} : Finset OctImIsotropicPoint) := by
    refine ⟨hcard, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact huv
    · exact hrel_uw
    · exact ⟨huv.1.symm, huv.2.2, huv.2.1⟩
    · exact (hxy rfl).elim
    · exact hrel_vw
    · exact ⟨hrel_uw.1.symm, hrel_uw.2.2, hrel_uw.2.1⟩
    · exact ⟨hrel_vw.1.symm, hrel_vw.2.2, hrel_vw.2.1⟩
    · exact (hxy rfl).elim
  refine ⟨w, rfl, ?_, hrel_uw, hrel_vw, ?_⟩
  · rfl
  · simp [zornZeroTriples, htriple]

private def natToOctIm (n : ℕ) : OctImF2 :=
  label3ToOctIm
    ((if n % 2 = 1 then 1 else 0, if (n / 8) % 2 = 1 then 1 else 0),
     ((if (n / 2) % 2 = 1 then 1 else 0, if (n / 16) % 2 = 1 then 1 else 0),
      (if (n / 4) % 2 = 1 then 1 else 0, if (n / 32) % 2 = 1 then 1 else 0)))

private theorem natToOctIm_zero : natToOctIm 0 = 0 := by
  funext i
  fin_cases i <;> decide

private theorem exists_natToOctIm (v : OctImF2) (hv : splitQuad v = 0) (hv0 : v ≠ 0) :
    ∃ n : Fin 64, n.val ≠ 0 ∧ natToOctIm n.val = v := by
  let n : ℕ :=
    (v 0).val + 2 * (v 1).val + 4 * (v 2).val +
      8 * (v 3).val + 16 * (v 4).val + 32 * (v 5).val
  have hlt : n < 64 := by
    have h0 : (v 0).val < 2 := ZMod.val_lt _
    have h1 : (v 1).val < 2 := ZMod.val_lt _
    have h2 : (v 2).val < 2 := ZMod.val_lt _
    have h3 : (v 3).val < 2 := ZMod.val_lt _
    have h4 : (v 4).val < 2 := ZMod.val_lt _
    have h5 : (v 5).val < 2 := ZMod.val_lt _
    omega
  have heq : natToOctIm n = v := by
    rw [← label3ToOctIm_octImToLabel3 hv]
    dsimp [natToOctIm]
    congr 1
    have hbit : ∀ i : Fin 7, v i = if (v i).val = 1 then 1 else 0 := by
      intro i
      rcases bit_eq_zero_or_one (v i) with h | h <;> simp [h]
      decide
    have h0lt : (v 0).val < 2 := ZMod.val_lt _
    have h1lt : (v 1).val < 2 := ZMod.val_lt _
    have h2lt : (v 2).val < 2 := ZMod.val_lt _
    have h3lt : (v 3).val < 2 := ZMod.val_lt _
    have h4lt : (v 4).val < 2 := ZMod.val_lt _
    have h5lt : (v 5).val < 2 := ZMod.val_lt _
    simp only [octImToLabel3]
    apply Prod.ext
    · apply Prod.ext
      · rw [hbit 0]; dsimp; have : n % 2 = (v 0).val := by omega
        rw [this]
      · rw [hbit 3]; dsimp; have : (n / 8) % 2 = (v 3).val := by omega
        rw [this]
    · apply Prod.ext
      · apply Prod.ext
        · rw [hbit 1]; dsimp; have : (n / 2) % 2 = (v 1).val := by omega
          rw [this]
        · rw [hbit 4]; dsimp; have : (n / 16) % 2 = (v 4).val := by omega
          rw [this]
      · apply Prod.ext
        · rw [hbit 2]; dsimp; have : (n / 4) % 2 = (v 2).val := by omega
          rw [this]
        · rw [hbit 5]; dsimp; have : (n / 32) % 2 = (v 5).val := by omega
          rw [this]
  refine ⟨⟨n, hlt⟩, ?_, heq⟩
  intro hn0
  apply hv0
  have hn0' : n = 0 := hn0
  rw [← heq, hn0']
  exact natToOctIm_zero

private def relOctImBool (u v : OctImF2) : Bool :=
  decide (u ≠ v ∧ mulF2 (embed u) (embed v) = zeroF2 ∧ mulF2 (embed v) (embed u) = zeroF2)

private theorem relOctImBool_check :
    (List.finRange 64).all (fun i =>
      (List.finRange 64).all (fun j =>
        let u := natToOctIm i.val
        let v := natToOctIm j.val
        if i.val != 0 && j.val != 0 && relOctImBool u v then
          (List.finRange 64).all (fun k =>
            let w := natToOctIm k.val
            if k.val != 0 && relOctImBool u w && relOctImBool v w then
              decide (w = u + v)
            else true)
        else true)) = true := by
  decide

theorem zornZeroRelated_triangle_eq_add {u v w : OctImIsotropicPoint}
    (huv : ZornZeroRelated u v) (huw : ZornZeroRelated u w) (hvw : ZornZeroRelated v w) :
    w.1 = u.1 + v.1 := by
  obtain ⟨i, hi0, hi⟩ := exists_natToOctIm u.1 u.2.1 u.2.2
  obtain ⟨j, hj0, hj⟩ := exists_natToOctIm v.1 v.2.1 v.2.2
  obtain ⟨k, hk0, hk⟩ := exists_natToOctIm w.1 w.2.1 w.2.2
  have hchk := relOctImBool_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h1 := hchk i j
  have hrel_uv : relOctImBool (natToOctIm i.val) (natToOctIm j.val) = true := by
    rw [hi, hj]
    exact decide_eq_true huv
  have hcond1 : ((i.val != 0) && (j.val != 0) &&
      relOctImBool (natToOctIm i.val) (natToOctIm j.val)) = true := by
    simp [hi0, hj0, hrel_uv]
  rw [hcond1] at h1
  dsimp at h1
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
  have h2 := h1 k
  have hrel_uw : relOctImBool (natToOctIm i.val) (natToOctIm k.val) = true := by
    rw [hi, hk]
    exact decide_eq_true huw
  have hrel_vw : relOctImBool (natToOctIm j.val) (natToOctIm k.val) = true := by
    rw [hj, hk]
    exact decide_eq_true hvw
  have hcond2 : ((k.val != 0) &&
      relOctImBool (natToOctIm i.val) (natToOctIm k.val) &&
      relOctImBool (natToOctIm j.val) (natToOctIm k.val)) = true := by
    simp [hk0, hrel_uw, hrel_vw]
  rw [hcond2] at h2
  dsimp at h2
  rw [← hi, ← hj, ← hk]
  exact decide_eq_true_eq.mp h2

/-- Every triple in `zornZeroTriples` is closed under `F₂⁶` / `F₂⁷` vector addition. -/
theorem zornZeroTriples_closed_add :
    ∀ s ∈ zornZeroTriples, ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      ∃ w ∈ s, w.1 = u.1 + v.1 ∧
        octImToLabel3 w.1 = octImToLabel3 u.1 + octImToLabel3 v.1 := by
  intro s hs u hu v hv huv
  have htr : zornZeroTriple s := (Finset.mem_filter.mp hs).2
  have hserase : ((s.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hv⟩),
      Finset.card_erase_of_mem hu, htr.1]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hserase
  have hw_erase : w ∈ (s.erase u).erase v := by
    rw [hw]
    exact Finset.mem_singleton_self w
  have hwv : w ≠ v := (Finset.mem_erase.mp hw_erase).1
  have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hw_erase).2).1
  have hw_mem : w ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hw_erase).2).2
  have hadd := zornZeroRelated_triangle_eq_add
    (htr.2 u hu v hv huv) (htr.2 u hu w hw_mem hwu.symm) (htr.2 v hv w hw_mem hwv.symm)
  refine ⟨w, hw_mem, hadd, ?_⟩
  rw [hadd]
  rfl

end ThreeQubitPauli

/-! ## Section D2 & D4: `Sp(6, 𝔽₂)` Symplectic Transvections and Line Preservation -/

section SymplecticTransvections

open InfoGeometry.Quantum.BinaryWeyl
open InfoGeometry.Projective.BinarySymplectic

/-- Six-dimensional `𝔽₂` symplectic vector space `(x₀, x₁, x₂, z₀, z₁, z₂)`. -/
abbrev Vec6 := Fin 6 → Bit

/-- Linear isomorphism aligning `Label3` with `Vec6` in `(x₀, x₁, x₂, z₀, z₁, z₂)` order. -/
def label3EquivVec6 : Label3 ≃ₗ[Bit] Vec6 where
  toFun v := ![v.1.1, v.2.1.1, v.2.2.1, v.1.2, v.2.1.2, v.2.2.2]
  invFun f := ((f 0, f 3), ((f 1, f 4), (f 2, f 5)))
  left_inv v := by
    rcases v with ⟨⟨x0, z0⟩, ⟨⟨x1, z1⟩, ⟨x2, z2⟩⟩⟩
    rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl
  map_add' v w := by
    funext i
    fin_cases i <;> rfl
  map_smul' c v := by
    funext i
    fin_cases i <;> rfl

/-- Standard `6 × 6` block symplectic matrix `J = [[0, I₃], [I₃, 0]]` over `𝔽₂`. -/
def J6 : Matrix (Fin 6) (Fin 6) Bit :=
  fun i j => if (i.val + 3) % 6 = j.val then 1 else 0

theorem J6_transpose : J6ᵀ = J6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem J6_sq : J6 * J6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Explicit matrix non-commutativity witness for `J6` against the rank-1 projector `E₀₀`. -/
theorem J6_noncommutative :
    let E00 : Matrix (Fin 6) (Fin 6) Bit := fun i j => if i = 0 ∧ j = 0 then 1 else 0
    J6 * E00 ≠ E00 * J6 := by
  intro E00 h
  have h03 := congr_fun (congr_fun h 0) 3
  revert h03
  decide

/-- Canonical symplectic bilinear form `⟨u, v⟩ = uᵀ J₆ v` on `𝔽₂⁶`. -/
def sympForm6 (u v : Vec6) : Bit :=
  u ⬝ᵥ J6.mulVec v

theorem sympForm6_eq_symplectic3 (v w : Label3) :
    sympForm6 (label3EquivVec6 v) (label3EquivVec6 w) = symplectic3 v w := by
  rcases v with ⟨⟨x0, z0⟩, ⟨⟨x1, z1⟩, ⟨x2, z2⟩⟩⟩
  rcases w with ⟨⟨u0, v0⟩, ⟨⟨u1, v1⟩, ⟨u2, v2⟩⟩⟩
  simp only [sympForm6, label3EquivVec6, LinearEquiv.coe_mk, dotProduct, J6, Matrix.mulVec,
    Fin.sum_univ_six, symplectic3, cocycle3]
  decide +revert

theorem sympForm6_comm (u v : Vec6) : sympForm6 u v = sympForm6 v u := by
  dsimp [sympForm6, dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hJ : J6 i j = J6 j i := by
    simpa [Matrix.transpose_apply] using congrArg (fun M : Matrix (Fin 6) (Fin 6) Bit => M j i) J6_transpose
  rw [hJ]
  ring

theorem sympForm6_self (a : Vec6) : sympForm6 a a = 0 := by
  dsimp [sympForm6, dotProduct, J6, Matrix.mulVec]
  simp only [Fin.sum_univ_six]
  decide +revert

theorem sympForm6_add_left (u v w : Vec6) :
    sympForm6 (u + v) w = sympForm6 u w + sympForm6 v w := by
  simp [sympForm6]

theorem sympForm6_add_right (u v w : Vec6) :
    sympForm6 u (v + w) = sympForm6 u v + sympForm6 u w := by
  simp [sympForm6, Matrix.mulVec_add, dotProduct_add]

theorem sympForm6_smul_left (c : Bit) (u v : Vec6) :
    sympForm6 (c • u) v = c * sympForm6 u v := by
  simp [sympForm6, smul_dotProduct]

theorem sympForm6_smul_right (c : Bit) (u v : Vec6) :
    sympForm6 u (c • v) = c * sympForm6 u v := by
  simp [sympForm6, Matrix.mulVec_smul, dotProduct_smul]

/-- Symplectic transvection map `τ_a(x) = x + ⟨x, a⟩ a` on `𝔽₂⁶`. -/
def transvectionVec (a x : Vec6) : Vec6 :=
  x + sympForm6 x a • a

/-- Symplectic transvection matrix `T_a = I₆ + a aᵀ J₆` over `𝔽₂`. -/
def transvectionMat (a : Vec6) : Matrix (Fin 6) (Fin 6) Bit :=
  1 + Matrix.vecMulVec a (J6.mulVec a)

/-- Three-point projective isotropic line `{v, w, v + w}` in `𝔽₂⁶`. -/
def isoLine6 (v w : Vec6) : Finset Vec6 :=
  {v, w, v + w}

theorem transvectionMat_mulVec (a x : Vec6) :
    (transvectionMat a).mulVec x = transvectionVec a x := by
  ext i
  simp only [transvectionMat, transvectionVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, sympForm6,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem transvectionMat_sub_one_sq (a : Vec6) :
    (transvectionMat a - 1) ^ 2 = 0 := by
  have hsub : transvectionMat a - 1 = Matrix.vecMulVec a (J6.mulVec a) := by
    simp [transvectionMat]
  rw [hsub, pow_two]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  calc
    ∑ k : Fin 6, a i * J6.mulVec a k * (a k * J6.mulVec a j)
        = (a i * J6.mulVec a j) * ∑ k : Fin 6, a k * J6.mulVec a k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ = (a i * J6.mulVec a j) * sympForm6 a a := rfl
    _ = 0 := by rw [sympForm6_self, mul_zero]

private theorem bit_sub_sub_sub_eq (p q r : Bit) : p - q - (q - r) = p - r := by
  revert p q r
  decide

theorem transvectionMat_sq (a : Vec6) :
    (transvectionMat a) ^ 2 = 1 := by
  have hsub : ∀ M : Matrix (Fin 6) (Fin 6) Bit, (M - 1) ^ 2 = M ^ 2 - 1 := by
    intro M
    rw [pow_two, pow_two, sub_mul, mul_sub, mul_sub, one_mul, mul_one]
    ext i j
    simp only [Matrix.sub_apply, one_mul]
    exact bit_sub_sub_sub_eq ((M * M) i j) (M i j) ((1 : Matrix (Fin 6) (Fin 6) Bit) i j)
  have h := hsub (transvectionMat a)
  rw [transvectionMat_sub_one_sq] at h
  exact sub_eq_zero.mp h.symm

/-- Non-commutativity witness (T16) for `Matrix (Fin 6) (Fin 6) Bit`: symplectic
transvections along a conjugate hyperbolic pair do not commute. -/
theorem transvectionMat_noncomm :
    ∃ A B : Matrix (Fin 6) (Fin 6) Bit, A * B ≠ B * A := by
  refine ⟨transvectionMat (Pi.single 0 1), transvectionMat (Pi.single 3 1), ?_⟩
  intro h
  have hmul := congrArg (fun M : Matrix (Fin 6) (Fin 6) Bit => M.mulVec (Pi.single 0 1)) h
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    transvectionMat_mulVec, transvectionMat_mulVec,
    transvectionMat_mulVec, transvectionMat_mulVec] at hmul
  have h0 := congrFun hmul 0
  simp only [transvectionVec, sympForm6, J6, dotProduct, Matrix.mulVec, Fin.sum_univ_six,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h0
  revert h0
  decide

theorem transvectionMat_det (a : Vec6) :
    (transvectionMat a).det = 1 := by
  have hsq : ((transvectionMat a).det) ^ 2 = 1 := by
    rw [pow_two, ← Matrix.det_mul, ← pow_two, transvectionMat_sq, Matrix.det_one]
  rcases bit_eq_zero_or_one (transvectionMat a).det with hd | hd
  · exfalso
    rw [hd] at hsq
    norm_num at hsq
  · exact hd

theorem transvectionVec_preserves_sympForm (a u v : Vec6) :
    sympForm6 (transvectionVec a u) (transvectionVec a v) = sympForm6 u v := by
  simp only [transvectionVec, sympForm6_add_left, sympForm6_add_right,
    sympForm6_smul_left, sympForm6_smul_right, sympForm6_self, mul_zero, add_zero]
  rw [sympForm6_comm a v, mul_comm (sympForm6 v a) (sympForm6 u a),
    add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem transvectionMat_symplectic (a : Vec6) :
    (transvectionMat a)ᵀ * J6 * transvectionMat a = J6 := by
  ext i j
  let ei : Vec6 := Pi.single i 1
  let ej : Vec6 := Pi.single j 1
  have hpres := transvectionVec_preserves_sympForm a ei ej
  rw [← transvectionMat_mulVec, ← transvectionMat_mulVec] at hpres
  have hlhs : sympForm6 ((transvectionMat a).mulVec ei) ((transvectionMat a).mulVec ej) =
      ((transvectionMat a)ᵀ * J6 * transvectionMat a) i j := by
    have hmul_ei : (transvectionMat a).mulVec ei = fun r => transvectionMat a r i := by
      ext r
      simp [ei, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hmul_ej : (transvectionMat a).mulVec ej = fun s => transvectionMat a s j := by
      ext s
      simp [ej, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hmul_ei, hmul_ej]
    simp only [sympForm6, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hrhs : sympForm6 ei ej = J6 i j := by
    simp [sympForm6, ei, ej, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [← hlhs, ← hrhs]
  exact hpres

/-- Symplectic transvection transported to `Label3`. -/
def transvectionLabel3 (a x : Label3) : Label3 :=
  label3EquivVec6.symm (transvectionVec (label3EquivVec6 a) (label3EquivVec6 x))

theorem transvection_preserves_pauli3_commute (a v w : Label3) :
    Commute (pauli3 (R := ℂ) (transvectionLabel3 a v))
        (pauli3 (R := ℂ) (transvectionLabel3 a w)) ↔
      Commute (pauli3 (R := ℂ) v) (pauli3 (R := ℂ) w) := by
  rw [pauli3_commute_iff, pauli3_commute_iff]
  simp only [← sympForm6_eq_symplectic3, transvectionLabel3, LinearEquiv.apply_symm_apply]
  rw [transvectionVec_preserves_sympForm]

theorem transvectionMat_non_identity_of_ne_zero {a : Vec6} (ha : a ≠ 0) :
    transvectionMat a ≠ 1 := by
  intro heq
  have hi0 : ∃ i, a i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha (funext hall)
  rcases hi0 with ⟨i, hi⟩
  have hj : ∃ j, (J6.mulVec a) j ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmul : J6.mulVec a = 0 := funext hall
    have hsq := congrArg (fun v => J6.mulVec v) hmul
    rw [Matrix.mulVec_mulVec, J6_sq, Matrix.one_mulVec, Matrix.mulVec_zero] at hsq
    exact ha hsq
  rcases hj with ⟨j, hj⟩
  have hij := congrArg (fun M : Matrix (Fin 6) (Fin 6) Bit => M i j) heq
  simp only [transvectionMat, Matrix.add_apply, Matrix.vecMulVec_apply] at hij
  have hai : a i = 1 := (bit_eq_zero_or_one (a i)).resolve_left hi
  have hjj : (J6.mulVec a) j = 1 := (bit_eq_zero_or_one _).resolve_left hj
  have hprod : a i * J6.mulVec a j = 0 := by
    have h := congrArg (fun x => x + (1 : Matrix (Fin 6) (Fin 6) Bit) i j) hij
    rw [add_comm ((1 : Matrix (Fin 6) (Fin 6) Bit) i j), add_assoc,
      CharTwo.add_self_eq_zero, add_zero] at h
    exact h
  rw [hai, hjj, mul_one] at hprod
  exact one_ne_zero hprod

/-- Every line `L ⊂ a⊥` is fixed pointwise (and hence setwise) by `transvectionVec a`. -/
theorem transvection_fixes_perp_line (a : Vec6) (L : Finset Vec6)
    (hL : ∀ x ∈ L, sympForm6 x a = 0) :
    L.image (transvectionVec a) = L := by
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [transvectionVec, hL x hx] using hx
  · intro hy
    exact ⟨y, hy, by simp [transvectionVec, hL y hy]⟩

/-- Any isotropic projective line in `𝔽₂⁶` maps bijectively under `transvectionVec a`
to an isotropic line whose `Label3` lift remains pairwise commuting in `𝒫₃`. -/
theorem transvection_preserves_isoLine_commute (a v w : Vec6)
    (hvw_symp : sympForm6 v w = 0) :
    (isoLine6 v w).image (transvectionVec a) =
      isoLine6 (transvectionVec a v) (transvectionVec a w) ∧
    (∀ x ∈ isoLine6 (transvectionVec a v) (transvectionVec a w),
      ∀ y ∈ isoLine6 (transvectionVec a v) (transvectionVec a w),
        Commute (pauli3 (R := ℂ) (label3EquivVec6.symm x))
          (pauli3 (R := ℂ) (label3EquivVec6.symm y))) := by
  have hadd : transvectionVec a (v + w) = transvectionVec a v + transvectionVec a w := by
    simp only [transvectionVec, sympForm6_add_left, add_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · ext z
    simp [isoLine6, hadd]
  · intro x hx y hy
    rw [pauli3_commute_iff, ← sympForm6_eq_symplectic3,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [isoLine6, Finset.mem_insert, Finset.mem_singleton] at hx hy
    have htvw : sympForm6 (transvectionVec a v) (transvectionVec a w) = 0 := by
      rw [transvectionVec_preserves_sympForm, hvw_symp]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact sympForm6_self _
    · exact htvw
    · rw [sympForm6_add_right, sympForm6_self, zero_add, htvw]
    · rw [sympForm6_comm, htvw]
    · exact sympForm6_self _
    · rw [sympForm6_add_right, sympForm6_self, add_zero, sympForm6_comm, htvw]
    · rw [sympForm6_add_left, sympForm6_self, zero_add, sympForm6_comm, htvw]
    · rw [sympForm6_add_left, sympForm6_self, add_zero, htvw]
    · exact sympForm6_self _

end SymplecticTransvections

/-! ## Section D6 & I3: `E₈ ⊃ G₂ × F₄` Branching and `E₇` Rank-7 Partition -/

section ExceptionalBranching

open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley

theorem e8_g2_f4_branching_dims :
    Module.finrank ℝ G2DerivationCarrier = 14 ∧
    Module.finrank ℝ F4DerivationCarrier = 52 ∧
    Module.finrank ℝ MixedCarrier = 182 ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    Module.finrank ℝ G2DerivationCarrier + Module.finrank ℝ F4DerivationCarrier +
      Module.finrank ℝ MixedCarrier = Module.finrank ℝ SplitE8Lie := by
  refine ⟨finrank_g2DerivationCarrier, finrank_f4DerivationCarrier,
    finrank_mixedCarrier, finrank_splitE8Lie, ?_⟩
  rw [finrank_g2DerivationCarrier, finrank_f4DerivationCarrier,
    finrank_mixedCarrier, finrank_splitE8Lie]

theorem e8_mixed_tensor_factors :
    Module.finrank ℝ splitOctonionTraceZero * Module.finrank ℝ h3TraceZero =
      Module.finrank ℝ MixedCarrier := by
  rw [finrank_splitOctonionTraceZero, finrank_h3TraceZero, finrank_mixedCarrier]

theorem e8_root_card_and_sector_split :
    let _instE8 : Fintype {v : Fin 8 → ℤ // IsRoot .E8 v} :=
      (inferInstance : Fintype {v : Fin (Tag.rank .E8) → ℤ // IsRoot .E8 v})
    let _instG2 : Fintype {v : Fin 2 → ℤ // IsRoot .G2 v} :=
      (inferInstance : Fintype {v : Fin (Tag.rank .G2) → ℤ // IsRoot .G2 v})
    let _instF4 : Fintype {v : Fin 4 → ℤ // IsRoot .F4 v} :=
      (inferInstance : Fintype {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v})
    Fintype.card {v : Fin 8 → ℤ // IsRoot .E8 v} = 240 ∧
    Fintype.card {v : Fin 2 → ℤ // IsRoot .G2 v} = 12 ∧
    Fintype.card {v : Fin 4 → ℤ // IsRoot .F4 v} = 48 ∧
    12 + 48 + (6 * 24 + 6 * 2 + 1 * 24) = 240 ∧
    6 + 18 + 24 + 48 + 144 = 240 := by
  let _instE8 : Fintype {v : Fin 8 → ℤ // IsRoot .E8 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .E8) → ℤ // IsRoot .E8 v})
  let _instG2 : Fintype {v : Fin 2 → ℤ // IsRoot .G2 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .G2) → ℤ // IsRoot .G2 v})
  let _instF4 : Fintype {v : Fin 4 → ℤ // IsRoot .F4 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v})
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · exact (card_isRoot .E8)
  · exact (card_isRoot .G2)
  · exact (card_isRoot .F4)

/-- Explicit 5-sector partition `(6 pure G₂) ⊕ (18 G₂ ⊕ Mix) ⊕ (24 pure F₄) ⊕ (48 F₄ ⊕ Mix) ⊕ (144 Mix)`
matching the index ranges of `SplitE8RootSystem.e8RootVec` and `e8RootEquiv`. -/
noncomputable def e8RootSectorPartitionEquiv :
    Fin 6 ⊕ Fin 18 ⊕ Fin 24 ⊕ Fin 48 ⊕ Fin 144 ≃ {v : Fin 8 → ℤ // IsRoot .E8 v} :=
  -- Nested `finSumFinEquiv` places the sectors at offsets `0, 6, 24, 48, 96`.
  let e240 : Fin 6 ⊕ Fin 18 ⊕ Fin 24 ⊕ Fin 48 ⊕ Fin 144 ≃ Fin 240 :=
    ((Equiv.sumCongr (Equiv.refl (Fin 6))
        ((Equiv.sumCongr (Equiv.refl (Fin 18))
            ((Equiv.sumCongr (Equiv.refl (Fin 24)) finSumFinEquiv).trans
              finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)
  e240.trans e8RootEquiv

theorem e8RootSectorPartitionEquiv_f4_sector_card :
    let _instF4 : Fintype {v : Fin 4 → ℤ // IsRoot .F4 v} :=
      (inferInstance : Fintype {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v})
    Fintype.card (Fin 48) = Fintype.card {v : Fin 4 → ℤ // IsRoot .F4 v} := by
  let _instF4 : Fintype {v : Fin 4 → ℤ // IsRoot .F4 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v})
  rw [Fintype.card_congr f4RootEquiv]

theorem e7_carrier_rank_and_roots :
    let _instE7 : Fintype {v : Fin 7 → ℤ // IsRoot .E7 v} :=
      (inferInstance : Fintype {v : Fin (Tag.rank .E7) → ℤ // IsRoot .E7 v})
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    Module.finrank ℝ h3zornE7Cartan = 7 ∧
    Fintype.card {v : Fin 7 → ℤ // IsRoot .E7 v} = 126 ∧
    Module.finrank ℝ h3zornE7Cartan + Fintype.card {v : Fin 7 → ℤ // IsRoot .E7 v} =
      Module.finrank ℝ H3ZornTKKLie := by
  let _instE7 : Fintype {v : Fin 7 → ℤ // IsRoot .E7 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .E7) → ℤ // IsRoot .E7 v})
  have h126 : Fintype.card {v : Fin 7 → ℤ // IsRoot .E7 v} = 126 := by
    rw [← Fintype.card_congr e7RootEquiv, Fintype.card_fin]
  refine ⟨finrank_H3ZornTKKLie, finrank_h3zornE7Cartan, h126, ?_⟩
  rw [finrank_h3zornE7Cartan, h126, finrank_H3ZornTKKLie]

theorem e7_rank7_partition_arithmetic :
    Module.finrank ℝ H3ZornTKKLie = Module.finrank ℝ h3zornE7Cartan * (1 + 5 + 13) ∧
    (7 : ℕ) + 35 + 91 = Module.finrank ℝ H3ZornTKKLie ∧
    ((7 : ℚ) / 133 = 1 / 19 ∧
     (35 : ℚ) / 133 = 5 / 19 ∧
     (91 : ℚ) / 133 = 13 / 19 ∧
     (1 : ℚ) / 19 + 5 / 19 + 13 / 19 = 1) := by
  rw [finrank_H3ZornTKKLie, finrank_h3zornE7Cartan]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end ExceptionalBranching

/-! ## Section G1, G2, G4, G5: `𝕆ₛ`, `ℂ ⊗ 𝕆ₛ` Peirce CAR, `J₃(𝕆ₛ)`, and `D_{X,Y}` -/

section SplitOctonionPeirceAndAlbert

open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Physics.QCDFureyZornProjectorBridge
open InfoGeometry.Physics.QCDCanonicalComplexZornBridge
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivationThreeBracketBridge

/-- Re-exported real circular split-octonion CAR packet from `SplitOctonionEllCircularCAR`. -/
theorem realCircularCAR_packet (a b : Fin 3) :
    InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus a *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus b +
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus b *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus a =
        (if a = b then (1 : InfoGeometry.Lie.SplitOctonionEllCircularCAR.CZ) else 0) ∧
    InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus a *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus b +
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus b *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus a = 0 ∧
    InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus a *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus b +
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus b *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus a = 0 :=
  ⟨rootPlus_mul_rootMinus_anticommutator a b,
   rootPlus_mul_rootPlus_anticommutator a b,
   rootMinus_mul_rootMinus_anticommutator a b⟩

/-- Embedding of real `ZornMatrix ℝ` into complex `ZornMatrix ℂ`. -/
noncomputable def zornRealToComplex : InfoGeometry.Canonical.ZornMatrix ℝ →ₗ[ℝ] ZornC where
  toFun X := { a := X.a, b := X.b, x := fun i => X.x i, y := fun i => X.y i }
  map_add' X Y := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp
    · simp
    · funext i; simp
    · funext i; simp
  map_smul' r X := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul ℂ r
      ({ a := (X.a : ℂ), b := (X.b : ℂ),
         x := fun i => (X.x i : ℂ), y := fun i => (X.y i : ℂ) } : ZornC)]
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp only [InfoGeometry.Canonical.ZornMatrix.smul_a, Complex.coe_algebraMap,
        Complex.ofReal_mul]
    · simp only [InfoGeometry.Canonical.ZornMatrix.smul_b, Complex.coe_algebraMap,
        Complex.ofReal_mul]
    · funext i
      simp only [InfoGeometry.Canonical.ZornMatrix.smul_x, Pi.smul_apply, smul_eq_mul,
        Complex.coe_algebraMap, Complex.ofReal_mul]
    · funext i
      simp only [InfoGeometry.Canonical.ZornMatrix.smul_y, Pi.smul_apply, smul_eq_mul,
        Complex.coe_algebraMap, Complex.ofReal_mul]

/-- `ℂ`-linear inverse of `(ℂ ⊗[ℝ] ZornMatrix ℝ) →ₗ[ℂ] ZornMatrix ℂ`. -/
noncomputable def complexZornTensorInv :
    ZornC →ₗ[ℂ] (ℂ ⊗[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ) where
  toFun X :=
    (1 : ℂ) ⊗ₜ[ℝ] { a := X.a.re, b := X.b.re, x := fun i => (X.x i).re, y := fun i => (X.y i).re } +
    Complex.I ⊗ₜ[ℝ] { a := X.a.im, b := X.b.im, x := fun i => (X.x i).im, y := fun i => (X.y i).im }
  map_add' u v := by
    have hre_add :
        ({ a := (u + v).a.re, b := (u + v).b.re,
            x := fun i => ((u + v).x i).re, y := fun i => ((u + v).y i).re } :
          InfoGeometry.Canonical.ZornMatrix ℝ) =
        { a := u.a.re, b := u.b.re, x := fun i => (u.x i).re, y := fun i => (u.y i).re } +
        { a := v.a.re, b := v.b.re, x := fun i => (v.x i).re, y := fun i => (v.y i).re } := by
      apply InfoGeometry.Canonical.ZornMatrix.ext <;> (try funext i) <;> simp [Pi.add_apply]
    have him_add :
        ({ a := (u + v).a.im, b := (u + v).b.im,
            x := fun i => ((u + v).x i).im, y := fun i => ((u + v).y i).im } :
          InfoGeometry.Canonical.ZornMatrix ℝ) =
        { a := u.a.im, b := u.b.im, x := fun i => (u.x i).im, y := fun i => (u.y i).im } +
        { a := v.a.im, b := v.b.im, x := fun i => (v.x i).im, y := fun i => (v.y i).im } := by
      apply InfoGeometry.Canonical.ZornMatrix.ext <;> (try funext i) <;> simp [Pi.add_apply]
    rw [hre_add, him_add, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
  map_smul' c X := by
    have hsplit_re :
        ({ a := (c • X).a.re, b := (c • X).b.re,
            x := fun i => ((c • X).x i).re, y := fun i => ((c • X).y i).re } :
          InfoGeometry.Canonical.ZornMatrix ℝ) =
        c.re • { a := X.a.re, b := X.b.re, x := fun i => (X.x i).re, y := fun i => (X.y i).re } -
        c.im • { a := X.a.im, b := X.b.im, x := fun i => (X.x i).im, y := fun i => (X.y i).im } := by
      apply InfoGeometry.Canonical.ZornMatrix.ext <;> (try funext i) <;>
        simp [InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b,
          InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_re]
    have hsplit_im :
        ({ a := (c • X).a.im, b := (c • X).b.im,
            x := fun i => ((c • X).x i).im, y := fun i => ((c • X).y i).im } :
          InfoGeometry.Canonical.ZornMatrix ℝ) =
        c.re • { a := X.a.im, b := X.b.im, x := fun i => (X.x i).im, y := fun i => (X.y i).im } +
        c.im • { a := X.a.re, b := X.b.re, x := fun i => (X.x i).re, y := fun i => (X.y i).re } := by
      apply InfoGeometry.Canonical.ZornMatrix.ext <;> (try funext i) <;>
        simp [InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b,
          InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_im]
    rw [hsplit_re, hsplit_im, TensorProduct.tmul_sub, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      smul_add]
    have hsmul_real : ∀ (r : ℝ) (z : ℂ) (M : InfoGeometry.Canonical.ZornMatrix ℝ),
        r • (z ⊗ₜ[ℝ] M) = ((r : ℂ) * z) ⊗ₜ[ℝ] M := by
      intro r z M
      rw [TensorProduct.smul_tmul', Complex.real_smul]
    have hsmul_cplx : ∀ (w z : ℂ) (M : InfoGeometry.Canonical.ZornMatrix ℝ),
        w • (z ⊗ₜ[ℝ] M) = (w * z) ⊗ₜ[ℝ] M := by
      intro w z M
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    rw [hsmul_real, hsmul_real, hsmul_real, hsmul_real, hsmul_cplx, hsmul_cplx]
    have hc_mul_1 : (RingHom.id ℂ) c * (1 : ℂ) = (c.re : ℂ) * 1 + (c.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hc_mul_I : (RingHom.id ℂ) c * Complex.I = -((c.im : ℂ) * 1) + (c.re : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hc_mul_1, hc_mul_I, TensorProduct.add_tmul, TensorProduct.add_tmul, TensorProduct.neg_tmul]
    abel

/-- Explicit `ℂ`-linear isomorphism `(ℂ ⊗[ℝ] ZornMatrix ℝ) ≃ₗ[ℂ] ZornMatrix ℂ`. -/
noncomputable def complexZornTensorEquiv :
    (ℂ ⊗[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ) ≃ₗ[ℂ] ZornC :=
  let toLM : (ℂ ⊗[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ) →ₗ[ℂ] ZornC :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun (c : ℂ) => c • zornRealToComplex
        map_add' := fun c₁ c₂ => by
          ext X
          · simp [add_smul]
          · simp [add_smul]
          · simp [add_smul]
          · simp [add_smul]
        map_smul' := fun (c₁ c₂ : ℂ) => by
          ext X
          · simp [mul_smul]
          · simp [mul_smul]
          · simp [mul_smul]
          · simp [mul_smul] }
  { toFun := toLM
    invFun := complexZornTensorInv
    left_inv := fun t => by
      have hid : (complexZornTensorInv.comp toLM).restrictScalars ℝ =
          (LinearMap.id : (ℂ ⊗[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ) →ₗ[ℝ]
            (ℂ ⊗[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ)) := by
        apply TensorProduct.ext'
        intro c X
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.id_apply,
          toLM, TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, zornRealToComplex,
          complexZornTensorInv, InfoGeometry.Canonical.ZornMatrix.smul_a,
          InfoGeometry.Canonical.ZornMatrix.smul_b, InfoGeometry.Canonical.ZornMatrix.smul_x,
          InfoGeometry.Canonical.ZornMatrix.smul_y, Pi.smul_apply, smul_eq_mul,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.mul_im, zero_add]
        have hre : InfoGeometry.Canonical.ZornMatrix.mk
            (c.re * X.a) (c.re * X.b) (fun i => c.re * X.x i) (fun i => c.re * X.y i) =
            c.re • X := by
          apply InfoGeometry.Canonical.ZornMatrix.ext
          · rfl
          · rfl
          · funext i; simp [smul_eq_mul]
          · funext i; simp [smul_eq_mul]
        have him : InfoGeometry.Canonical.ZornMatrix.mk
            (c.im * X.a) (c.im * X.b) (fun i => c.im * X.x i) (fun i => c.im * X.y i) =
            c.im • X := by
          apply InfoGeometry.Canonical.ZornMatrix.ext
          · rfl
          · rfl
          · funext i; simp [smul_eq_mul]
          · funext i; simp [smul_eq_mul]
        rw [hre, him, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
        congr 1
        apply Complex.ext <;> simp [Complex.real_smul]
      exact LinearMap.congr_fun hid t
    right_inv := fun X => by
      simp only [toLM, complexZornTensorInv, LinearMap.coe_mk, AddHom.coe_mk, map_add,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul,
        zornRealToComplex]
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · apply Complex.ext <;> simp
      · apply Complex.ext <;> simp
      · funext i; apply Complex.ext <;> simp
      · funext i; apply Complex.ext <;> simp
    map_add' := toLM.map_add
    map_smul' := toLM.map_smul }

/-- Upper Peirce projector `ρ₊ = OP1` in `ZornMatrix ℂ ≅ ℂ ⊗ 𝕆ₛ`. -/
noncomputable def cRhoPlus : ZornC := (OP1 : ZornC)

/-- Lower Peirce projector `ρ₋ = OP2` in `ZornMatrix ℂ ≅ ℂ ⊗ 𝕆ₛ`. -/
noncomputable def cRhoMinus : ZornC := (OP2 : ZornC)

/-- Upper Peirce CAR annihilation ladder operator `a_i` in `ZornMatrix ℂ`. -/
noncomputable def cAnnihilate (i : Fin 3) : ZornC := upperLane (Pi.single i (1 : ℂ))

/-- Lower Peirce CAR creation ladder operator `a_i†` in `ZornMatrix ℂ`. -/
noncomputable def cCreate (i : Fin 3) : ZornC := lowerLane (Pi.single i (1 : ℂ))

theorem cRhoPlus_idempotent : zMul cRhoPlus cRhoPlus = cRhoPlus := op1_idempotent

theorem cRhoMinus_idempotent : zMul cRhoMinus cRhoMinus = cRhoMinus := op2_idempotent

theorem cRhoPlus_mul_cRhoMinus : zMul cRhoPlus cRhoMinus = 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [cRhoPlus, cRhoMinus, OP1, OP2, zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · simp [cRhoPlus, cRhoMinus, OP1, OP2, zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · funext i; fin_cases i <;>
      simp [cRhoPlus, cRhoMinus, OP1, OP2, zMul, InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i; fin_cases i <;>
      simp [cRhoPlus, cRhoMinus, OP1, OP2, zMul, InfoGeometry.Canonical.ZornMatrix.cross]

theorem cRhoPlus_add_cRhoMinus : cRhoPlus + cRhoMinus = (1 : ZornC) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [cRhoPlus, cRhoMinus, OP1, OP2]

theorem cAnnihilate_mul_cCreate (i j : Fin 3) :
    zMul (cAnnihilate i) (cCreate j) = if i = j then cRhoPlus else 0 := by
  fin_cases i <;> fin_cases j <;> apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals first
    | (funext k; fin_cases k <;>
        simp [cAnnihilate, cCreate, cRhoPlus, upperLane, lowerLane, OP1, zMul,
          InfoGeometry.Canonical.ZornMatrix.cross])
    | simp [cAnnihilate, cCreate, cRhoPlus, upperLane, lowerLane, OP1, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot]

theorem cCreate_mul_cAnnihilate (i j : Fin 3) :
    zMul (cCreate j) (cAnnihilate i) = if i = j then cRhoMinus else 0 := by
  fin_cases i <;> fin_cases j <;> apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals first
    | (funext k; fin_cases k <;>
        simp [cAnnihilate, cCreate, cRhoMinus, upperLane, lowerLane, OP2, zMul,
          InfoGeometry.Canonical.ZornMatrix.cross])
    | simp [cAnnihilate, cCreate, cRhoMinus, upperLane, lowerLane, OP2, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot]

/-- Complexified split-octonion Peirce CAR anticommutator `{a_i, a_j†} = δ_{ij} • 1`. -/
theorem cCAR_anticommutator (i j : Fin 3) :
    zMul (cAnnihilate i) (cCreate j) + zMul (cCreate j) (cAnnihilate i) =
      if i = j then (1 : ZornC) else 0 := by
  rw [cAnnihilate_mul_cCreate, cCreate_mul_cAnnihilate]
  split_ifs
  · exact cRhoPlus_add_cRhoMinus
  · exact add_zero 0

theorem cAnnihilate_anticommutator_zero (i j : Fin 3) :
    zMul (cAnnihilate i) (cAnnihilate j) + zMul (cAnnihilate j) (cAnnihilate i) = 0 := by
  fin_cases i <;> fin_cases j <;> apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals first
    | (funext k; fin_cases k <;>
        simp [cAnnihilate, upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross])
    | simp [cAnnihilate, upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]

theorem cCreate_anticommutator_zero (i j : Fin 3) :
    zMul (cCreate i) (cCreate j) + zMul (cCreate j) (cCreate i) = 0 := by
  fin_cases i <;> fin_cases j <;> apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals first
    | (funext k; fin_cases k <;>
        simp [cCreate, lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross])
    | simp [cCreate, lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]

private theorem vec3_val_zero {α : Type*} (a b c : α) : ![a, b, c] 0 = a := rfl
private theorem vec3_val_one {α : Type*} (a b c : α) : ![a, b, c] 1 = b := rfl
private theorem vec3_val_two {α : Type*} (a b c : α) : ![a, b, c] 2 = c := rfl

/-- Left-regular multiplication endomorphism `L_X(Y) = zMul X Y` on `ZornMatrix ℂ`. -/
noncomputable def cLeftMul (X : ZornC) : ZornC →ₗ[ℂ] ZornC where
  toFun Y := zMul X Y
  map_add' Y₁ Y₂ := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · dsimp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]; ring
    · dsimp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]; ring
    · funext k; fin_cases k <;>
        simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.vecHead, Matrix.vecTail, vec3_val_two] <;>
        ring
    · funext k; fin_cases k <;>
        simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.vecHead, Matrix.vecTail, vec3_val_two] <;>
        ring
  map_smul' c Y := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · dsimp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]
      simp only [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y,
        Pi.smul_apply, smul_eq_mul]; ring
    · dsimp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]
      simp only [InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y,
        Pi.smul_apply, smul_eq_mul]; ring
    · funext k; fin_cases k <;>
        simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross,
          InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b,
          InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.vecHead, Matrix.vecTail, vec3_val_two] <;>
        ring
    · funext k; fin_cases k <;>
        simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross,
          InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b,
          InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.vecHead, Matrix.vecTail, vec3_val_two] <;>
        ring

private theorem zMul_cAnnihilate_a (i : Fin 3) (Y : ZornC) :
    (zMul (cAnnihilate i) Y).a = Y.y i := by
  fin_cases i <;>
    simp [cAnnihilate, upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]

private theorem zMul_cAnnihilate_b (i : Fin 3) (Y : ZornC) :
    (zMul (cAnnihilate i) Y).b = 0 := by
  simp [cAnnihilate, upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]

private theorem zMul_cAnnihilate_x (i k : Fin 3) (Y : ZornC) :
    (zMul (cAnnihilate i) Y).x k = if k = i then Y.b else 0 := by
  fin_cases i <;> fin_cases k <;>
    simp [cAnnihilate, upperLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross,
      Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]

private theorem zMul_cAnnihilate_y (i k : Fin 3) (Y : ZornC) :
    (zMul (cAnnihilate i) Y).y k =
      InfoGeometry.Canonical.ZornMatrix.cross (Pi.single i (1 : ℂ)) Y.x k := by
  simp [cAnnihilate, upperLane, zMul]

private theorem zMul_cCreate_a (j : Fin 3) (Y : ZornC) :
    (zMul (cCreate j) Y).a = 0 := by
  simp [cCreate, lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]

private theorem zMul_cCreate_b (j : Fin 3) (Y : ZornC) :
    (zMul (cCreate j) Y).b = Y.x j := by
  fin_cases j <;>
    simp [cCreate, lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.dot]

private theorem zMul_cCreate_x (j k : Fin 3) (Y : ZornC) :
    (zMul (cCreate j) Y).x k =
      -InfoGeometry.Canonical.ZornMatrix.cross (Pi.single j (1 : ℂ)) Y.y k := by
  simp [cCreate, lowerLane, zMul]

private theorem zMul_cCreate_y (j k : Fin 3) (Y : ZornC) :
    (zMul (cCreate j) Y).y k = if k = j then Y.a else 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [cCreate, lowerLane, zMul, InfoGeometry.Canonical.ZornMatrix.cross,
      Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]

/-- Associative operator-level CAR `{L_{a_i}, L_{a_j†}} = δ_{ij} • id` on `ZornMatrix ℂ`. -/
theorem cLeftMul_CAR_anticommutator (i j : Fin 3) :
    cLeftMul (cAnnihilate i) ∘ₗ cLeftMul (cCreate j) +
      cLeftMul (cCreate j) ∘ₗ cLeftMul (cAnnihilate i) =
      if i = j then LinearMap.id else 0 := by
  apply LinearMap.ext
  intro Y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cLeftMul, LinearMap.coe_mk, AddHom.coe_mk]
  fin_cases i <;> fin_cases j <;>
    simp only [↓reduceIte, LinearMap.id_apply] <;>
    apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals try (funext k; fin_cases k)
  all_goals
    (simp [Pi.add_apply, Pi.zero_apply,
      zMul_cAnnihilate_a, zMul_cAnnihilate_b, zMul_cAnnihilate_x, zMul_cAnnihilate_y,
      zMul_cCreate_a, zMul_cCreate_b, zMul_cCreate_x, zMul_cCreate_y,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Matrix.vecHead, Matrix.vecTail, Pi.single_apply] <;> try ring)

/-! ### G4: Split-Albert `J₃(𝕆ₛ)` Idempotents, Peirce Projections & 3 Generations -/

open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrixZNamespace
open InfoGeometry.Algebra.Generations

theorem albert_idempotent_sum_one :
    InfoGeometry.Algebra.CubicJordanOs.e₁ +
      InfoGeometry.Algebra.CubicJordanOs.e₂ +
      InfoGeometry.Algebra.CubicJordanOs.e₃ =
      InfoGeometry.Algebra.CubicJordanOs.eOne :=
  InfoGeometry.Algebra.CubicJordanOs.e_sum_one

theorem albert_peirce_projections (X : AlbertMatrix) :
    ((peirce X).diag₁ = traceBilin X AlbertMatrix.e₁ ∧
      (peirce X).diag₂ = traceBilin X AlbertMatrix.e₂ ∧
      (peirce X).diag₃ = traceBilin X AlbertMatrix.e₃) ∧
    ((peirce X).off₁₂ = X.z₃ ∧ (peirce X).off₂₃ = X.z₁ ∧ (peirce X).off₃₁ = X.z₂) :=
  ⟨AlbertMatrix.peirce_diag_proj X, AlbertMatrix.peirce_off_proj X⟩

theorem albert_freudenthal_and_penrose_closure (X : AlbertMatrixZ) :
    adjointQuadZ (adjointQuadZ X) = (normCubicZ X) • X ∧
    (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ
        InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up0
        InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up1 =
      InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down2 ∧
     (∀ i : Fin 3,
       InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ
           (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up i)
           (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up i) =
         InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ ∧
       InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ
           (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down i)
           (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down i) =
         InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ) ∧
     InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.associator
         InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up0
         InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up1
         InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down1 =
       InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up0) := by
  have hp := InfoGeometry.Algebra.CubicJordanPeirce.penrose_global_closure
  exact ⟨freudenthal_identityZ X, hp.1, hp.2.1, hp.2.2.2.2.2⟩

theorem albert_three_generations_table :
    Function.Injective basisFermion ∧
    (threeGenerationTable.map FermionQuantumNumbers.electricCharge).sum = 0 :=
  ⟨basisFermion_injective, three_generation_table_charge_sum_zero⟩

/-! ### G5: Standard Derivation `D_{X,Y}` Normal Form & Peirce Associator `[up_i, dn_j, up_k]` -/

theorem zorn_standard_derivation_normal_form (x y z : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    directCanonicalStanDerMap x y z =
      ((x * y - y * x) * z - z * (x * y - y * x)) -
        3 • ((x * y) * z - x * (y * z)) :=
  directCanonicalStanDerMap_apply_normal_form x y z

theorem zorn_three_bracket_derivation (x y a b : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    splitThreeBracket x y (a * b) =
      splitThreeBracket x y a * b + a * splitThreeBracket x y b :=
  splitThreeBracket_derivation x y a b

/-- Exact integral split-octonion Peirce associator `[up i, down j, up k]` (coefficient `1`,
correcting `T41:3323`'s `1/2` factor; note `associator X Y Z = (XY)Z - X(YZ)`). -/
theorem splitOct_peirce_associator_udu (i j k : Fin 3) :
    InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.associator
        (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up i)
        (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down j)
        (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up k) =
      InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.subZ
        (if i = j then InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up k
          else InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ)
        (if j = k then InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up i
          else InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.zeroZ) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

private theorem zMul_cRhoPlus_cAnnihilate (k : Fin 3) :
    zMul cRhoPlus (cAnnihilate k) = cAnnihilate k := by
  fin_cases k <;> apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals first
    | (funext m; fin_cases m <;>
        simp [cRhoPlus, cAnnihilate, OP1, upperLane, zMul,
          InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail])
    | simp [cRhoPlus, cAnnihilate, OP1, upperLane, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot]

private theorem zMul_cAnnihilate_cRhoMinus (i : Fin 3) :
    zMul (cAnnihilate i) cRhoMinus = cAnnihilate i := by
  fin_cases i <;> apply InfoGeometry.Canonical.ZornMatrix.ext
  all_goals first
    | (funext m; fin_cases m <;>
        simp [cRhoMinus, cAnnihilate, OP2, upperLane, zMul,
          InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail])
    | simp [cRhoMinus, cAnnihilate, OP2, upperLane, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot]

private theorem zMul_zero_left (X : ZornC) : zMul 0 X = 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · funext m; fin_cases m <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross]
  · funext m; fin_cases m <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross]

private theorem zMul_zero_right (X : ZornC) : zMul X 0 = 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot]
  · funext m; fin_cases m <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross]
  · funext m; fin_cases m <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.cross]

/-- Complexified `ZornMatrix ℂ` Peirce associator `[a_i, a_j†, a_k] = δ_{ij} a_k - δ_{jk} a_i`. -/
theorem zorn_peirce_associator_udu (i j k : Fin 3) :
    zMul (zMul (cAnnihilate i) (cCreate j)) (cAnnihilate k) -
      zMul (cAnnihilate i) (zMul (cCreate j) (cAnnihilate k)) =
      (if i = j then cAnnihilate k else 0) - (if j = k then cAnnihilate i else 0) := by
  rw [cAnnihilate_mul_cCreate i j, cCreate_mul_cAnnihilate k j]
  by_cases hij : i = j <;> by_cases hjk : j = k
  · have hkj : k = j := hjk.symm
    rw [if_pos hij, if_pos hkj, if_pos hij, if_pos hjk,
      zMul_cRhoPlus_cAnnihilate, zMul_cAnnihilate_cRhoMinus]
  · have hkj : k ≠ j := fun h => hjk h.symm
    rw [if_pos hij, if_neg hkj, if_pos hij, if_neg hjk,
      zMul_cRhoPlus_cAnnihilate, zMul_zero_right, sub_zero]
  · have hkj : k = j := hjk.symm
    rw [if_neg hij, if_pos hkj, if_neg hij, if_pos hjk,
      zMul_zero_left, zMul_cAnnihilate_cRhoMinus, zero_sub]
  · have hkj : k ≠ j := fun h => hjk h.symm
    rw [if_neg hij, if_neg hkj, if_neg hij, if_neg hjk,
      zMul_zero_left, zMul_zero_right]

end SplitOctonionPeirceAndAlbert

/-! ## Section H1, H2, H4, H6: Para-Dolbeault Bigrading, Kasteleyn–Dirac `D_χ` & Pfaffian–Det -/

section ParaDolbeaultAndKasteleynDirac

open InfoGeometry.Canonical.PlabicDiracKrein
open InfoGeometry.Canonical.FinitePlabicKasteleyn

/-- Finite algebraic Para-Dolbeault bigraded complex over an `ℝ`-module `E`. -/
structure ParaDolbeaultComplex (E : Type*) [AddCommGroup E] [Module ℝ E] where
  dPlus : ℤ → ℤ → (E →ₗ[ℝ] E)
  dMinus : ℤ → ℤ → (E →ₗ[ℝ] E)
  deltaPlus : ℤ → ℤ → (E →ₗ[ℝ] E)
  deltaMinus : ℤ → ℤ → (E →ₗ[ℝ] E)

namespace ParaDolbeaultComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Total bigraded space `ℤ → ℤ → E`. -/
abbrev TotalForm (E : Type*) := ℤ → ℤ → E

/-- Single-bidegree injection `(p₀, q₀, x) ↦ TotalForm E`. -/
def singleForm (p₀ q₀ : ℤ) (x : E) : TotalForm E :=
  fun p q => if p = p₀ ∧ q = q₀ then x else 0

omit [Module ℝ E] in
@[simp] theorem singleForm_self (p₀ q₀ : ℤ) (x : E) :
    singleForm p₀ q₀ x p₀ q₀ = x := by
  simp [singleForm]

/-- Total operator induced by `dPlus` (bidegree `(+1, 0)`). -/
def totalDPlus (C : ParaDolbeaultComplex E) : TotalForm E →ₗ[ℝ] TotalForm E where
  toFun ω p q := C.dPlus (p - 1) q (ω (p - 1) q)
  map_add' ω₁ ω₂ := by funext p q; simp
  map_smul' r ω := by funext p q; simp

/-- Total operator induced by `dMinus` (bidegree `(0, +1)`). -/
def totalDMinus (C : ParaDolbeaultComplex E) : TotalForm E →ₗ[ℝ] TotalForm E where
  toFun ω p q := C.dMinus p (q - 1) (ω p (q - 1))
  map_add' ω₁ ω₂ := by funext p q; simp
  map_smul' r ω := by funext p q; simp

/-- Total operator induced by `deltaPlus` (bidegree `(-1, 0)`). -/
def totalDeltaPlus (C : ParaDolbeaultComplex E) : TotalForm E →ₗ[ℝ] TotalForm E where
  toFun ω p q := C.deltaPlus (p + 1) q (ω (p + 1) q)
  map_add' ω₁ ω₂ := by funext p q; simp
  map_smul' r ω := by funext p q; simp

/-- Total operator induced by `deltaMinus` (bidegree `(0, -1)`). -/
def totalDeltaMinus (C : ParaDolbeaultComplex E) : TotalForm E →ₗ[ℝ] TotalForm E where
  toFun ω p q := C.deltaMinus p (q + 1) (ω p (q + 1))
  map_add' ω₁ ω₂ := by funext p q; simp
  map_smul' r ω := by funext p q; simp

theorem totalDPlus_singleForm (C : ParaDolbeaultComplex E) (p₀ q₀ : ℤ) (x : E) (p q : ℤ) :
    C.totalDPlus (singleForm p₀ q₀ x) p q =
      if p = p₀ + 1 ∧ q = q₀ then C.dPlus p₀ q₀ x else 0 := by
  dsimp [totalDPlus, singleForm]
  by_cases h : p = p₀ + 1 ∧ q = q₀
  · simp [h]
  · have h' : ¬ (p - 1 = p₀ ∧ q = q₀) := fun ⟨h1, h2⟩ => h ⟨by omega, h2⟩
    simp [h, h']

theorem totalDMinus_singleForm (C : ParaDolbeaultComplex E) (p₀ q₀ : ℤ) (x : E) (p q : ℤ) :
    C.totalDMinus (singleForm p₀ q₀ x) p q =
      if p = p₀ ∧ q = q₀ + 1 then C.dMinus p₀ q₀ x else 0 := by
  dsimp [totalDMinus, singleForm]
  by_cases h : p = p₀ ∧ q = q₀ + 1
  · simp [h]
  · have h' : ¬ (p = p₀ ∧ q - 1 = q₀) := fun ⟨h1, h2⟩ => h ⟨h1, by omega⟩
    simp [h, h']

theorem totalDeltaPlus_singleForm (C : ParaDolbeaultComplex E) (p₀ q₀ : ℤ) (x : E) (p q : ℤ) :
    C.totalDeltaPlus (singleForm p₀ q₀ x) p q =
      if p = p₀ - 1 ∧ q = q₀ then C.deltaPlus p₀ q₀ x else 0 := by
  dsimp [totalDeltaPlus, singleForm]
  by_cases h : p = p₀ - 1 ∧ q = q₀
  · simp [h]
  · have h' : ¬ (p + 1 = p₀ ∧ q = q₀) := fun ⟨h1, h2⟩ => h ⟨by omega, h2⟩
    simp [h, h']

theorem totalDeltaMinus_singleForm (C : ParaDolbeaultComplex E) (p₀ q₀ : ℤ) (x : E) (p q : ℤ) :
    C.totalDeltaMinus (singleForm p₀ q₀ x) p q =
      if p = p₀ ∧ q = q₀ - 1 then C.deltaMinus p₀ q₀ x else 0 := by
  dsimp [totalDeltaMinus, singleForm]
  by_cases h : p = p₀ ∧ q = q₀ - 1
  · simp [h]
  · have h' : ¬ (p = p₀ ∧ q + 1 = q₀) := fun ⟨h1, h2⟩ => h ⟨h1, by omega⟩
    simp [h, h']

/-- Bidegree separation for `(d₊, d₋)`: `(d₊ + d₋)² = 0` forces `d₊² = 0`, `d₋² = 0`,
and `{d₊, d₋} = 0`. -/
theorem totalD_split_sq_zero (C : ParaDolbeaultComplex E)
    (hsq : (C.totalDPlus + C.totalDMinus) ∘ₗ (C.totalDPlus + C.totalDMinus) = 0) :
    C.totalDPlus ∘ₗ C.totalDPlus = 0 ∧
    C.totalDMinus ∘ₗ C.totalDMinus = 0 ∧
    C.totalDPlus ∘ₗ C.totalDMinus + C.totalDMinus ∘ₗ C.totalDPlus = 0 := by
  have component_eq : ∀ p₀ q₀ : ℤ, ∀ x : E,
      C.dPlus (p₀ + 1) q₀ (C.dPlus p₀ q₀ x) = 0 ∧
      C.dMinus p₀ (q₀ + 1) (C.dMinus p₀ q₀ x) = 0 ∧
      C.dPlus p₀ (q₀ + 1) (C.dMinus p₀ q₀ x) + C.dMinus (p₀ + 1) q₀ (C.dPlus p₀ q₀ x) = 0 := by
    intro p₀ q₀ x
    have eval_at : ∀ p q : ℤ,
        (C.totalDPlus (C.totalDPlus (singleForm p₀ q₀ x)) p q +
          C.totalDPlus (C.totalDMinus (singleForm p₀ q₀ x)) p q) +
        (C.totalDMinus (C.totalDPlus (singleForm p₀ q₀ x)) p q +
          C.totalDMinus (C.totalDMinus (singleForm p₀ q₀ x)) p q) = 0 := by
      intro p q
      have h0 := congrArg (fun F : TotalForm E →ₗ[ℝ] TotalForm E => F (singleForm p₀ q₀ x) p q) hsq
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Pi.add_apply,
        LinearMap.zero_apply, Pi.zero_apply] at h0
      abel_nf at h0 ⊢
      exact h0
    refine ⟨?_, ?_, ?_⟩
    · have h20 := eval_at (p₀ + 2) q₀
      dsimp only [totalDPlus, totalDMinus, singleForm, LinearMap.coe_mk, AddHom.coe_mk] at h20
      have h1 : (p₀ + 2 - 1 - 1 = p₀ ∧ q₀ = q₀) := ⟨by omega, rfl⟩
      have h2 : ¬ (p₀ + 2 - 1 = p₀ ∧ q₀ - 1 = q₀) := by omega
      have h4 : ¬ (p₀ + 2 = p₀ ∧ q₀ - 1 - 1 = q₀) := by omega
      simp only [h1, h2, h4, and_self, ↓reduceIte, map_zero, add_zero] at h20
      simpa only [show p₀ + 2 - 1 = p₀ + 1 by omega, show p₀ + 2 - 1 - 1 = p₀ by omega] using h20
    · have h02 := eval_at p₀ (q₀ + 2)
      dsimp only [totalDPlus, totalDMinus, singleForm, LinearMap.coe_mk, AddHom.coe_mk] at h02
      have h1 : ¬ (p₀ - 1 - 1 = p₀ ∧ q₀ + 2 = q₀) := by omega
      have h2 : ¬ (p₀ - 1 = p₀ ∧ q₀ + 2 - 1 = q₀) := by omega
      have h4 : (p₀ = p₀ ∧ q₀ + 2 - 1 - 1 = q₀) := ⟨rfl, by omega⟩
      simp only [h1, h2, h4, and_self, ↓reduceIte, map_zero, add_zero, zero_add] at h02
      simpa only [show q₀ + 2 - 1 = q₀ + 1 by omega, show q₀ + 2 - 1 - 1 = q₀ by omega] using h02
    · have h11 := eval_at (p₀ + 1) (q₀ + 1)
      dsimp only [totalDPlus, totalDMinus, singleForm, LinearMap.coe_mk, AddHom.coe_mk] at h11
      have h1 : ¬ (p₀ + 1 - 1 - 1 = p₀ ∧ q₀ + 1 = q₀) := by omega
      have h2 : (p₀ + 1 - 1 = p₀ ∧ q₀ + 1 - 1 = q₀) := ⟨by omega, by omega⟩
      have h4 : ¬ (p₀ + 1 = p₀ ∧ q₀ + 1 - 1 - 1 = q₀) := by omega
      simp only [h2, and_self, ↓reduceIte] at h11
      simp only [show ¬ (p₀ - 1 = p₀ ∧ q₀ + 1 = q₀) by omega,
        show ¬ (p₀ + 1 = p₀ ∧ q₀ - 1 = q₀) by omega,
        ↓reduceIte, map_zero, add_zero, zero_add] at h11
      simpa only [show p₀ + 1 - 1 = p₀ by omega, show q₀ + 1 - 1 = q₀ by omega] using h11
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext; intro ω; funext p q
    have hc := (component_eq (p - 2) q (ω (p - 2) q)).1
    dsimp [totalDPlus]
    simpa [show p - 2 + 1 = p - 1 by omega, show p - 1 - 1 = p - 2 by omega] using hc
  · apply LinearMap.ext; intro ω; funext p q
    have hc := (component_eq p (q - 2) (ω p (q - 2))).2.1
    dsimp [totalDMinus]
    simpa [show q - 2 + 1 = q - 1 by omega, show q - 1 - 1 = q - 2 by omega] using hc
  · apply LinearMap.ext; intro ω; funext p q
    have hc := (component_eq (p - 1) (q - 1) (ω (p - 1) (q - 1))).2.2
    dsimp [totalDPlus, totalDMinus]
    simpa [show p - 1 + 1 = p by omega, show q - 1 + 1 = q by omega] using hc

/-- Bidegree separation for `(δ₊, δ₋)`: `(δ₊ + δ₋)² = 0` forces `δ₊² = 0`, `δ₋² = 0`,
and `{δ₊, δ₋} = 0`. -/
theorem totalDelta_split_sq_zero (C : ParaDolbeaultComplex E)
    (hsq : (C.totalDeltaPlus + C.totalDeltaMinus) ∘ₗ (C.totalDeltaPlus + C.totalDeltaMinus) = 0) :
    C.totalDeltaPlus ∘ₗ C.totalDeltaPlus = 0 ∧
    C.totalDeltaMinus ∘ₗ C.totalDeltaMinus = 0 ∧
    C.totalDeltaPlus ∘ₗ C.totalDeltaMinus + C.totalDeltaMinus ∘ₗ C.totalDeltaPlus = 0 := by
  have component_eq : ∀ p₀ q₀ : ℤ, ∀ x : E,
      C.deltaPlus (p₀ - 1) q₀ (C.deltaPlus p₀ q₀ x) = 0 ∧
      C.deltaMinus p₀ (q₀ - 1) (C.deltaMinus p₀ q₀ x) = 0 ∧
      C.deltaPlus p₀ (q₀ - 1) (C.deltaMinus p₀ q₀ x) +
        C.deltaMinus (p₀ - 1) q₀ (C.deltaPlus p₀ q₀ x) = 0 := by
    intro p₀ q₀ x
    have eval_at : ∀ p q : ℤ,
        (C.totalDeltaPlus (C.totalDeltaPlus (singleForm p₀ q₀ x)) p q +
          C.totalDeltaPlus (C.totalDeltaMinus (singleForm p₀ q₀ x)) p q) +
        (C.totalDeltaMinus (C.totalDeltaPlus (singleForm p₀ q₀ x)) p q +
          C.totalDeltaMinus (C.totalDeltaMinus (singleForm p₀ q₀ x)) p q) = 0 := by
      intro p q
      have h0 := congrArg (fun F : TotalForm E →ₗ[ℝ] TotalForm E => F (singleForm p₀ q₀ x) p q) hsq
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Pi.add_apply,
        LinearMap.zero_apply, Pi.zero_apply] at h0
      abel_nf at h0 ⊢
      exact h0
    refine ⟨?_, ?_, ?_⟩
    · have h20 := eval_at (p₀ - 2) q₀
      dsimp only [totalDeltaPlus, totalDeltaMinus, singleForm, LinearMap.coe_mk, AddHom.coe_mk] at h20
      have h1 : (p₀ - 2 + 1 + 1 = p₀ ∧ q₀ = q₀) := ⟨by omega, rfl⟩
      have h2 : ¬ (p₀ - 2 + 1 = p₀ ∧ q₀ + 1 = q₀) := by omega
      have h4 : ¬ (p₀ - 2 = p₀ ∧ q₀ + 1 + 1 = q₀) := by omega
      simp only [h1, h2, h4, and_self, ↓reduceIte, map_zero, add_zero] at h20
      simpa only [show p₀ - 2 + 1 = p₀ - 1 by omega, show p₀ - 2 + 1 + 1 = p₀ by omega] using h20
    · have h02 := eval_at p₀ (q₀ - 2)
      dsimp only [totalDeltaPlus, totalDeltaMinus, singleForm, LinearMap.coe_mk, AddHom.coe_mk] at h02
      have h1 : ¬ (p₀ + 1 + 1 = p₀ ∧ q₀ - 2 = q₀) := by omega
      have h2 : ¬ (p₀ + 1 = p₀ ∧ q₀ - 2 + 1 = q₀) := by omega
      have h4 : (p₀ = p₀ ∧ q₀ - 2 + 1 + 1 = q₀) := ⟨rfl, by omega⟩
      simp only [h1, h2, h4, and_self, ↓reduceIte, map_zero, add_zero, zero_add] at h02
      simpa only [show q₀ - 2 + 1 = q₀ - 1 by omega, show q₀ - 2 + 1 + 1 = q₀ by omega] using h02
    · have h11 := eval_at (p₀ - 1) (q₀ - 1)
      dsimp only [totalDeltaPlus, totalDeltaMinus, singleForm, LinearMap.coe_mk, AddHom.coe_mk] at h11
      have h1 : ¬ (p₀ - 1 + 1 + 1 = p₀ ∧ q₀ - 1 = q₀) := by omega
      have h2 : (p₀ - 1 + 1 = p₀ ∧ q₀ - 1 + 1 = q₀) := ⟨by omega, by omega⟩
      have h4 : ¬ (p₀ - 1 = p₀ ∧ q₀ - 1 + 1 + 1 = q₀) := by omega
      simp only [h2, and_self, ↓reduceIte] at h11
      simp only [show ¬ (p₀ + 1 = p₀ ∧ q₀ - 1 = q₀) by omega,
        show ¬ (p₀ - 1 = p₀ ∧ q₀ + 1 = q₀) by omega,
        ↓reduceIte, map_zero, add_zero, zero_add] at h11
      simpa only [show p₀ - 1 + 1 = p₀ by omega, show q₀ - 1 + 1 = q₀ by omega] using h11
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext; intro ω; funext p q
    have hc := (component_eq (p + 2) q (ω (p + 2) q)).1
    dsimp [totalDeltaPlus]
    simpa [show p + 2 - 1 = p + 1 by omega, show p + 1 + 1 = p + 2 by omega] using hc
  · apply LinearMap.ext; intro ω; funext p q
    have hc := (component_eq p (q + 2) (ω p (q + 2))).2.1
    dsimp [totalDeltaMinus]
    simpa [show q + 2 - 1 = q + 1 by omega, show q + 1 + 1 = q + 2 by omega] using hc
  · apply LinearMap.ext; intro ω; funext p q
    have hc := (component_eq (p + 1) (q + 1) (ω (p + 1) (q + 1))).2.2
    dsimp [totalDeltaPlus, totalDeltaMinus]
    simpa [show p + 1 - 1 = p by omega, show q + 1 - 1 = q by omega] using hc

end ParaDolbeaultComplex

/-- Chiral grading matrix `Γ = diag(1, -1)` on any `ℝ`-module `V`. -/
def chiralGamma (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (Module.End ℝ V) :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Chiral Hodge–Dirac block operator `𝔻_χ = [[0, D_-], [D_+, 0]]` on `V ⊕ V`. -/
def chiralHodgeDirac {V : Type*} [AddCommGroup V] [Module ℝ V]
    (DPlus DMinus : Module.End ℝ V) :
    Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (Module.End ℝ V) :=
  Matrix.fromBlocks 0 (Matrix.of fun _ _ => DMinus) (Matrix.of fun _ _ => DPlus) 0

theorem chiralHodgeDirac_anticomm_gamma {V : Type*} [AddCommGroup V] [Module ℝ V]
    (DPlus DMinus : Module.End ℝ V) :
    chiralHodgeDirac DPlus DMinus * chiralGamma V +
      chiralGamma V * chiralHodgeDirac DPlus DMinus = 0 := by
  ext (i | i) (j | j) <;>
    simp [chiralHodgeDirac, chiralGamma, Matrix.fromBlocks_multiply]

theorem chiralHodgeDirac_sq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (DPlus DMinus : Module.End ℝ V) :
    chiralHodgeDirac DPlus DMinus * chiralHodgeDirac DPlus DMinus =
      Matrix.fromBlocks (Matrix.of fun _ _ => DMinus * DPlus) 0 0
        (Matrix.of fun _ _ => DPlus * DMinus) := by
  ext (i | i) (j | j) <;>
    simp [chiralHodgeDirac, Matrix.mul_apply]

/-- Concrete nonzero `Fin 2 × Fin 2 → ℝ` witness of the Para-Dolbeault bigraded complex. -/
def paraDolbeaultWitness : ParaDolbeaultComplex ℝ where
  dPlus p q := if p = 0 ∧ (q = 0 ∨ q = 1) then LinearMap.id else 0
  dMinus p q := if q = 0 ∧ (p = 0 ∨ p = 1) then (if p = 0 then LinearMap.id else -LinearMap.id) else 0
  deltaPlus p q := if p = 1 ∧ (q = 0 ∨ q = 1) then LinearMap.id else 0
  deltaMinus p q := if q = 1 ∧ (p = 0 ∨ p = 1) then (if p = 0 then LinearMap.id else -LinearMap.id) else 0

/-- Linear embedding of concrete `2 × 2` bigraded forms `Fin 2 × Fin 2 → ℝ` into
`ParaDolbeaultComplex.TotalForm ℝ`. -/
def fin22ToTotalForm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] ParaDolbeaultComplex.TotalForm ℝ where
  toFun f p q :=
    if hp : (0 ≤ p ∧ p < 2) then
      if hq : (0 ≤ q ∧ q < 2) then f (⟨p.toNat, by omega⟩, ⟨q.toNat, by omega⟩) else 0
    else 0
  map_add' f g := by
    funext p q
    by_cases hp : 0 ≤ p ∧ p < 2 <;> by_cases hq : 0 ≤ q ∧ q < 2
    · simp only [eq_true hp, eq_true hq, ↓reduceDIte, Pi.add_apply]
    · simp only [eq_true hp, eq_false hq, ↓reduceDIte, Pi.add_apply, add_zero]
    · simp only [eq_false hp, ↓reduceDIte, Pi.add_apply, add_zero]
    · simp only [eq_false hp, ↓reduceDIte, Pi.add_apply, add_zero]
  map_smul' r f := by
    funext p q
    by_cases hp : 0 ≤ p ∧ p < 2 <;> by_cases hq : 0 ≤ q ∧ q < 2
    · simp only [eq_true hp, eq_true hq, ↓reduceDIte, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · simp only [eq_true hp, eq_false hq, ↓reduceDIte, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, mul_zero]
    · simp only [eq_false hp, ↓reduceDIte, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_zero]
    · simp only [eq_false hp, ↓reduceDIte, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_zero]

theorem paraDolbeaultWitness_d_sq_zero :
    (paraDolbeaultWitness.totalDPlus + paraDolbeaultWitness.totalDMinus) ∘ₗ
      (paraDolbeaultWitness.totalDPlus + paraDolbeaultWitness.totalDMinus) = 0 := by
  apply LinearMap.ext; intro ω; funext p q
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Pi.add_apply,
    ParaDolbeaultComplex.totalDPlus, ParaDolbeaultComplex.totalDMinus,
    paraDolbeaultWitness, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  split_ifs <;> simp_all <;> try omega

theorem paraDolbeaultWitness_delta_sq_zero :
    (paraDolbeaultWitness.totalDeltaPlus + paraDolbeaultWitness.totalDeltaMinus) ∘ₗ
      (paraDolbeaultWitness.totalDeltaPlus + paraDolbeaultWitness.totalDeltaMinus) = 0 := by
  apply LinearMap.ext; intro ω; funext p q
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Pi.add_apply,
    ParaDolbeaultComplex.totalDeltaPlus, ParaDolbeaultComplex.totalDeltaMinus,
    paraDolbeaultWitness, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  split_ifs <;> simp_all

theorem paraDolbeaultWitness_nonzero :
    paraDolbeaultWitness.totalDPlus (fin22ToTotalForm (fun pq => if pq = (0, 0) then 1 else 0)) 1 0 = 1 := by
  simp [ParaDolbeaultComplex.totalDPlus, paraDolbeaultWitness, fin22ToTotalForm]

theorem paraDolbeaultWitness_chiral_dirac_props :
    let DPlus := paraDolbeaultWitness.totalDPlus + paraDolbeaultWitness.totalDeltaMinus
    let DMinus := paraDolbeaultWitness.totalDMinus + paraDolbeaultWitness.totalDeltaPlus
    chiralHodgeDirac DPlus DMinus * chiralGamma (ParaDolbeaultComplex.TotalForm ℝ) +
      chiralGamma (ParaDolbeaultComplex.TotalForm ℝ) * chiralHodgeDirac DPlus DMinus = 0 ∧
    paraDolbeaultWitness.totalDPlus ∘ₗ paraDolbeaultWitness.totalDPlus = 0 ∧
    paraDolbeaultWitness.totalDMinus ∘ₗ paraDolbeaultWitness.totalDMinus = 0 ∧
    paraDolbeaultWitness.totalDPlus ∘ₗ paraDolbeaultWitness.totalDMinus +
      paraDolbeaultWitness.totalDMinus ∘ₗ paraDolbeaultWitness.totalDPlus = 0 := by
  have hd := ParaDolbeaultComplex.totalD_split_sq_zero paraDolbeaultWitness paraDolbeaultWitness_d_sq_zero
  exact ⟨chiralHodgeDirac_anticomm_gamma _ _, hd.1, hd.2.1, hd.2.2⟩

/-! ### H2 & H4: Kasteleyn–Dirac `𝒟_χ`, Krein Supertrace, and Index -/

section KasteleynDirac

variable {VB VW : Type*} [Fintype VB] [Fintype VW] [DecidableEq VB] [DecidableEq VW]

omit [DecidableEq VB] [DecidableEq VW] in
/-- Gram trace cyclicity `Tr(Kᴴ K) = Tr(K Kᴴ)` over any commutative star-ring. -/
theorem kasteleyn_gram_trace_eq {R : Type*} [CommRing R] [StarRing R] (K : Matrix VW VB R) :
    Matrix.trace (Kᴴ * K) = Matrix.trace (K * Kᴴ) :=
  Matrix.trace_mul_comm Kᴴ K

/-- Krein supertrace `sTr_K(M) := Tr(η M)` with `η = diag(1, -1)`. -/
def kreinSupertrace {R : Type*} [Ring R] [StarRing R]
    (M : Matrix (VB ⊕ VW) (VB ⊕ VW) R) : R :=
  Matrix.trace ((kreinSignature : Matrix (VB ⊕ VW) (VB ⊕ VW) R) * M)

private theorem trace_fromBlocks {m n R : Type*} [Fintype m] [Fintype n] [AddCommMonoid R]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem kreinSupertrace_diracDHK_eq_zero {R : Type*} [Ring R] [StarRing R]
    (K : Matrix VW VB R) :
    kreinSupertrace (diracDHK K) = 0 := by
  unfold kreinSupertrace
  have hmul : (kreinSignature : Matrix (VB ⊕ VW) (VB ⊕ VW) R) * diracDHK K =
      Matrix.fromBlocks 0 K.conjTranspose (-K) 0 := by
    ext (i | i) (j | j) <;>
      simp [kreinSignature, diracDHK, Matrix.fromBlocks_multiply]
  rw [hmul, trace_fromBlocks]
  simp

theorem kreinSupertrace_diracDHK_sq_eq_zero {R : Type*} [CommRing R] [StarRing R]
    (K : Matrix VW VB R) :
    kreinSupertrace (diracDHK K * diracDHK K) = 0 := by
  unfold kreinSupertrace
  rw [diracDHK_sq]
  have hmul : (kreinSignature : Matrix (VB ⊕ VW) (VB ⊕ VW) R) *
      Matrix.fromBlocks (K.conjTranspose * K) 0 0 (K * K.conjTranspose) =
      Matrix.fromBlocks (K.conjTranspose * K) 0 0 (-(K * K.conjTranspose)) := by
    ext (i | i) (j | j) <;>
      simp [kreinSignature, Matrix.fromBlocks_multiply]
  rw [hmul, trace_fromBlocks, Matrix.trace_neg]
  rw [kasteleyn_gram_trace_eq K, add_neg_cancel]

theorem kreinSupertrace_one_eq_sub {R : Type*} [Ring R] [StarRing R] :
    kreinSupertrace (1 : Matrix (VB ⊕ VW) (VB ⊕ VW) R) =
      (Fintype.card VB : R) - (Fintype.card VW : R) := by
  unfold kreinSupertrace
  rw [mul_one]
  change Matrix.trace (Matrix.fromBlocks (1 : Matrix VB VB R) 0 0 (-1 : Matrix VW VW R)) = _
  rw [trace_fromBlocks, Matrix.trace_neg, Matrix.trace_one, Matrix.trace_one, sub_eq_add_neg]

theorem kreinSupertrace_one_eq_zero_of_balanced {R : Type*} [Ring R] [StarRing R]
    (hbal : Fintype.card VB = Fintype.card VW) :
    kreinSupertrace (1 : Matrix (VB ⊕ VW) (VB ⊕ VW) R) = 0 := by
  rw [kreinSupertrace_one_eq_sub, hbal, sub_self]

/-- Algebraic index theorem for bipartite Kasteleyn–Dirac `diracDHK K`:
`dim ker K - dim ker Kᴴ = N_circ - N_bullet` (here `VB = Fin N_circ`, `VW = Fin N_bullet`). -/
theorem kasteleyn_dirac_index {N_bullet N_circ : ℕ}
    (K : Matrix (Fin N_bullet) (Fin N_circ) ℂ) :
    (Module.finrank ℂ (LinearMap.ker K.mulVecLin) : ℤ) -
      (Module.finrank ℂ (LinearMap.ker Kᴴ.mulVecLin) : ℤ) =
      (N_circ : ℤ) - (N_bullet : ℤ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker Kᴴ.mulVecLin
  have hr1 : Module.finrank ℂ (LinearMap.range K.mulVecLin) = K.rank := rfl
  have hr2 : Module.finrank ℂ (LinearMap.range Kᴴ.mulVecLin) = Kᴴ.rank := rfl
  have hrk : Kᴴ.rank = K.rank := Matrix.rank_conjTranspose K
  rw [hr1] at h1
  rw [hr2, hrk] at h2
  simp only [Module.finrank_pi, Fintype.card_fin] at h1 h2
  omega

/-- Kasteleyn `edgeSumDirac` linkage for `FinitePlabicGraph`. -/
theorem edgeSumDirac_krein_index {G : FinitePlabicGraph}
    (S : KasteleynSigning G) (weight : G.Edge → ℂ) :
    kreinSupertrace (edgeSumDirac S weight) = 0 ∧
    kreinSupertrace (edgeSumDirac S weight * edgeSumDirac S weight) = 0 ∧
    kreinSupertrace (1 : Matrix (G.Black ⊕ G.White) (G.Black ⊕ G.White) ℂ) =
      (Fintype.card G.Black : ℂ) - (Fintype.card G.White : ℂ) :=
  ⟨kreinSupertrace_diracDHK_eq_zero _,
   kreinSupertrace_diracDHK_sq_eq_zero _,
   kreinSupertrace_one_eq_sub⟩

end KasteleynDirac

/-! ### H6: Skew-Block Pfaffian–Determinant Identity -/

section SkewBlockDeterminant

/-- `2n × 2n` skew-block matrix `[[0, K], [-Kᵀ, 0]]` over any `[CommRing R]`. -/
def skewBlock {n : ℕ} {R : Type*} [CommRing R] (K : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks 0 K (-Kᵀ) 0

theorem skewBlock_transpose_eq_neg {n : ℕ} {R : Type*} [CommRing R]
    (K : Matrix (Fin n) (Fin n) R) :
    (skewBlock K)ᵀ = -skewBlock K := by
  ext (i | i) (j | j) <;>
    simp [skewBlock, Matrix.fromBlocks_transpose]

/-- Exact skew-block determinant identity `det [[0, K], [-Kᵀ, 0]] = (det K)^2` over any
`[CommRing R]` (with `+1` sign, avoiding singular odd-block Berezinian formulas). -/
theorem det_skewBlock_eq_det_sq {n : ℕ} {R : Type*} [CommRing R]
    (K : Matrix (Fin n) (Fin n) R) :
    Matrix.det (skewBlock K) = (Matrix.det K) ^ 2 := by
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 0 (-1) 1 0
  let L : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 1 0 (-1) 1
  let U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 1 1 0 1
  have hJ_mul : L * U * J = Matrix.fromBlocks 1 (-1) 0 1 := by
    ext (i | i) (j | j) <;>
      simp [L, U, J, Matrix.fromBlocks_multiply]
  have hdetL : Matrix.det L = 1 := by
    simp [L, Matrix.det_fromBlocks_zero₁₂]
  have hdetU : Matrix.det U = 1 := by
    simp [U, Matrix.det_fromBlocks_zero₂₁]
  have hdetR : Matrix.det
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (-1) 0 (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    simp [Matrix.det_fromBlocks_zero₂₁]
  have hdetJ : Matrix.det J = 1 := by
    have h := congrArg Matrix.det hJ_mul
    rw [Matrix.det_mul, Matrix.det_mul, hdetL, hdetU, hdetR, one_mul, one_mul] at h
    exact h
  have hprod : skewBlock K * J = Matrix.fromBlocks K 0 0 Kᵀ := by
    ext (i | i) (j | j) <;>
      simp [skewBlock, J, Matrix.fromBlocks_multiply]
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hdetJ, mul_one, Matrix.det_fromBlocks_zero₁₂, Matrix.det_transpose, ← pow_two] at hdet
  exact hdet

end SkewBlockDeterminant

end ParaDolbeaultAndKasteleynDirac

end InfoGeometry.Quantum.ThreeQubitPauliHexagonShear
