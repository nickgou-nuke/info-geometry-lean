import Mathlib.Tactic
import InfoGeometry.Algebra.CPTComplexStructure
import InfoGeometry.OperatorAlgebra.CliffordCAR

/-!
# Split Clifford Realization

Finite algebraic Clifford identities used by the arithmetic split-Clifford
lane.  This file proves only algebraic identities in the repo's `Cl11Atom`
surface and the finite CAR layer.  Analytic Hilbert-Polya/self-adjointness
claims are deliberately not asserted here.
-/

open InfoGeometry.Algebra.CPT
open InfoGeometry.OperatorAlgebra.CliffordCAR

noncomputable section

namespace InfoGeometry.Arithmetic.SplitCliffordRealization

universe uK

variable {K : Type*} [Ring K] [Algebra ℝ K] (atom : Cl11Atom K)
variable (hAtom : Cl11AtomLaws atom)
include hAtom

/-! ## Euler/chirality identities -/

omit [Algebra ℝ K] in
theorem euler_anticommutes_r0 :
    EulerOperator atom * atom.r0 = -(atom.r0 * EulerOperator atom) := by
  dsimp [EulerOperator, ComplexStructure]
  have hanti : atom.r5 * atom.r0 = -(atom.r0 * atom.r5) := by
    rw [hAtom.2.2, neg_neg]
  calc
    (atom.r0 * atom.r5) * atom.r0
        = atom.r0 * (atom.r5 * atom.r0) := by noncomm_ring
    _ = atom.r0 * (-(atom.r0 * atom.r5)) := by rw [hanti]
    _ = -(atom.r0 * (atom.r0 * atom.r5)) := by noncomm_ring

omit [Algebra ℝ K] in
theorem euler_anticommutes_r5 :
    EulerOperator atom * atom.r5 = -(atom.r5 * EulerOperator atom) := by
  dsimp [EulerOperator, ComplexStructure]
  have hanti : atom.r5 * atom.r0 = -(atom.r0 * atom.r5) := by
    rw [hAtom.2.2, neg_neg]
  have hright : atom.r5 * (atom.r0 * atom.r5) = atom.r0 := by
    calc
      atom.r5 * (atom.r0 * atom.r5)
          = (atom.r5 * atom.r0) * atom.r5 := by noncomm_ring
      _ = (-(atom.r0 * atom.r5)) * atom.r5 := by rw [hanti]
      _ = -(atom.r0 * (atom.r5 * atom.r5)) := by noncomm_ring
          _ = -(atom.r0 * (-1)) := by rw [hAtom.2.1]
      _ = atom.r0 := by noncomm_ring
  calc
    (atom.r0 * atom.r5) * atom.r5
        = atom.r0 * (atom.r5 * atom.r5) := by noncomm_ring
    _ = atom.r0 * (-1) := by rw [hAtom.2.1]
    _ = -atom.r0 := by noncomm_ring
    _ = -(atom.r5 * (atom.r0 * atom.r5)) := by rw [hright]

omit [Algebra ℝ K] in
theorem euler_anticommutes_J :
    EulerOperator atom * ComplexStructure atom =
      -(ComplexStructure atom * EulerOperator atom) := by
  simpa [ComplexStructure] using euler_anticommutes_r5 atom hAtom

theorem euler_anticommutes_linear_combination (a b : ℝ) :
    EulerOperator atom * (a • atom.r0 + b • atom.r5) =
      -((a • atom.r0 + b • atom.r5) * EulerOperator atom) := by
  calc
    EulerOperator atom * (a • atom.r0 + b • atom.r5)
        = a • (EulerOperator atom * atom.r0) +
            b • (EulerOperator atom * atom.r5) := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]
    _ = a • (-(atom.r0 * EulerOperator atom)) +
            b • (-(atom.r5 * EulerOperator atom)) := by
      rw [euler_anticommutes_r0 atom hAtom, euler_anticommutes_r5 atom hAtom]
    _ = -(a • (atom.r0 * EulerOperator atom) +
            b • (atom.r5 * EulerOperator atom)) := by
      rw [smul_neg, smul_neg]
      abel
    _ = -((a • atom.r0) * EulerOperator atom +
            (b • atom.r5) * EulerOperator atom) := by
      simp
    _ = -((a • atom.r0 + b • atom.r5) * EulerOperator atom) := by
      rw [add_mul]

/-! ## Chiral projectors -/

theorem chiral_sheets_orthogonal_rev :
    chiralProjectorMinus atom * chiralProjectorPlus atom = 0 := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  calc
    ((1 / 2 : ℝ) • (1 - atom.r0)) * ((1 / 2 : ℝ) • (1 + atom.r0))
        = ((1 / 2 : ℝ) * (1 / 2 : ℝ)) •
            ((1 - atom.r0) * (1 + atom.r0)) := by
      rw [smul_mul_smul]
    _ = (1 / 4 : ℝ) • ((1 - atom.r0) * (1 + atom.r0)) := by norm_num
    _ = (1 / 4 : ℝ) • (0 : K) := by
      have h : (1 - atom.r0) * (1 + atom.r0) = 0 := by
        calc
          (1 - atom.r0) * (1 + atom.r0)
              = 1 - atom.r0 * atom.r0 := by noncomm_ring
          _ = 0 := by rw [hAtom.1]; noncomm_ring
      rw [h]
    _ = 0 := smul_zero _

theorem chiral_plus_idempotent :
    chiralProjectorPlus atom * chiralProjectorPlus atom =
      chiralProjectorPlus atom := by
  have hpart := chiral_sheets_partition_unity atom
  have horth := chiral_sheets_orthogonal atom hAtom
  symm
  calc
    chiralProjectorPlus atom
        = chiralProjectorPlus atom * 1 := by rw [mul_one]
    _ = chiralProjectorPlus atom *
          (chiralProjectorPlus atom + chiralProjectorMinus atom) := by rw [hpart]
    _ = chiralProjectorPlus atom * chiralProjectorPlus atom +
          chiralProjectorPlus atom * chiralProjectorMinus atom := by rw [mul_add]
    _ = chiralProjectorPlus atom * chiralProjectorPlus atom + 0 := by rw [horth]
    _ = chiralProjectorPlus atom * chiralProjectorPlus atom := by rw [add_zero]

theorem chiral_minus_idempotent :
    chiralProjectorMinus atom * chiralProjectorMinus atom =
      chiralProjectorMinus atom := by
  have hpart := chiral_sheets_partition_unity atom
  have horth := chiral_sheets_orthogonal_rev atom hAtom
  symm
  calc
    chiralProjectorMinus atom
        = chiralProjectorMinus atom * 1 := by rw [mul_one]
    _ = chiralProjectorMinus atom *
          (chiralProjectorPlus atom + chiralProjectorMinus atom) := by rw [hpart]
    _ = chiralProjectorMinus atom * chiralProjectorPlus atom +
          chiralProjectorMinus atom * chiralProjectorMinus atom := by rw [mul_add]
    _ = 0 + chiralProjectorMinus atom * chiralProjectorMinus atom := by rw [horth]
    _ = chiralProjectorMinus atom * chiralProjectorMinus atom := by rw [zero_add]

/-! ## Even/odd projectors from the Euler involution -/

def evenProjector (atom : Cl11Atom K) : K := (1 / 2 : ℝ) • (1 + EulerOperator atom)

def oddProjector (atom : Cl11Atom K) : K := (1 / 2 : ℝ) • (1 - EulerOperator atom)

theorem even_odd_orthogonal : evenProjector atom * oddProjector atom = 0 := by
  dsimp [evenProjector, oddProjector]
  calc
    ((1 / 2 : ℝ) • (1 + EulerOperator atom)) *
        ((1 / 2 : ℝ) • (1 - EulerOperator atom))
        = ((1 / 2 : ℝ) * (1 / 2 : ℝ)) •
            ((1 + EulerOperator atom) * (1 - EulerOperator atom)) := by
      rw [smul_mul_smul]
    _ = (1 / 4 : ℝ) • ((1 + EulerOperator atom) * (1 - EulerOperator atom)) := by
      norm_num
    _ = (1 / 4 : ℝ) • (1 - EulerOperator atom * EulerOperator atom) := by
      congr 1
      noncomm_ring
    _ = (1 / 4 : ℝ) • (1 - 1 : K) := by rw [euler_operator_sq_one atom hAtom]
    _ = (1 / 4 : ℝ) • (0 : K) := by congr 1; noncomm_ring
    _ = 0 := smul_zero _

theorem even_odd_partition_unity : evenProjector atom + oddProjector atom = 1 := by
  dsimp [evenProjector, oddProjector]
  rw [← smul_add]
  have hsum :
      (1 + EulerOperator atom) + (1 - EulerOperator atom) =
        (2 : ℝ) • (1 : K) := by
    simp [two_smul]
  rw [hsum, smul_smul]
  norm_num

theorem euler_fixes_even :
    EulerOperator atom * evenProjector atom = evenProjector atom := by
  dsimp [evenProjector]
  calc
    EulerOperator atom * ((1 / 2 : ℝ) • (1 + EulerOperator atom))
        = (1 / 2 : ℝ) •
            (EulerOperator atom * (1 + EulerOperator atom)) := by
      rw [mul_smul_comm]
    _ = (1 / 2 : ℝ) •
          (EulerOperator atom * 1 + EulerOperator atom * EulerOperator atom) := by
      rw [mul_add]
    _ = (1 / 2 : ℝ) • (EulerOperator atom + 1) := by
      rw [mul_one, euler_operator_sq_one atom hAtom]
    _ = (1 / 2 : ℝ) • (1 + EulerOperator atom) := by
      congr 1
      abel

theorem euler_flips_odd :
    EulerOperator atom * oddProjector atom = -(oddProjector atom) := by
  dsimp [oddProjector]
  calc
    EulerOperator atom * ((1 / 2 : ℝ) • (1 - EulerOperator atom))
        = (1 / 2 : ℝ) •
            (EulerOperator atom * (1 - EulerOperator atom)) := by
      rw [mul_smul_comm]
    _ = (1 / 2 : ℝ) •
          (EulerOperator atom * 1 - EulerOperator atom * EulerOperator atom) := by
      rw [mul_sub]
    _ = (1 / 2 : ℝ) • (EulerOperator atom - 1) := by
      rw [mul_one, euler_operator_sq_one atom hAtom]
    _ = (1 / 2 : ℝ) • (-(1 - EulerOperator atom)) := by
      congr 1
      noncomm_ring
    _ = -((1 / 2 : ℝ) • (1 - EulerOperator atom)) := by
      rw [smul_neg]

/-! ## Clifford square identity -/

omit [Algebra ℝ K] in
theorem clifford_square_identity (p q : K)
    (hp : p * atom.r0 = atom.r0 * p)
    (hq : q * atom.r0 = atom.r0 * q)
    (hp5 : p * atom.r5 = atom.r5 * p)
    (hq5 : q * atom.r5 = atom.r5 * q) :
    (atom.r0 * p + atom.r5 * q) * (atom.r0 * p + atom.r5 * q) =
      (p * p - q * q) + atom.r0 * atom.r5 * (p * q - q * p) := by
  have hanti : atom.r5 * atom.r0 = -(atom.r0 * atom.r5) := by
    rw [hAtom.2.2, neg_neg]
  have h00 : (atom.r0 * p) * (atom.r0 * p) = atom.r0 * atom.r0 * (p * p) := by
    calc
      (atom.r0 * p) * (atom.r0 * p)
          = atom.r0 * (p * atom.r0) * p := by noncomm_ring
      _ = atom.r0 * (atom.r0 * p) * p := by rw [hp]
      _ = atom.r0 * atom.r0 * (p * p) := by noncomm_ring
  have h05 : (atom.r0 * p) * (atom.r5 * q) = atom.r0 * atom.r5 * (p * q) := by
    calc
      (atom.r0 * p) * (atom.r5 * q)
          = atom.r0 * (p * atom.r5) * q := by noncomm_ring
      _ = atom.r0 * (atom.r5 * p) * q := by rw [hp5]
      _ = atom.r0 * atom.r5 * (p * q) := by noncomm_ring
  have h50 : (atom.r5 * q) * (atom.r0 * p) = atom.r5 * atom.r0 * (q * p) := by
    calc
      (atom.r5 * q) * (atom.r0 * p)
          = atom.r5 * (q * atom.r0) * p := by noncomm_ring
      _ = atom.r5 * (atom.r0 * q) * p := by rw [hq]
      _ = atom.r5 * atom.r0 * (q * p) := by noncomm_ring
  have h55 : (atom.r5 * q) * (atom.r5 * q) = atom.r5 * atom.r5 * (q * q) := by
    calc
      (atom.r5 * q) * (atom.r5 * q)
          = atom.r5 * (q * atom.r5) * q := by noncomm_ring
      _ = atom.r5 * (atom.r5 * q) * q := by rw [hq5]
      _ = atom.r5 * atom.r5 * (q * q) := by noncomm_ring
  calc
    (atom.r0 * p + atom.r5 * q) * (atom.r0 * p + atom.r5 * q)
        = (atom.r0 * p) * (atom.r0 * p) +
            (atom.r0 * p) * (atom.r5 * q) +
            ((atom.r5 * q) * (atom.r0 * p) +
              (atom.r5 * q) * (atom.r5 * q)) := by
      noncomm_ring
    _ = atom.r0 * atom.r0 * (p * p) +
          atom.r0 * atom.r5 * (p * q) +
          (atom.r5 * atom.r0 * (q * p) +
            atom.r5 * atom.r5 * (q * q)) := by
      rw [h00, h05, h50, h55]
    _ = 1 * (p * p) + atom.r0 * atom.r5 * (p * q) +
          ((-(atom.r0 * atom.r5)) * (q * p) + (-1) * (q * q)) := by
      rw [hAtom.1, hAtom.2.1, hanti]
    _ = (p * p - q * q) + atom.r0 * atom.r5 * (p * q - q * p) := by
      noncomm_ring

omit [Algebra ℝ K] in
theorem clifford_square_identity_commuting (p q : K)
    (hp : p * atom.r0 = atom.r0 * p)
    (hq : q * atom.r0 = atom.r0 * q)
    (hp5 : p * atom.r5 = atom.r5 * p)
    (hq5 : q * atom.r5 = atom.r5 * q)
    (hpq_comm : p * q = q * p) :
    (atom.r0 * p + atom.r5 * q) * (atom.r0 * p + atom.r5 * q) =
      (p * p - q * q) := by
  rw [clifford_square_identity atom hAtom p q hp hq hp5 hq5]
  rw [hpq_comm, sub_self, mul_zero, add_zero]

/-! ## Combined Dirac square with explicit commutation premises -/

def ChiralityOperator (atom : Cl11Atom K) : Type _ :=
  {rho : K // rho * rho = 1 ∧
    rho * atom.r0 = -(atom.r0 * rho) ∧
    rho * atom.r5 = -(atom.r5 * rho)}

namespace ChiralityOperator

omit [Algebra ℝ K] hAtom in
def rho (chi : ChiralityOperator atom) : K := chi.1

omit [Algebra ℝ K] hAtom in
theorem rho_sq_one (chi : ChiralityOperator atom) :
    chi.rho * chi.rho = 1 := chi.2.1

omit [Algebra ℝ K] hAtom in
theorem anticomm_r0 (chi : ChiralityOperator atom) :
    chi.rho * atom.r0 = -(atom.r0 * chi.rho) := chi.2.2.1

omit [Algebra ℝ K] hAtom in
theorem anticomm_r5 (chi : ChiralityOperator atom) :
    chi.rho * atom.r5 = -(atom.r5 * chi.rho) := chi.2.2.2

end ChiralityOperator

omit [Algebra ℝ K] in
theorem dirac_operator_square (chi : ChiralityOperator atom) (p q Q : K)
    (hp_comm_r0 : p * atom.r0 = atom.r0 * p)
    (hq_comm_r0 : q * atom.r0 = atom.r0 * q)
    (hp_comm_r5 : p * atom.r5 = atom.r5 * p)
    (hq_comm_r5 : q * atom.r5 = atom.r5 * q)
    (hp_comm_rho : p * chi.1 = chi.1 * p)
    (hq_comm_rho : q * chi.1 = chi.1 * q)
    (hQ_comm_r0 : Q * atom.r0 = atom.r0 * Q)
    (hQ_comm_r5 : Q * atom.r5 = atom.r5 * Q)
    (hQ_comm_rho : Q * chi.1 = chi.1 * Q)
    (hQ_comm_p : Q * p = p * Q)
    (hQ_comm_q : Q * q = q * Q) :
    (atom.r0 * p + atom.r5 * q + chi.1 * Q) *
        (atom.r0 * p + atom.r5 * q + chi.1 * Q) =
      (p * p - q * q + atom.r0 * atom.r5 * (p * q - q * p)) + Q * Q := by
  set Dcl := atom.r0 * p + atom.r5 * q
  set Dchi := chi.1 * Q
  have h_sq_cl :
      Dcl * Dcl =
        (p * p - q * q) + atom.r0 * atom.r5 * (p * q - q * p) := by
    subst Dcl
    exact clifford_square_identity atom hAtom p q hp_comm_r0 hq_comm_r0 hp_comm_r5 hq_comm_r5
  have h_sq_chi : Dchi * Dchi = Q * Q := by
    subst Dchi
    calc
      (chi.1 * Q) * (chi.1 * Q)
          = chi.1 * (Q * chi.1) * Q := by noncomm_ring
      _ = chi.1 * (chi.1 * Q) * Q := by rw [hQ_comm_rho]
      _ = (chi.1 * chi.1) * (Q * Q) := by noncomm_ring
      _ = 1 * (Q * Q) := by rw [chi.2.1]
      _ = Q * Q := by noncomm_ring
  have hr0_rev : atom.r0 * chi.1 = -(chi.1 * atom.r0) := by
    rw [chi.2.2.1, neg_neg]
  have hr5_rev : atom.r5 * chi.1 = -(chi.1 * atom.r5) := by
    rw [chi.2.2.2, neg_neg]
  have hA : (atom.r0 * p) * (chi.1 * Q) = -(chi.1 * atom.r0 * Q * p) := by
    calc
      (atom.r0 * p) * (chi.1 * Q)
          = atom.r0 * (p * chi.1) * Q := by noncomm_ring
      _ = atom.r0 * (chi.1 * p) * Q := by rw [hp_comm_rho]
      _ = (atom.r0 * chi.1) * (p * Q) := by noncomm_ring
      _ = (-(chi.1 * atom.r0)) * (p * Q) := by rw [hr0_rev]
      _ = (-(chi.1 * atom.r0)) * (Q * p) := by rw [hQ_comm_p]
      _ = -(chi.1 * atom.r0 * Q * p) := by noncomm_ring
  have hB : (atom.r5 * q) * (chi.1 * Q) = -(chi.1 * atom.r5 * Q * q) := by
    calc
      (atom.r5 * q) * (chi.1 * Q)
          = atom.r5 * (q * chi.1) * Q := by noncomm_ring
      _ = atom.r5 * (chi.1 * q) * Q := by rw [hq_comm_rho]
      _ = (atom.r5 * chi.1) * (q * Q) := by noncomm_ring
      _ = (-(chi.1 * atom.r5)) * (q * Q) := by rw [hr5_rev]
      _ = (-(chi.1 * atom.r5)) * (Q * q) := by rw [hQ_comm_q]
      _ = -(chi.1 * atom.r5 * Q * q) := by noncomm_ring
  have hC : (chi.1 * Q) * (atom.r0 * p) = chi.1 * atom.r0 * Q * p := by
    calc
      (chi.1 * Q) * (atom.r0 * p)
          = chi.1 * (Q * atom.r0) * p := by noncomm_ring
      _ = chi.1 * (atom.r0 * Q) * p := by rw [hQ_comm_r0]
      _ = chi.1 * atom.r0 * Q * p := by noncomm_ring
  have hD : (chi.1 * Q) * (atom.r5 * q) = chi.1 * atom.r5 * Q * q := by
    calc
      (chi.1 * Q) * (atom.r5 * q)
          = chi.1 * (Q * atom.r5) * q := by noncomm_ring
      _ = chi.1 * (atom.r5 * Q) * q := by rw [hQ_comm_r5]
      _ = chi.1 * atom.r5 * Q * q := by noncomm_ring
  have h_cross : Dcl * Dchi + Dchi * Dcl = 0 := by
    subst Dcl
    subst Dchi
    calc
      (atom.r0 * p + atom.r5 * q) * (chi.1 * Q) +
          (chi.1 * Q) * (atom.r0 * p + atom.r5 * q)
          = (atom.r0 * p) * (chi.1 * Q) +
              (atom.r5 * q) * (chi.1 * Q) +
              ((chi.1 * Q) * (atom.r0 * p) +
                (chi.1 * Q) * (atom.r5 * q)) := by
        noncomm_ring
      _ = -(chi.1 * atom.r0 * Q * p) +
            -(chi.1 * atom.r5 * Q * q) +
            (chi.1 * atom.r0 * Q * p +
              chi.1 * atom.r5 * Q * q) := by
        rw [hA, hB, hC, hD]
      _ = 0 := by noncomm_ring
  calc
    (Dcl + Dchi) * (Dcl + Dchi)
        = Dcl * Dcl + (Dcl * Dchi + Dchi * Dcl) + Dchi * Dchi := by
      noncomm_ring
    _ = Dcl * Dcl + 0 + Dchi * Dchi := by rw [h_cross]
    _ = ((p * p - q * q) + atom.r0 * atom.r5 * (p * q - q * p)) + Q * Q := by
      rw [h_sq_cl, h_sq_chi]
      simp [add_assoc]

def eulerAsChirality (atom : Cl11Atom K) (hAtom : Cl11AtomLaws atom) : ChiralityOperator atom where
  val := EulerOperator atom
  property := ⟨euler_operator_sq_one atom hAtom,
    euler_anticommutes_r0 atom hAtom,
    euler_anticommutes_r5 atom hAtom⟩

/-! ## Packet -/

def RealizationData (K : Type*) [Ring K] [Algebra ℝ K] : Type _ :=
  {cl11 : Cl11Atom K // Cl11AtomLaws cl11}

namespace Realization

theorem euler_sq_one (P : RealizationData K) :
    EulerOperator P.1 * EulerOperator P.1 = 1 :=
  euler_operator_sq_one P.1 P.2

theorem euler_anticomm_r0 (P : RealizationData K) :
    EulerOperator P.1 * P.1.r0 = -(P.1.r0 * EulerOperator P.1) :=
  euler_anticommutes_r0 P.1 P.2

theorem euler_anticomm_r5 (P : RealizationData K) :
    EulerOperator P.1 * P.1.r5 = -(P.1.r5 * EulerOperator P.1) :=
  euler_anticommutes_r5 P.1 P.2

theorem chiral_orthogonal (P : RealizationData K) :
    chiralProjectorPlus P.1 * chiralProjectorMinus P.1 = 0 :=
  chiral_sheets_orthogonal P.1 P.2

theorem chiral_partition (P : RealizationData K) :
    chiralProjectorPlus P.1 + chiralProjectorMinus P.1 = 1 :=
  chiral_sheets_partition_unity P.1

theorem even_odd_orthogonal (P : RealizationData K) :
    evenProjector P.1 * oddProjector P.1 = 0 :=
  _root_.InfoGeometry.Arithmetic.SplitCliffordRealization.even_odd_orthogonal P.1 P.2

theorem even_odd_partition (P : RealizationData K) :
    evenProjector P.1 + oddProjector P.1 = 1 :=
  even_odd_partition_unity P.1 P.2

theorem euler_fixes_even (P : RealizationData K) :
    EulerOperator P.1 * evenProjector P.1 = evenProjector P.1 :=
  _root_.InfoGeometry.Arithmetic.SplitCliffordRealization.euler_fixes_even P.1 P.2

theorem euler_flips_odd (P : RealizationData K) :
    EulerOperator P.1 * oddProjector P.1 = -(oddProjector P.1) :=
  _root_.InfoGeometry.Arithmetic.SplitCliffordRealization.euler_flips_odd P.1 P.2

theorem car_nilpotence :
    ∀ i : Fin n, ann n i * ann n i = 0 :=
  ann_sq_zero n

theorem car_anticomm :
    ∀ i j : Fin n, ann n i * ann n j + ann n j * ann n i = 0 :=
  ann_ann_anticomm n

theorem car_identity :
    ∀ i j, ann n i * cre n j + cre n j * ann n i =
      (if i = j then (1 : Clnn n) else 0) :=
  _root_.InfoGeometry.OperatorAlgebra.CliffordCAR.car_identity n

end Realization

def mkRealization (cl11 : Cl11Atom K) (laws : Cl11AtomLaws cl11) :
    RealizationData K :=
  ⟨cl11, laws⟩

/-- Owner target for the split Clifford realization lane. -/
abbrev SplitCliffordRealizationTarget (K : Type uK) [Ring K] [Algebra ℝ K] :
  Type uK :=
  RealizationData K

/-- The split Clifford realization packet is constructible directly. -/
def capstone_split_clifford_realization (cl11 : Cl11Atom K)
    (laws : Cl11AtomLaws cl11) :
    SplitCliffordRealizationTarget K :=
  mkRealization cl11 laws

end InfoGeometry.Arithmetic.SplitCliffordRealization
