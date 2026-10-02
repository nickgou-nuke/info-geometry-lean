import InfoGeometry.QuantumContext.MassAsCommutantCoupling
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-!
# Operator Peirce Decomposition, Chiral Routing, and Inductive Colimit Transport

This module lifts the finite $2 \times 2$ matrix results of `ChiralBipolarAttention.lean`
into the full abstract operator-algebraic setting:
1. Arbitrary carrier spaces $W$ over a commutative base ring $R$.
2. Arbitrary projection operators $P \in \operatorname{End}_R(W)$ with $P^2 = P$.
3. General off-diagonal bipolar routing:
   $$C(A) = P A (1 - P) + (1 - P) A P$$
4. Complete algebraic verification that $C(A)$ satisfies the Peirce sector swap,
   anticommutes with the grading $G = 2P - 1$, and produces the Dirac mass shell.
5. Invariant transport along algebra homomorphisms $\iota : \operatorname{End}_R(W_n) \to \operatorname{End}_R(W_{n+1})$
   forming the inductive colimit tower (UHF / Cuntz limits).

Zero debt, 0 sorry, 0 admit, kernel-verified in Lean 4.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.OperatorPeirceColimitTransport

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling

variable {R : Type*} [CommRing R]
variable {Carrier : Type*} [Ring Carrier] [Algebra R Carrier]

/-- The general off-diagonal bipolar routing operator associated with an idempotent $P$
    and any carrier operator $A$:
    $$C(P, A) = P A (1 - P) + (1 - P) A P$$ -/
def generalBipolar (P A : Carrier) : Carrier :=
  P * A * (complementIdempotent P) + (complementIdempotent P) * A * P

/-- **Theorem 1 (General Bipolar Sector Swap)**:
    For ANY idempotent $P$ and ANY operator $A$, the general bipolar routing operator
    strictly satisfies the Peirce swap condition:
    $$P \cdot C(P, A) = C(P, A) \cdot (1 - P)$$ -/
theorem generalBipolar_swaps (P A : Carrier) (hP : IsIdempotentElem P) :
    P * (generalBipolar P A) = (generalBipolar P A) * (complementIdempotent P) := by
  unfold generalBipolar
  rw [mul_add, add_mul]
  have hP_comp : P * (complementIdempotent P) = 0 :=
    idempotent_mul_complement P hP.eq
  have hcomp_P : (complementIdempotent P) * P = 0 :=
    complement_mul_idempotent P hP.eq
  have hP_P : P * P = P := hP.eq
  have hcomp_comp : (complementIdempotent P) * (complementIdempotent P) = complementIdempotent P :=
    complementIdempotent_sq P hP.eq
  -- Left side: P * (P * A * comp + comp * A * P) = P * A * comp + 0
  have h_left : P * (P * A * complementIdempotent P) = P * A * complementIdempotent P := by
    rw [← mul_assoc P P, hP_P]
  have h_left_vanish : P * (complementIdempotent P * A * P) = 0 := by
    rw [← mul_assoc P (complementIdempotent P), hP_comp, zero_mul, zero_mul]
  -- Right side: (P * A * comp + comp * A * P) * comp = P * A * comp + 0
  have h_right : (P * A * complementIdempotent P) * complementIdempotent P = P * A * complementIdempotent P := by
    rw [mul_assoc (P * A), hcomp_comp]
  have h_right_vanish : (complementIdempotent P * A * P) * complementIdempotent P = 0 := by
    rw [mul_assoc (complementIdempotent P * A) P, hP_comp, mul_zero]
  rw [h_left, h_left_vanish, h_right, h_right_vanish, add_zero, add_zero]

/-- **Theorem 2 (General Bipolar Anticommutation)**:
    The general bipolar routing operator strictly anticommutes with the grading $G = 2P - 1$:
    $$G \cdot C(P, A) + C(P, A) \cdot G = 0$$ -/
theorem generalBipolar_anticommutes (P A : Carrier) (hP : IsIdempotentElem P) :
    grading P * generalBipolar P A + generalBipolar P A * grading P = 0 :=
  grading_anticommutes P (generalBipolar P A) (generalBipolar_swaps P A hP)

/-- Balanced operator condition: the two off-diagonal channels square to the same scalar mass. -/
def IsBalancedOperatorCoupling (P A : Carrier) (mass : R) : Prop :=
  (generalBipolar P A) * (generalBipolar P A) = algebraMap R Carrier (mass ^ 2)

/-- **Theorem 3 (Relativistic Dirac Dispersion in General Operator Algebras)**:
    $$(p G + C(P, A))^2 = (p^2 + m^2) \cdot 1$$ -/
theorem generalBipolar_hamiltonian_square (P A : Carrier) (momentum mass : R)
    (hP : IsIdempotentElem P) (h_bal : IsBalancedOperatorCoupling P A mass) :
    (momentum • grading P + generalBipolar P A) *
        (momentum • grading P + generalBipolar P A) =
      algebraMap R Carrier (momentum ^ 2 + mass ^ 2) := by
  apply hamiltonian_square P (generalBipolar P A) momentum mass hP
    (generalBipolar_swaps P A hP) h_bal

/-! ### Inductive Colimit Transport across Algebra Homomorphisms -/

variable {Target : Type*} [Ring Target] [Algebra R Target]

/-- **Theorem 4 (Homomorphism Preserves Idempotency)**:
    An algebra homomorphism maps idempotents to idempotents. -/
theorem map_idempotent (f : Carrier →ₐ[R] Target) (P : Carrier) (hP : IsIdempotentElem P) :
    IsIdempotentElem (f P) := by
  change f P * f P = f P
  rw [← map_mul, hP.eq]

/-- **Theorem 5 (Homomorphism Commutes with Complement Idempotent)**:
    $$f(1 - P) = 1 - f(P)$$ -/
theorem map_complementIdempotent (f : Carrier →ₐ[R] Target) (P : Carrier) :
    f (complementIdempotent P) = complementIdempotent (f P) := by
  unfold complementIdempotent
  simp only [map_sub, map_one]

/-- **Theorem 6 (Homomorphism Commutes with Grading)**:
    $$f(G_P) = G_{f(P)}$$ -/
theorem map_grading (f : Carrier →ₐ[R] Target) (P : Carrier) :
    f (grading P) = grading (f P) := by
  unfold grading
  simp only [map_sub, map_complementIdempotent]

/-- **Theorem 7 (Homomorphism Commutes with General Bipolar Routing)**:
    $$f(C(P, A)) = C(f(P), f(A))$$ -/
theorem map_generalBipolar (f : Carrier →ₐ[R] Target) (P A : Carrier) :
    f (generalBipolar P A) = generalBipolar (f P) (f A) := by
  unfold generalBipolar
  simp only [map_add, map_mul, map_complementIdempotent]

/-- **Theorem 8 (Inductive Colimit Invariant Transport of Balanced Coupling)**:
    If $(P, A)$ is balanced at stage $n$, it remains balanced under the bonding map $f$. -/
theorem map_balancedCoupling (f : Carrier →ₐ[R] Target) (P A : Carrier) (mass : R)
    (h_bal : IsBalancedOperatorCoupling P A mass) :
    IsBalancedOperatorCoupling (f P) (f A) mass := by
  unfold IsBalancedOperatorCoupling
  rw [← map_generalBipolar, ← map_mul, h_bal]
  simp only [AlgHom.commutes]

/-- **Theorem 9 (The Master Colimit Invariant: Dirac Mass Shell Preservation)**:
    The complete relativistic Dirac dispersion relation:
    $$(p G + C)^2 = (p^2 + m^2) \cdot 1$$
    is strictly preserved under every stage-bonding homomorphism $\iota_n$ in the colimit tower:
    $$f\left((p G_P + C(P, A))^2\right) = (p G_{f(P)} + C(f(P), f(A)))^2 = (p^2 + m^2) \cdot 1$$ -/
theorem colimit_transport_dirac_dispersion (f : Carrier →ₐ[R] Target)
    (P A : Carrier) (momentum mass : R)
    (hP : IsIdempotentElem P) (h_bal : IsBalancedOperatorCoupling P A mass) :
    f ((momentum • grading P + generalBipolar P A) *
        (momentum • grading P + generalBipolar P A)) =
      algebraMap R Target (momentum ^ 2 + mass ^ 2) ∧
    (momentum • grading (f P) + generalBipolar (f P) (f A)) *
        (momentum • grading (f P) + generalBipolar (f P) (f A)) =
      algebraMap R Target (momentum ^ 2 + mass ^ 2) := by
  have h_base := generalBipolar_hamiltonian_square P A momentum mass hP h_bal
  have h_mapped : f ((momentum • grading P + generalBipolar P A) *
      (momentum • grading P + generalBipolar P A)) =
      algebraMap R Target (momentum ^ 2 + mass ^ 2) := by
    rw [h_base]
    simp only [AlgHom.commutes]
  have h_target := generalBipolar_hamiltonian_square (f P) (f A) momentum mass
    (map_idempotent f P hP) (map_balancedCoupling f P A mass h_bal)
  exact ⟨h_mapped, h_target⟩

end InfoGeometry.QuantumContext.OperatorPeirceColimitTransport
