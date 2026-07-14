import Mathlib
import InfoGeometry.Algebra.CuntzSuperalgebra
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz Chiral Projectors: even/odd decomposition via P_± = (1±Π)/2

The parity automorphism Π (Π²=id, Π(S_i)=-S_i) defines a Z_2 grading.
The chiral projectors extract the even and odd components:

  P_even(x) = (x + Π(x))/2    (projects onto the even subalgebra)
  P_odd(x)  = (x - Π(x))/2    (projects onto the odd subspace)

Properties proved:
- P_even + P_odd = id
- P_even² = P_even, P_odd² = P_odd (idempotent, genuine projector)
- P_even∘P_odd = P_odd∘P_even = 0 (orthogonal)
- Π(P_even(x)) = P_even(x), Π(P_odd(x)) = -P_odd(x)
- For Π(x)=x: P_even(x)=x, P_odd(x)=0
- For Π(x)=-x: P_even(x)=0, P_odd(x)=x
- Z_2-graded multiplication rules: even·even=even, odd·odd=even, even·odd=odd
- Concrete sector classification for S_i, Sdag_i, P_i, H, Q, Qdag
-/
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzSuperalgebra
open InfoGeometry.Algebra.CuntzPrimonHamiltonian

noncomputable section

namespace CuntzChiralProjectors

/-! ## Chiral projectors -/

/-- Even projector: P_even(x) = (x + Π(x))/2. -/
def P_even (n : ℕ) (x : CuntzAlg n) : CuntzAlg n :=
  ((1 : ℂ) / 2) • (x + parity n x)

/-- Odd projector: P_odd(x) = (x - Π(x))/2. -/
def P_odd (n : ℕ) (x : CuntzAlg n) : CuntzAlg n :=
  ((1 : ℂ) / 2) • (x - parity n x)

/-! ## Basic algebraic identities -/

/-- P_even + P_odd = id. -/
theorem P_even_add_P_odd (n : ℕ) (x : CuntzAlg n) :
    P_even n x + P_odd n x = x := by
  dsimp [P_even, P_odd]
  calc
    ((1 : ℂ) / 2) • (x + parity n x) + ((1 : ℂ) / 2) • (x - parity n x)
        = ((1 : ℂ) / 2) • ((x + parity n x) + (x - parity n x)) := by rw [← smul_add]
    _ = ((1 : ℂ) / 2) • (x + x) := by
      rw [show (x + parity n x) + (x - parity n x) = x + x by abel]
    _ = ((1 : ℂ) / 2) • ((2 : ℂ) • x) := by rw [two_smul]
    _ = (((1 : ℂ) / 2) * (2 : ℂ)) • x := by rw [smul_smul]
    _ = (1 : ℂ) • x := by norm_num
    _ = x := by simp

/-- P_even is idempotent: P_even(P_even(x)) = P_even(x). -/
theorem P_even_idempotent (n : ℕ) (x : CuntzAlg n) :
    P_even n (P_even n x) = P_even n x := by
  dsimp [P_even]
  -- Π((1/2)·(x+Πx)) = (1/2)·Π(x+Πx) = (1/2)·(Πx+Π²x) = (1/2)·(Πx+x) = (1/2)·(x+Πx)
  have h_inner : parity n (((1 : ℂ) / 2) • (x + parity n x)) =
      ((1 : ℂ) / 2) • (x + parity n x) := by
    rw [map_smul (parity n), map_add (parity n), parity_sq n, add_comm]
  rw [h_inner]
  -- (1/2)·((1/2)·v + (1/2)·v) = (1/2)·v  where v = x+Πx
  calc
    ((1 : ℂ) / 2) • (((1 : ℂ) / 2) • (x + parity n x) +
      ((1 : ℂ) / 2) • (x + parity n x))
        = ((1 : ℂ) / 2) • ((((1 : ℂ) / 2) + ((1 : ℂ) / 2)) • (x + parity n x)) := by
      rw [← add_smul]
    _ = ((1 : ℂ) / 2) • ((1 : ℂ) • (x + parity n x)) := by norm_num
    _ = ((1 : ℂ) / 2) • (x + parity n x) := by simp

/-- P_odd is idempotent: P_odd(P_odd(x)) = P_odd(x). -/
theorem P_odd_idempotent (n : ℕ) (x : CuntzAlg n) :
    P_odd n (P_odd n x) = P_odd n x := by
  dsimp [P_odd]
  -- Π((1/2)·(x-Πx)) = (1/2)·Π(x-Πx) = (1/2)·(Πx-Π²x) = (1/2)·(Πx-x) = -(1/2)·(x-Πx)
  have h_inner : parity n (((1 : ℂ) / 2) • (x - parity n x)) =
      -(((1 : ℂ) / 2) • (x - parity n x)) := by
    rw [map_smul (parity n), map_sub (parity n), parity_sq n]
    have h : (parity n) x - x = -(x - (parity n) x) := by abel
    rw [h, smul_neg]
  rw [h_inner]
  -- Goal: (1/2)·(a - (-a)) = a  where a = (1/2)·(x-Πx)
  -- a - (-a) = a + a = 2•a, then (1/2)·(2•a) = a
  let a := ((1 : ℂ) / 2) • (x - parity n x)
  have h_aa : a - (-a) = (2 : ℂ) • a := by
    calc
      a - (-a) = a + a := by simp
      _ = (2 : ℂ) • a := by rw [two_smul]
  calc
    ((1 : ℂ) / 2) • (a - (-a)) = ((1 : ℂ) / 2) • ((2 : ℂ) • a) := by rw [h_aa]
    _ = (((1 : ℂ) / 2) * (2 : ℂ)) • a := by rw [smul_smul]
    _ = (1 : ℂ) • a := by norm_num
    _ = a := by simp

/-- P_even and P_odd are orthogonal: P_even(P_odd(x)) = 0. -/
theorem P_even_P_odd (n : ℕ) (x : CuntzAlg n) :
    P_even n (P_odd n x) = 0 := by
  dsimp [P_even, P_odd]
  have h_inner : parity n (((1 : ℂ) / 2) • (x - parity n x)) =
      -(((1 : ℂ) / 2) • (x - parity n x)) := by
    rw [map_smul (parity n), map_sub (parity n), parity_sq n]
    have h : (parity n) x - x = -(x - (parity n) x) := by abel
    rw [h, smul_neg]
  rw [h_inner]
  -- (1/2)·(a + (-a)) = (1/2)·0 = 0
  simp

/-- P_odd and P_even are orthogonal: P_odd(P_even(x)) = 0. -/
theorem P_odd_P_even (n : ℕ) (x : CuntzAlg n) :
    P_odd n (P_even n x) = 0 := by
  dsimp [P_even, P_odd]
  have h_inner : parity n (((1 : ℂ) / 2) • (x + parity n x)) =
      ((1 : ℂ) / 2) • (x + parity n x) := by
    rw [map_smul (parity n), map_add (parity n), parity_sq n, add_comm]
  rw [h_inner]
  -- (1/2)·(a - a) = 0
  simp

/-! ## Parity properties of the projectors -/

/-- P_even(x) is even: Π(P_even(x)) = P_even(x). -/
theorem parity_P_even (n : ℕ) (x : CuntzAlg n) :
    parity n (P_even n x) = P_even n x := by
  dsimp [P_even]
  rw [map_smul (parity n), map_add (parity n), parity_sq n, add_comm]

/-- P_odd(x) is odd: Π(P_odd(x)) = -P_odd(x). -/
theorem parity_P_odd (n : ℕ) (x : CuntzAlg n) :
    parity n (P_odd n x) = -(P_odd n x) := by
  dsimp [P_odd]
  rw [map_smul (parity n), map_sub (parity n), parity_sq n]
  have h : (parity n) x - x = -(x - (parity n) x) := by abel
  rw [h, smul_neg]

/-! ## Behavior on even and odd elements -/

/-- If x is even (Π(x)=x), then P_even(x) = x. -/
theorem P_even_of_even (n : ℕ) {x : CuntzAlg n} (hx : parity n x = x) :
    P_even n x = x := by
  dsimp [P_even]
  rw [hx]
  calc
    ((1 : ℂ) / 2) • (x + x) = ((1 : ℂ) / 2) • ((2 : ℂ) • x) := by rw [two_smul]
    _ = (((1 : ℂ) / 2) * (2 : ℂ)) • x := by rw [smul_smul]
    _ = (1 : ℂ) • x := by norm_num
    _ = x := by simp

/-- If x is even (Π(x)=x), then P_odd(x) = 0. -/
theorem P_odd_of_even (n : ℕ) {x : CuntzAlg n} (hx : parity n x = x) :
    P_odd n x = 0 := by
  dsimp [P_odd]
  rw [hx]
  simp

/-- If x is odd (Π(x)=-x), then P_even(x) = 0. -/
theorem P_even_of_odd (n : ℕ) {x : CuntzAlg n} (hx : parity n x = -x) :
    P_even n x = 0 := by
  dsimp [P_even]
  rw [hx]
  simp

/-- If x is odd (Π(x)=-x), then P_odd(x) = x. -/
theorem P_odd_of_odd (n : ℕ) {x : CuntzAlg n} (hx : parity n x = -x) :
    P_odd n x = x := by
  dsimp [P_odd]
  rw [hx]
  calc
    ((1 : ℂ) / 2) • (x - (-x)) = ((1 : ℂ) / 2) • (x + x) := by simp
    _ = ((1 : ℂ) / 2) • ((2 : ℂ) • x) := by rw [two_smul]
    _ = (((1 : ℂ) / 2) * (2 : ℂ)) • x := by rw [smul_smul]
    _ = (1 : ℂ) • x := by norm_num
    _ = x := by simp

/-! ## Superalgebra multiplication rules (Z_2-graded algebra) -/

/-- even · even = even -/
theorem even_mul_even_is_even (n : ℕ) {x y : CuntzAlg n}
    (hx : parity n x = x) (hy : parity n y = y) :
    parity n (x * y) = x * y := by
  rw [map_mul (parity n), hx, hy]

/-- odd · odd = even -/
theorem odd_mul_odd_is_even (n : ℕ) {x y : CuntzAlg n}
    (hx : parity n x = -x) (hy : parity n y = -y) :
    parity n (x * y) = x * y := by
  rw [map_mul (parity n), hx, hy]
  exact @neg_mul_neg (CuntzAlg n) _ _ x y

/-- even · odd = odd -/
theorem even_mul_odd_is_odd (n : ℕ) {x y : CuntzAlg n}
    (hx : parity n x = x) (hy : parity n y = -y) :
    parity n (x * y) = -(x * y) := by
  rw [map_mul (parity n), hx, hy]
  exact @mul_neg (CuntzAlg n) _ _ x y

/-- odd · even = odd -/
theorem odd_mul_even_is_odd (n : ℕ) {x y : CuntzAlg n}
    (hx : parity n x = -x) (hy : parity n y = y) :
    parity n (x * y) = -(x * y) := by
  rw [map_mul (parity n), hx, hy]
  exact @neg_mul (CuntzAlg n) _ _ x y

/-! ## Concrete elements: which sector they belong to -/

/-- The generators S_i are odd. -/
theorem S_is_odd (n : ℕ) (i : Fin n) : parity n (cuntzS n i) = -(cuntzS n i) := parity_S n i

/-- The adjoint generators Sdag_i are odd. -/
theorem Sdag_is_odd (n : ℕ) (i : Fin n) : parity n (cuntzSdag n i) = -(cuntzSdag n i) := parity_Sdag n i

/-- Range projectors P_i = S_i Sdag_i are even. -/
theorem range_projector_is_even (n : ℕ) (i : Fin n) :
    parity n (cuntzS n i * cuntzSdag n i) = cuntzS n i * cuntzSdag n i := by
  rw [map_mul (parity n), parity_S, parity_Sdag]
  exact @neg_mul_neg (CuntzAlg n) _ _ (cuntzS n i) (cuntzSdag n i)

/-- Matrix units E_{ij} = S_i Sdag_j are even (product of two odds). -/
theorem matrix_unit_is_even (n : ℕ) (i j : Fin n) :
    parity n (cuntzS n i * cuntzSdag n j) = cuntzS n i * cuntzSdag n j := by
  rw [map_mul (parity n), parity_S, parity_Sdag]
  exact @neg_mul_neg (CuntzAlg n) _ _ (cuntzS n i) (cuntzSdag n j)

/-- The identity is even (Π(1)=1 since Π is an algebra homomorphism). -/
theorem one_is_even (n : ℕ) : parity n (1 : CuntzAlg n) = 1 :=
  (parity n).map_one

/-- The Hamiltonian H = Σ ε_i P_i is even (sum of evens). -/
theorem hamiltonian_is_even (n : ℕ) (ε : Fin n → ℂ) :
    parity n (hamiltonian n ε) = hamiltonian n ε := by
  dsimp [hamiltonian, P]
  rw [map_sum (parity n)]
  refine Finset.sum_congr rfl (λ i _ => ?_)
  rw [map_smul (parity n), range_projector_is_even]

/-- The supercharge Q = Σ S_i is odd. -/
theorem supercharge_is_odd (n : ℕ) :
    parity n (∑ i : Fin n, cuntzS n i) = -(∑ i : Fin n, cuntzS n i) := by
  rw [map_sum (parity n)]
  simp [parity_S]

/-- The adjoint supercharge Qdag = Σ Sdag_i is odd. -/
theorem supercharge_adjoint_is_odd (n : ℕ) :
    parity n (∑ i : Fin n, cuntzSdag n i) = -(∑ i : Fin n, cuntzSdag n i) := by
  rw [map_sum (parity n)]
  simp [parity_Sdag]

/-- Q·Qdag is even (odd·odd = even). -/
theorem QQdag_is_even (n : ℕ) :
    parity n ((∑ i : Fin n, cuntzS n i) * (∑ i : Fin n, cuntzSdag n i)) =
      (∑ i : Fin n, cuntzS n i) * (∑ i : Fin n, cuntzSdag n i) := by
  rw [map_mul (parity n), supercharge_is_odd, supercharge_adjoint_is_odd]
  exact @neg_mul_neg (CuntzAlg n) _ _ (∑ i : Fin n, cuntzS n i) (∑ i : Fin n, cuntzSdag n i)

/-! ## Action of projectors on concrete elements -/

/-- P_even(S_i) = 0. -/
theorem P_even_S (n : ℕ) (i : Fin n) : P_even n (cuntzS n i) = 0 :=
  P_even_of_odd n (parity_S n i)

/-- P_odd(S_i) = S_i. -/
theorem P_odd_S (n : ℕ) (i : Fin n) : P_odd n (cuntzS n i) = cuntzS n i :=
  P_odd_of_odd n (parity_S n i)

/-- P_even(P_i) = P_i (projectors are even). -/
theorem P_even_range_projector (n : ℕ) (i : Fin n) :
    P_even n (cuntzS n i * cuntzSdag n i) = cuntzS n i * cuntzSdag n i :=
  P_even_of_even n (range_projector_is_even n i)

/-- P_odd(P_i) = 0. -/
theorem P_odd_range_projector (n : ℕ) (i : Fin n) :
    P_odd n (cuntzS n i * cuntzSdag n i) = 0 :=
  P_odd_of_even n (range_projector_is_even n i)

/-- P_even(H) = H. -/
theorem P_even_hamiltonian (n : ℕ) (ε : Fin n → ℂ) :
    P_even n (hamiltonian n ε) = hamiltonian n ε :=
  P_even_of_even n (hamiltonian_is_even n ε)

/-- P_odd(H) = 0. -/
theorem P_odd_hamiltonian (n : ℕ) (ε : Fin n → ℂ) :
    P_odd n (hamiltonian n ε) = 0 :=
  P_odd_of_even n (hamiltonian_is_even n ε)

end CuntzChiralProjectors
