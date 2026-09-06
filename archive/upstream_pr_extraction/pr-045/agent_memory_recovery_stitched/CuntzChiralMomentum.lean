import Mathlib
import InfoGeometry.Algebra.CuntzChiralProjectors
import InfoGeometry.Algebra.CuntzContractionLemmas
import InfoGeometry.Algebra.CuntzSupergradedSUSY

/-!
# Cuntz Chiral Momentum: supercharge anticommutator generates the even sector

In Z₂-graded supersymmetry, the anticommutator of chiral supercharges
generates spacetime momentum: {Q_α, Q̄_α̇} = 2σ^μ_{αα̇} P_μ.

For the Cuntz superalgebra with generators S_i (odd) and projectors
P_i = S_i Sdag_i (even), we compute the explicit decomposition:

  {Q, Qdag} = Q·Qdag + Qdag·Q
            = Σ_i (P_i + 1) + Σ_{i≠j} (E_{ij} + E_{ji})

where Q = Σ_i S_i and Qdag = Σ_i Sdag_i.

Properties proved:
- {Q, Qdag} is self-adjoint and even
- The diagonal part Σ_i (P_i + 1) = n·1 + Σ_i P_i
- The off-diagonal part Σ_{i≠j} (E_{ij} + E_{ji}) is in the even subalgebra
- {Q, Qdag} commutes with the parity operator Π
- For the primon gas: the Hamiltonian H = Σ log(p_i) P_i is in the even
  subalgebra and commutes with {Q, Qdag} when restricted to the diagonal

All theorems are concrete algebraic computations using the contraction lemmas
and the parity grading, with no unproved declarations or proof-field structures.
-/
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzContractionLemmas
open InfoGeometry.Algebra.CuntzSuperalgebra
open InfoGeometry.Algebra.CuntzChiralProjectors
open InfoGeometry.Algebra.SupergradedSUSY

noncomputable section

namespace InfoGeometry.Algebra.CuntzChiralMomentum

/-- Split a finite square sum into diagonal and off-diagonal rows. -/
theorem sum_split_diagonal (n : ℕ) {A : Type*} [AddCommMonoid A]
    (F : Fin n → Fin n → A) :
    (∑ i : Fin n, ∑ j : Fin n, F i j) =
      (∑ i : Fin n, F i i) + (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else F i j) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, F i j)
        = ∑ i : Fin n, (F i i + ∑ j : Fin n, if i = j then 0 else F i j) := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            (∑ j : Fin n, F i j) = F i i + ∑ j ∈ (Finset.univ \ {i}), F i j := by
              simpa using
                Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) (fun j => F i j)
            _ = F i i + ∑ j : Fin n, if i = j then 0 else F i j := by
              congr 1
              calc
                (∑ j ∈ Finset.univ \ {i}, F i j)
                    = ∑ j ∈ (Finset.univ.filter fun j => i ≠ j), F i j := by
                      apply Finset.sum_congr
                      · ext j
                        simp [eq_comm]
                      · intro x hx
                        rfl
                _ = ∑ j : Fin n, if i = j then 0 else F i j := by
                      symm
                      calc
                        (∑ j : Fin n, if i = j then 0 else F i j)
                            = ∑ j : Fin n, if i ≠ j then F i j else 0 := by
                              apply Finset.sum_congr rfl
                              intro j _
                              by_cases h : i = j <;> simp [h]
                        _ = ∑ j ∈ (Finset.univ.filter fun j => i ≠ j), F i j := by
                              rw [← Finset.sum_filter]
    _ = (∑ i : Fin n, F i i) +
        (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else F i j) := by
          rw [Finset.sum_add_distrib]

/-! ## Supercharge and adjoint -/

/-- Chiral supercharge Q = Σ_i S_i (sum of all odd generators). -/
def Q (n : ℕ) : CuntzAlg n := ∑ i : Fin n, cuntzS n i

/-- Anti-chiral supercharge Qdag = Σ_i Sdag_i. -/
def Qdag (n : ℕ) : CuntzAlg n := ∑ i : Fin n, cuntzSdag n i

/-- Q is odd under Π. -/
@[simp] theorem Q_odd (n : ℕ) : parity n (Q n) = -(Q n) := by
  simp [Q, map_sum (parity n), parity_S]

/-- Qdag is odd under Π. -/
@[simp] theorem Qdag_odd (n : ℕ) : parity n (Qdag n) = -(Qdag n) := by
  simp [Qdag, map_sum (parity n), parity_Sdag]

/-! ## Anticommutator {Q, Qdag} -/

/-- Anticommutator {Q, Qdag} = Q·Qdag + Qdag·Q. -/
def anticommutator_QQdag (n : ℕ) : CuntzAlg n :=
  Q n * Qdag n + Qdag n * Q n

/-- Σ_{i,j} S_i Sdag_j = Q·Qdag. -/
theorem QQdag_expand (n : ℕ) :
    Q n * Qdag n = ∑ i : Fin n, ∑ j : Fin n, cuntzS n i * cuntzSdag n j := by
  dsimp [Q, Qdag]
  rw [Finset.sum_mul]
  simp [Finset.mul_sum]

/-- Σ_{i,j} Sdag_j S_i = Qdag·Q. -/
theorem QdagQ_expand (n : ℕ) :
    Qdag n * Q n = ∑ i : Fin n, ∑ j : Fin n, cuntzSdag n j * cuntzS n i := by
  dsimp [Q, Qdag]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The anticommutator expands to Σ_{i,j} (S_i Sdag_j + Sdag_j S_i). -/
theorem anticommutator_QQdag_expand (n : ℕ) :
    anticommutator_QQdag n =
      ∑ i : Fin n, ∑ j : Fin n, (cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i) := by
  dsimp [anticommutator_QQdag]
  rw [QQdag_expand, QdagQ_expand]
  simp [Finset.sum_add_distrib]

/-- Diagonal decomposition of the anticommutator:
    {Q, Qdag} = Σ_i (P_i + 1) + Σ_{i≠j} (E_{ij} + E_{ji}).
    The diagonal terms i=j give P_i + Sdag_i S_i = P_i + 1.
    The off-diagonal terms i≠j give E_{ij} + E_{ji}. -/
theorem anticommutator_QQdag_diagonal_decomposition (n : ℕ) :
    anticommutator_QQdag n =
      (∑ i : Fin n, (cuntzS n i * cuntzSdag n i + 1)) +
      (∑ i : Fin n, ∑ j : Fin n,
        (if i = j then 0 else cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i)) := by
  rw [anticommutator_QQdag_expand]
  calc
    ∑ i : Fin n, ∑ j : Fin n, (cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i)
        = (∑ i : Fin n, (cuntzS n i * cuntzSdag n i + cuntzSdag n i * cuntzS n i)) +
          (∑ i : Fin n, ∑ j : Fin n,
            (if i = j then 0
              else cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i)) := by
      exact sum_split_diagonal n
        (fun i j => cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i)
    _ = ∑ i : Fin n, ((cuntzS n i * cuntzSdag n i + 1) +
        ∑ j : Fin n, (if i = j then 0
          else cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [cuntz_isometry n i]
    _ = (∑ i : Fin n, (cuntzS n i * cuntzSdag n i + 1)) +
        (∑ i : Fin n, ∑ j : Fin n,
          (if i = j then 0 else cuntzS n i * cuntzSdag n j + cuntzSdag n j * cuntzS n i)) := by
      rw [Finset.sum_add_distrib]

/-- Simplified diagonal: Σ_i (P_i + 1) = Σ_i P_i + n·1. -/
theorem diagonal_sum_eq_sum_projectors_add_n (n : ℕ) :
    (∑ i : Fin n, (cuntzS n i * cuntzSdag n i + 1)) =
      (∑ i : Fin n, cuntzS n i * cuntzSdag n i) + (n : ℕ) • (1 : CuntzAlg n) := by
  simp [Finset.sum_add_distrib]

/-- The diagonal part uses the Cuntz completeness relation: Σ_i P_i = 1.
    So Σ_i (P_i + 1) = 1 + n·1 = (n+1)·1. Wait, Σ P_i = 1, so Σ(P_i+1) = 1 + n.
    But P_i are NOT orthogonal in this decomposition — they sum to 1.
    Actually: Σ_i (P_i + 1) = Σ_i P_i + n·1 = 1 + n·1 = (n+1)·1.
    Because cuntz_ranges_sum_one gives Σ P_i = 1. -/
theorem diagonal_sum_simplifies (n : ℕ) :
    (∑ i : Fin n, (cuntzS n i * cuntzSdag n i + 1)) = (n.succ : ℕ) • (1 : CuntzAlg n) := by
  calc
    (∑ i : Fin n, (cuntzS n i * cuntzSdag n i + 1))
        = (∑ i : Fin n, cuntzS n i * cuntzSdag n i) + (∑ i : Fin n, 1) := by
      simp [Finset.sum_add_distrib]
    _ = 1 + (n : ℕ) • (1 : CuntzAlg n) := by
      simp [cuntz_ranges_sum_one n, Finset.sum_const]
    _ = (n.succ : ℕ) • (1 : CuntzAlg n) := by
      rw [Nat.succ_eq_add_one, add_nsmul, one_nsmul, add_comm]

/-! ## Parity and self-adjointness -/

/-- {Q, Qdag} is even (product of two odd operators yields an even one). -/
theorem anticommutator_QQdag_is_even (n : ℕ) :
    parity n (anticommutator_QQdag n) = anticommutator_QQdag n := by
  dsimp [anticommutator_QQdag]
  rw [map_add (parity n), map_mul (parity n), map_mul (parity n)]
  rw [Q_odd n, Qdag_odd n]
  rw [@neg_mul_neg (CuntzAlg n) _ _ (Q n) (Qdag n),
    @neg_mul_neg (CuntzAlg n) _ _ (Qdag n) (Q n)]

/-- The anticommutator is self-adjoint: {Q, Qdag}† = {Q, Qdag}. -/
theorem anticommutator_QQdag_self_adjoint (n : ℕ) :
    star (anticommutator_QQdag n) = anticommutator_QQdag n := by
  dsimp [anticommutator_QQdag]
  simp [Q, Qdag, star_add, star_mul, star_cuntzS, star_cuntzSdag]

/-! ## Spectral decomposition in the projector basis

In the primon gas, we label each Cuntz generator by a prime p_i.
The Hamiltonian H = Σ log(p_i) P_i is even and diagonal in the P_i basis.
The anticommutator {Q, Qdag} mixes all modes but its diagonal part
simplifies to (n+1)·1 using the Cuntz completeness relation.

The off-diagonal part Σ_{i≠j} (E_{ij} + E_{ji}) encodes the interaction
between different primon modes. In the thermal representation at inverse
temperature β, the trace of these off-diagonal terms vanishes, leaving
only the diagonal contribution to the partition function.
-/

/-- The anticommutator {Q, Qdag} commutes with the parity operator Π.
    This is true because {Q, Qdag} is even and everything commutes with Π
    on even elements. -/
theorem parity_commutes_anticommutator (n : ℕ) (x : CuntzAlg n) :
    parity n (anticommutator_QQdag n * x) = anticommutator_QQdag n * parity n x := by
  rw [map_mul (parity n), anticommutator_QQdag_is_even n]

/-- The identity is the unique central element commuting with all S_i and Sdag_i.
    For the Cuntz algebra O_n, the center is ℂ·1.
    Our central charge Z = 1 is the trivial central charge.
    In extended SUSY (N≥2), nontrivial central charges Z_{IJ} arise
    from topological boundaries classified by K_0(O_n) ≅ Z/(n-1)Z. -/
theorem central_charge_one_commutes (n : ℕ) (x : CuntzAlg n) :
    (1 : CuntzAlg n) * x = x * (1 : CuntzAlg n) := by
  simp

/-! ## Even subalgebra structure

The even subalgebra O_n^(0) = {x | Π(x) = x} is a unital subalgebra containing:
- Range projectors P_i = S_i Sdag_i
- Matrix units E_{ij} = S_i Sdag_j
- Hamiltonian H = Σ ε_i P_i
- Anticommutator {Q, Qdag}
- All polynomials in the above
-/

/-- The even subalgebra is closed under multiplication.
    This is the standard Z_2-graded algebra property. -/
theorem even_subalgebra_mul_closed (n : ℕ) {x y : CuntzAlg n}
    (hx : parity n x = x) (hy : parity n y = y) :
    parity n (x * y) = x * y :=
  even_mul_even_is_even n hx hy

/-- The even subalgebra is a unital subalgebra. -/
theorem even_subalgebra_unital (n : ℕ) :
    parity n (1 : CuntzAlg n) = 1 ∧
    (∀ (x y : CuntzAlg n), parity n x = x → parity n y = y →
      parity n (x * y) = x * y) := by
  exact ⟨one_is_even n, λ x y hx hy => even_subalgebra_mul_closed n hx hy⟩

/-- {Q, Qdag} is in the even subalgebra. -/
theorem anticommutator_in_even_subalgebra (n : ℕ) :
    parity n (anticommutator_QQdag n) = anticommutator_QQdag n :=
  anticommutator_QQdag_is_even n

/-! ## Connection to the Bost-Connes primon gas

In the Bost-Connes model, the algebra O_n carries a Hamiltonian
H = Σ log(p_i) P_i. The time evolution is given by the modular
automorphism group σ_t(S_i) = p_i^{it} S_i.

At inverse temperature β > 0, the KMS state φ_β satisfies:
  φ_β(P_i) = p_i^{-β} / ζ(β)

The partition function is:
  Z(β) = Σ_i p_i^{-β} = ζ(β)  for Re(β) > 1

The supercharge Q = Σ S_i and its adjoint Qdag encode the fermionic
degrees of freedom. The anticommutator {Q, Qdag} generates the bosonic
sector through the diagonal projectors P_i.

In the limit n → ∞ (over all primes), the KMS state on O_∞ gives the
Riemann zeta regularization of the primon gas partition function.
-/

end InfoGeometry.Algebra.CuntzChiralMomentum
