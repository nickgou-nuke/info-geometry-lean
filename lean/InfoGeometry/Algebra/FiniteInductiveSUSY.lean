import Mathlib.Tactic

/-!
# Finite inductive SUSY closure

This file proves the finite inductive spine:

* nilpotency is transported by bonding ring homomorphisms;
* odd-odd superclosure is transported;
* centrality against transported odd charges is transported;
* the Dirac-square identity persists at every finite stage.

No colimit or completion theorem is claimed here.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteInductiveSUSY

variable {A : ℕ → Type*} [∀ n : ℕ, Ring (A n)]

/-- Super-anticommutator. -/
def anticomm {B : Type*} [Ring B] (x y : B) : B :=
  x * y + y * x

/-- Ring homomorphisms preserve the super-anticommutator. -/
theorem map_anticomm
    {B C : Type*} [Ring B] [Ring C]
    (φ : B →+* C) (Q R : B) :
    φ (anticomm Q R) = anticomm (φ Q) (φ R) := by
  change φ (Q * R + R * Q) = φ Q * φ R + φ R * φ Q
  rw [map_add, map_mul, map_mul]

/--
Transport of one finite `N=2` closure relation.

If `{Q,R}=H+Z` at one stage, then every ring-homomorphic transport preserves
the same closure relation.
-/
theorem map_superclosure
    {B C : Type*} [Ring B] [Ring C]
    (φ : B →+* C) (Q R H Z : B)
    (hclosure : anticomm Q R = H + Z) :
    anticomm (φ Q) (φ R) = φ H + φ Z := by
  calc
    anticomm (φ Q) (φ R)
        = φ (anticomm Q R) := by
          exact (map_anticomm φ Q R).symm
    _ = φ (H + Z) := by
          rw [hclosure]
    _ = φ H + φ Z := by
          simp

/-- Nilpotency is stable along an inductive chain of ring homomorphisms. -/
theorem nilpotent_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (Q : ∀ n : ℕ, A n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n)) :
    ∀ n : ℕ, Q n * Q n = 0 := by
  intro n
  induction n with
  | zero =>
      exact hQ0
  | succ n ih =>
      rw [hQstep n]
      calc
        φ n (Q n) * φ n (Q n)
            = φ n (Q n * Q n) := by
              exact (map_mul (φ n) (Q n) (Q n)).symm
        _ = φ n 0 := by
              rw [ih]
        _ = 0 := by
              simp

/--
Odd-odd closure is stable along an inductive chain.

This proves the finite-stage preservation law
`{Qₙ,Rₙ}=Hₙ+Zₙ` for every `n` from the stage-zero relation and transport
equations.
-/
theorem superclosure_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (Q R H Z : ∀ n : ℕ, A n)
    (hclosure0 : anticomm (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hHstep : ∀ n : ℕ, H (Nat.succ n) = φ n (H n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ, anticomm (Q n) (R n) = H n + Z n := by
  intro n
  induction n with
  | zero =>
      exact hclosure0
  | succ n ih =>
      rw [hQstep n, hRstep n, hHstep n, hZstep n]
      exact map_superclosure (φ n) (Q n) (R n) (H n) (Z n) ih

/-- Centrality against one transported charge is stable along the chain. -/
theorem central_commutes_with_charge_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (Q Z : ∀ n : ℕ, A n)
    (hcentral0 : Z 0 * Q 0 = Q 0 * Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ, Z n * Q n = Q n * Z n := by
  intro n
  induction n with
  | zero =>
      exact hcentral0
  | succ n ih =>
      rw [hZstep n, hQstep n]
      calc
        φ n (Z n) * φ n (Q n)
            = φ n (Z n * Q n) := by
              exact (map_mul (φ n) (Z n) (Q n)).symm
        _ = φ n (Q n * Z n) := by
              rw [ih]
        _ = φ n (Q n) * φ n (Z n) := by
              exact map_mul (φ n) (Q n) (Z n)

/-- Centrality of the transported central lane against both odd charges. -/
theorem central_commutes_with_two_charges_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (Q R Z : ∀ n : ℕ, A n)
    (hZQ0 : Z 0 * Q 0 = Q 0 * Z 0)
    (hZR0 : Z 0 * R 0 = R 0 * Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ,
      Z n * Q n = Q n * Z n ∧
      Z n * R n = R n * Z n := by
  intro n
  constructor
  · exact central_commutes_with_charge_chain φ Q Z hZQ0 hQstep hZstep n
  · exact central_commutes_with_charge_chain φ R Z hZR0 hRstep hZstep n

/--
At one stage, nilpotent odd charges plus odd-odd closure imply the Dirac-square
identity.

This is the finite local relation
`Q²=R²=0`, `{Q,R}=H+Z` ⟹ `(Q+R)²=H+Z`.
-/
theorem nilpotent_dirac_square_eq_closure
    {B : Type*} [Ring B]
    (Q R H Z : B)
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hclosure : anticomm Q R = H + Z) :
    (Q + R) * (Q + R) = H + Z := by
  calc
    (Q + R) * (Q + R)
        = Q * Q + Q * R + R * Q + R * R := by
          noncomm_ring
    _ = 0 + Q * R + R * Q + 0 := by
          rw [hQ, hR]
    _ = Q * R + R * Q := by
          simp
    _ = anticomm Q R := by
          rfl
    _ = H + Z := hclosure

/--
Main finite inductive invariant theorem.

If an inductive chain transports the two odd charges, the even Hamiltonian
lane, and the central lane by ring homomorphisms, then the Dirac-square closure
`(Qₙ + Rₙ)² = Hₙ + Zₙ` holds at every finite stage.
-/
theorem dirac_square_closure_chain
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (Q R H Z : ∀ n : ℕ, A n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hR0 : R 0 * R 0 = 0)
    (hclosure0 : anticomm (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hHstep : ∀ n : ℕ, H (Nat.succ n) = φ n (H n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ, (Q n + R n) * (Q n + R n) = H n + Z n := by
  intro n
  have hQn : Q n * Q n = 0 :=
    nilpotent_chain φ Q hQ0 hQstep n
  have hRn : R n * R n = 0 :=
    nilpotent_chain φ R hR0 hRstep n
  have hcln : anticomm (Q n) (R n) = H n + Z n :=
    superclosure_chain φ Q R H Z hclosure0 hQstep hRstep hHstep hZstep n
  exact nilpotent_dirac_square_eq_closure (Q n) (R n) (H n) (Z n) hQn hRn hcln

end InfoGeometry.Algebra.FiniteInductiveSUSY
