import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Canonical.BostConnesKMS

/-!
# Bost-Connes anticommutation on generators

This file formalizes a generator-level anticommutation relation between the
Liouville grading operator Γ and the prime-indexed generators in the
Bost--Connes system.

For any prime p:
    Γ ∘ S_p = -S_p ∘ Γ

Equivalently: Γ S_p + S_p Γ = 0

The Dirac-style comparison is interpretive background only.

-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Canonical.BostConnesAnticommutation

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Canonical.BostConnesKMS

/-!
## Main Theorem: Anticommutation on Generators
-/

variable {Op : Type*} [Ring Op] [StarRing Op]

/--
The Liouville grading as a scalar action on Bost-Connes generators.

For any n : ℕ+, Γ acts on S_n by multiplication by λ(n) = (-1)^{Ω(n)}.
-/
def liouvilleAction (C : BostConnesCuntzSystem Op) (n : ℕ+) : Op :=
  (liouville n : ℤ) • (S C n)

/--
Arithmetic sign rule: `λ(pn) = -λ(n)` for prime `p`.

Proof: Ω(pn) = Ω(p) + Ω(n) = 1 + Ω(n), so
  λ(pn) = (-1)^{Ω(pn)} = (-1)^{Ω(n)+1} = -(-1)^{Ω(n)} = -λ(n)
-/
lemma liouville_prime_mul_neg (p n : ℕ) (hp : Nat.Prime p) (hn : n ≥ 1) :
    liouville (p * n) = -liouville n :=
  liouville_prime_mul p n hp hn

/--
Generator anticommutation statement: `Γ(S_{pn}) = -S_p · Γ(S_n)`.

This is the scalar-form relation used in the proof.
-/
theorem liouville_action_anticommutes (C : BostConnesCuntzSystem Op) 
    (p : ℕ) (hp : Nat.Prime p) (n : ℕ+) :
    liouvilleAction C (MultiplicativeIndexing.primePNat p hp * n) = 
      -(S C (MultiplicativeIndexing.primePNat p hp) * liouvilleAction C n) := by
  have h := liouville_prime_mul_neg p n.val hp n.property
  have hcomm :
      S C (MultiplicativeIndexing.primePNat p hp) * (liouville ↑n : Op) =
        (liouville ↑n : Op) * S C (MultiplicativeIndexing.primePNat p hp) := by
    exact (Int.cast_commute (α := Op) (liouville ↑n) (S C (MultiplicativeIndexing.primePNat p hp))).eq.symm
  have hmul :
      S C (MultiplicativeIndexing.primePNat p hp) * (liouville ↑n • (S C n)) =
        liouville ↑n • (S C (MultiplicativeIndexing.primePNat p hp) * S C n) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    calc
      S C (MultiplicativeIndexing.primePNat p hp) * ((liouville ↑n : Op) * S C n)
          = (S C (MultiplicativeIndexing.primePNat p hp) * (liouville ↑n : Op)) * S C n := by
              rw [mul_assoc]
      _ = ((liouville ↑n : Op) * S C (MultiplicativeIndexing.primePNat p hp)) * S C n := by
              rw [hcomm]
      _ = (liouville ↑n : Op) * (S C (MultiplicativeIndexing.primePNat p hp) * S C n) := by
              rw [mul_assoc]
  rw [liouvilleAction, liouvilleAction, S_mul]
  change liouville (p * n.val) • (S C (MultiplicativeIndexing.primePNat p hp) * S C n) =
    -(S C (MultiplicativeIndexing.primePNat p hp) * (liouville ↑n • (S C n)))
  rw [h, hmul, ← neg_zsmul]

/--
Anticommutation in multiplicative form.

For any prime p and any n, m : ℕ+:
  Γ(S_p S_n S_m) = -S_p Γ(S_n S_m)

This shows the anticommutation extends to products.
-/
theorem anticommutation_multiplicative (C : BostConnesCuntzSystem Op)
    (p : ℕ) (hp : Nat.Prime p) (n m : ℕ+) :
    liouvilleAction C (MultiplicativeIndexing.primePNat p hp * (n * m)) = 
      -(S C (MultiplicativeIndexing.primePNat p hp) * liouvilleAction C (n * m)) :=
  liouville_action_anticommutes C p hp (n * m)

end InfoGeometry.Canonical.BostConnesAnticommutation
