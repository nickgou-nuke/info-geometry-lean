import Mathlib

/-!
# Bost-Connes KMS State — Multiplicative Indexing

Zero axioms. BostConnesData structure carries the monoid homomorphism
S : PNat →* O_infty, Cuntz relations, and time evolution.
-/

noncomputable section

namespace InfoGeometry.Canonical.BostConnesKMS

open Complex

variable (O_infty : Type*) [Ring O_infty] [StarRing O_infty] [Algebra ℂ O_infty]

/--
Bost-Connes data: monoid homomorphism, Cuntz isometries, time evolution.
-/
structure BostConnesData where
  S_hom : PNat →* O_infty
  isometry : ∀ n, star (S_hom n) * S_hom n = 1
  orth_prime : ∀ p q, [Fact p.Prime] → [Fact q.Prime] → (p ≠ q) →
    star (S_hom ⟨p, (Fact.out : p.Prime).pos⟩) *
    S_hom ⟨q, (Fact.out : q.Prime).pos⟩ = 0
  σ : ℝ → O_infty →+* O_infty
  σ_apply_S : ∀ t n, σ t (S_hom n) = ((n : ℕ) : ℂ) ^ (t * Complex.I) • S_hom n
  σ_complex : ℂ → O_infty →ₗ[ℂ] O_infty
  σ_complex_apply_S : ∀ z n, σ_complex z (S_hom n) = ((n : ℕ) : ℂ) ^ (-z) • S_hom n

/-- S_n shorthand. -/
def S (D : BostConnesData O_infty) (n : PNat) : O_infty := D.S_hom n

/-- Prime generator. -/
def S_prime (D : BostConnesData O_infty) (p : ℕ) [Fact p.Prime] : O_infty :=
  S D ⟨p, Nat.Prime.pos (Fact.out)⟩

/--
KMS state at inverse temperature β.
  φ(A·B) = φ(B·σ_{iβ}(A))
-/
structure KMSState (D : BostConnesData O_infty) (β : ℝ) where
  val : O_infty →ₗ[ℂ] ℂ
  map_one : val 1 = 1
  kms_condition : ∀ A B, val (A * B) = val (B * D.σ_complex (Complex.I * (β : ℂ)) A)

end InfoGeometry.Canonical.BostConnesKMS
