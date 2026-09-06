import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeLatticeGasVariational

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCutoffNative

open InfoGeometry.Arithmetic.PrimeLatticeGasVariational

abbrev PrimeCutoff (M : ℕ) : Type :=
  {p : Nat.Primes // (p : ℕ) ≤ M}

@[simp] theorem PrimeCutoff.val_prime
    {M : ℕ} (p : PrimeCutoff M) : Nat.Prime (p : ℕ) :=
  p.1.2

@[simp] theorem PrimeCutoff.val_le
    {M : ℕ} (p : PrimeCutoff M) : (p : ℕ) ≤ M :=
  p.2

def toPrimeCutoff {M : ℕ} (p : PrimeSites M) : PrimeCutoff M :=
  ⟨⟨p.1, PrimeSites.value_prime p⟩, PrimeSites.value_le_cutoff p⟩

def toPrimeSite {M : ℕ} (p : PrimeCutoff M) : PrimeSites M :=
  ⟨p.1.1, by
    simp [primeSiteFinset, p.2, p.1.2]⟩

@[simp] theorem toPrimeSite_toPrimeCutoff
    {M : ℕ} (p : PrimeSites M) :
    toPrimeSite (toPrimeCutoff p) = p := by
  rfl

@[simp] theorem toPrimeCutoff_toPrimeSite
    {M : ℕ} (p : PrimeCutoff M) :
    toPrimeCutoff (toPrimeSite p) = p := by
  cases p with
  | mk p hp =>
    cases p with
    | mk p hprime =>
      rfl

instance finitePrimeCutoff (M : ℕ) : Finite (PrimeCutoff M) :=
  Finite.of_injective toPrimeSite (by
    intro p q h
    calc
      p = toPrimeCutoff (toPrimeSite p) :=
        (toPrimeCutoff_toPrimeSite p).symm
      _ = toPrimeCutoff (toPrimeSite q) := congrArg toPrimeCutoff h
      _ = q := toPrimeCutoff_toPrimeSite q)

noncomputable instance fintypePrimeCutoff (M : ℕ) : Fintype (PrimeCutoff M) :=
  Fintype.ofFinite (PrimeCutoff M)

noncomputable def primeSitesEquiv (M : ℕ) : PrimeSites M ≃ PrimeCutoff M where
  toFun := toPrimeCutoff
  invFun := toPrimeSite
  left_inv := toPrimeSite_toPrimeCutoff
  right_inv := toPrimeCutoff_toPrimeSite

@[simp] theorem primeSitesEquiv_apply
    {M : ℕ} (p : PrimeSites M) :
    primeSitesEquiv M p = toPrimeCutoff p :=
  rfl

@[simp] theorem primeSitesEquiv_symm_apply
    {M : ℕ} (p : PrimeCutoff M) :
    (primeSitesEquiv M).symm p = toPrimeSite p :=
  rfl

theorem fintype_card_primeCutoff (M : ℕ) :
    Fintype.card (PrimeCutoff M) = primeSiteCount M := by
  calc
    Fintype.card (PrimeCutoff M) = Fintype.card (PrimeSites M) :=
      (Fintype.card_congr (primeSitesEquiv M)).symm
    _ = primeSiteCount M := fintype_card_PrimeSites M

theorem prod_primeCutoff_eq_prod_primeSites
    {R : Type*} [CommMonoid R] (M : ℕ)
    (f : PrimeCutoff M → R) :
    (∏ p : PrimeCutoff M, f p) =
      ∏ q : PrimeSites M, f (primeSitesEquiv M q) := by
  symm
  exact Fintype.prod_equiv
    (primeSitesEquiv M)
    (fun q : PrimeSites M => f (primeSitesEquiv M q))
    f
    (fun q => rfl)

end InfoGeometry.Arithmetic.PrimeCutoffNative
