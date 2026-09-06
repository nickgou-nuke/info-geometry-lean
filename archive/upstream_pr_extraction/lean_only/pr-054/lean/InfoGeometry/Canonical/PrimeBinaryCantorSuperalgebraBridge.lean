import Mathlib.Tactic
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
import InfoGeometry.Quantum.Hurwitz
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge

Finite theorem-safe bridge between three existing repo surfaces:

* binary Cantor cylinders on finite binary words;
* finite prime superalgebra / Möbius parity readback;
* finite Hurwitz 24-shell units.

This file does not assert any fractal dimension theorem, self-similarity limit,
new superalgebra construction, or RH claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge

open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
open InfoGeometry.Quantum.Hurwitz

/-! ## Supergraded prime labels -/

/-- The finite supergrade used for the prime label convention. -/
@[rep_depth operator]
inductive PrimeSectorGrade where
  | bosonic
  | fermionic
  deriving DecidableEq, Repr

/-- Prime `2` is the bosonic label; odd primes are in the fermionic label. -/
@[rep_depth operator]
def primeSectorGrade (p : ℕ) : PrimeSectorGrade :=
  if p = 2 then .bosonic else .fermionic

@[simp]
theorem primeSectorGrade_two :
    primeSectorGrade 2 = PrimeSectorGrade.bosonic := by
  simp [primeSectorGrade]

/-- Prime labels other than `2` are assigned to the fermionic sector. -/
@[rep_depth operator]
theorem primeSectorGrade_prime_ne_two
    {p : ℕ} (_hp : Nat.Prime p) (h2 : p ≠ 2) :
    primeSectorGrade p = PrimeSectorGrade.fermionic := by
  simp [primeSectorGrade, h2]

@[simp]
theorem primeSectorGrade_bosonic_iff
    {p : ℕ} :
    primeSectorGrade p = PrimeSectorGrade.bosonic ↔ p = 2 := by
  simp [primeSectorGrade]

@[simp]
theorem primeSectorGrade_fermionic_iff
    {p : ℕ} :
    primeSectorGrade p = PrimeSectorGrade.fermionic ↔ p ≠ 2 := by
  simp [primeSectorGrade]

/-- Möbius parity readback on represented squarefree prime-bit states. -/
@[rep_depth operator]
theorem mobiusParity_readback
    (P : FermionicPrimeRegister) (ψ : FermionicPrimeState P) :
    ArithmeticFunction.moebius (representedSquarefreeNat P ψ) =
      fermionParity P ψ := by
  simpa using (mobius_eq_fermionParity P ψ)

/-- Finite supertrace readback equals the finite inverse Euler product. -/
@[rep_depth operator]
theorem finiteSupertrace_readback
    (P : FermionicPrimeRegister) (x : ℕ → ℂ) :
    finiteSupertraceDirichlet P x = finiteInverseEulerProduct P x := by
  simpa using (finiteSupertraceDirichlet_eq_inverseEulerProduct P x)

/-! ## Hurwitz shell readback -/

/-- The 24 Hurwitz shell directions are norm-one units. -/
@[rep_depth operator]
theorem hurwitzDirection_isHurwitzUnit (i : Fin 24) :
    IsHurwitzUnit (hurwitzDirection i) :=
  Quantum.Hurwitz.hurwitzDirection_isHurwitzUnit i

/-
The finite theorem content remains:
* binary Cantor cylinder splitting;
* prime supergraded labels with bosonic `2` and fermionic odd primes;
* prime Möbius/supertrace readback;
* Hurwitz 24-shell units.
-/

end InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge
