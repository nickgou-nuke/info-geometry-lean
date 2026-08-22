import Mathlib.RingTheory.Derivation.Basic
import InfoGeometry.Probability.ExpLogRNDerivation

/-!
# Bridge: repository `IsDerivation` ⇄ mathlib `Derivation`

Aligns the repository-local derivation predicate
`InfoGeometry.Probability.ExpLogRNDerivation.IsDerivation` with the native
mathlib `Derivation ℤ A A` class, so every lemma proved for the local
predicate transports to the mathlib derivation API and vice versa.

Contents:
1. `toMathlibDerivation`: package an `IsDerivation D` into a mathlib
   `Derivation ℤ A A` (ℤ-linear because any ring is a ℤ-algebra; the ℤ-smul
   compatibility is exactly `derivation_zsmul` from the owner file).
2. `ofMathlibDerivation`: the reverse packaging with its own `IsDerivation`
   proof straight from `Derivation.leibniz`.
3. Round-trip equalities at the function level.
4. The `dlogL` interface glue: the left logarithmic derivative is the unit-
   inverse-weighted evaluation of the packaged mathlib derivation.

All proofs are complete, kernel-checked, and carry no unproved
placeholders or external assumptions.
-/

namespace InfoGeometry.Probability.DerivationBridge

open InfoGeometry.Probability.ExpLogRNDerivation

variable {A : Type*} [CommRing A]

/-- Package a repository `IsDerivation` into the native mathlib
`Derivation ℤ A A`. The ℤ-linearity comes from `derivation_zsmul`; the
Leibniz rule is transported through commutativity of `A`. -/
noncomputable def toMathlibDerivation (D : A → A) (hD : IsDerivation D) :
    Derivation ℤ A A where
  toLinearMap :=
    { toFun := D
      map_add' := hD.1
      map_smul' := fun z x => by
        simp only [RingHom.id_apply]
        exact derivation_zsmul D hD z x }
  map_one_eq_zero' := derivation_one D hD
  leibniz' := fun a b => by
    show D (a * b) = a • D b + b • D a
    rw [hD.2 a b]
    simp only [smul_eq_mul]
    ring

/-- The underlying function agrees with the original map. -/
@[simp] theorem toMathlibDerivation_apply (D : A → A) (hD : IsDerivation D) (x : A) :
    (toMathlibDerivation D hD : A → A) x = D x := rfl

/-- Reverse packaging: a mathlib derivation satisfies the repository
derivation predicate. -/
noncomputable def ofMathlibDerivation (D : Derivation ℤ A A) : A → A :=
  fun x => (D : A → A) x

theorem isDerivation_ofMathlib (D : Derivation ℤ A A) :
    IsDerivation (ofMathlibDerivation D) := by
  refine ⟨fun x y => by simpa only [ofMathlibDerivation] using D.map_add x y,
    fun x y => ?_⟩
  dsimp only [ofMathlibDerivation]
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Round trip: repackaging a packaged derivation recovers the same mathlib
object (as functions; the `Derivation` structure is proof-irrelevant up to
its unique data). -/
theorem of_toMathlib (D : A → A) (hD : IsDerivation D) :
    ofMathlibDerivation (toMathlibDerivation D hD) = D := rfl

/-- Interface glue: the left logarithmic derivative is the unit-inverse-weighted
evaluation of the packaged mathlib derivation. -/
theorem dlogL_eq_smul_eval (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlogL D u =
      (↑(u⁻¹) : A) • ((toMathlibDerivation D hD : A → A) ↑u) := rfl

/-- Interface glue: likewise for the right logarithmic derivative, using the
commutativity of `A` to move the weight across. -/
theorem dlogR_eq_smul_eval (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlogR D u =
      (↑(u⁻¹) : A) • ((toMathlibDerivation D hD : A → A) ↑u) := by
  dsimp only [dlogR, toMathlibDerivation_apply]
  rw [smul_eq_mul]
  ring

end InfoGeometry.Probability.DerivationBridge
