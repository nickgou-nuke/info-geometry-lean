import InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split-Cartan character interface

This owner records the finite logarithmic form of a split-Cartan character.
It deliberately stops at the additive Cartan character: no parabolic
induction, irreducibility, or non-abelian Fourier transform is asserted.
The sign convention is `ν = -s`, so the existing Mellin kernel
`exp (-⟪s,t⟫)` is the standard character `exp (⟪ν,t⟫)`.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2SplitCartanCharacter

open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Cartan := CanonicalZornG2CartanMellinBridge.Cartan

/-- The logarithmic split-Cartan character with Langlands-style parameter `ν`.
    The argument is the additive logarithmic Cartan coordinate. -/
def splitCartanCharacter (ν : Fin 2 → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  Complex.exp (∑ i : Fin 2, ν i * (t i : ℂ))

@[simp] theorem splitCartanCharacter_zero (ν : Fin 2 → ℂ) :
    splitCartanCharacter ν 0 = 1 := by
  simp [splitCartanCharacter]

theorem splitCartanCharacter_add (ν : Fin 2 → ℂ)
    (t u : Fin 2 → ℝ) :
    splitCartanCharacter ν (fun i => t i + u i) =
      splitCartanCharacter ν t * splitCartanCharacter ν u := by
  unfold splitCartanCharacter
  rw [← Complex.exp_add]
  congr 1
  change (∑ i : Fin 2, ν i * ((t i + u i : ℝ) : ℂ)) = _
  calc
    (∑ i : Fin 2, ν i * ((t i + u i : ℝ) : ℂ)) =
        ∑ i : Fin 2, (ν i * (t i : ℂ) + ν i * (u i : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          push_cast
          ring
    _ = (∑ i : Fin 2, ν i * (t i : ℂ)) +
        (∑ i : Fin 2, ν i * (u i : ℂ)) := by
          rw [Finset.sum_add_distrib]

theorem splitCartanCharacter_ne_zero (ν : Fin 2 → ℂ) (t : Fin 2 → ℝ) :
    splitCartanCharacter ν t ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- The split-Cartan character as a unit-valued multiplicative character. -/
def splitCartanCharacterUnits (ν : Fin 2 → ℂ) (t : Fin 2 → ℝ) : ℂˣ :=
  Units.mk0 (splitCartanCharacter ν t) (splitCartanCharacter_ne_zero ν t)

/-- Homomorphism packaging of the additive logarithmic Cartan character. -/
def splitCartanCharacterHom (ν : Fin 2 → ℂ) :
    Multiplicative (Fin 2 → ℝ) →* ℂˣ where
  toFun t := splitCartanCharacterUnits ν (Multiplicative.toAdd t)
  map_one' := by
    ext
    exact splitCartanCharacter_zero ν
  map_mul' t u := by
    ext
    exact splitCartanCharacter_add ν (Multiplicative.toAdd t) (Multiplicative.toAdd u)

theorem rankTwoCartanMellinCharacter_eq_splitCartanCharacter_neg
    (s : Fin 2 → ℂ) (t : Fin 2 → ℝ) :
    rankTwoCartanMellinCharacter s t =
      splitCartanCharacter (fun i => -s i) t := by
  unfold rankTwoCartanMellinCharacter splitCartanCharacter
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

theorem canonicalG2CartanMellinCharacter_eq_splitCartanCharacter_neg
    (s : Fin 2 → ℂ) (x : Cartan) :
    canonicalG2CartanMellinCharacter s x =
      splitCartanCharacter (fun i => -s i)
        (fun i => (simpleWeightOnCartan i x : ℝ)) := by
  unfold canonicalG2CartanMellinCharacter
  exact rankTwoCartanMellinCharacter_eq_splitCartanCharacter_neg s _

end InfoGeometry.Lie.CanonicalZornG2SplitCartanCharacter
