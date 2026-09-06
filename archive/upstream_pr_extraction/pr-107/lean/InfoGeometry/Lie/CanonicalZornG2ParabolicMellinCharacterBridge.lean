import InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
import InfoGeometry.Lie.CanonicalZornG2SplitCartanCharacter

/-!
# Parabolic `A`-character readout for the canonical rank-two Cartan

The standard parabolic convention writes a character of the split torus as
`χ_ν (exp X) = exp (ν X)`.  The Cartan Mellin owner uses the thermodynamic
convention `exp (-⟪s, X⟫)`.  This file records only the honest dictionary
`ν = -s`, using the already constructed `ℂˣ`-valued character.  It does not
introduce a reductive group, a parabolic subgroup, or an induced
representation.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2ParabolicMellinCharacterBridge

open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Lie.CanonicalZornG2SplitCartanCharacter
open InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev Cartan := CanonicalZornG2CartanMellinBridge.Cartan

/-- The logarithmic split-Cartan character with spectral parameter `ν`.

This is the character kernel on the additive Cartan coordinate.  It is not a
claim that a concrete Lie group `A = exp 𝔞₀` has been constructed here.
-/
def logarithmicACharacter (ν : Fin 2 → ℂ) (x : Cartan) : ℂ :=
  Complex.exp (∑ i : Fin 2, ν i * (simpleWeightOnCartan i x : ℂ))

def parabolicSpectralParameter (s : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => -s i

theorem logarithmicACharacter_neg_eq_mellin
    (s : Fin 2 → ℂ) (x : Cartan) :
    logarithmicACharacter (parabolicSpectralParameter s) x =
      canonicalG2CartanMellinCharacter s x := by
  unfold logarithmicACharacter parabolicSpectralParameter
    canonicalG2CartanMellinCharacter rankTwoCartanMellinCharacter
  congr 1
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem logarithmicACharacter_eq_mellin_neg
    (ν : Fin 2 → ℂ) (x : Cartan) :
    logarithmicACharacter ν x =
      canonicalG2CartanMellinCharacter (fun i => -ν i) x := by
  have hparam : parabolicSpectralParameter (fun i => -ν i) = ν := by
    funext i
    simp [parabolicSpectralParameter]
  have h := logarithmicACharacter_neg_eq_mellin (s := fun i => -ν i) (x := x)
  rw [hparam] at h
  exact h

@[simp] theorem logarithmicACharacter_zero (ν : Fin 2 → ℂ) :
    logarithmicACharacter ν 0 = 1 := by
  rw [logarithmicACharacter_eq_mellin_neg]
  exact canonicalG2CartanMellinCharacter_zero _

theorem logarithmicACharacter_add
    (ν : Fin 2 → ℂ) (x y : Cartan) :
    logarithmicACharacter ν (x + y) =
      logarithmicACharacter ν x * logarithmicACharacter ν y := by
  rw [logarithmicACharacter_eq_mellin_neg,
    logarithmicACharacter_eq_mellin_neg,
    logarithmicACharacter_eq_mellin_neg,
    canonicalG2CartanMellinCharacter_add]

theorem logarithmicACharacter_ne_zero
    (ν : Fin 2 → ℂ) (x : Cartan) :
    logarithmicACharacter ν x ≠ 0 := by
  rw [logarithmicACharacter_eq_mellin_neg]
  exact canonicalG2CartanMellinCharacter_ne_zero _ _

theorem logarithmicACharacter_eq_splitCartanCharacter
    (ν : Fin 2 → ℂ) (x : Cartan) :
    logarithmicACharacter ν x =
      splitCartanCharacter ν
        (fun i => (simpleWeightOnCartan i x : ℝ)) := by
  calc
    logarithmicACharacter ν x =
        canonicalG2CartanMellinCharacter (fun i => -ν i) x :=
      logarithmicACharacter_eq_mellin_neg ν x
    _ = splitCartanCharacter (fun i => -(-ν i))
          (fun i => (simpleWeightOnCartan i x : ℝ)) := by
      exact canonicalG2CartanMellinCharacter_eq_splitCartanCharacter_neg
        (fun i => -ν i) x
    _ = splitCartanCharacter ν
          (fun i => (simpleWeightOnCartan i x : ℝ)) := by
      congr 1
      funext i
      simp

/-- The parabolic split-Cartan character with parameter `ν`.

The source is the multiplicative adapter for the additive Cartan, so this is
the type-level character corresponding to `χ_ν(exp X) = exp (ν X)` under the
identification `ν = -s`.
-/
def parabolicACharacter (ν : Fin 2 → ℂ) : Multiplicative Cartan →* ℂˣ :=
  canonicalG2CartanMellinCharacterHom (fun i => -ν i)

theorem parabolicACharacter_parameter_dictionary
    (s : Fin 2 → ℂ) :
    parabolicACharacter (fun i => -s i) =
      canonicalG2CartanMellinCharacterHom s := by
  unfold parabolicACharacter
  congr 1
  funext i
  simp

theorem parabolicACharacter_apply
    (ν : Fin 2 → ℂ) (x : Cartan) :
    (parabolicACharacter ν (Multiplicative.ofAdd x) : ℂ) =
      Complex.exp (∑ i : Fin 2,
        ν i * (simpleWeightOnCartan i x : ℂ)) := by
  change canonicalG2CartanMellinCharacter (fun i => -ν i) x = _
  unfold canonicalG2CartanMellinCharacter rankTwoCartanMellinCharacter
  congr 1
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]

theorem parabolicACharacter_one (ν : Fin 2 → ℂ) :
    parabolicACharacter ν 1 = 1 := by
  exact (parabolicACharacter ν).map_one

theorem parabolicACharacter_mul
    (ν : Fin 2 → ℂ) (x y : Multiplicative Cartan) :
    parabolicACharacter ν (x * y) =
      parabolicACharacter ν x * parabolicACharacter ν y := by
  exact (parabolicACharacter ν).map_mul x y

end InfoGeometry.Lie.CanonicalZornG2ParabolicMellinCharacterBridge
