import re

with open('lean/InfoGeometry/Lie/CanonicalZornG2ParabolicMellinCharacterBridge.lean', 'r') as f:
    content = f.read()

# Replace the proof of parabolicACharacter_apply
old_proof = """theorem parabolicACharacter_apply
    (ν : Fin 2 → ℂ) (x : Cartan) :
    (parabolicACharacter ν (Multiplicative.ofAdd x) : ℂ) =
      Complex.exp (∑ i : Fin 2,
        ν i * (simpleWeightOnCartan i x : ℂ)) := by
  unfold parabolicACharacter canonicalG2CartanMellinCharacterHom
    canonicalG2CartanMellinCharacterUnits
    canonicalG2CartanMellinCharacter rankTwoCartanMellinCharacter
  simp only [Multiplicative.toAdd_ofAdd]
  rw [← Complex.exp_neg]
  congr 1
  simp only [Pi.neg_apply, Complex.ofReal_neg, neg_mul,
    Finset.sum_neg_distrib]
  ring"""

new_proof = """theorem parabolicACharacter_apply
    (ν : Fin 2 → ℂ) (x : Cartan) :
    (parabolicACharacter ν (Multiplicative.ofAdd x) : ℂ) =
      Complex.exp (∑ i : Fin 2,
        ν i * (simpleWeightOnCartan i x : ℂ)) := by
  unfold parabolicACharacter canonicalG2CartanMellinCharacterHom
    canonicalG2CartanMellinCharacterUnits
    canonicalG2CartanMellinCharacter rankTwoCartanMellinCharacter
  simp only [Multiplicative.toAdd_ofAdd]
  rw [← Complex.exp_neg]
  congr 1
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]"""

content = content.replace(old_proof, new_proof)

with open('lean/InfoGeometry/Lie/CanonicalZornG2ParabolicMellinCharacterBridge.lean', 'w') as f:
    f.write(content)
