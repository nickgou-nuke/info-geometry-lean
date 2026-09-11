import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2RootAutPC3Conjugation
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts

/-!
# Native obstruction for the proposed PC-word rotation

The native obstruction `not_c_conj_pc3Aut_eq_pc1Aut` shows that the proposed
rotation of the singleton PC word

```lean
c * pcWord (oneAt (2 : Fin 6)) * c⁻¹ = pcWord (oneAt (0 : Fin 6))
```

is incompatible with the current kernel-checked coordinate conventions.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutPCConjugation

open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2RootAutPC3Conjugation
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts

/-- Under the current native carrier conventions, conjugating the singleton PC
word at coordinate `2` by `c` does not produce the singleton PC word at
coordinate `0`. -/
theorem not_c_conj_pcWord_oneAt_two_eq_oneAt_zero :
    ¬ c * G2TwoSylowSubgroup.pcWord (oneAt (2 : Fin 6)) * c⁻¹ =
      G2TwoSylowSubgroup.pcWord (oneAt (0 : Fin 6)) := by
  intro h
  have h₁ : G2TwoSylowSubgroup.pcWord (oneAt (2 : Fin 6)) = pc3Aut := by
    rw [pcWord_oneAt_eq_generator]
    rfl
  have h₂ : G2TwoSylowSubgroup.pcWord (oneAt (0 : Fin 6)) = pc1Aut := by
    rw [pcWord_oneAt_eq_generator]
    rfl
  apply not_c_conj_pc3Aut_eq_pc1Aut
  calc
    c * pc3Aut * c⁻¹ =
        c * G2TwoSylowSubgroup.pcWord (oneAt (2 : Fin 6)) * c⁻¹ := by
      simpa [h₁]
    _ = G2TwoSylowSubgroup.pcWord (oneAt (0 : Fin 6)) := h
    _ = pc1Aut := by simpa [h₂]

end InfoGeometry.Algebra.Zorn.G2RootAutPCConjugation
