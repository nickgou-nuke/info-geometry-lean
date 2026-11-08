import InfoGeometry.Physics.ZornMultiplicationOverBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A concrete associative slice of the operator-valued Zorn carrier

The full noncommutative Zorn carrier is not made into an associative operator
algebra.  For a commutative coefficient ring, however, the existing
single-colour matrix embedding is multiplicative.  This owner packages that
fact as a genuine `MulHom` and records injectivity of the slice.
-/

namespace InfoGeometry.Physics.PalatialTwistor

open InfoGeometry.Physics.NCG

variable {C : Type*} [CommRing C]

def singleColourMulHom (c : Fin 3) :
    Matrix (Fin 2) (Fin 2) C →ₙ* NCZornElement C where
  toFun := singleColourEmbedding c
  map_mul' M N := singleColourEmbedding_map_mul c M N

@[simp] theorem singleColourMulHom_apply (c : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) C) :
    singleColourMulHom c M = singleColourEmbedding c M := rfl

theorem singleColourEmbedding_injective (c : Fin 3) :
    Function.Injective (singleColourEmbedding c :
      Matrix (Fin 2) (Fin 2) C → NCZornElement C) := by
  intro M N h
  funext i j
  fin_cases i <;> fin_cases j
  · exact congrArg NCZornElement.n_plus h
  · have hs := congrFun (congrArg NCZornElement.sigma_plus h) c
    simpa [singleColourEmbedding] using hs
  · have hs := congrFun (congrArg NCZornElement.sigma_minus h) c
    simpa [singleColourEmbedding] using hs
  · exact congrArg NCZornElement.n_minus h

theorem singleColourMulHom_injective (c : Fin 3) :
    Function.Injective (singleColourMulHom (C := C) c) :=
  by
    change Function.Injective (singleColourEmbedding c :
      Matrix (Fin 2) (Fin 2) C → NCZornElement C)
    exact singleColourEmbedding_injective c

theorem singleColour_associativity_on_image (c : Fin 3)
    (M N P : Matrix (Fin 2) (Fin 2) C) :
    ((singleColourEmbedding c M) * (singleColourEmbedding c N)) *
        singleColourEmbedding c P =
      singleColourEmbedding c M *
        ((singleColourEmbedding c N) * (singleColourEmbedding c P)) := by
  calc
    ((singleColourEmbedding c M) * (singleColourEmbedding c N)) *
          singleColourEmbedding c P =
        singleColourEmbedding c (M * N) * singleColourEmbedding c P := by
          exact congrArg (fun X => X * singleColourEmbedding c P)
            (singleColourEmbedding_map_mul c M N).symm
    _ = singleColourEmbedding c ((M * N) * P) := by
          exact (singleColourEmbedding_map_mul c (M * N) P).symm
    _ = singleColourEmbedding c (M * (N * P)) := by
          rw [Matrix.mul_assoc]
    _ = singleColourEmbedding c M *
          singleColourEmbedding c (N * P) := by
          exact singleColourEmbedding_map_mul c M (N * P)
    _ = singleColourEmbedding c M *
          (singleColourEmbedding c N * singleColourEmbedding c P) := by
          exact congrArg (fun X => singleColourEmbedding c M * X)
            (singleColourEmbedding_map_mul c N P)

end InfoGeometry.Physics.PalatialTwistor
