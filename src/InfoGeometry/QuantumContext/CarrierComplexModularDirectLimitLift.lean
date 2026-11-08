/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.CarrierInnerComplexFlowNaturality

/-!
# Universal algebra-hom lift of the fixed-seed complex inner action

The complex exponential and its opposite-parameter exponential give inverse
elements in the algebraic matrix direct limit. Conjugation by them defines a
compatible family of `ℂ`-algebra homomorphisms from every full matrix stage
to the carrier. The direct-limit universal property gives the bundled
homomorphism, and its stage restrictions uniquely determine it. The scope is
algebraic and uses a fixed finite seed; no arbitrary-parameter
star-preservation, holomorphicity, or completion claim is made.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.CarrierComplexModularDirectLimitLift

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.CarrierInnerModularBoundary
open InfoGeometry.QuantumContext.CarrierInnerComplexFlowNaturality

/-- The finite-stage complex exponentials at opposite parameters multiply to
the identity in either order. -/
theorem complexModularExponential_mul_neg (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) :
    complexModularExponential k logits β z *
      complexModularExponential k logits β (-z) = 1 := by
  rw [complexModularExponential, complexModularExponential,
    Matrix.diagonal_mul_diagonal]
  have hdiag :
      (fun i : Fin (2 ^ k) =>
        complexModularPhase k logits β z i *
          complexModularPhase k logits β (-z) i) = fun _ => 1 := by
    funext i
    dsimp [complexModularPhase]
    rw [← Complex.exp_add]
    rw [show Complex.I * z * (β : ℂ) * (logits i : ℂ) +
        Complex.I * (-z) * (β : ℂ) * (logits i : ℂ) = 0 by ring]
    simp
  rw [hdiag, Matrix.diagonal_one]

/-- The opposite order of the finite-stage exponentials also gives the
identity. -/
theorem complexModularExponential_neg_mul (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) :
    complexModularExponential k logits β (-z) *
      complexModularExponential k logits β z = 1 := by
  rw [complexModularExponential, complexModularExponential,
    Matrix.diagonal_mul_diagonal]
  have hdiag :
      (fun i : Fin (2 ^ k) =>
        complexModularPhase k logits β (-z) i *
          complexModularPhase k logits β z i) = fun _ => 1 := by
    funext i
    dsimp [complexModularPhase]
    rw [← Complex.exp_add]
    rw [show Complex.I * (-z) * (β : ℂ) * (logits i : ℂ) +
        Complex.I * z * (β : ℂ) * (logits i : ℂ) = 0 by ring]
    simp
  rw [hdiag, Matrix.diagonal_one]

/-- The embedded complex exponential and its opposite-parameter exponential
are two-sided inverses in the algebraic matrix direct limit. -/
theorem carrierComplexModularExponential_mul_neg (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) :
    stageInjection k (complexModularExponential k logits β z) *
      stageInjection k (complexModularExponential k logits β (-z)) = 1 := by
  rw [← stageInjection_mul, complexModularExponential_mul_neg, map_one]

/-- The reverse product of the embedded exponentials is also the identity. -/
theorem carrierComplexModularExponential_neg_mul (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) :
    stageInjection k (complexModularExponential k logits β (-z)) *
      stageInjection k (complexModularExponential k logits β z) = 1 := by
  rw [← stageInjection_mul, complexModularExponential_neg_mul, map_one]

private theorem innerConjugation_mul {A : Type*} [Ring A]
    (u v x y : A) (hvu : v * u = 1) :
    (u * x * v) * (u * y * v) = u * (x * y) * v := by
  calc
    (u * x * v) * (u * y * v) = u * x * (v * u) * y * v := by
      simp only [mul_assoc]
    _ = u * x * 1 * y * v := by rw [hvu]
    _ = u * (x * y) * v := by simp only [one_mul, mul_assoc]

/-- Stage `n` mapped into the carrier, followed by conjugation by the fixed
seed's complex exponential and its inverse. -/
def stageComplexConjugation (k n : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) (z : ℂ) : MatrixStage n →ₐ[ℂ] Carrier where
  toFun A :=
    stageInjection k (complexModularExponential k logits β z) *
      stageInjection n A *
        stageInjection k (complexModularExponential k logits β (-z))
  map_one' := by
    calc
      stageInjection k (complexModularExponential k logits β z) *
          stageInjection n (1 : MatrixStage n) *
          stageInjection k (complexModularExponential k logits β (-z)) =
        stageInjection k (complexModularExponential k logits β z) *
          1 * stageInjection k (complexModularExponential k logits β (-z)) := by
            rw [map_one]
      _ = 1 := by rw [mul_one, carrierComplexModularExponential_mul_neg]
  map_mul' A B := by
    change stageInjection k (complexModularExponential k logits β z) *
        stageInjection n (A * B) *
          stageInjection k (complexModularExponential k logits β (-z)) = _
    rw [stageInjection_mul]
    exact (innerConjugation_mul
      (stageInjection k (complexModularExponential k logits β z))
      (stageInjection k (complexModularExponential k logits β (-z)))
      (stageInjection n A) (stageInjection n B)
      (carrierComplexModularExponential_neg_mul k logits β z)).symm
  map_zero' := by
    calc
      stageInjection k (complexModularExponential k logits β z) *
          stageInjection n (0 : MatrixStage n) *
          stageInjection k (complexModularExponential k logits β (-z)) =
        stageInjection k (complexModularExponential k logits β z) *
          0 * stageInjection k (complexModularExponential k logits β (-z)) := by
            rw [map_zero]
      _ = 0 := by simp
  map_add' A B := by
    change stageInjection k (complexModularExponential k logits β z) *
        stageInjection n (A + B) *
          stageInjection k (complexModularExponential k logits β (-z)) = _
    rw [stageInjection_add]
    simp only [add_mul, mul_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [map_smul, map_one]
    calc
      stageInjection k (complexModularExponential k logits β z) *
          (c • (1 : Carrier)) *
          stageInjection k (complexModularExponential k logits β (-z)) =
        c • (stageInjection k (complexModularExponential k logits β z) *
          1 * stageInjection k (complexModularExponential k logits β (-z))) := by
            calc
              _ = (stageInjection k (complexModularExponential k logits β z) *
                  (c • (1 : Carrier))) *
                    stageInjection k (complexModularExponential k logits β (-z)) := by
                  rw [mul_assoc]
              _ = (c • (stageInjection k
                  (complexModularExponential k logits β z) * 1)) *
                    stageInjection k (complexModularExponential k logits β (-z)) := by
                  rw [Algebra.mul_smul_comm]
              _ = c • ((stageInjection k
                  (complexModularExponential k logits β z) * 1) *
                    stageInjection k (complexModularExponential k logits β (-z))) := by
                  rw [Algebra.smul_mul_assoc]
      _ = c • (1 : Carrier) := by
        rw [mul_one, carrierComplexModularExponential_mul_neg]

/-- The stage conjugation maps are compatible with every matrix-tower
bonding homomorphism. -/
theorem stageComplexConjugation_compatible {k m n : ℕ} (hmn : m ≤ n)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) (A : MatrixStage m) :
    stageComplexConjugation k n logits β z (rawMap hmn A) =
      stageComplexConjugation k m logits β z A := by
  change stageInjection k (complexModularExponential k logits β z) *
      stageInjection n (rawMap hmn A) *
        stageInjection k (complexModularExponential k logits β (-z)) =
    stageInjection k (complexModularExponential k logits β z) *
      stageInjection m A *
        stageInjection k (complexModularExponential k logits β (-z))
  rw [stageInjection_transition hmn]

/-- The compatible stage maps lifted by the universal property of the actual
algebraic matrix direct limit. -/
noncomputable def carrierComplexModularFlowAlgHom (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) :
    Carrier →ₐ[ℂ] Carrier := by
  exact DirectLimit.Algebra.lift MatrixStage
    (fun _ _ h => rawMap h) Carrier
    (fun n => stageComplexConjugation k n logits β z)
    (by
      intro m n h A
      exact stageComplexConjugation_compatible h logits β z A)

/-- Stage readout of the lifted algebra homomorphism. -/
@[simp]
theorem carrierComplexModularFlowAlgHom_stage (k n : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) (A : MatrixStage n) :
    carrierComplexModularFlowAlgHom k logits β z (stageInjection n A) =
      stageComplexConjugation k n logits β z A := by
  unfold carrierComplexModularFlowAlgHom
  rw [stageInjection_apply]
  change DirectLimit.Algebra.lift MatrixStage
      (fun _ _ h => rawMap h) Carrier
      (fun n => stageComplexConjugation k n logits β z) _
      (DirectLimit.Algebra.of MatrixStage
        (fun _ _ h => rawMap h) n A) = _
  rw [DirectLimit.Algebra.lift_of]

/-- The bundled lift has the same pointwise values as the previously defined
complex inner action on every element of the carrier. -/
theorem carrierComplexModularFlowAlgHom_eq_pointwise (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) (x : Carrier) :
    carrierComplexModularFlowAlgHom k logits β z x =
      carrierComplexModularFlow k logits β z x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [← stageInjection_apply, carrierComplexModularFlowAlgHom_stage]
      rfl

/-- Uniqueness of the lifted homomorphism: any `ℂ`-algebra homomorphism from
the carrier with these stage readouts equals the universal lift. -/
theorem carrierComplexModularFlowAlgHom_unique (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ)
    (f : Carrier →ₐ[ℂ] Carrier)
    (hf : ∀ n A, f (stageInjection n A) =
      stageComplexConjugation k n logits β z A) :
    f = carrierComplexModularFlowAlgHom k logits β z := by
  apply DFunLike.ext
  intro x
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [← stageInjection_apply, hf n A,
        carrierComplexModularFlowAlgHom_stage]

end InfoGeometry.QuantumContext.CarrierComplexModularDirectLimitLift

end
