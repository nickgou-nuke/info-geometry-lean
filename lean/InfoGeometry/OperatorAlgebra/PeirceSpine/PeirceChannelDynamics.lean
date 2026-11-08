/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Grading covariance of the Peirce corner channel

A residual Kraus operator in the even Peirce sector makes the corner channel
commute with pinching. Consequently the even sector is invariant under every
finite iterate of the channel. No commutativity of the matrix algebra is assumed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The adjoint preserves the even Peirce sector. -/
theorem star_evenGrade (P X : Mat) (hPs : star P = P) :
    star (evenGrade P X) = evenGrade P (star X) := by
  simp only [evenGrade, star_add, star_mul, star_sub, star_one, hPs, mul_assoc]

/-- Each of the two odd Kraus operators and an even residual Kraus operator
preserves parity by conjugation; hence their sum commutes with pinching. -/
theorem corner_channel_pinching_covariant (P A W X : Mat)
    (hP : P * P = P) (hPs : star P = P) (hW : evenGrade P W = W) :
    evenGrade P (InfoGeometry.Quantum.Choi.krausMap
      (cornerKrausWithResidual P A W) X) =
    InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
      (evenGrade P X) := by
  have hWs : evenGrade P (star W) = star W := by
    rw [← star_evenGrade P W hPs, hW]
  change evenGrade P (∑ i, cornerKrausWithResidual P A W i * X *
    star (cornerKrausWithResidual P A W i)) =
    ∑ i, cornerKrausWithResidual P A W i * evenGrade P X *
      star (cornerKrausWithResidual P A W i)
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  change evenGrade P (conePlus P A * X * star (conePlus P A) +
    coneMinus P (star A) * X * star (coneMinus P (star A)) + W * X * star W) =
    conePlus P A * evenGrade P X * star (conePlus P A) +
    coneMinus P (star A) * evenGrade P X * star (coneMinus P (star A)) +
      W * evenGrade P X * star W
  have hs : star (coneMinus P (star A)) = conePlus P A := by
    rw [← star_conePlus hPs A, star_star]
  rw [star_conePlus hPs A, hs, ← hWs, ← hW]
  unfold evenGrade conePlus coneMinus
  peirce_nf hP

theorem page_density_even (P A C : Mat) (hP : P * P = P) :
    evenGrade P (pageDensityOp P A C) = pageDensityOp P A C := by
  unfold evenGrade pageDensityOp qgtPlus qgtMinus conePlus coneMinus
  peirce_nf hP

/-- Every iterate of the existing density evolution remains in the even
sector when the residual Kraus operator belongs to that sector. -/
theorem cornerEvolution_even (P A W : Mat) (hP : P * P = P)
    (hPs : star P = P) (hW : evenGrade P W = W) (k : ℕ) :
    evenGrade P (cornerEvolution P A W k) = cornerEvolution P A W k := by
  induction k with
  | zero => exact page_density_even P A (star A) hP
  | succ k ih =>
      change evenGrade P (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) (cornerEvolution P A W k)) =
        InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
          (cornerEvolution P A W k)
      rw [corner_channel_pinching_covariant P A W _ hP hPs hW, ih]

/-- The positive residual has a canonical square root in the even sector.
The commutation with `P` is proved from the Peirce identities. -/
theorem exists_even_residual (P A : Mat) (hP : P * P = P)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, evenGrade P W = W ∧ star W * W = 1 - genV P A (star A) := by
  let R : Mat := 1 - genV P A (star A)
  let W : Mat := CFC.sqrt R
  have hRP : Commute R P := by
    change (1 - genV P A (star A)) * P = P * (1 - genV P A (star A))
    unfold genV anticomm conePlus coneMinus
    peirce_nf hP
  have hWP : Commute W P := by
    change Commute (cfcₙ NNReal.sqrt R) P
    exact hRP.cfcₙ_nnreal NNReal.sqrt
  have hWQ : W * (1 - P) = (1 - P) * W := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hWP.eq]
  have hEven : evenGrade P W = W := by
    unfold evenGrade
    simp only [mul_assoc]
    rw [hWP.eq, hWQ]
    peirce_nf hP
  refine ⟨W, hEven, ?_⟩
  have hstar : star W = W := (CFC.sqrt_nonneg R).star_eq
  rw [hstar]
  exact CFC.sqrt_mul_sqrt_self R hBound.nonneg

/-- Under the original metric bound the residual may be chosen so the
trace-preserving channel and its entire density evolution preserve grading. -/
theorem exists_graded_corner_evolution (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) (hTrace : Matrix.trace P = 1)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, star W * W = 1 - genV P A (star A) ∧
      (∀ X : Mat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) X) = Matrix.trace X) ∧
      (∀ k, (cornerEvolution P A W k).PosSemidef ∧
        Matrix.trace (cornerEvolution P A W k) = 1 ∧
        evenGrade P (cornerEvolution P A W k) = cornerEvolution P A W k) := by
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual P A hP hBound
  refine ⟨W, hResidual, fun X => cornerKrausWithResidual_trace P A W X hPs hResidual, ?_⟩
  intro k
  exact ⟨(cornerEvolution_is_density P A W hP hPs hTrace hBound hResidual k).1,
    (cornerEvolution_is_density P A W hP hPs hTrace hBound hResidual k).2,
    cornerEvolution_even P A W hP hPs hEven k⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics

end
