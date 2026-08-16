import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Chiral Hodge differential data

This owner keeps the Hodge/Tomita involution and the chiral grading distinct.
The codifferential, Hestenes phase axis, Hodge--Dirac operator, and Hodge
Laplacian are derived from the primitive data.  No modular-surprisal
identification is assumed here.
-/

namespace InfoGeometry.Dynamics.ChiralHodgeDifferential

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable section

local notation "EndH" => H →L[ℝ] H

structure Data where
  /-- Hodge/Tomita reflection. -/
  J : EndH
  /-- Chiral/fundamental grading. -/
  Gamma : EndH
  /-- Exterior-differential branch. -/
  d : EndH
  J_sq : J * J = (1 : EndH)
  Gamma_sq : Gamma * Gamma = (1 : EndH)
  J_Gamma_anticomm : J * Gamma = -(Gamma * J)
  d_sq : d * d = 0
  d_odd : Gamma * d = -(d * Gamma)

namespace Data

variable (D : Data (H := H))

noncomputable def delta : EndH := D.J * D.d * D.J

noncomputable def hestenesAxis : EndH := D.J * D.Gamma

/-- Symmetric Jordan channel obtained by left/right multiplication by the
Hestenes phase axis. -/
noncomputable def jordanChannel (A : EndH) : EndH :=
  (2 : ℝ)⁻¹ • (D.hestenesAxis * A + A * D.hestenesAxis)

/-- Antisymmetric Lie channel obtained by left/right multiplication by the
Hestenes phase axis. -/
noncomputable def lieChannel (A : EndH) : EndH :=
  (2 : ℝ)⁻¹ • (D.hestenesAxis * A - A * D.hestenesAxis)

noncomputable def hodgeDirac : EndH := D.d + D.delta

noncomputable def hodgeLaplacian : EndH :=
  D.d * D.delta + D.delta * D.d

/-- The two-coordinate relative surprisal in the native operator carrier. -/
noncomputable def relativeSurprisal (κ a : ℝ) : EndH :=
  κ • (1 : EndH) + a • D.Gamma

theorem delta_sq : D.delta * D.delta = 0 := by
  dsimp [delta]
  calc
    (D.J * D.d * D.J) * (D.J * D.d * D.J) =
        D.J * D.d * (D.J * D.J) * D.d * D.J := by
          noncomm_ring
    _ = D.J * D.d * (1 : EndH) * D.d * D.J := by
          rw [D.J_sq]
    _ = D.J * (D.d * D.d) * D.J := by
          noncomm_ring
    _ = 0 := by
          rw [D.d_sq]
          simp

theorem delta_odd : D.Gamma * D.delta = -(D.delta * D.Gamma) := by
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  dsimp [delta]
  calc
    D.Gamma * (D.J * D.d * D.J) =
        (D.Gamma * D.J) * D.d * D.J := by
          noncomm_ring
    _ = (-(D.J * D.Gamma)) * D.d * D.J := by
          rw [hGammaJ]
    _ = -(D.J * (D.Gamma * D.d) * D.J) := by
          noncomm_ring
    _ = -(D.J * (-(D.d * D.Gamma)) * D.J) := by
          rw [D.d_odd]
    _ = D.J * (D.d * D.Gamma) * D.J := by
          simp
    _ = D.J * D.d * (D.Gamma * D.J) := by
          noncomm_ring
    _ = D.J * D.d * (-(D.J * D.Gamma)) := by
          rw [hGammaJ]
    _ = -(D.J * D.d * D.J * D.Gamma) := by
          rw [mul_neg]
          congr 1

theorem hestenesAxis_sq : D.hestenesAxis * D.hestenesAxis = -(1 : EndH) := by
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  dsimp [hestenesAxis]
  calc
    (D.J * D.Gamma) * (D.J * D.Gamma) =
        D.J * (D.Gamma * D.J) * D.Gamma := by
          noncomm_ring
    _ = D.J * (-(D.J * D.Gamma)) * D.Gamma := by
          rw [hGammaJ]
    _ = -(1 : EndH) := by
          calc
            D.J * (-(D.J * D.Gamma)) * D.Gamma =
                -(D.J * D.J * D.Gamma * D.Gamma) := by
                  noncomm_ring
            _ = -(1 : EndH) := by
                  rw [D.J_sq]
                  simp only [one_mul]
                  rw [D.Gamma_sq]

theorem hestenesAxis_gamma_anticommute :
    D.hestenesAxis * D.Gamma + D.Gamma * D.hestenesAxis = 0 := by
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  dsimp [hestenesAxis]
  calc
    (D.J * D.Gamma) * D.Gamma + D.Gamma * (D.J * D.Gamma) =
        D.J * (D.Gamma * D.Gamma) + (D.Gamma * D.J) * D.Gamma := by
          noncomm_ring
    _ = D.J * (D.Gamma * D.Gamma) + (-(D.J * D.Gamma)) * D.Gamma := by
          rw [hGammaJ]
    _ = D.J * (D.Gamma * D.Gamma) - D.J * (D.Gamma * D.Gamma) := by
          noncomm_ring
    _ = 0 := by
          rw [D.Gamma_sq]
          simp

theorem hestenesAxis_gamma_commutator :
    D.hestenesAxis * D.Gamma - D.Gamma * D.hestenesAxis =
      (2 : ℝ) • D.J := by
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  dsimp [hestenesAxis]
  calc
    (D.J * D.Gamma) * D.Gamma - D.Gamma * (D.J * D.Gamma) =
        D.J * (D.Gamma * D.Gamma) - (D.Gamma * D.J) * D.Gamma := by
          noncomm_ring
    _ = D.J * (D.Gamma * D.Gamma) - (-(D.J * D.Gamma)) * D.Gamma := by
          rw [hGammaJ]
    _ = D.J * (D.Gamma * D.Gamma) + D.J * (D.Gamma * D.Gamma) := by
          noncomm_ring
    _ = (2 : ℝ) • D.J := by
          rw [D.Gamma_sq]
          simp [two_smul]

/-! ## Real nilpotent/projector basis

The three operators below are derived from the existing real involutions.  In
particular, `J` remains the Hodge/Tomita involution, `Gamma` remains the
grading, and `hestenesAxis = J * Gamma` is the real phase axis.  No complex
scalar or second Clifford carrier is introduced.
-/

noncomputable def nilpotentPlus : EndH :=
  (2 : ℝ)⁻¹ • (D.J - D.hestenesAxis)

noncomputable def nilpotentMinus : EndH :=
  (2 : ℝ)⁻¹ • (D.J + D.hestenesAxis)

noncomputable def nilpotentZero : EndH :=
  (2 : ℝ)⁻¹ • D.Gamma

theorem hestenesAxis_mul_J : D.hestenesAxis * D.J = -D.Gamma := by
  dsimp [hestenesAxis]
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  calc
    (D.J * D.Gamma) * D.J = D.J * (D.Gamma * D.J) := by rw [mul_assoc]
    _ = D.J * (-(D.J * D.Gamma)) := by rw [hGammaJ]
    _ = -(D.J * (D.J * D.Gamma)) := by rw [mul_neg]
    _ = -D.Gamma := by rw [← mul_assoc, D.J_sq]; simp

theorem J_mul_hestenesAxis : D.J * D.hestenesAxis = D.Gamma := by
  dsimp [hestenesAxis]
  rw [← mul_assoc, D.J_sq]
  simp

private theorem nilpotentPlus_numerator_sq :
    (D.J - D.hestenesAxis) * (D.J - D.hestenesAxis) = 0 := by
  calc
    (D.J - D.hestenesAxis) * (D.J - D.hestenesAxis) =
        D.J * D.J - D.J * D.hestenesAxis -
          D.hestenesAxis * D.J + D.hestenesAxis * D.hestenesAxis := by
            noncomm_ring
    _ = 0 := by
      rw [D.J_sq, J_mul_hestenesAxis, hestenesAxis_mul_J, D.hestenesAxis_sq]
      module

private theorem nilpotentMinus_numerator_sq :
    (D.J + D.hestenesAxis) * (D.J + D.hestenesAxis) = 0 := by
  calc
    (D.J + D.hestenesAxis) * (D.J + D.hestenesAxis) =
        D.J * D.J + D.J * D.hestenesAxis +
          D.hestenesAxis * D.J + D.hestenesAxis * D.hestenesAxis := by
            noncomm_ring
    _ = 0 := by
      rw [D.J_sq, J_mul_hestenesAxis, hestenesAxis_mul_J, D.hestenesAxis_sq]
      module

private theorem smul_mul_smul (c d : ℝ) (A B : EndH) :
    (c • A) * (d • B) = (c * d) • (A * B) := by
  simp only [Algebra.smul_def]
  calc
    (algebraMap ℝ EndH c * A) * (algebraMap ℝ EndH d * B) =
        algebraMap ℝ EndH c * (A * algebraMap ℝ EndH d) * B := by
          simp only [mul_assoc]
    _ = algebraMap ℝ EndH c * (algebraMap ℝ EndH d * A) * B := by
          rw [(Algebra.commutes d A).symm]
    _ = (algebraMap ℝ EndH c * algebraMap ℝ EndH d) * (A * B) := by
          simp only [mul_assoc]
    _ = (c * d) • (A * B) := by
          rw [← map_mul, Algebra.smul_def]

@[simp] theorem nilpotentPlus_sq : D.nilpotentPlus * D.nilpotentPlus = 0 := by
  dsimp [nilpotentPlus]
  rw [smul_mul_smul, nilpotentPlus_numerator_sq]
  simp

@[simp] theorem nilpotentMinus_sq : D.nilpotentMinus * D.nilpotentMinus = 0 := by
  dsimp [nilpotentMinus]
  rw [smul_mul_smul, nilpotentMinus_numerator_sq]
  simp

theorem nilpotentPlus_mul_nilpotentMinus :
    D.nilpotentPlus * D.nilpotentMinus =
      (2 : ℝ)⁻¹ • ((1 : EndH) + D.Gamma) := by
  dsimp [nilpotentPlus, nilpotentMinus]
  rw [smul_mul_smul]
  have hprod :
      (D.J - D.hestenesAxis) * (D.J + D.hestenesAxis) =
        (2 : ℝ) • ((1 : EndH) + D.Gamma) := by
    calc
      (D.J - D.hestenesAxis) * (D.J + D.hestenesAxis) =
          D.J * D.J + D.J * D.hestenesAxis -
            D.hestenesAxis * D.J - D.hestenesAxis * D.hestenesAxis := by
              noncomm_ring
      _ = (2 : ℝ) • ((1 : EndH) + D.Gamma) := by
        rw [D.J_sq, J_mul_hestenesAxis, hestenesAxis_mul_J,
          D.hestenesAxis_sq]
        module
  rw [hprod]
  simp [smul_smul]

theorem nilpotentMinus_mul_nilpotentPlus :
    D.nilpotentMinus * D.nilpotentPlus =
      (2 : ℝ)⁻¹ • ((1 : EndH) - D.Gamma) := by
  dsimp [nilpotentPlus, nilpotentMinus]
  rw [smul_mul_smul]
  have hprod :
      (D.J + D.hestenesAxis) * (D.J - D.hestenesAxis) =
        (2 : ℝ) • ((1 : EndH) - D.Gamma) := by
    calc
      (D.J + D.hestenesAxis) * (D.J - D.hestenesAxis) =
          D.J * D.J - D.J * D.hestenesAxis +
            D.hestenesAxis * D.J - D.hestenesAxis * D.hestenesAxis := by
              noncomm_ring
      _ = (2 : ℝ) • ((1 : EndH) - D.Gamma) := by
        rw [D.J_sq, J_mul_hestenesAxis, hestenesAxis_mul_J,
          D.hestenesAxis_sq]
        module
  rw [hprod]
  simp [smul_smul]

theorem nilpotent_anticommutator :
    D.nilpotentPlus * D.nilpotentMinus +
        D.nilpotentMinus * D.nilpotentPlus = (1 : EndH) := by
  rw [nilpotentPlus_mul_nilpotentMinus,
    nilpotentMinus_mul_nilpotentPlus]
  module

theorem nilpotent_commutator :
    D.nilpotentPlus * D.nilpotentMinus -
        D.nilpotentMinus * D.nilpotentPlus = D.Gamma := by
  rw [nilpotentPlus_mul_nilpotentMinus,
    nilpotentMinus_mul_nilpotentPlus]
  module

theorem nilpotentPlus_add_nilpotentMinus :
    D.nilpotentPlus + D.nilpotentMinus = D.J := by
  dsimp [nilpotentPlus, nilpotentMinus]
  module

theorem nilpotentMinus_sub_nilpotentPlus :
    D.nilpotentMinus - D.nilpotentPlus = D.hestenesAxis := by
  dsimp [nilpotentPlus, nilpotentMinus]
  module

theorem nilpotentZero_two : (2 : ℝ) • D.nilpotentZero = D.Gamma := by
  dsimp [nilpotentZero]
  module

theorem nilpotentZero_mul_plus_sub_plus_mul_zero :
    D.nilpotentZero * D.nilpotentPlus -
        D.nilpotentPlus * D.nilpotentZero = D.nilpotentPlus := by
  dsimp [nilpotentZero, nilpotentPlus]
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  have hGammaK : D.Gamma * D.hestenesAxis = -D.J := by
    dsimp [hestenesAxis]
    calc
      D.Gamma * (D.J * D.Gamma) =
          (D.Gamma * D.J) * D.Gamma := by rw [mul_assoc]
      _ = (-(D.J * D.Gamma)) * D.Gamma := by rw [hGammaJ]
      _ = -((D.J * D.Gamma) * D.Gamma) := by simp
      _ = -(D.J * (D.Gamma * D.Gamma)) := by rw [mul_assoc]
      _ = -D.J := by rw [D.Gamma_sq]; simp
  have hKGamma : D.hestenesAxis * D.Gamma = D.J := by
    dsimp [hestenesAxis]
    rw [mul_assoc, D.Gamma_sq]
    simp
  rw [smul_mul_smul, smul_mul_smul]
  have hKGamma' : (D.J * D.Gamma) * D.Gamma = D.J := by
    rw [mul_assoc, D.Gamma_sq]
    simp
  have hnum :
      D.Gamma * (D.J - D.hestenesAxis) -
          (D.J - D.hestenesAxis) * D.Gamma =
        (2 : ℝ) • (D.J - D.hestenesAxis) := by
    calc
      D.Gamma * (D.J - D.hestenesAxis) -
          (D.J - D.hestenesAxis) * D.Gamma =
          D.Gamma * D.J - D.Gamma * D.hestenesAxis -
            D.J * D.Gamma + D.hestenesAxis * D.Gamma := by
              noncomm_ring
      _ = (2 : ℝ) • (D.J - D.hestenesAxis) := by
        rw [hGammaJ, hGammaK, hKGamma]
        change -(D.J * D.Gamma) - -D.J - D.J * D.Gamma + D.J =
          (2 : ℝ) • (D.J - D.J * D.Gamma)
        module
  rw [← smul_sub, hnum]
  module

theorem nilpotentZero_mul_minus_sub_minus_mul_zero :
    D.nilpotentZero * D.nilpotentMinus -
        D.nilpotentMinus * D.nilpotentZero = -D.nilpotentMinus := by
  dsimp [nilpotentZero, nilpotentMinus]
  have hGammaJ : D.Gamma * D.J = -(D.J * D.Gamma) := by
    rw [D.J_Gamma_anticomm]
    simp
  have hGammaK : D.Gamma * D.hestenesAxis = -D.J := by
    dsimp [hestenesAxis]
    calc
      D.Gamma * (D.J * D.Gamma) =
          (D.Gamma * D.J) * D.Gamma := by rw [mul_assoc]
      _ = (-(D.J * D.Gamma)) * D.Gamma := by rw [hGammaJ]
      _ = -((D.J * D.Gamma) * D.Gamma) := by simp
      _ = -(D.J * (D.Gamma * D.Gamma)) := by rw [mul_assoc]
      _ = -D.J := by rw [D.Gamma_sq]; simp
  have hKGamma : D.hestenesAxis * D.Gamma = D.J := by
    dsimp [hestenesAxis]
    rw [mul_assoc, D.Gamma_sq]
    simp
  rw [smul_mul_smul, smul_mul_smul]
  have hKGamma' : (D.J * D.Gamma) * D.Gamma = D.J := by
    rw [mul_assoc, D.Gamma_sq]
    simp
  have hnum :
      D.Gamma * (D.J + D.hestenesAxis) -
          (D.J + D.hestenesAxis) * D.Gamma =
        -(2 : ℝ) • (D.J + D.hestenesAxis) := by
    calc
      D.Gamma * (D.J + D.hestenesAxis) -
          (D.J + D.hestenesAxis) * D.Gamma =
          D.Gamma * D.J + D.Gamma * D.hestenesAxis -
            D.J * D.Gamma - D.hestenesAxis * D.Gamma := by
              noncomm_ring
      _ = -(2 : ℝ) • (D.J + D.hestenesAxis) := by
        rw [hGammaJ, hGammaK, hKGamma]
        change -(D.J * D.Gamma) + -D.J - D.J * D.Gamma - D.J =
          -(2 : ℝ) • (D.J + D.J * D.Gamma)
        module
  rw [← smul_sub, hnum]
  module

/-! ## Complementary idempotents generated by the nilpotent pair -/

/-- The `+` projector generated by the nilpotent pair. -/
noncomputable def nilpotentPlusProjector : EndH :=
  (2 : ℝ)⁻¹ • ((1 : EndH) + D.Gamma)

/-- The `-` projector generated by the nilpotent pair. -/
noncomputable def nilpotentMinusProjector : EndH :=
  (2 : ℝ)⁻¹ • ((1 : EndH) - D.Gamma)

theorem nilpotentPlusProjector_eq_product :
    D.nilpotentPlusProjector = D.nilpotentPlus * D.nilpotentMinus := by
  rw [nilpotentPlus_mul_nilpotentMinus]
  rfl

theorem nilpotentMinusProjector_eq_product :
    D.nilpotentMinusProjector = D.nilpotentMinus * D.nilpotentPlus := by
  rw [nilpotentMinus_mul_nilpotentPlus]
  rfl

@[simp] theorem nilpotentPlusProjector_sq :
    D.nilpotentPlusProjector * D.nilpotentPlusProjector =
      D.nilpotentPlusProjector := by
  unfold nilpotentPlusProjector
  rw [smul_mul_smul]
  have h : ((1 : EndH) + D.Gamma) * ((1 : EndH) + D.Gamma) =
      (2 : ℝ) • ((1 : EndH) + D.Gamma) := by
    calc
      ((1 : EndH) + D.Gamma) * ((1 : EndH) + D.Gamma) =
          1 + D.Gamma + D.Gamma + D.Gamma * D.Gamma := by noncomm_ring
      _ = 1 + D.Gamma + D.Gamma + 1 := by rw [D.Gamma_sq]
      _ = (2 : ℝ) • ((1 : EndH) + D.Gamma) := by module
  rw [h, smul_smul]
  norm_num

@[simp] theorem nilpotentMinusProjector_sq :
    D.nilpotentMinusProjector * D.nilpotentMinusProjector =
      D.nilpotentMinusProjector := by
  unfold nilpotentMinusProjector
  rw [smul_mul_smul]
  have h : ((1 : EndH) - D.Gamma) * ((1 : EndH) - D.Gamma) =
      (2 : ℝ) • ((1 : EndH) - D.Gamma) := by
    calc
      ((1 : EndH) - D.Gamma) * ((1 : EndH) - D.Gamma) =
          1 - D.Gamma - D.Gamma + D.Gamma * D.Gamma := by noncomm_ring
      _ = 1 - D.Gamma - D.Gamma + 1 := by rw [D.Gamma_sq]
      _ = (2 : ℝ) • ((1 : EndH) - D.Gamma) := by module
  rw [h, smul_smul]
  norm_num

theorem nilpotentPlusProjector_mul_minusProjector :
    D.nilpotentPlusProjector * D.nilpotentMinusProjector = 0 := by
  unfold nilpotentPlusProjector nilpotentMinusProjector
  rw [smul_mul_smul]
  have h : ((1 : EndH) + D.Gamma) * ((1 : EndH) - D.Gamma) = 0 := by
    calc
      ((1 : EndH) + D.Gamma) * ((1 : EndH) - D.Gamma) =
          1 - D.Gamma + D.Gamma - D.Gamma * D.Gamma := by noncomm_ring
      _ = 1 - D.Gamma + D.Gamma - 1 := by rw [D.Gamma_sq]
      _ = 0 := by module
  rw [h]
  simp

theorem nilpotentMinusProjector_mul_plusProjector :
    D.nilpotentMinusProjector * D.nilpotentPlusProjector = 0 := by
  unfold nilpotentMinusProjector nilpotentPlusProjector
  rw [smul_mul_smul]
  have h : ((1 : EndH) - D.Gamma) * ((1 : EndH) + D.Gamma) = 0 := by
    calc
      ((1 : EndH) - D.Gamma) * ((1 : EndH) + D.Gamma) =
          1 + D.Gamma - D.Gamma - D.Gamma * D.Gamma := by noncomm_ring
      _ = 1 + D.Gamma - D.Gamma - 1 := by rw [D.Gamma_sq]
      _ = 0 := by module
  rw [h]
  simp

theorem nilpotentPlusProjector_add_minusProjector :
    D.nilpotentPlusProjector + D.nilpotentMinusProjector = (1 : EndH) := by
  unfold nilpotentPlusProjector nilpotentMinusProjector
  module

theorem nilpotentPlusProjector_sub_minusProjector :
    D.nilpotentPlusProjector - D.nilpotentMinusProjector = D.Gamma := by
  unfold nilpotentPlusProjector nilpotentMinusProjector
  module

theorem hestenesAxis_mul_eq_jordan_add_lie (A : EndH) :
    D.hestenesAxis * A = D.jordanChannel A + D.lieChannel A := by
  dsimp [jordanChannel, lieChannel]
  module

theorem jordanChannel_gamma_eq_zero :
    D.jordanChannel D.Gamma = 0 := by
  dsimp [jordanChannel]
  rw [D.hestenesAxis_gamma_anticommute]
  simp

theorem lieChannel_gamma_eq_hodgeInvolution :
    D.lieChannel D.Gamma = D.J := by
  dsimp [lieChannel]
  rw [D.hestenesAxis_gamma_commutator]
  module

theorem jordanChannel_hestenesAxis_eq_neg_identity :
    D.jordanChannel D.hestenesAxis = -(1 : EndH) := by
  dsimp [jordanChannel]
  rw [D.hestenesAxis_sq]
  module

theorem lieChannel_hestenesAxis_eq_zero :
    D.lieChannel D.hestenesAxis = 0 := by
  dsimp [lieChannel]
  module

theorem hestenesAxis_mul_relativeSurprisal (κ a : ℝ) :
    D.hestenesAxis * D.relativeSurprisal κ a =
      κ • D.hestenesAxis + a • (D.hestenesAxis * D.Gamma) := by
  dsimp [relativeSurprisal]
  rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]

theorem jordanChannel_add (A B : EndH) :
    D.jordanChannel (A + B) = D.jordanChannel A + D.jordanChannel B := by
  dsimp [jordanChannel]
  simp only [mul_add, add_mul, smul_add]
  abel

theorem jordanChannel_smul (r : ℝ) (A : EndH) :
    D.jordanChannel (r • A) = r • D.jordanChannel A := by
  dsimp [jordanChannel]
  simp only [mul_smul_comm, smul_mul_assoc, smul_add, smul_smul]
  rw [mul_comm]

theorem jordanChannel_one :
    D.jordanChannel (1 : EndH) = D.hestenesAxis := by
  dsimp [jordanChannel]
  rw [mul_one, one_mul, ← two_smul ℝ D.hestenesAxis, smul_smul]
  norm_num

theorem jordanChannel_gamma :
    D.jordanChannel D.Gamma = 0 :=
  D.jordanChannel_gamma_eq_zero

theorem jordanChannel_relativeSurprisal (κ a : ℝ) :
    D.jordanChannel (D.relativeSurprisal κ a) = κ • D.hestenesAxis := by
  calc
    D.jordanChannel (D.relativeSurprisal κ a) =
        D.jordanChannel (κ • (1 : EndH)) + D.jordanChannel (a • D.Gamma) := by
          exact D.jordanChannel_add _ _
    _ = κ • D.jordanChannel (1 : EndH) + a • D.jordanChannel D.Gamma := by
          rw [D.jordanChannel_smul, D.jordanChannel_smul]
    _ = κ • D.hestenesAxis := by
          rw [D.jordanChannel_one, D.jordanChannel_gamma]
          simp

theorem lieChannel_add (A B : EndH) :
    D.lieChannel (A + B) = D.lieChannel A + D.lieChannel B := by
  dsimp [lieChannel]
  simp only [mul_add, add_mul]
  module

theorem lieChannel_smul (r : ℝ) (A : EndH) :
    D.lieChannel (r • A) = r • D.lieChannel A := by
  dsimp [lieChannel]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
  rw [mul_comm]

theorem lieChannel_one :
    D.lieChannel (1 : EndH) = 0 := by
  dsimp [lieChannel]
  rw [mul_one, one_mul, sub_self]
  simp

theorem lieChannel_gamma :
    D.lieChannel D.Gamma = D.J :=
  D.lieChannel_gamma_eq_hodgeInvolution

theorem lieChannel_relativeSurprisal (κ a : ℝ) :
    D.lieChannel (D.relativeSurprisal κ a) =
      a • D.J := by
  calc
    D.lieChannel (D.relativeSurprisal κ a) =
        D.lieChannel (κ • (1 : EndH)) + D.lieChannel (a • D.Gamma) := by
          exact D.lieChannel_add _ _
    _ = κ • D.lieChannel (1 : EndH) + a • D.lieChannel D.Gamma := by
          rw [D.lieChannel_smul, D.lieChannel_smul]
    _ = a • D.J := by
          rw [D.lieChannel_one, D.lieChannel_gamma]
          simp

theorem hodgeDirac_sq :
    D.hodgeDirac * D.hodgeDirac = D.hodgeLaplacian := by
  dsimp [hodgeDirac, hodgeLaplacian]
  calc
    (D.d + D.delta) * (D.d + D.delta) =
        D.d * D.d + D.d * D.delta + D.delta * D.d + D.delta * D.delta := by
          noncomm_ring
    _ = D.d * D.delta + D.delta * D.d := by
          rw [D.d_sq, D.delta_sq]
          simp

theorem hodgeDirac_odd :
    D.Gamma * D.hodgeDirac = -(D.hodgeDirac * D.Gamma) := by
  dsimp [hodgeDirac]
  rw [mul_add, D.d_odd, D.delta_odd, add_mul]
  simp [add_comm]

theorem hodgeLaplacian_even :
    D.Gamma * D.hodgeLaplacian = D.hodgeLaplacian * D.Gamma := by
  have hD := D.hodgeDirac_odd
  have hsq := D.hodgeDirac_sq
  calc
    D.Gamma * D.hodgeLaplacian =
        D.Gamma * (D.hodgeDirac * D.hodgeDirac) := by rw [hsq]
    _ = (D.hodgeDirac * D.hodgeDirac) * D.Gamma := by
      calc
        D.Gamma * (D.hodgeDirac * D.hodgeDirac) =
            (D.Gamma * D.hodgeDirac) * D.hodgeDirac := by
              noncomm_ring
        _ = (-(D.hodgeDirac * D.Gamma)) * D.hodgeDirac := by
              rw [hD]
        _ = -(D.hodgeDirac * (D.Gamma * D.hodgeDirac)) := by
              noncomm_ring
        _ = -(D.hodgeDirac * (-(D.hodgeDirac * D.Gamma))) := by
              rw [hD]
        _ = (D.hodgeDirac * D.hodgeDirac) * D.Gamma := by
              simp only [mul_neg, neg_neg]
              noncomm_ring
    _ = D.hodgeLaplacian * D.Gamma := by rw [hsq]

end Data
end
end InfoGeometry.Dynamics.ChiralHodgeDifferential
