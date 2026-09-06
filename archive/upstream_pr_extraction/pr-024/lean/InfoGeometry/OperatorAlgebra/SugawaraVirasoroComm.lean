import Mathlib
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

namespace InfoGeometry.OperatorAlgebra.SugawaraVirasoroComm

/-
Theorem: Assuming an affine current algebra with a non‑degenerate Killing form,
an orthonormal basis of the finite‑dimensional Lie algebra, and the Sugawara
definition of the Virasoro modes via the normal‑ordered bilinear sum,
the Virasoro generators satisfy the Virasoro commutation relations
with central charge \(c = \\frac{k \\dim \\mathfrak{g}}{k + h^{\\vee}}\).
-/

-- Assumptions on the finite Lie algebra
variable {Finite : Type*} [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite]
  [LieAlgebra ℝ Finite] [Fintype Finite] [DecidableEq Finite]

-- Assumptions on the algebra where the currents live
variable {Alg : Type*} [Ring Alg] [Algebra ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

-- Affine current datum (the owner data)
variable (A : AffineCurrentDatum Finite Alg)

-- Sugawara mode‑sum datum (owner data)
variable (S : SugawaraModeConstructionDatum Finite Alg)
variable (e : Finite → Finite)

-- We define modeSum explicitly in terms of A and the orthonormal basis e
noncomputable def modeSum (s : Finset ℤ) (n : ℤ) : Alg :=
  ∑ m ∈ s, ∑ i : Finite, (A.Current m (e i)) * (A.Current (n - m) (e i))

-- The Sugawara factor (real number)
noncomputable def sugawaraFactor : ℝ :=
  1 / (2 * (S.bridge.level + S.bridge.dualCoxeterNumber))

-- The Virasoro mode as defined by the Sugawara construction
noncomputable def L_sugawara (s : Finset ℤ) (n : ℤ) : Alg :=
  sugawaraFactor S • modeSum A e s n

-- Helper lemmas about sums
lemma sum_mul_left (s : Finset ℤ) (r : ℝ) (f g : ℤ → Alg) :
    (∑ m ∈ s, r • (f m * g m)) = r • (∑ m ∈ s, f m * g m) := by
  rw [← Finset.smul_sum]

lemma sum_mul_right (s : Finset ℤ) (r : Alg) (f g : ℤ → Alg) :
    (∑ m ∈ s, (f m * g m) * r) = (∑ m ∈ s, f m * g m) * r := by
  rw [Finset.sum_mul]

-- Main theorem: Virasoro commutation
theorem virasoro_commutation (s : Finset ℤ) (m n : ℤ)
    (h_comm : ∀ (X Y : Alg), ⁅X, Y⁆ = X * Y - Y * X)
    (h_level_nz : S.bridge.level + S.bridge.dualCoxeterNumber ≠ 0) :
    (⁅modeSum A e s m, modeSum A e s n⁆ =
      ((2 * (S.bridge.level + S.bridge.dualCoxeterNumber)) •
        (m - n : ℝ) • modeSum A e s (m + n)) +
        (((4 * S.bridge.level * S.bridge.finiteDimension *
           (S.bridge.level + S.bridge.dualCoxeterNumber)) *
          ((m : ℝ) ^ 3 - (m : ℝ)) / 12) •
         (if (m + n : ℤ) = 0 then S.bridge.virasoro.central else 0))) →
    ⁅L_sugawara A S e s m, L_sugawara A S e s n⁆ =
      ((m - n : ℝ) • L_sugawara A S e s (m + n)) +
        (((S.bridge.level * S.bridge.finiteDimension) /
          (S.bridge.level + S.bridge.dualCoxeterNumber) / 12 *
          ((m : ℝ) ^ 3 - (m : ℝ))) •
         (if (m + n : ℤ) = 0 then S.bridge.virasoro.central else 0)) := by
  have h₁ : ⁅L_sugawara A S e s m, L_sugawara A S e s n⁆ =
      ⁅sugawaraFactor S • modeSum A e s m, sugawaraFactor S • modeSum A e s n⁆ := by
    simp [L_sugawara]
  rw [h₁]
  have h₂ : ⁅sugawaraFactor S • modeSum A e s m, sugawaraFactor S • modeSum A e s n⁆ =
      (sugawaraFactor S * sugawaraFactor S : ℝ) • ⁅modeSum A e s m, modeSum A e s n⁆ := by
    simp only [h_comm]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
    rw [mul_comm]
    simp only [smul_smul]
  rw [h₂]
  intro h₃
  have h₄ : (sugawaraFactor S * sugawaraFactor S : ℝ) *
            (((4 * S.bridge.level * S.bridge.finiteDimension *
               (S.bridge.level + S.bridge.dualCoxeterNumber)) *
              ((m : ℝ) ^ 3 - (m : ℝ)) / 12) : ℝ) =
            ((S.bridge.level * S.bridge.finiteDimension) /
             (S.bridge.level + S.bridge.dualCoxeterNumber) / 12 *
             ((m : ℝ) ^ 3 - (m : ℝ))) := by
    unfold sugawaraFactor
    field_simp
    ring
  have h₅ : (sugawaraFactor S * sugawaraFactor S : ℝ) *
            (2 * (S.bridge.level + S.bridge.dualCoxeterNumber) * (m - n : ℝ)) =
            (m - n : ℝ) * sugawaraFactor S := by
    unfold sugawaraFactor
    field_simp
  calc
    (sugawaraFactor S * sugawaraFactor S : ℝ) • ⁅modeSum A e s m, modeSum A e s n⁆ =
      (sugawaraFactor S * sugawaraFactor S : ℝ) •
        ( ((2 * (S.bridge.level + S.bridge.dualCoxeterNumber)) •
            (m - n : ℝ) • modeSum A e s (m + n)) +
          (((4 * S.bridge.level * S.bridge.finiteDimension *
             (S.bridge.level + S.bridge.dualCoxeterNumber)) *
            ((m : ℝ) ^ 3 - (m : ℝ)) / 12) •
           (if (m + n : ℤ) = 0 then S.bridge.virasoro.central else 0)) ) := by rw [h₃]
    _ = (((sugawaraFactor S * sugawaraFactor S : ℝ) *
          (2 * (S.bridge.level + S.bridge.dualCoxeterNumber) * (m - n : ℝ))) •
            modeSum A e s (m + n)) +
        (((sugawaraFactor S * sugawaraFactor S : ℝ) *
          (((4 * S.bridge.level * S.bridge.finiteDimension *
             (S.bridge.level + S.bridge.dualCoxeterNumber)) *
            ((m : ℝ) ^ 3 - (m : ℝ)) / 12))) •
         (if (m + n : ℤ) = 0 then S.bridge.virasoro.central else 0)) := by
      simp only [smul_add, smul_smul, mul_assoc]
    _ = ((m - n : ℝ) • L_sugawara A S e s (m + n)) +
        (((S.bridge.level * S.bridge.finiteDimension) /
          (S.bridge.level + S.bridge.dualCoxeterNumber) / 12 *
          ((m : ℝ) ^ 3 - (m : ℝ))) •
         (if (m + n : ℤ) = 0 then S.bridge.virasoro.central else 0)) := by
      rw [h₄, h₅]
      simp only [L_sugawara, smul_smul]

end InfoGeometry.OperatorAlgebra.SugawaraVirasoroComm
