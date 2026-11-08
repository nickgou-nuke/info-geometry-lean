import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-!
# Sugawara Rescaling of Quadratic Current Mode Sums to Virasoro Generators

This module proves that rescaling a finite quadratic current mode sum `modeSum`
by the Sugawara factor `1 / (2 * (k + h^∨))` converts the unnormalized quadratic
mode commutator into the Virasoro commutator with central charge
$c = k \dim(\mathfrak{g}) / (k + h^\vee)$.

## 1. Real Math in This File
- `modeSum`, `sugawaraFactor`, `L_sugawara`
- `sum_mul_left`, `sum_mul_right`, `virasoro_commutation`

## 2. Meaningful Mathematical Results Used
- `InfoGeometry.OperatorAlgebra.AffineVirasoroBridge`

## 3. Excluded Wrapper Patterns
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

namespace InfoGeometry.OperatorAlgebra.SugawaraVirasoroComm

variable {Finite : Type*} [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite]
  [LieAlgebra ℝ Finite] [Fintype Finite] [DecidableEq Finite]

variable {Alg : Type*} [Ring Alg] [Algebra ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (A : AffineCurrentDatum Finite Alg)
variable (S : SugawaraModeConstructionDatum Finite Alg)
variable (e : Finite → Finite)

/-- Finite quadratic current mode sum $\sum_{m \in s} \sum_i J_m(e_i)\,J_{n-m}(e_i)$. -/
noncomputable def modeSum (s : Finset ℤ) (n : ℤ) : Alg :=
  ∑ m ∈ s, ∑ i : Finite, (A.Current m (e i)) * (A.Current (n - m) (e i))

/-- Sugawara normalization factor $\frac{1}{2(k + h^\vee)}$. -/
noncomputable def sugawaraFactor : ℝ :=
  1 / (2 * (S.bridge.level + S.bridge.dualCoxeterNumber))

/-- Sugawara-normalized finite Virasoro mode `sugawaraFactor S • modeSum A e s n`. -/
noncomputable def L_sugawara (s : Finset ℤ) (n : ℤ) : Alg :=
  sugawaraFactor S • modeSum A e s n

/-- Scalar multiplication pulls out of a finite sum of binary products. -/
lemma sum_mul_left (s : Finset ℤ) (r : ℝ) (f g : ℤ → Alg) :
    (∑ m ∈ s, r • (f m * g m)) = r • (∑ m ∈ s, f m * g m) := by
  rw [← Finset.smul_sum]

/-- Right multiplication distributes over a finite sum of binary products. -/
lemma sum_mul_right (s : Finset ℤ) (r : Alg) (f g : ℤ → Alg) :
    (∑ m ∈ s, (f m * g m) * r) = (∑ m ∈ s, f m * g m) * r := by
  rw [Finset.sum_mul]

/-- Rescaling the unnormalized quadratic current mode sum by `sugawaraFactor S`
yields the Virasoro commutation relation with central charge
$c = k \dim(\mathfrak{g}) / (k + h^\vee)$. -/
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
