import InfoGeometry.Canonical.PoissonGibbsKANModuliProbabilityTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Independent coupling readout from the quotient probability vector

The coupling below is the product-style finite lift of the quotient Gibbs
probability vector to a uniform expert column profile.  It is a readout, not
an optimizer or a claim about Sinkhorn convergence.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Inference

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

theorem averagePoissonWeightOnModuli_sum_one {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) :
    ∑ i : Data, averagePoissonWeightOnModuli M ε i q = 1 := by
  refine Quotient.inductionOn q ?_
  intro v
  simpa only [averagePoissonWeightOnModuli_quotientMap] using
    averagePoissonWeight_sum_one M ε v

theorem averagePoissonWeightOnModuli_pos {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature)
    (q : KANModuliSpace Theta K) (i : Data) :
    0 < averagePoissonWeightOnModuli M ε i q := by
  refine Quotient.inductionOn q ?_
  intro v
  have hp : 0 < averagePoissonWeight M ε i v := by
    unfold averagePoissonWeight
    have hK : 0 < (K : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne K))
    exact div_pos
      (Finset.sum_pos (fun k _ => poissonWeight_pos M (v k) ε.1 i)
        Finset.univ_nonempty) hK
  simpa only [averagePoissonWeightOnModuli_quotientMap] using hp

noncomputable def independentPoissonCouplingOnModuli {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) :
    KANModuliSpace Theta K → Data → Fin K → ℝ :=
  fun q i _ => averagePoissonWeightOnModuli M ε i q / (K : ℝ)

theorem continuous_independentPoissonCouplingOnModuli {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) (k : Fin K) :
    Continuous (fun q => independentPoissonCouplingOnModuli M ε q i k) := by
  unfold independentPoissonCouplingOnModuli
  exact (continuous_averagePoissonWeightOnModuli M hmean ε i).div
    continuous_const (fun _ => by
      exact_mod_cast (NeZero.ne K : K ≠ 0))

theorem independentPoissonCouplingOnModuli_rowMass {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) (i : Data) :
    transportRowMass
      (independentPoissonCouplingOnModuli M ε q) i =
      averagePoissonWeightOnModuli M ε i q := by
  unfold transportRowMass independentPoissonCouplingOnModuli
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K : K ≠ 0)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hK]

theorem independentPoissonCouplingOnModuli_colMass {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) (k : Fin K) :
    transportColMass
      (independentPoissonCouplingOnModuli M ε q) k = (K : ℝ)⁻¹ := by
  unfold transportColMass independentPoissonCouplingOnModuli
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K : K ≠ 0)
  rw [← Finset.sum_div, averagePoissonWeightOnModuli_sum_one]
  exact one_div (K : ℝ)

end InfoGeometry.Canonical.KANModuli
