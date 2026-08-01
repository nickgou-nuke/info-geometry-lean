import InfoGeometry.Canonical.PoissonGibbsKANModuliCouplingTopological

/-!
# Positive transport certificate from the quotient Gibbs readout

The independent coupling is now packaged as the native finite
`UnbalancedTransportCertificate`.  All positivity obligations are discharged
from the quotient probability readout and its two marginal identities.
-/

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Inference

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

noncomputable def poissonGibbsTransportCertificateOnModuli
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) :
    UnbalancedTransportCertificate (Row := Data) (Col := Fin K) :=
  ⟨(
      independentPoissonCouplingOnModuli M ε q,
      fun i => averagePoissonWeightOnModuli M ε i q,
      fun _ => (K : ℝ)⁻¹),
    by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i k
        change 0 ≤ averagePoissonWeightOnModuli M ε i q / (K : ℝ)
        exact div_nonneg
          (averagePoissonWeightOnModuli_pos M ε q i).le
          (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne K)).le)
      · intro i
        rw [independentPoissonCouplingOnModuli_rowMass]
        exact averagePoissonWeightOnModuli_pos M ε q i
      · intro k
        rw [independentPoissonCouplingOnModuli_colMass]
        exact inv_pos.mpr (by
          exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne K)))
      · intro i
        exact averagePoissonWeightOnModuli_pos M ε q i
      · intro k
        exact inv_pos.mpr (by
          exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne K)))⟩

theorem poissonGibbsTransportCertificateOnModuli_coupling
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) :
    (poissonGibbsTransportCertificateOnModuli M ε q).coupling =
      independentPoissonCouplingOnModuli M ε q := by
  change independentPoissonCouplingOnModuli M ε q =
    independentPoissonCouplingOnModuli M ε q
  rfl

theorem poissonGibbsTransportCertificateOnModuli_row_target
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) (i : Data) :
    (poissonGibbsTransportCertificateOnModuli M ε q).targetRowMass i =
      averagePoissonWeightOnModuli M ε i q := by
  change averagePoissonWeightOnModuli M ε i q =
    averagePoissonWeightOnModuli M ε i q
  rfl

theorem continuous_poissonGibbsCertificate_coupling
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) (k : Fin K) :
    Continuous (fun q =>
      (poissonGibbsTransportCertificateOnModuli M ε q).coupling i k) := by
  change Continuous (fun q => independentPoissonCouplingOnModuli M ε q i k)
  exact continuous_independentPoissonCouplingOnModuli M hmean ε i k

theorem continuous_poissonGibbsCertificate_rowTarget
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) :
    Continuous (fun q =>
      (poissonGibbsTransportCertificateOnModuli (K := K) M ε q).targetRowMass i) := by
  change Continuous (fun q => averagePoissonWeightOnModuli M ε i q)
  exact continuous_averagePoissonWeightOnModuli M hmean ε i

theorem continuous_poissonGibbsCertificate_colTarget
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (k : Fin K) :
    Continuous (fun _q : KANModuliSpace Theta K =>
      (poissonGibbsTransportCertificateOnModuli M ε _q).targetColMass k) := by
  change Continuous (fun _q : KANModuliSpace Theta K => (K : ℝ)⁻¹)
  exact continuous_const

end InfoGeometry.Canonical.KANModuli
