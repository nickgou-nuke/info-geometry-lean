import Mathlib
import InfoGeometry.Canonical.PrimePartitionPolynomials

noncomputable section
namespace InfoGeometry.Canonical.PrimePartitionN1Sandbox

open scoped BigOperators
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeHurwitzLimit

theorem interactionEnergy_fin_one_zero
    (D : FinitePrimeChainData 1) (lam : ℝ) (σ : Fin 1 → Bool) :
    interactionEnergy D lam σ = 0 := by
  simp [interactionEnergy, FinitePrimeChainData.spinCoupling, spinSign]

theorem partitionPolynomial_fin_one_eq (D : FinitePrimeChainData 1) (lam : ℝ) :
    partitionPolynomial D lam = Polynomial.C (1 : ℂ) + Polynomial.X := by
  classical
  unfold partitionPolynomial
  let e : (Fin 1 → Bool) ≃ Bool := Equiv.piUnique (fun _ => Bool)
  let f : (Fin 1 → Bool) → Polynomial ℂ := fun σ =>
    Polynomial.C ((configurationWeight D lam σ : ℝ) : ℂ) *
      Polynomial.X ^ occupiedCount σ
  let g : Bool → Polynomial ℂ := fun b => f (e.symm b)
  change (∑ σ : Fin 1 → Bool, f σ) = Polynomial.C (1 : ℂ) + Polynomial.X
  rw [Fintype.sum_equiv e f g]
  · have htrue : e.symm true = (fun _ : Fin 1 => true) := by
      funext i
      fin_cases i
      rfl
    have hfalse : e.symm false = (fun _ : Fin 1 => false) := by
      funext i
      fin_cases i
      rfl
    rw [Fintype.sum_bool]
    dsimp [g]
    rw [htrue, hfalse]
    simp [g, f, configurationWeight, interactionEnergy_fin_one_zero, occupiedCount]
    ring
  · intro σ
    simp [g]

theorem partitionPolynomial_fin_one_root_eq_neg_one
    (D : FinitePrimeChainData 1) (lam : ℝ)
    {z : ℂ} (hz : (partitionPolynomial D lam).IsRoot z) :
    z = -1 := by
  rw [partitionPolynomial_fin_one_eq D lam] at hz
  have hz' : (1 : ℂ) + z = 0 := by
    simpa [Polynomial.IsRoot] using hz
  linear_combination hz'

theorem partitionPolynomial_fin_one_root_on_unit_circle
    (D : FinitePrimeChainData 1) (lam : ℝ)
    {z : ℂ} (hz : (partitionPolynomial D lam).IsRoot z) :
    OnUnitCircle z := by
  rw [partitionPolynomial_fin_one_root_eq_neg_one D lam hz]
  norm_num [OnUnitCircle]

end InfoGeometry.Canonical.PrimePartitionN1Sandbox
