import InfoGeometry.QuantumGeometry.SLDLyapunov

noncomputable section

namespace InfoGeometry.QuantumGeometry.SLD

open scoped ComplexOrder

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def lyapunovLinearMap (density : Matrix Index Index ℂ) :
    Matrix Index Index ℂ →ₗ[ℂ] Matrix Index Index ℂ where
  toFun score := (1 / 2 : ℂ) • jordanProd density score
  map_add' := by
    intro first second
    simp only [jordanProd, mul_add, add_mul, smul_add]
    abel
  map_smul' := by
    intro scalar score
    simp only [jordanProd, mul_smul_comm, smul_mul_assoc, ← smul_add, RingHom.id_apply]
    exact smul_comm _ _ _

theorem lyapunovLinearMap_bijective (density : Matrix Index Index ℂ)
    (positive : density.PosDef) : Function.Bijective (lyapunovLinearMap density) := by
  constructor
  · intro first second equal
    obtain ⟨score, _, unique⟩ := existsUnique_sld_of_posDef density
      (lyapunovLinearMap density first) positive
    exact (unique first rfl).trans (unique second equal).symm
  · intro variation
    obtain ⟨score, solves, _⟩ := existsUnique_sld_of_posDef density variation positive
    exact ⟨score, solves.symm⟩

def lyapunovEquiv (density : Matrix Index Index ℂ) (positive : density.PosDef) :
    Matrix Index Index ℂ ≃ₗ[ℂ] Matrix Index Index ℂ :=
  LinearEquiv.ofBijective (lyapunovLinearMap density) (lyapunovLinearMap_bijective density positive)

def sld (density : Matrix Index Index ℂ) (positive : density.PosDef)
    (variation : Matrix Index Index ℂ) : Matrix Index Index ℂ :=
  (lyapunovEquiv density positive).symm variation

theorem sld_solves (density : Matrix Index Index ℂ) (positive : density.PosDef)
    (variation : Matrix Index Index ℂ) : IsSLD density variation (sld density positive variation) :=
  ((lyapunovEquiv density positive).apply_symm_apply variation).symm

theorem sld_selfAdjoint (density : Matrix Index Index ℂ) (positive : density.PosDef)
    (variation : Matrix Index Index ℂ) (self_adjoint : star variation = variation) :
    star (sld density positive variation) = sld density positive variation := by
  exact (existsUnique_sld_of_posDef density variation positive).unique
    (isSLD_star density variation _ positive.isHermitian.eq self_adjoint
      (sld_solves density positive variation)) (sld_solves density positive variation)

theorem trace_variation_score (density variation first second : Matrix Index Index ℂ)
    (solves : IsSLD density variation first) :
    Matrix.trace (variation * second) = sldFisherInner density first second := by
  rw [show variation = (1 / 2 : ℂ) • jordanProd density first from solves]
  simp only [jordanProd, smul_mul_assoc, add_mul, Matrix.trace_smul, Matrix.trace_add,
    smul_eq_mul, sldFisherInner, mul_add, Matrix.trace_add]
  congr 1
  rw [Matrix.mul_assoc density first second]
  congr 1
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle second first density, Matrix.mul_assoc]

def buresTangentMetric (density : Matrix Index Index ℂ) (positive : density.PosDef)
    (first second : Matrix Index Index ℂ) : ℝ :=
  (1 / 4 : ℝ) * (Matrix.trace (first * sld density positive second)).re

theorem buresTangentMetric_symm (density : Matrix Index Index ℂ) (positive : density.PosDef)
    (first second : Matrix Index Index ℂ) :
    buresTangentMetric density positive first second =
      buresTangentMetric density positive second first := by
  unfold buresTangentMetric
  rw [trace_variation_score density first _ _ (sld_solves density positive first),
    trace_variation_score density second _ _ (sld_solves density positive second),
    sldFisherInner_comm]

theorem buresTangentMetric_nonneg (density : Matrix Index Index ℂ) (positive : density.PosDef)
    (variation : Matrix Index Index ℂ) (self_adjoint : star variation = variation) :
    0 ≤ buresTangentMetric density positive variation variation := by
  unfold buresTangentMetric
  apply mul_nonneg (by norm_num)
  rw [trace_variation_score density variation _ _ (sld_solves density positive variation),
    sldFisherInner_self_commuting]
  have nonnegative := (positive.posSemidef.conjTranspose_mul_mul_same
    (sld density positive variation)).trace_nonneg
  change 0 ≤ Matrix.trace (star (sld density positive variation) * density *
    sld density positive variation) at nonnegative
  rw [sld_selfAdjoint density positive variation self_adjoint,
    ← Matrix.trace_mul_cycle density (sld density positive variation)
      (sld density positive variation), Matrix.mul_assoc] at nonnegative
  exact (Complex.nonneg_iff.mp nonnegative).1

end InfoGeometry.QuantumGeometry.SLD
