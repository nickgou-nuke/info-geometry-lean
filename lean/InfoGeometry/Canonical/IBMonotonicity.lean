import InfoGeometry.Canonical.IBPythagorean
import InfoGeometry.Algebra.FiniteSpinAlgebra

open MeasureTheory
open ProbabilityTheory

namespace InfoGeometry.Canonical.IBMonotonicity

open IBFunctional
open IBPythagorean

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]

/--
One full BA step decreases the global free energy whenever the two analytic
descent obligations have been discharged.
-/
theorem IB_monotone_descent_from_witness
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_encoder : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (p_old : X → ProbabilityMeasure T)
    (hstep :
      ∃ hKL_old : FiniteKLFamily (q_n : Measure T) p_old,
        ∃ hKL_next :
          FiniteKLFamily
            ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
            (IBNextEncoder q_n β D hInt),
          IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
              ≤ IBGlobalFreeEnergy pX q_n β D p_old hKL_old ∧
            IBMarginalDescentWitness
              pX q_n (IBNextMarginal pX q_n β D hInt h_meas)
              β D (IBNextEncoder q_n β D hInt) hKL_encoder hKL_next) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hstep.2.choose
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hstep.choose := by
  rcases hstep with ⟨hKL_old, hKL_next, h_encoder, h_marginal⟩
  exact le_trans h_marginal h_encoder

/--
Curried monotonicity form: the full BA descent follows from the separate
encoder and marginal descent inequalities.
-/
theorem IB_monotone_descent
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_encoder : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (p_old : X → ProbabilityMeasure T)
    (hKL_old : FiniteKLFamily (q_n : Measure T) p_old)
    (hKL_next :
      FiniteKLFamily
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (IBNextEncoder q_n β D hInt))
    (h_encoder :
      IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
        ≤ IBGlobalFreeEnergy pX q_n β D p_old hKL_old)
    (h_marginal : IBMarginalDescentWitness pX q_n (IBNextMarginal pX q_n β D hInt h_meas) β D (IBNextEncoder q_n β D hInt) hKL_encoder hKL_next) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hKL_next
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hKL_old := by
  exact le_trans h_marginal h_encoder

end InfoGeometry.Canonical.IBMonotonicity
