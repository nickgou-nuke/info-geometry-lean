import InfoGeometry.Canonical.IBPythagorean

open MeasureTheory
open ProbabilityTheory

namespace IBMonotonicity

open InfoGeometry.Canonical.IBFunctional
open InfoGeometry.Canonical.IBPythagorean

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]

/--
Analytic obligations for one explicit BA descent step:
encoder descent at fixed `q_n`, then marginal descent at fixed encoder.
-/
structure IBDescentWitness
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_encoder : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (p_old : X → ProbabilityMeasure T) : Prop where
  hKL_old : FiniteKLFamily (q_n : Measure T) p_old
  hKL_next :
    FiniteKLFamily
      ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
      (IBNextEncoder q_n β D hInt)
  encoder_descent :
    IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
      ≤ IBGlobalFreeEnergy pX q_n β D p_old hKL_old
  marginal_descent :
    IBNextMarginalDescentWitness pX q_n β D hInt h_meas hKL_encoder hKL_next

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
    (hstep : IBDescentWitness pX q_n β D hInt h_meas hKL_encoder p_old) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hstep.hKL_next
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hstep.hKL_old := by
  exact le_trans hstep.marginal_descent.descent hstep.encoder_descent

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
    (h_marginal : IBNextMarginalDescentWitness pX q_n β D hInt h_meas hKL_encoder hKL_next) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hKL_next
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hKL_old := by
  exact le_trans h_marginal.descent h_encoder

end IBMonotonicity
