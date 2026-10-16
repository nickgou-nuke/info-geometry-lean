/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite PMF bind and `Fin.cons` transport

This leaf identifies the recursively sampled first state plus continuation
with a pushforward of their joint PMF. It is the algebraic bridge required to
consume a state-dependent continuation law in the trajectory induction.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovFinConsBind

open ProbabilityTheory

variable {ι : Type*} {n : ℕ}

local instance (m : ℕ) : MeasurableSpace (Fin m → ι) := ⊤

/-- Joint law of a first state sampled from `p` and a continuation sampled
conditionally from `q`. -/
def firstStateContinuationPMF (p : PMF ι) (q : ι → PMF (Fin n → ι)) :
    PMF (ι × (Fin n → ι)) :=
  p.bind fun j => (q j).map fun tail => (j, tail)

/-- Mapping the joint first-state/continuation law through `Fin.cons` gives
exactly the recursive PMF bind of the state-dependent prepended paths. -/
theorem bind_map_finCons_eq_joint_map
    (p : PMF ι) (q : ι → PMF (Fin n → ι)) :
    p.bind (fun j => (q j).map (@Fin.cons n (fun _ => ι) j)) =
      (firstStateContinuationPMF p q).map
        (fun pair => @Fin.cons n (fun _ => ι) pair.1 pair.2) := by
  simp only [firstStateContinuationPMF, PMF.map_bind]
  congr 1
  funext j
  rw [PMF.map_comp]
  rfl

/-- Measure form of `bind_map_finCons_eq_joint_map`, suitable for comparison
with the pushforward measures of finite trajectory kernels. -/
theorem bind_map_finCons_toMeasure_eq_joint_map_toMeasure
    (p : PMF ι) (q : ι → PMF (Fin n → ι)) :
    (p.bind (fun j => (q j).map (@Fin.cons n (fun _ => ι) j))).toMeasure =
      ((firstStateContinuationPMF p q).map
        (fun pair => @Fin.cons n (fun _ => ι) pair.1 pair.2)).toMeasure := by
  exact congrArg PMF.toMeasure (bind_map_finCons_eq_joint_map p q)

end InfoGeometry.QuantumContext.FiniteMarkovFinConsBind
end
