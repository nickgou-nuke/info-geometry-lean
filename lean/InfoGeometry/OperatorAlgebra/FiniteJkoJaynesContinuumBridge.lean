import InfoGeometry.OperatorAlgebra.JaynesFiniteState
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ContinuumLimit
import InfoGeometry.OperatorAlgebra.LogExchangeMonodromy

/-!
# Finite Jaynes / JKO / Continuum Bridge

This file records only the closed algebraic overlap between three existing owner
surfaces:

* finite Jaynes empirical averages from `JaynesFiniteState`;
* observable/state-side coarse graining from `ErlangenJaynesGromov`;
* the exact square-zero rescaled-step law from `ContinuumLimit`.

The theorems here are intentionally finite and algebraic. They do not assert a
general Wasserstein/Fokker--Planck limit, metric ergodicity, positivity, or a
noncommutative KMS/modular completion theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteJkoJaynesContinuumBridge

open InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov
open InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov.OperatorErlangenSystem
open InfoGeometry.OperatorAlgebra.JaynesFiniteState
open InfoGeometry.OperatorAlgebra.ContinuumLimit

universe uK uA uS uι

section

variable {K : Type uK} {A : Type uA} {S : Type uS} {ι : Type uι}
variable [Field K] [Ring A] [Algebra K A]
variable [Monoid S] [Fintype ι]

/--
Projecting a finite empirical state by observable pullback commutes with the
finite empirical average.
-/
theorem semigroupProjection_projectState_finiteEmpiricalState
    {E : OperatorErlangenSystem K A S}
    (P : E.SemigroupProjection)
    (weight : K)
    (sample : FiniteObservableSample K A ι)
    (hweight : weight * (Fintype.card ι : K) = 1) :
    P.projectState (finiteEmpiricalState weight sample hweight) =
      finiteEmpiricalState weight (fun i => P.projectState (sample i)) hweight := by
  ext a
  simp [finiteEmpiricalState_apply,
    InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov.OperatorErlangenSystem.SemigroupProjection.projectState_apply,
    Finset.mul_sum]

/--
Bundled finite families are closed under observable pullback along a semigroup
projection.
-/
def projectedFiniteStateFamily
    {E : OperatorErlangenSystem K A S}
    (P : E.SemigroupProjection)
    (F : FiniteStateCompatibleFamily (R := K) (A := A) (ι := ι)) :
    FiniteStateCompatibleFamily (R := K) (A := A) (ι := ι) where
  weight := F.weight
  sample := fun i => P.projectState (F.sample i)
  hweight := F.hweight

@[simp]
theorem projectedFiniteStateFamily_averageState
    {E : OperatorErlangenSystem K A S}
    (P : E.SemigroupProjection)
    (F : FiniteStateCompatibleFamily (R := K) (A := A) (ι := ι)) :
    (projectedFiniteStateFamily (K := K) (A := A) (S := S) (ι := ι) P F).averageState =
      P.projectState F.averageState := by
  simpa [projectedFiniteStateFamily,
    FiniteStateCompatibleFamily.averageState] using
    (semigroupProjection_projectState_finiteEmpiricalState
      (K := K) (A := A) (S := S) (ι := ι)
      P F.weight F.sample F.hweight).symm

/--
Any finite empirical state reads the projected exact nilpotent `n`-step update
as the corresponding continuum parabolic flow.
-/
theorem finiteEmpiricalState_projection_scaledParabolicStep_pow_eq_flow
    (weight : K)
    (sample : FiniteObservableSample K A ι)
    (hweight : weight * (Fintype.card ι : K) = 1)
    (P : ParabolicContinuumProjectionPacket (K := K) (A := A))
    (t : K) {n : ℕ} (hn : (n : K) ≠ 0) :
    finiteEmpiricalState weight sample hweight
        (P.projection ((scaledParabolicStep P.generator t n) ^ n)) =
      finiteEmpiricalState weight sample hweight
        (continuumParabolicFlow P.generator t) := by
  simpa using congrArg
    (finiteEmpiricalState weight sample hweight)
    (P.projection_fixes_scaled_pow t hn)

/--
Bundled finite empirical families satisfy the same exact projected-step /
continuum-flow readout law.
-/
theorem averageState_projection_scaledParabolicStep_pow_eq_flow
    (F : FiniteStateCompatibleFamily (R := K) (A := A) (ι := ι))
    (P : ParabolicContinuumProjectionPacket (K := K) (A := A))
    (t : K) {n : ℕ} (hn : (n : K) ≠ 0) :
    F.averageState (P.projection ((scaledParabolicStep P.generator t n) ^ n)) =
      F.averageState (continuumParabolicFlow P.generator t) := by
  simpa [FiniteStateCompatibleFamily.averageState] using
    finiteEmpiricalState_projection_scaledParabolicStep_pow_eq_flow
      (K := K) (A := A) (ι := ι)
      F.weight F.sample F.hweight P t hn

/--
If the semigroup projection used on states is the same algebra map as the
projection carried by the nilpotent continuum packet, then the projected finite
average reads the exact `n`-step update as the continuum flow.
-/
theorem semigroupProjection_projectState_averageState_scaledParabolicStep_pow_eq_flow
    {E : OperatorErlangenSystem K A S}
    (SP : E.SemigroupProjection)
    (F : FiniteStateCompatibleFamily (R := K) (A := A) (ι := ι))
    (P : ParabolicContinuumProjectionPacket (K := K) (A := A))
    (hproj : SP.project = P.projection)
    (t : K) {n : ℕ} (hn : (n : K) ≠ 0) :
    SP.projectState F.averageState ((scaledParabolicStep P.generator t n) ^ n) =
      F.averageState (continuumParabolicFlow P.generator t) := by
  rw [InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov.OperatorErlangenSystem.SemigroupProjection.projectState_apply]
  rw [hproj]
  exact averageState_projection_scaledParabolicStep_pow_eq_flow
    (K := K) (A := A) (ι := ι) F P t hn

end

section LogExchange

open InfoGeometry.OperatorAlgebra.LogExchangeMonodromy

variable {ι : Type uι} [Fintype ι]

/--
Concrete finite Jaynes readout for the LCFT/KAN parabolic corridor.

The abstract square-zero and continuum-flow hypotheses are discharged by the
owner theorem `componentN_rescaled_parabolic_pow_exact`, so a finite empirical
average reads the exact rescaled `n`-step update as the concrete `componentN`
flow.
-/
theorem finiteEmpiricalState_componentN_rescaled_parabolic_pow_eq
    (weight : ℂ)
    (sample : FiniteObservableSample ℂ LogExchangeMatrix ι)
    (hweight : weight * (Fintype.card ι : ℂ) = 1)
    (t : ℂ) {n : ℕ} (hn : (n : ℂ) ≠ 0) :
    finiteEmpiricalState weight sample hweight
        ((scaledParabolicStep
          (_root_.InfoGeometry.Clifford.LogCftMonodromy.epsilon : LogExchangeMatrix) t n) ^ n) =
      finiteEmpiricalState weight sample hweight
        (_root_.InfoGeometry.Dynamics.KanDecomposition.componentN t) := by
  exact congrArg (finiteEmpiricalState weight sample hweight)
    (componentN_rescaled_parabolic_pow_exact t hn)

end LogExchange

end InfoGeometry.OperatorAlgebra.FiniteJkoJaynesContinuumBridge
