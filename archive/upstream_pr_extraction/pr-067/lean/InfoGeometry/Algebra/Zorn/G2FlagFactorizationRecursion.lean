import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic

/-!
# Structural recursion for flag factorizations

This owner contains the non-enumerative induction principle needed to turn a
predecessor certificate into a flag factorization theorem.  It deliberately
does not assert a predecessor map for the concrete `G₂` tables: that map and
its carrier-alignment equations are separate mathematical data.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationRecursion

variable {G : Type*} [Group G]

/-- A target expression whose value is intended to be the factorized form of a
representative.  The definition is intentionally abstract so the recursion
principle is reusable by concrete flag and Bruhat owners. -/
structure FactorizationTarget (G K ι : Type*) [Group G] where
  representative : K → ι → G
  factorized : K → ι → G

/-- Data for one predecessor step.  The generator is explicit: both the
representative and its proposed factorization are obtained from the same
predecessor by the same left action. -/
structure FactorizationStep
    {G K ι : Type*} [Group G] (T : FactorizationTarget G K ι)
    (k : K) (n : ι) (r : ι → ι → Prop) where
  predecessor : ι
  generator : G
  predecessor_lt : r predecessor n
  representative_step :
    T.representative k n = generator * T.representative k predecessor
  factorized_step :
    T.factorized k n = generator * T.factorized k predecessor

/-- A certified predecessor equality closes one recursive step. -/
theorem FactorizationStep.factorization_of_predecessor
    {G K ι : Type*} [Group G]
    {T : FactorizationTarget G K ι}
    {k : K} {n : ι} {r : ι → ι → Prop}
    (step : FactorizationStep T k n r)
    (hpred : T.representative k step.predecessor =
      T.factorized k step.predecessor) :
    T.representative k n = T.factorized k n := by
  rw [step.representative_step, step.factorized_step, hpred]

/-- Well-founded predecessor recursion transports equality of representatives
and factorized expressions from the predecessor to the current index. -/
theorem factorization_of_predecessor
    {ι : Type*} (T : FactorizationTarget G K ι)
    (r : ι → ι → Prop) (hwell : WellFounded r)
    (hbase : ∀ k i, (∀ j, ¬ r j i) →
      T.representative k i = T.factorized k i)
    (hstep : ∀ k i, (∃ j, r j i) → FactorizationStep T k i r) :
    ∀ k i, T.representative k i = T.factorized k i := by
  intro k i
  induction i using hwell.induction with
  | h i ih =>
      by_cases hmin : ∀ j, ¬ r j i
      · exact hbase k i hmin
      · obtain ⟨j, g, hji, hr, hf⟩ := hstep k i (by
          push_neg at hmin
          exact hmin)
        rw [hr, hf, ih j hji]

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def g2FlagFactorizationTarget :
    FactorizationTarget SplitOctF2Aut (Fin 12) (Fin 189) where
  representative := fun _ i => flagRepresentative i
  factorized := fun k i =>
    collect (leftFactorWord k i) *
      weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (rightFactorWord k i)

/-/ The concrete certificate required to connect an orbit cell to the
generic recursion.  Producing an inhabitant is the CAS-backed mathematical
work; this structure does not hide it behind a proposition-valued theorem. -/
structure G2OrbitFactorizationStep (k : Fin 12) (i : Fin 189) where
  predecessor : Fin 189
  generator : Fin 8
  predecessor_mem : predecessor ∈ orbitCells k
  current_mem : i ∈ orbitCells k
  predecessor_lt : predecessor.val < i.val
  representative_step :
    flagRepresentative i = flagGeneratorValue generator *
      flagRepresentative predecessor
  factorized_step :
    g2FlagFactorizationTarget.factorized k i =
      flagGeneratorValue generator *
        g2FlagFactorizationTarget.factorized k predecessor

noncomputable def G2OrbitFactorizationStep.toGeneric
    {k : Fin 12} {i : Fin 189}
    (step : G2OrbitFactorizationStep k i) :
    FactorizationStep g2FlagFactorizationTarget k i
      (fun j i => j.val < i.val) where
  predecessor := step.predecessor
  generator := flagGeneratorValue step.generator
  predecessor_lt := step.predecessor_lt
  representative_step := step.representative_step
  factorized_step := step.factorized_step

/-- Concrete G₂ consequence of a supplied predecessor certificate.  The
certificate contains the genuine carrier-alignment work; this theorem only
performs the induction and never enumerates the flag table. -/
theorem flagRepresentative_factorization_of_predecessor_certificate
    (hbase : ∀ k i, (∀ j : Fin 189, ¬ j.val < i.val) →
      flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i))
    (hstep : ∀ k i, (∃ j : Fin 189, j.val < i.val) →
      FactorizationStep g2FlagFactorizationTarget k i
        (fun j i => j.val < i.val)) :
    ∀ (k : Fin 12) (i : Fin 189),
      flagRepresentative i =
        collect (leftFactorWord k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            collect (rightFactorWord k i) := by
  apply factorization_of_predecessor g2FlagFactorizationTarget
    (fun i j => i.val < j.val) (by
      exact InvImage.wf Fin.val wellFounded_lt)
  · intro k i hi
    simpa [g2FlagFactorizationTarget] using hbase k i hi
  · intro k i hi
    exact hstep k i hi

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationRecursion
