import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic

/-!
# Structural recursion for selected-row factorizations

This owner contains the non-enumerative induction principle needed to turn an
explicit predecessor interface into a selected-row factorization theorem. It
deliberately does not assert a predecessor map for the concrete `G₂` tables:
that map and its carrier-alignment equations are separate mathematical data.
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

/-- Right-oriented analogue of `FactorizationStep`.  This is needed when a
    word table grows by appending a suffix rather than by prepending a
    generator. -/
structure RightFactorizationStep
    {G K ι : Type*} [Group G] (T : FactorizationTarget G K ι)
    (k : K) (n : ι) (r : ι → ι → Prop) where
  predecessor : ι
  generator : G
  predecessor_lt : r predecessor n
  representative_step :
    T.representative k n = T.representative k predecessor * generator
  factorized_step :
    T.factorized k n = T.factorized k predecessor * generator

theorem RightFactorizationStep.factorization_of_predecessor
    {G K ι : Type*} [Group G]
    {T : FactorizationTarget G K ι}
    {k : K} {n : ι} {r : ι → ι → Prop}
    (step : RightFactorizationStep T k n r)
    (hpred : T.representative k step.predecessor =
      T.factorized k step.predecessor) :
    T.representative k n = T.factorized k n := by
  rw [step.representative_step, step.factorized_step, hpred]

theorem factorization_of_right_predecessor
    {G K ι : Type*} [Group G]
    (T : FactorizationTarget G K ι)
    (r : ι → ι → Prop) (hwell : WellFounded r)
    (hbase : ∀ k i, (∀ j, ¬ r j i) →
      T.representative k i = T.factorized k i)
    (hstep : ∀ k i, (∃ j, r j i) → RightFactorizationStep T k i r) :
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

/-! The following API uses an explicit natural-valued depth rather than the
serialization order of a finite index.  It is intentionally additive: the
legacy `Fin.val` API below remains available for existing consumers, while
new concrete certificates can migrate to this soundness boundary. -/

structure DepthFactorizationStep
    {G K ι : Type*} [Group G] (T : FactorizationTarget G K ι)
    (depth : ι → ℕ) (k : K) (n : ι) where
  predecessor : ι
  generator : G
  predecessor_depth_lt : depth predecessor < depth n
  representative_step :
    T.representative k n =
      generator * T.representative k predecessor
  factorized_step :
    T.factorized k n =
      generator * T.factorized k predecessor

theorem factorization_of_depth
    {G K ι : Type*} [Group G]
    (T : FactorizationTarget G K ι)
    (depth : ι → ℕ)
    (hbase : ∀ k i, depth i = 0 →
      T.representative k i = T.factorized k i)
    (hstep : ∀ k i, depth i ≠ 0 →
      DepthFactorizationStep T depth k i) :
    ∀ k i, T.representative k i = T.factorized k i := by
  intro k i
  induction h : depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
      by_cases hzero : n = 0
      · exact hbase k i (h.trans hzero)
      · obtain ⟨j, g, hlt, hrep, hfac⟩ := hstep k i (by
          intro hi
          exact hzero (h.symm.trans hi))
        have hlt' : depth j < n := by
          simpa [h] using hlt
        have hpred : T.representative k j = T.factorized k j :=
          ih (depth j) hlt' j rfl
        rw [hrep, hfac, hpred]

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

noncomputable def g2FlagFactorizationTarget :
    FactorizationTarget SplitOctF2Aut (Fin 12) (Fin 189) where
  representative := fun _ i => flagRepresentative i
  factorized := fun k i =>
    collect (leftFactorWord k i) *
      weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
      collect (rightFactorWord k i)

/-! The same cell seam has the opposite orientation on the factorized target:
    the canonical left factor is the accumulated suffix after the matrix
    anti-homomorphism is accounted for. -/
theorem factorized_cell6_2_left_step :
    g2FlagFactorizationTarget.factorized 6 2 =
      collect [((1 : Fin 6), 1), ((4 : Fin 6), 1)] *
        g2FlagFactorizationTarget.factorized 6 1 := by
  change
    (collect [((1 : Fin 6), 1), ((4 : Fin 6), 1)] *
      weylNF (orbitWeyl 6).1 (orbitWeyl 6).2 * collect []) =
      collect [((1 : Fin 6), 1), ((4 : Fin 6), 1)] *
        (collect [] * weylNF (orbitWeyl 6).1 (orbitWeyl 6).2 * collect [])
  simp [collect]

theorem legacy_cell6_2_factorization_false :
    ¬ (flagRepresentative (2 : Fin 189) =
      collect (leftFactorWord 6 2) *
        weylNF (orbitWeyl 6).1 (orbitWeyl 6).2 *
          collect (rightFactorWord 6 2)) := by
  intro h
  have hm := congrArg autMatrix h
  revert hm
  decide

structure G2CellPredecessorCertificate (k : Fin 12) where
  depth : Fin 189 → ℕ
  predecessor : ∀ i, i ∈ orbitCells k → i ≠ orbitCellAnchor k → Fin 189
  predecessor_mem : ∀ i (hi : i ∈ orbitCells k) (hne : i ≠ orbitCellAnchor k),
    predecessor i hi hne ∈ orbitCells k
  predecessor_depth_lt : ∀ i (hi : i ∈ orbitCells k)
    (hne : i ≠ orbitCellAnchor k),
    depth (predecessor i hi hne) < depth i
  depth_zero_iff_anchor : ∀ i, i ∈ orbitCells k →
    (depth i = 0 ↔ i = orbitCellAnchor k)
  base_sound :
    flagRepresentative (orbitCellAnchor k) =
      g2FlagFactorizationTarget.factorized k (orbitCellAnchor k)
  generator : ∀ i, i ∈ orbitCells k → i ≠ orbitCellAnchor k → Fin 8
  representative_step : ∀ i (hi : i ∈ orbitCells k)
    (hne : i ≠ orbitCellAnchor k),
    flagRepresentative i =
      flagGeneratorValue (generator i hi hne) *
        flagRepresentative (predecessor i hi hne)
  factorized_step : ∀ i (hi : i ∈ orbitCells k)
    (hne : i ≠ orbitCellAnchor k),
    g2FlagFactorizationTarget.factorized k i =
      flagGeneratorValue (generator i hi hne) *
        g2FlagFactorizationTarget.factorized k (predecessor i hi hne)

theorem flagRepresentative_factorization_of_cell_certificate
    (C : G2CellPredecessorCertificate k) :
    ∀ i, i ∈ orbitCells k →
      flagRepresentative i = g2FlagFactorizationTarget.factorized k i := by
  intro i hi
  induction h : C.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
      by_cases hzero : n = 0
      · have hanchor : i = orbitCellAnchor k :=
          (C.depth_zero_iff_anchor i hi).mp (h.trans hzero)
        simpa [hanchor] using C.base_sound
      · have hne : i ≠ orbitCellAnchor k := by
          intro hanchor
          have : C.depth i = 0 := by simpa [hanchor] using
            (C.depth_zero_iff_anchor i hi).mpr hanchor
          exact hzero (h.symm.trans this)
        let j := C.predecessor i hi hne
        have hj : j ∈ orbitCells k := C.predecessor_mem i hi hne
        have hlt : C.depth j < n := by
          simpa [h] using C.predecessor_depth_lt i hi hne
        have hpred : flagRepresentative j =
            g2FlagFactorizationTarget.factorized k j :=
          ih (C.depth j) hlt j hj rfl
        rw [C.representative_step i hi hne,
          C.factorized_step i hi hne, hpred]

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
performs the induction and never enumerates the flag table.

This legacy interface uses `Fin.val` as its well-founded measure.  Concrete
certificates should prefer `G2CellPredecessorCertificate` below unless the
export order itself has been proved to be predecessor-monotone. -/
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
