import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeStages
import InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge

/-!
# Cyclotomic labels on finite Heisenberg mode stages

The finite-mode colimit is indexed by finite subsets of `Option ℤ`.  This
owner records the honest order-three label of those basis indices and proves
that the label sets are monotone under stage inclusion.  It does not assign a
cyclotomic degree to an arbitrary linear combination, where no canonical
single degree exists.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological

open InfoGeometry.Canonical

noncomputable section

instance heisenbergBasisIndexTopologicalSpace :
    TopologicalSpace (Option ℤ) := ⊥

instance heisenbergBasisIndexDiscreteTopology :
    DiscreteTopology (Option ℤ) := ⟨rfl⟩

/-- The central basis label has degree zero; a current mode has its residue
modulo three. -/
def heisenbergBasisCyclotomicDegree : Option ℤ → ZMod 3
  | none => 0
  | some k => heisenbergModeDegree k

@[simp] theorem heisenbergBasisCyclotomicDegree_none :
    heisenbergBasisCyclotomicDegree none = 0 := by
  rfl

@[simp] theorem heisenbergBasisCyclotomicDegree_some (k : ℤ) :
    heisenbergBasisCyclotomicDegree (some k) = heisenbergModeDegree k := by
  rfl

theorem heisenbergBasisCyclotomicDegree_neg (k : ℤ) :
    heisenbergBasisCyclotomicDegree (some (-k)) =
      -heisenbergBasisCyclotomicDegree (some k) := by
  simpa using heisenbergModeDegree_neg k

/-- The finite set of cyclotomic labels visible at a stage. -/
def stageCyclotomicDegreeSet (s : Finset (Option ℤ)) : Finset (ZMod 3) :=
  s.image heisenbergBasisCyclotomicDegree

theorem stageCyclotomicDegreeSet_mono
    {s t : Finset (Option ℤ)} (hst : s ⊆ t) :
    stageCyclotomicDegreeSet s ⊆ stageCyclotomicDegreeSet t := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hst hi, rfl⟩

theorem basisJK_stage_degree_mem
    (s : Finset (Option ℤ)) (i : Option ℤ) (hi : i ∈ s) :
    heisenbergBasisCyclotomicDegree i ∈ stageCyclotomicDegreeSet s := by
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- The index-to-degree readout is continuous for the discrete index topology. -/
theorem continuous_heisenbergBasisCyclotomicDegree :
    Continuous heisenbergBasisCyclotomicDegree := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_heisenbergBasisCyclotomicDegree :
    IsLocallyConstant heisenbergBasisCyclotomicDegree := by
  exact IsLocallyConstant.of_discrete
    (f := heisenbergBasisCyclotomicDegree)

end
end InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
