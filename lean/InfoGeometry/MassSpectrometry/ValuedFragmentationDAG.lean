import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.FragmentationDAG

/-!
# Mass-valued fragmentation DAG

This module adds the physically meaningful mass valuation to the abstract
rank-certified DAG owner.  The base `FragmentationDAG` remains combinatorial;
this extension records strictly positive fragment masses and strict mass loss
along cleavage edges.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

/-- A rank-certified fragmentation DAG equipped with a strictly positive mass
valuation that decreases along every directed edge. -/
structure ValuedFragmentationDAG (n : ℕ) extends FragmentationDAG n where
  massOf : Fin n → ℝ
  mass_pos : ∀ v, 0 < massOf v
  mass_decreases : ∀ {u v}, edge u v → massOf v < massOf u

namespace ValuedFragmentationDAG

variable {n : ℕ} (D : ValuedFragmentationDAG n)

/-- Forget the mass valuation and retain the certified DAG. -/
def toDAG : FragmentationDAG n := D.toFragmentationDAG

/-- Neutral-loss coordinate `Δm = m(u)-m(v)`. -/
def deltaMass (u v : Fin n) : ℝ :=
  D.massOf u - D.massOf v

/-- Every cleavage edge has strictly positive neutral loss. -/
theorem deltaMass_pos {u v : Fin n} (h : D.edge u v) :
    0 < D.deltaMass u v := by
  exact sub_pos.mpr (D.mass_decreases h)

/-- Every nonempty fragmentation path strictly decreases physical mass. -/
theorem transGen_mass_lt {u v : Fin n}
    (path : Relation.TransGen D.edge u v) :
    D.massOf v < D.massOf u := by
  induction path with
  | single step => exact D.mass_decreases step
  | tail _ step ih =>
      exact lt_trans (D.mass_decreases step) ih

/-- A nonempty fragmentation path has positive total endpoint mass loss. -/
theorem endpoint_deltaMass_pos {u v : Fin n}
    (path : Relation.TransGen D.edge u v) :
    0 < D.deltaMass u v := by
  exact sub_pos.mpr (D.transGen_mass_lt path)

/-- Mass decrease alone independently certifies absence of nonempty cycles. -/
theorem mass_certifies_acyclic :
    ∀ u : Fin n, ¬ Relation.TransGen D.edge u u := by
  intro u loop
  exact lt_irrefl (D.massOf u) (D.transGen_mass_lt loop)

/-- The mass-valued DAG agrees with the base owner's DAG theorem. -/
theorem base_isDAG : D.toDAG.IsDAG :=
  D.toDAG.isDAG

end ValuedFragmentationDAG

end InfoGeometry.MassSpectrometry
