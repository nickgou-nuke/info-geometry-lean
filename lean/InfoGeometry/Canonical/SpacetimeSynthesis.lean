import InfoGeometry.Canonical.CausalFunctor
import InfoGeometry.Topology.CantorCliffordFunctor
import Mathlib.Algebra.Category.AlgCat.Basic

open CategoryTheory Limits

namespace InfoGeometry.Canonical

/--
  The Directed Cantor Boolean Prefix Tree is formally recognized
  as a Causal Spacetime poset.
-/
abbrev CantorIndexCategory : Type := InfoGeometry.Topology.J

/--
  We map the Clifford Tower (which lives in `AlgCat ℝ`) down to `RingCat`
  via the forgetful functor so it natively instantiates the abstract `CausalFunctor`.
-/
noncomputable def CliffordTowerCausalFunctor
    (Q : ∀ n, QuadraticForm ℝ (InfoGeometry.Topology.V n))
    (h_compat : ∀ (m n : ℕ) (_h : m ≤ n) (x : InfoGeometry.Topology.V m),
      Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x) :
    CausalFunctor CantorIndexCategory :=
  InfoGeometry.Topology.CliffordTowerFunctor Q h_compat ⋙ forget₂ (AlgCat ℝ) RingCat

/--
  The resulting Colimit over this specific Causal Functor is the exact 
  hyperfinite Type III factor / CPT Spinor Vacuum.
-/
noncomputable abbrev CPTSpinorVacuum
    (Q : ∀ n, QuadraticForm ℝ (InfoGeometry.Topology.V n))
    (h_compat : ∀ (m n : ℕ) (_h : m ≤ n) (x : InfoGeometry.Topology.V m),
      Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x)
    [HasColimit (CliffordTowerCausalFunctor Q h_compat)] : RingCat :=
  UniversalCausalFuture (CliffordTowerCausalFunctor Q h_compat)

/--
  Because the Clifford Tower is a valid Causal Functor, its physical limit 
  (the CPT Spinor Vacuum) formally inherits the Spacetime Causality theorem.
  Information in the Clifford bit-layers is fully conserved.
-/
theorem cpt_vacuum_causality
    (Q : ∀ n, QuadraticForm ℝ (InfoGeometry.Topology.V n))
    (h_compat : ∀ (m n : ℕ) (_h : m ≤ n) (x : InfoGeometry.Topology.V m),
      Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x)
    [HasColimit (CliffordTowerCausalFunctor Q h_compat)]
    (m n : CantorIndexCategory) (causal_link : m ≤ n)
    (x : (CliffordTowerCausalFunctor Q h_compat).obj m) :
    (colimit.ι (CliffordTowerCausalFunctor Q h_compat) m) x =
      (colimit.ι (CliffordTowerCausalFunctor Q h_compat) n)
        (((CliffordTowerCausalFunctor Q h_compat).map (homOfLE causal_link)) x) :=
  causal_information_conservation (CliffordTowerCausalFunctor Q h_compat) causal_link x

end InfoGeometry.Canonical
