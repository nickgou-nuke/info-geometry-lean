import Mathlib
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham

/-!
# Topological Klein quadric / Grothendieck–de Rham bridge

This owner packages the existing projective Klein/Grothendieck/de Rham
bridge into native topological continuity statements.

It does not claim a new equivalence theorem.  It records the continuity of the
split quartic potential, the chiral determinant potential, and the logarithmic
data on the slit plane / punctured plane.
-/

namespace InfoGeometry.Topology.KleinQuadricGrothendieckDeRhamTopological

open Complex
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive

noncomputable section

abbrev FourVectorC := InfoGeometry.Projective.KleinQuadric.DeRhamMotive.FourVectorC

/-- The split Klein potential is a continuous polynomial function. -/
theorem continuous_splitPotential : Continuous (splitPotential : FourVectorC → ℂ) := by
  unfold splitPotential
  fun_prop

/-- The Klein-null locus of the split potential is closed. -/
theorem isClosed_splitPotential_zero :
    IsClosed ({v : FourVectorC | splitPotential v = 0} : Set FourVectorC) := by
  simpa [Set.preimage] using
    (IsClosed.preimage continuous_splitPotential isClosed_singleton :
      IsClosed (splitPotential ⁻¹' ({0} : Set ℂ)))

/-- The Klein-chiral determinant potential is continuous on the product space. -/
theorem continuous_chiralDetPotential :
    Continuous (fun p : FourVectorC × FourVectorC =>
      chiralDetPotential p.1 p.2) := by
  have hs : Continuous (splitPotential : FourVectorC → ℂ) :=
    continuous_splitPotential
  simpa [chiralDetPotential] using
    ((hs.comp continuous_fst).mul (hs.comp continuous_snd)).mul
      (hs.comp (continuous_fst.sub continuous_snd))

/-- The zero-locus of the chiral Klein determinant potential is closed. -/
theorem isClosed_chiralDetPotential_zero :
    IsClosed ({p : FourVectorC × FourVectorC | chiralDetPotential p.1 p.2 = 0} :
      Set (FourVectorC × FourVectorC)) := by
  simpa [Set.preimage] using
    (IsClosed.preimage continuous_chiralDetPotential isClosed_singleton :
      IsClosed
        ((fun p : FourVectorC × FourVectorC => chiralDetPotential p.1 p.2) ⁻¹'
          ({0} : Set ℂ)))

/-- The Grothendieck `dlog` form is continuous on the punctured plane. -/
theorem continuousOn_grothendieck_dlog :
    ContinuousOn (fun z : ℂ => grothendieck_dlog z) ({0}ᶜ : Set ℂ) := by
  simpa [grothendieck_dlog] using
    (continuousOn_inv₀ : ContinuousOn (fun z : ℂ => z⁻¹) ({0}ᶜ : Set ℂ))

/-- The logarithmic Grothendieck potential is continuous on the slit plane. -/
theorem continuousOn_grothendieckLog :
    ContinuousOn (fun z : ℂ => grothendieckLog z) Complex.slitPlane := by
  simpa [grothendieckLog] using
    (continuousOn_id.clog (fun z hz => hz) :
      ContinuousOn (fun z : ℂ => Complex.log z) Complex.slitPlane)
