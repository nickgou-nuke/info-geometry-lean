import InfoGeometry.Clifford.ChevalleyPureSpinor
import InfoGeometry.Canonical.TwistorExteriorSpinorCompatibility

/-!
# Exterior/Plücker/pure-spinor compatibility

This owner records the first common point of the two exterior branches.  A
decomposable Plücker readout is Klein-null, while the corresponding split
exterior spinor action has an isotropic annihilator.  The stronger statement
that every decomposable homogeneous form has maximal annihilator is left as a
separate finite-dimensional extension.
-/

namespace InfoGeometry.Canonical.ExteriorPluckerPureSpinorCompatibility

open InfoGeometry.Clifford
open Module

noncomputable section

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- The exterior-algebra vacuum spinor. -/
def vacuum : SpinorSpace L := algebraMap ℝ (SpinorSpace L) 1

@[simp] theorem vacuum_ne_zero : vacuum (L := L) ≠ 0 := by
  simp [vacuum]

theorem dual_polarization_annihilates_vacuum (f : Dual L) :
    (0, f) ∈ annihilator (vacuum (L := L)) := by
  change spinorAction (0, f) (vacuum (L := L)) = 0
  simp [spinorAction, extAction, intAction, vacuum]

theorem vacuum_annihilator_isotropic :
    IsIsotropic (annihilator (vacuum (L := L))) := by
  intro x hx y hy
  exact annihilator_isotropic (vacuum_ne_zero (L := L)) hx hy

theorem vacuum_dual_pair_isotropic (f g : Dual L) :
    QuadraticMap.polar (Qsplit L) (0, f) (0, g) = 0 := by
  apply annihilator_isotropic (vacuum_ne_zero (L := L))
  · exact dual_polarization_annihilates_vacuum f
  · exact dual_polarization_annihilates_vacuum g

theorem vacuum_annihilator_eq_dual_polarization :
    annihilator (vacuum (L := L)) = {x : SplitSpace L | x.1 = 0} := by
  ext x
  rcases x with ⟨u, f⟩
  constructor
  · intro hx
    change spinorAction (u, f) (vacuum (L := L)) = 0 at hx
    change extAction u (vacuum (L := L)) + intAction f (vacuum (L := L)) = 0 at hx
    simp [vacuum, extAction, intAction] at hx
    exact hx
  · intro hu
    change u = 0 at hu
    subst u
    exact dual_polarization_annihilates_vacuum f

theorem vacuum_annihilator_is_maximal_isotropic
    [Projective ℝ L] :
    IsMaximalIsotropic (annihilator (vacuum (L := L))) := by
  refine ⟨vacuum_annihilator_isotropic, ?_⟩
  intro T hT hsub x hx
  rcases x with ⟨u, f⟩
  have hu : u = 0 := by
    by_contra hne
    obtain ⟨g, hg⟩ := Projective.exists_dual_eq_one ℝ hne
    have hmem : (0, g) ∈ T :=
      hsub (dual_polarization_annihilates_vacuum g)
    have hzero := hT hx hmem
    have hval : g u = 0 := by
      simpa [Qsplit, Bsplit, QuadraticMap.polar] using hzero
    exact hne (by simpa [hval] using hg)
  subst u
  exact dual_polarization_annihilates_vacuum f

end

end InfoGeometry.Canonical.ExteriorPluckerPureSpinorCompatibility
