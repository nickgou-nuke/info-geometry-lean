import InfoGeometry.Canonical.ParaComplexConnectionBridge

namespace InfoGeometry.Canonical.ParaComplexNeutralForm

noncomputable section

open ParaComplexConnection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A symmetric neutral form compatible with a para-complex involution. -/
structure Datum (PCS : ParaComplexStructure V) where
  form : LinearMap.BilinForm ℝ V
  symmetric : ∀ x y, form x y = form y x
  anti_isometry : ∀ x y, form (PCS.tau x) (PCS.tau y) = - form x y

variable (PCS : ParaComplexStructure V) (B : LinearMap.BilinForm ℝ V)

/-- Compatibility needed for isotropy of the two Peirce eigenspaces. -/
def AntiCompatible : Prop := ∀ x y, B (PCS.tau x) y + B x (PCS.tau y) = 0

theorem plus_isotropic (h : AntiCompatible PCS B) {u v : V}
    (hu : u ∈ plusEigenspace PCS) (hv : v ∈ plusEigenspace PCS) : B u v = 0 := by
  have hu' := (mem_plusEigenspace_iff PCS u).1 hu
  have hv' := (mem_plusEigenspace_iff PCS v).1 hv
  have hh := h u v
  rw [hu', hv'] at hh
  linarith

theorem minus_isotropic (h : AntiCompatible PCS B) {u v : V}
    (hu : u ∈ minusEigenspace PCS) (hv : v ∈ minusEigenspace PCS) : B u v = 0 := by
  have hu' := (mem_minusEigenspace_iff PCS u).1 hu
  have hv' := (mem_minusEigenspace_iff PCS v).1 hv
  have hh := h u v
  rw [hu', hv'] at hh
  simp only [map_neg] at hh
  change -(B u v) + -(B u v) = 0 at hh
  have hval : B u v = 0 := by linarith [hh]
  exact hval

/-- The two Peirce eigenspaces have trivial intersection under a genuine involution. -/
theorem plus_projector_isotropic (h : AntiCompatible PCS B) (x y : V) :
    B (peircePlus PCS x) (peircePlus PCS y) = 0 :=
  plus_isotropic PCS B h (peircePlus_mem_plusEigenspace PCS x)
    (peircePlus_mem_plusEigenspace PCS y)

theorem minus_projector_isotropic (h : AntiCompatible PCS B) (x y : V) :
    B (peirceMinus PCS x) (peirceMinus PCS y) = 0 :=
  minus_isotropic PCS B h (peirceMinus_mem_minusEigenspace PCS x)
    (peirceMinus_mem_minusEigenspace PCS y)

theorem eigenspaces_disjoint {u : V}
    (hu : u ∈ plusEigenspace PCS) (hv : u ∈ minusEigenspace PCS) : u = 0 := by
  have hp := (mem_plusEigenspace_iff PCS u).1 hu
  have hm := (mem_minusEigenspace_iff PCS u).1 hv
  have heq : u = -u := hp.symm.trans hm
  have hsum : u + u = 0 := by
    have h := congrArg (fun x : V => x + u) heq
    simpa using h
  have htwo : (2 : ℝ) • u = 0 := by simpa [two_smul] using hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end
end InfoGeometry.Canonical.ParaComplexNeutralForm

namespace InfoGeometry.Canonical.ParaComplexNeutralForm
noncomputable section
open ParaComplexConnection
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (PCS : ParaComplexStructure V)

/-- A symmetric, nondegenerate neutral form with the cross-pairing hypotheses
needed for the two Peirce leaves to be mutual annihilators. -/
structure NondegenerateDatum (PCS : ParaComplexStructure V) where
  form : LinearMap.BilinForm ℝ V
  symmetric : ∀ x y, form x y = form y x
  anti_compatible : AntiCompatible PCS form
  nondegenerate : ∀ x, (∀ y, form x y = 0) → x = 0
  plus_cross_nondegenerate : ∀ u ∈ minusEigenspace PCS,
    (∀ v ∈ plusEigenspace PCS, form u v = 0) → u = 0
  minus_cross_nondegenerate : ∀ u ∈ plusEigenspace PCS,
    (∀ v ∈ minusEigenspace PCS, form u v = 0) → u = 0

def annihilates (D : NondegenerateDatum PCS)
    (S : Submodule ℝ V) (x : V) : Prop := ∀ y ∈ S, D.form x y = 0

theorem plus_annihilator_eq (D : NondegenerateDatum PCS) :
    {x | annihilates PCS D (plusEigenspace PCS) x} = (plusEigenspace PCS : Set V) := by
  ext x
  constructor
  · intro hx
    let xp : V := peircePlus PCS x
    let xm : V := peirceMinus PCS x
    have hxm : xm ∈ minusEigenspace PCS := peirceMinus_mem_minusEigenspace PCS x
    have hcross : ∀ v ∈ plusEigenspace PCS, D.form xm v = 0 := by
      intro v hv
      have hzero := hx v hv
      have hxp := plus_isotropic PCS D.form D.anti_compatible
        (peircePlus_mem_plusEigenspace PCS x) hv
      have hdecomp : x = xp + xm := by
        dsimp [xp, xm]
        exact (peirce_sum_id PCS x).symm
      rw [hdecomp] at hzero
      simp only [map_add, LinearMap.add_apply] at hzero
      linarith
    have hxm0 : xm = 0 := D.plus_cross_nondegenerate xm hxm hcross
    have hxplus : x ∈ plusEigenspace PCS := by
      rw [show x = xp + xm by exact (peirce_sum_id PCS x).symm, hxm0, add_zero]
      exact peircePlus_mem_plusEigenspace PCS x
    exact hxplus
  · intro hx y hy
    exact plus_isotropic PCS D.form D.anti_compatible hx hy

theorem minus_annihilator_eq (D : NondegenerateDatum PCS) :
    {x | annihilates PCS D (minusEigenspace PCS) x} = (minusEigenspace PCS : Set V) := by
  ext x
  constructor
  · intro hx
    let xp : V := peircePlus PCS x
    let xm : V := peirceMinus PCS x
    have hxp : xp ∈ plusEigenspace PCS := peircePlus_mem_plusEigenspace PCS x
    have hcross : ∀ v ∈ minusEigenspace PCS, D.form xp v = 0 := by
      intro v hv
      have hzero := hx v hv
      have hxm := minus_isotropic PCS D.form D.anti_compatible
        (peirceMinus_mem_minusEigenspace PCS x) hv
      have hdecomp : x = xp + xm := by
        dsimp [xp, xm]
        exact (peirce_sum_id PCS x).symm
      rw [hdecomp] at hzero
      simp only [map_add, LinearMap.add_apply] at hzero
      linarith
    have hxp0 : xp = 0 := D.minus_cross_nondegenerate xp hxp hcross
    rw [show x = xp + xm by exact (peirce_sum_id PCS x).symm, hxp0, zero_add]
    exact peirceMinus_mem_minusEigenspace PCS x
  · intro hx y hy
    exact minus_isotropic PCS D.form D.anti_compatible hx hy

end
end InfoGeometry.Canonical.ParaComplexNeutralForm

namespace InfoGeometry.Canonical.ParaComplexNeutralForm
noncomputable section
open ParaComplexConnection
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (PCS : ParaComplexStructure V)

/-- An isotropic extension of the positive Peirce leaf. -/
def IsotropicPlusExtension (D : NondegenerateDatum PCS) (S : Submodule ℝ V) : Prop :=
  plusEigenspace PCS ≤ S ∧ ∀ x ∈ S, ∀ y ∈ S, D.form x y = 0

/-- An isotropic extension of the negative Peirce leaf. -/
def IsotropicMinusExtension (D : NondegenerateDatum PCS) (S : Submodule ℝ V) : Prop :=
  minusEigenspace PCS ≤ S ∧ ∀ x ∈ S, ∀ y ∈ S, D.form x y = 0

theorem isotropic_plus_extension_eq (D : NondegenerateDatum PCS) (S : Submodule ℝ V)
    (hS : IsotropicPlusExtension PCS D S) : S = plusEigenspace PCS := by
  apply le_antisymm
  · intro x hx
    have hxann : annihilates PCS D (plusEigenspace PCS) x := by
      intro y hy
      exact hS.2 x hx y (hS.1 hy)
    have hxset : x ∈ {x | annihilates PCS D (plusEigenspace PCS) x} := hxann
    rw [plus_annihilator_eq PCS D] at hxset
    exact hxset
  · exact hS.1

theorem isotropic_minus_extension_eq (D : NondegenerateDatum PCS) (S : Submodule ℝ V)
    (hS : IsotropicMinusExtension PCS D S) : S = minusEigenspace PCS := by
  apply le_antisymm
  · intro x hx
    have hxann : annihilates PCS D (minusEigenspace PCS) x := by
      intro y hy
      exact hS.2 x hx y (hS.1 hy)
    have hxset : x ∈ {x | annihilates PCS D (minusEigenspace PCS) x} := hxann
    rw [minus_annihilator_eq PCS D] at hxset
    exact hxset
  · exact hS.1

/-- The finite-dimensional rank identity supplied by the canonical Peirce equivalence. -/
theorem finrank_peirce_sum [FiniteDimensional ℝ V] :
    Module.finrank ℝ V =
      Module.finrank ℝ (plusEigenspace PCS) + Module.finrank ℝ (minusEigenspace PCS) := by
  rw [LinearEquiv.finrank_eq (peirceDecomposition PCS), Module.finrank_prod]

/-- Equal leaf dimensions follow from an explicitly supplied cross linear equivalence. -/
theorem finrank_peirce_eq_of_cross_equiv [FiniteDimensional ℝ V]
    (e : plusEigenspace PCS ≃ₗ[ℝ] minusEigenspace PCS) :
    Module.finrank ℝ (plusEigenspace PCS) = Module.finrank ℝ (minusEigenspace PCS) :=
  e.finrank_eq

end
end InfoGeometry.Canonical.ParaComplexNeutralForm

namespace InfoGeometry.Canonical.ParaComplexNeutralForm
noncomputable section
open ParaComplexConnection
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (PCS : ParaComplexStructure V)

/-- In finite dimension, a supplied cross equivalence identifies the total rank
with twice the rank of either Peirce leaf. -/
theorem finrank_v_eq_two_mul_plus_of_cross_equiv [FiniteDimensional ℝ V]
    (D : NondegenerateDatum PCS)
    (e : plusEigenspace PCS ≃ₗ[ℝ] minusEigenspace PCS) :
    Module.finrank ℝ V = 2 * Module.finrank ℝ (plusEigenspace PCS) := by
  rw [finrank_peirce_sum PCS]
  rw [finrank_peirce_eq_of_cross_equiv PCS e]
  ring

end
end InfoGeometry.Canonical.ParaComplexNeutralForm
