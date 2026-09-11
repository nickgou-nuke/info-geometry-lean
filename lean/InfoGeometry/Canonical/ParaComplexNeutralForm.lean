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
