import InfoGeometry.Canonical.SplitOctonionCanonicalThreeForm

/-!
# Four coordinate planes in the split-octonion carrier

This owner records the explicit coordinate splitting
`(1, l) ⊕ (i, il) ⊕ (j, jl) ⊕ (k, kl)` in the native rational
split-octonion carrier.  It proves reconstruction and orthogonality for the
existing polarized coordinate form.  It does not identify this configuration
with an amplituhedron, a twistor space, or a holonomy manifold.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

noncomputable section

abbrev FourPlaneCarrier := StandardRationalSplitOctonion

def oneLPlaneComponent (x : FourPlaneCarrier) : FourPlaneCarrier :=
  Pi.single IntegralSplitBasis.one (x .one) +
    Pi.single IntegralSplitBasis.l (x .l)

def iPlaneComponent (x : FourPlaneCarrier) : FourPlaneCarrier :=
  Pi.single IntegralSplitBasis.i (x .i) +
    Pi.single IntegralSplitBasis.il (x .il)

def jPlaneComponent (x : FourPlaneCarrier) : FourPlaneCarrier :=
  Pi.single IntegralSplitBasis.j (x .j) +
    Pi.single IntegralSplitBasis.jl (x .jl)

def kPlaneComponent (x : FourPlaneCarrier) : FourPlaneCarrier :=
  Pi.single IntegralSplitBasis.k (x .k) +
    Pi.single IntegralSplitBasis.kl (x .kl)

abbrev FourPlaneComponentCarrier := Fin 4 → FourPlaneCarrier

def fourPlaneComponents (x : FourPlaneCarrier) : FourPlaneComponentCarrier :=
  ![oneLPlaneComponent x, iPlaneComponent x, jPlaneComponent x, kPlaneComponent x]

def fourPlaneReassemble (v : FourPlaneComponentCarrier) : FourPlaneCarrier :=
  v 0 + v 1 + v 2 + v 3

theorem continuous_fourPlaneReassemble :
    Continuous fourPlaneReassemble := by
  unfold fourPlaneReassemble
  fun_prop

theorem continuous_oneLPlaneComponent :
    Continuous oneLPlaneComponent := by
  unfold oneLPlaneComponent
  apply continuous_pi
  intro b
  cases b <;> simp [Pi.single_apply] <;> fun_prop

theorem continuous_iPlaneComponent :
    Continuous iPlaneComponent := by
  unfold iPlaneComponent
  apply continuous_pi
  intro b
  cases b <;> simp [Pi.single_apply] <;> fun_prop

theorem continuous_jPlaneComponent :
    Continuous jPlaneComponent := by
  unfold jPlaneComponent
  apply continuous_pi
  intro b
  cases b <;> simp [Pi.single_apply] <;> fun_prop

theorem continuous_kPlaneComponent :
    Continuous kPlaneComponent := by
  unfold kPlaneComponent
  apply continuous_pi
  intro b
  cases b <;> simp [Pi.single_apply] <;> fun_prop

theorem continuous_fourPlaneComponents :
    Continuous fourPlaneComponents := by
  unfold fourPlaneComponents
  apply continuous_pi
  intro b
  fin_cases b
  · exact continuous_oneLPlaneComponent
  · exact continuous_iPlaneComponent
  · exact continuous_jPlaneComponent
  · exact continuous_kPlaneComponent

theorem continuous_trialityColorCycle :
    Continuous (trialityColorCycle : FourPlaneCarrier → FourPlaneCarrier) := by
  unfold trialityColorCycle
  apply continuous_pi
  intro b
  cases b <;>
    simp [colorCycleBasisEquiv, colorCycleBasis, colorCycleBasisInv] <;>
    fun_prop

theorem trialityColorCycle_oneLPlaneComponent (x : FourPlaneCarrier) :
    oneLPlaneComponent (trialityColorCycle x) =
      trialityColorCycle (oneLPlaneComponent x) := by
  funext b
  cases b <;>
    simp [oneLPlaneComponent, trialityColorCycle, colorCycleBasisEquiv,
      colorCycleBasis, colorCycleBasisInv, rationalBasis]

theorem trialityColorCycle_iPlaneComponent (x : FourPlaneCarrier) :
    iPlaneComponent (trialityColorCycle x) =
      trialityColorCycle (kPlaneComponent x) := by
  funext b
  cases b <;>
    simp [iPlaneComponent, kPlaneComponent, trialityColorCycle,
      colorCycleBasisEquiv, colorCycleBasis, colorCycleBasisInv, rationalBasis]

theorem trialityColorCycle_jPlaneComponent (x : FourPlaneCarrier) :
    jPlaneComponent (trialityColorCycle x) =
      trialityColorCycle (iPlaneComponent x) := by
  funext b
  cases b <;>
    simp [jPlaneComponent, iPlaneComponent, trialityColorCycle,
      colorCycleBasisEquiv, colorCycleBasis, colorCycleBasisInv, rationalBasis]

theorem trialityColorCycle_kPlaneComponent (x : FourPlaneCarrier) :
    kPlaneComponent (trialityColorCycle x) =
      trialityColorCycle (jPlaneComponent x) := by
  funext b
  cases b <;>
    simp [kPlaneComponent, jPlaneComponent, trialityColorCycle,
      colorCycleBasisEquiv, colorCycleBasis, colorCycleBasisInv, rationalBasis]

@[simp] theorem fourPlaneComponents_apply_zero (x : FourPlaneCarrier) :
    fourPlaneComponents x 0 = oneLPlaneComponent x := by
  rfl

@[simp] theorem fourPlaneComponents_apply_one (x : FourPlaneCarrier) :
    fourPlaneComponents x 1 = iPlaneComponent x := by
  rfl

@[simp] theorem fourPlaneComponents_apply_two (x : FourPlaneCarrier) :
    fourPlaneComponents x 2 = jPlaneComponent x := by
  rfl

@[simp] theorem fourPlaneComponents_apply_three (x : FourPlaneCarrier) :
    fourPlaneComponents x 3 = kPlaneComponent x := by
  rfl

def coordinatePlane (b₁ b₂ : IntegralSplitBasis) :
    Submodule ℚ FourPlaneCarrier :=
  Submodule.span ℚ ({rationalBasis b₁, rationalBasis b₂} : Set FourPlaneCarrier)

def oneLPlane : Submodule ℚ FourPlaneCarrier :=
  coordinatePlane IntegralSplitBasis.one IntegralSplitBasis.l

def iPlane : Submodule ℚ FourPlaneCarrier :=
  coordinatePlane IntegralSplitBasis.i IntegralSplitBasis.il

def jPlane : Submodule ℚ FourPlaneCarrier :=
  coordinatePlane IntegralSplitBasis.j IntegralSplitBasis.jl

def kPlane : Submodule ℚ FourPlaneCarrier :=
  coordinatePlane IntegralSplitBasis.k IntegralSplitBasis.kl

private theorem coordinatePlane_finrank_of_distinct
    (b₁ b₂ : IntegralSplitBasis) (h : b₁ ≠ b₂) :
    Module.finrank ℚ (coordinatePlane b₁ b₂) = 2 := by
  let v : Fin 2 → FourPlaneCarrier := ![rationalBasis b₁, rationalBasis b₂]
  have hv : LinearIndependent ℚ v := by
    rw [linearIndependent_fin2]
    constructor
    · intro hz
      have hz' := congrFun hz b₂
      simp [v, rationalBasis] at hz'
    · intro a ha
      have ha' := congrFun ha b₁
      simp [v, rationalBasis, h] at ha'
  have hrange : Set.range v =
      ({rationalBasis b₁, rationalBasis b₂} : Set FourPlaneCarrier) := by
    ext z
    simp [v, or_comm]
  change Module.finrank ℚ
      (Submodule.span ℚ
        ({rationalBasis b₁, rationalBasis b₂} : Set FourPlaneCarrier)) = 2
  rw [← hrange, finrank_span_eq_card hv]
  rfl

theorem oneLPlane_finrank : Module.finrank ℚ oneLPlane = 2 := by
  exact coordinatePlane_finrank_of_distinct _ _ (by decide)

theorem iPlane_finrank : Module.finrank ℚ iPlane = 2 := by
  exact coordinatePlane_finrank_of_distinct _ _ (by decide)

theorem jPlane_finrank : Module.finrank ℚ jPlane = 2 := by
  exact coordinatePlane_finrank_of_distinct _ _ (by decide)

theorem kPlane_finrank : Module.finrank ℚ kPlane = 2 := by
  exact coordinatePlane_finrank_of_distinct _ _ (by decide)

private theorem oneLPlaneComponent_eq_span_generators (x : FourPlaneCarrier) :
    oneLPlaneComponent x =
      x .one • rationalBasis IntegralSplitBasis.one +
        x .l • rationalBasis IntegralSplitBasis.l := by
  funext b
  cases b <;> simp [oneLPlaneComponent, rationalBasis, Pi.smul_apply]

private theorem iPlaneComponent_eq_span_generators (x : FourPlaneCarrier) :
    iPlaneComponent x =
      x .i • rationalBasis IntegralSplitBasis.i +
        x .il • rationalBasis IntegralSplitBasis.il := by
  funext b
  cases b <;> simp [iPlaneComponent, rationalBasis, Pi.smul_apply]

private theorem jPlaneComponent_eq_span_generators (x : FourPlaneCarrier) :
    jPlaneComponent x =
      x .j • rationalBasis IntegralSplitBasis.j +
        x .jl • rationalBasis IntegralSplitBasis.jl := by
  funext b
  cases b <;> simp [jPlaneComponent, rationalBasis, Pi.smul_apply]

private theorem kPlaneComponent_eq_span_generators (x : FourPlaneCarrier) :
    kPlaneComponent x =
      x .k • rationalBasis IntegralSplitBasis.k +
        x .kl • rationalBasis IntegralSplitBasis.kl := by
  funext b
  cases b <;> simp [kPlaneComponent, rationalBasis, Pi.smul_apply]

theorem oneLPlaneComponent_mem (x : FourPlaneCarrier) :
    oneLPlaneComponent x ∈ oneLPlane := by
  rw [oneLPlaneComponent_eq_span_generators]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem iPlaneComponent_mem (x : FourPlaneCarrier) :
    iPlaneComponent x ∈ iPlane := by
  rw [iPlaneComponent_eq_span_generators]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem jPlaneComponent_mem (x : FourPlaneCarrier) :
    jPlaneComponent x ∈ jPlane := by
  rw [jPlaneComponent_eq_span_generators]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem kPlaneComponent_mem (x : FourPlaneCarrier) :
    kPlaneComponent x ∈ kPlane := by
  rw [kPlaneComponent_eq_span_generators]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem fourPlane_reconstruction (x : FourPlaneCarrier) :
    oneLPlaneComponent x + iPlaneComponent x +
        jPlaneComponent x + kPlaneComponent x = x := by
  funext b
  cases b <;>
    simp [oneLPlaneComponent, iPlaneComponent, jPlaneComponent,
      kPlaneComponent]

@[simp] theorem fourPlaneReassemble_components (x : FourPlaneCarrier) :
    fourPlaneReassemble (fourPlaneComponents x) = x := by
  unfold fourPlaneReassemble fourPlaneComponents
  exact fourPlane_reconstruction x

theorem oneLPlane_orthogonal_iPlane (x y : FourPlaneCarrier) :
    splitInner (oneLPlaneComponent x) (iPlaneComponent y) = 0 := by
  simp [oneLPlaneComponent, iPlaneComponent, splitInner, coordinateSplitNorm]
  ring

theorem oneLPlane_orthogonal_jPlane (x y : FourPlaneCarrier) :
    splitInner (oneLPlaneComponent x) (jPlaneComponent y) = 0 := by
  simp [oneLPlaneComponent, jPlaneComponent, splitInner, coordinateSplitNorm]
  ring

theorem oneLPlane_orthogonal_kPlane (x y : FourPlaneCarrier) :
    splitInner (oneLPlaneComponent x) (kPlaneComponent y) = 0 := by
  simp [oneLPlaneComponent, kPlaneComponent, splitInner, coordinateSplitNorm]
  ring

theorem iPlane_orthogonal_jPlane (x y : FourPlaneCarrier) :
    splitInner (iPlaneComponent x) (jPlaneComponent y) = 0 := by
  simp [iPlaneComponent, jPlaneComponent, splitInner, coordinateSplitNorm]
  ring

theorem iPlane_orthogonal_kPlane (x y : FourPlaneCarrier) :
    splitInner (iPlaneComponent x) (kPlaneComponent y) = 0 := by
  simp [iPlaneComponent, kPlaneComponent, splitInner, coordinateSplitNorm]
  ring

theorem jPlane_orthogonal_kPlane (x y : FourPlaneCarrier) :
    splitInner (jPlaneComponent x) (kPlaneComponent y) = 0 := by
  simp [jPlaneComponent, kPlaneComponent, splitInner, coordinateSplitNorm]
  ring

/-- The canonical four-plane configuration packaged as a reusable property.

This records the four coordinate 2-planes together with their finite-rank
readout, the component-wise reconstruction theorem, and the pairwise
orthogonality theorems already proved above.  It does not identify the
configuration with any amplituhedral or twistor object.
-/
structure SplitOctonionFourPlaneConfiguration where
  oneLPlane : Submodule ℚ FourPlaneCarrier
  iPlane : Submodule ℚ FourPlaneCarrier
  jPlane : Submodule ℚ FourPlaneCarrier
  kPlane : Submodule ℚ FourPlaneCarrier
  oneLPlane_finrank : Module.finrank ℚ oneLPlane = 2
  iPlane_finrank : Module.finrank ℚ iPlane = 2
  jPlane_finrank : Module.finrank ℚ jPlane = 2
  kPlane_finrank : Module.finrank ℚ kPlane = 2
  oneLPlaneComponent_mem : ∀ x : FourPlaneCarrier, oneLPlaneComponent x ∈ oneLPlane
  iPlaneComponent_mem : ∀ x : FourPlaneCarrier, iPlaneComponent x ∈ iPlane
  jPlaneComponent_mem : ∀ x : FourPlaneCarrier, jPlaneComponent x ∈ jPlane
  kPlaneComponent_mem : ∀ x : FourPlaneCarrier, kPlaneComponent x ∈ kPlane
  reconstruction :
    ∀ x : FourPlaneCarrier,
      oneLPlaneComponent x + iPlaneComponent x +
        jPlaneComponent x + kPlaneComponent x = x
  orthogonal_oneL_i :
    ∀ x y : FourPlaneCarrier,
      splitInner (oneLPlaneComponent x) (iPlaneComponent y) = 0
  orthogonal_oneL_j :
    ∀ x y : FourPlaneCarrier,
      splitInner (oneLPlaneComponent x) (jPlaneComponent y) = 0
  orthogonal_oneL_k :
    ∀ x y : FourPlaneCarrier,
      splitInner (oneLPlaneComponent x) (kPlaneComponent y) = 0
  orthogonal_i_j :
    ∀ x y : FourPlaneCarrier,
      splitInner (iPlaneComponent x) (jPlaneComponent y) = 0
  orthogonal_i_k :
    ∀ x y : FourPlaneCarrier,
      splitInner (iPlaneComponent x) (kPlaneComponent y) = 0
  orthogonal_j_k :
    ∀ x y : FourPlaneCarrier,
      splitInner (jPlaneComponent x) (kPlaneComponent y) = 0

/-- The canonical property for the coordinate four-plane splitting. -/
def standardSplitOctonionFourPlaneConfiguration :
    SplitOctonionFourPlaneConfiguration where
  oneLPlane := oneLPlane
  iPlane := iPlane
  jPlane := jPlane
  kPlane := kPlane
  oneLPlane_finrank := oneLPlane_finrank
  iPlane_finrank := iPlane_finrank
  jPlane_finrank := jPlane_finrank
  kPlane_finrank := kPlane_finrank
  oneLPlaneComponent_mem := oneLPlaneComponent_mem
  iPlaneComponent_mem := iPlaneComponent_mem
  jPlaneComponent_mem := jPlaneComponent_mem
  kPlaneComponent_mem := kPlaneComponent_mem
  reconstruction := fourPlane_reconstruction
  orthogonal_oneL_i := oneLPlane_orthogonal_iPlane
  orthogonal_oneL_j := oneLPlane_orthogonal_jPlane
  orthogonal_oneL_k := oneLPlane_orthogonal_kPlane
  orthogonal_i_j := iPlane_orthogonal_jPlane
  orthogonal_i_k := iPlane_orthogonal_kPlane
  orthogonal_j_k := jPlane_orthogonal_kPlane

end

end InfoGeometry.Canonical
