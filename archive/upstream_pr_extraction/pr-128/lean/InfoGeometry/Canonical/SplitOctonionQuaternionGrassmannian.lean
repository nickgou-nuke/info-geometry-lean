import InfoGeometry.Canonical.SplitOctonionColorCycleMultiplicativity
import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace InfoGeometry.Canonical

/-!
# Algebraic Grassmannian of split-quaternion subspaces

This file records the theorem-safe part of the proposed octonion
Grassmannian.  A point is a rational submodule containing the unit, closed
under the already defined split-octonion product, and of dimension four.
No homogeneous-space identification is asserted here.
-/

def rationalOctonionOne : StandardRationalSplitOctonion :=
  Pi.single IntegralSplitBasis.one (1 : ℚ)

/-- The predicate defining a four-dimensional split-quaternion subspace. -/
structure IsSplitQuaternionSubalgebra
    (W : Submodule ℚ StandardRationalSplitOctonion) : Prop where
  one_mem : rationalOctonionOne ∈ W
  mul_mem : ∀ {x y : StandardRationalSplitOctonion}, x ∈ W → y ∈ W →
    splitOctonionMulQ x y ∈ W
  finrank_eq_four : Module.finrank ℚ W = 4

/-- The commutator in the native rational split-octonion carrier. -/
def splitQuaternionCommutator
    (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion :=
  splitOctonionMulQ x y - splitOctonionMulQ y x

theorem splitQuaternionCommutator_mem
    {W : Submodule ℚ StandardRationalSplitOctonion}
    (hW : IsSplitQuaternionSubalgebra W)
    {x y : StandardRationalSplitOctonion}
    (hx : x ∈ W) (hy : y ∈ W) :
    splitQuaternionCommutator x y ∈ W := by
  unfold splitQuaternionCommutator
  exact W.sub_mem (hW.mul_mem hx hy) (hW.mul_mem hy hx)

/-- The algebraic Grassmannian is a subtype of such submodules. -/
abbrev SplitQuaternionGrassmannian :=
  {W : Submodule ℚ StandardRationalSplitOctonion // IsSplitQuaternionSubalgebra W}

theorem rationalOctonionOne_eq_algAut_one
    (g : SplitRationalOctonionAlgAut) :
    g.toLinearEquiv rationalOctonionOne = rationalOctonionOne :=
  g.map_one'

/-- Transport of a subspace by an algebra automorphism. -/
noncomputable def mapSplitQuaternionSubalgebra
    (g : SplitRationalOctonionAlgAut)
    (W : SplitQuaternionGrassmannian) : SplitQuaternionGrassmannian := by
  let carrier : Submodule ℚ StandardRationalSplitOctonion :=
    W.1.map g.toLinearEquiv.toLinearMap
  have hone : rationalOctonionOne ∈ carrier := by
    rw [Submodule.mem_map]
    refine ⟨rationalOctonionOne, W.2.one_mem, ?_⟩
    exact g.map_one'
  have hmul : ∀ {x y : StandardRationalSplitOctonion}, x ∈ carrier → y ∈ carrier →
      splitOctonionMulQ x y ∈ carrier := by
    intro x y hx hy
    rcases (Submodule.mem_map.mp hx) with ⟨x₀, hx₀, rfl⟩
    rcases (Submodule.mem_map.mp hy) with ⟨y₀, hy₀, rfl⟩
    refine ⟨splitOctonionMulQ x₀ y₀, W.2.mul_mem hx₀ hy₀, ?_⟩
    exact g.map_mul' x₀ y₀
  have hfin : Module.finrank ℚ carrier = 4 := by
    have e := Submodule.equivMapOfInjective
      g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective W.1
    exact e.finrank_eq.symm.trans W.2.finrank_eq_four
  exact ⟨carrier, ⟨hone, hmul, hfin⟩⟩

theorem mapSplitQuaternionSubalgebra_one_mem
    (g : SplitRationalOctonionAlgAut)
    (W : SplitQuaternionGrassmannian) :
    rationalOctonionOne ∈ (mapSplitQuaternionSubalgebra g W).1 :=
  (mapSplitQuaternionSubalgebra g W).2.one_mem

theorem mapSplitQuaternionSubalgebra_mul_mem
    (g : SplitRationalOctonionAlgAut)
    (W : SplitQuaternionGrassmannian)
    {x y : StandardRationalSplitOctonion}
    (hx : x ∈ (mapSplitQuaternionSubalgebra g W).1)
    (hy : y ∈ (mapSplitQuaternionSubalgebra g W).1) :
    splitOctonionMulQ x y ∈ (mapSplitQuaternionSubalgebra g W).1 :=
  (mapSplitQuaternionSubalgebra g W).2.mul_mem hx hy

theorem mapSplitQuaternionSubalgebra_finrank
    (g : SplitRationalOctonionAlgAut)
    (W : SplitQuaternionGrassmannian) :
    Module.finrank ℚ (mapSplitQuaternionSubalgebra g W).1 = 4 :=
  (mapSplitQuaternionSubalgebra g W).2.finrank_eq_four

/-!
## The intrinsic imaginary three-plane

For a unital four-dimensional subalgebra, restrict the existing scalar
projection to the subalgebra.  Its image is all of `ℚ`, because the unit is in
the carrier.  Rank--nullity therefore gives a canonical three-dimensional
kernel.  This is the finite algebraic shadow of the imaginary part of a
quaternion slice; no homogeneous-space or Lie-group identification is used.
-/

noncomputable def scalarPartOnSubalgebra
    (W : SplitQuaternionGrassmannian) : W.1 →ₗ[ℚ] ℚ :=
  scalarPart.comp W.1.subtype

noncomputable def imaginaryKernel
    (W : SplitQuaternionGrassmannian) : Submodule ℚ W.1 :=
  LinearMap.ker (scalarPartOnSubalgebra W)

theorem scalarPartOnSubalgebra_surjective
    (W : SplitQuaternionGrassmannian) :
    Function.Surjective (scalarPartOnSubalgebra W) := by
  intro q
  refine ⟨⟨q • rationalOctonionOne, W.1.smul_mem q W.2.one_mem⟩, ?_⟩
  simp [scalarPartOnSubalgebra, rationalOctonionOne, scalarPart]

theorem imaginaryKernel_finrank
    (W : SplitQuaternionGrassmannian) :
    Module.finrank ℚ (imaginaryKernel W) = 3 := by
  let f := scalarPartOnSubalgebra W
  have htop : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact scalarPartOnSubalgebra_surjective W
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop] at h
  have htopfin : Module.finrank ℚ (⊤ : Submodule ℚ ℚ) = 1 := by
    simp
  rw [htopfin, W.2.finrank_eq_four] at h
  change Module.finrank ℚ f.ker = 3
  omega

/-- Embed the scalar-zero kernel into the existing imaginary carrier. -/
noncomputable def imaginaryKernelToImaginary
    (W : SplitQuaternionGrassmannian) :
    imaginaryKernel W →ₗ[ℚ] imaginarySplitOctonion where
  toFun x := ⟨x.1.1, by
    change scalarPart x.1.1 = 0
    exact x.2⟩
  map_add' x y := by rfl
  map_smul' c x := by rfl

/-- The intrinsic three-plane associated with a split-quaternion slice. -/
noncomputable def imaginaryAssociativePlane
    (W : SplitQuaternionGrassmannian) :
    Submodule ℚ imaginarySplitOctonion :=
  Submodule.map (imaginaryKernelToImaginary W) ⊤

theorem imaginaryKernelToImaginary_injective
    (W : SplitQuaternionGrassmannian) :
    Function.Injective (imaginaryKernelToImaginary W) := by
  intro x y h
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      simp [imaginaryKernelToImaginary] at h
      cases h
      rfl

theorem imaginaryAssociativePlane_finrank
    (W : SplitQuaternionGrassmannian) :
    Module.finrank ℚ (imaginaryAssociativePlane W) = 3 := by
  have e := Submodule.equivMapOfInjective
    (imaginaryKernelToImaginary W)
    (imaginaryKernelToImaginary_injective W)
    (⊤ : Submodule ℚ (imaginaryKernel W))
  change Module.finrank ℚ (Submodule.map (imaginaryKernelToImaginary W) ⊤) = 3
  rw [← e.finrank_eq]
  simp only [finrank_top]
  exact imaginaryKernel_finrank W

/-!
The plane is intrinsically imaginary: its elements are the images of the
scalar-zero kernel, rather than an independently chosen three-dimensional
subspace.  This is the native replacement for the informal assertion that
the imaginary part of a unital quaternion slice is its scalar-zero part.
-/

theorem imaginaryAssociativePlane_mem_scalar_zero
    (W : SplitQuaternionGrassmannian)
    {x : imaginarySplitOctonion}
    (hx : x ∈ imaginaryAssociativePlane W) :
    scalarPart x.1 = 0 := by
  rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
  change scalarPartOnSubalgebra W y.1 = 0
  have hy' : scalarPartOnSubalgebra W y.1 = 0 := y.2
  simpa [scalarPartOnSubalgebra] using hy'

/-- The canonical 3-form restricted to the intrinsic associative plane. -/
noncomputable def volumeForm
    (W : SplitQuaternionGrassmannian) :
    imaginaryAssociativePlane W →
      imaginaryAssociativePlane W →
      imaginaryAssociativePlane W → ℚ :=
  fun x y z =>
    canonicalSplitG2ThreeFormValue (x : imaginarySplitOctonion)
      (y : imaginarySplitOctonion) (z : imaginarySplitOctonion)

theorem volumeForm_restriction
    (W : SplitQuaternionGrassmannian)
    (x y z : imaginaryAssociativePlane W) :
    volumeForm W x y z =
      canonicalSplitG2ThreeFormValue
        (x : imaginarySplitOctonion)
        (y : imaginarySplitOctonion)
        (z : imaginarySplitOctonion) := by
  rfl

theorem colorCycle_maps_splitQuaternionGrassmannian
    (W : SplitQuaternionGrassmannian) :
    IsSplitQuaternionSubalgebra
      (mapSplitQuaternionSubalgebra colorCycleAlgAut W).1 :=
  (mapSplitQuaternionSubalgebra colorCycleAlgAut W).2

end InfoGeometry.Canonical
