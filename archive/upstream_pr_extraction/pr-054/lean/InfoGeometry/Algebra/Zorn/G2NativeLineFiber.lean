import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
import InfoGeometry.Algebra.Zorn.G2NativeBaseFiber

/-!
# Native three-line fiber through the common isotropic PC-fixed point

The annihilator of the native point `nativeBasePoint` contains six additional
nonzero vectors.  Pairing a vector `y` with `nativeBasePoint + y` gives the
three two-dimensional subspaces through the point.  This owner records that
fiber directly from native split-Zorn multiplication; it does not identify it
with the exported finite incidence certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiber

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

def kernelCandidate (y : OctImF2) : Prop :=
  y ≠ 0 ∧ y ≠ nativeBasePoint ∧
    mul (embed nativeBasePoint) (embed y) = zero

instance : DecidablePred kernelCandidate := by
  intro y
  unfold kernelCandidate
  infer_instance

def candidates : Finset OctImF2 :=
  Finset.univ.filter kernelCandidate

def lineSet (y : OctImF2) : Finset OctImF2 :=
  {nativeBasePoint, y, nativeBasePoint + y}

def nativeLines : Finset (Finset OctImF2) :=
  candidates.image lineSet

theorem octImAction_add (g : SplitOctF2Aut) (x y : OctImF2) :
    octImAction g (x + y) = octImAction g x + octImAction g y := by
  let A : Imaginary := octImToImaginary x
  let B : Imaginary := octImToImaginary y
  have hxy : InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.imaginaryAdd A B =
      octImToImaginary (x + y) := by
    apply imaginaryOctImEquiv.injective
    change imaginaryToOctIm
        (InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.imaginaryAdd A B) =
      imaginaryToOctIm (octImToImaginary (x + y))
    calc
      imaginaryToOctIm
          (InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.imaginaryAdd A B) =
          imaginaryToOctIm A + imaginaryToOctIm B :=
        InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.imaginaryToOctIm_imaginaryAdd A B
      _ = x + y := by
        have hx : imaginaryToOctIm (octImToImaginary x) = x :=
          imaginaryOctImEquiv.right_inv x
        have hy : imaginaryToOctIm (octImToImaginary y) = y :=
          imaginaryOctImEquiv.right_inv y
        simpa [A, B] using congrArg₂ (· + ·) hx hy
      _ = imaginaryToOctIm (octImToImaginary (x + y)) := by
        symm
        exact imaginaryOctImEquiv.right_inv (x + y)
  unfold octImAction
  rw [← hxy]
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary g
        (InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.imaginaryAdd A B)) = _
  rw [InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.actImaginary_imaginaryAdd]
  rw [InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.imaginaryToOctIm_imaginaryAdd]
  rfl

theorem lineSet_action (g : SplitOctF2Aut) (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : OctImF2) :
    lineSet (octImAction g y) = (lineSet y).image (octImAction g) := by
  simp only [lineSet, Finset.image_insert, Finset.image_singleton]
  rw [hg, octImAction_add]
  simp [hg]

theorem octImAction_zero (g : SplitOctF2Aut) : octImAction g 0 = 0 := by
  unfold octImAction
  have hzero : G2ImaginaryIsotropicPoints.actImaginary g (octImToImaginary 0) =
      (zeroImaginary : Imaginary) := by
    apply Subtype.ext
    change g⁻¹.1 (octImToImaginary 0).1 = (zeroImaginary : Imaginary).1
    change (g⁻¹ : SplitOctF2Aut).1 zero = zero
    exact InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.automorphism_map_zero g⁻¹
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary g (octImToImaginary 0)) = 0
  rw [hzero]
  exact imaginaryOctImEquiv.right_inv 0

theorem octImAction_one (v : OctImF2) : octImAction 1 v = v := by
  unfold octImAction
  rw [one_smul]
  exact imaginaryOctImEquiv.right_inv v

theorem octImAction_injective (g : SplitOctF2Aut) :
    Function.Injective (octImAction g) := by
  intro x y hxy
  have h := congrArg (octImAction g⁻¹) hxy
  rw [← octImAction_mul, ← octImAction_mul, inv_mul_cancel,
    octImAction_one, octImAction_one] at h
  exact h

theorem kernelCandidate_action (i : Fin 6) (y : OctImF2) (hy : y ∈ candidates) :
    octImAction (pcGenerator i) y ∈ candidates := by
  rcases Finset.mem_filter.mp hy with ⟨hy_univ, hy_ne_zero, hy_ne_base, hy_mul⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro hzero
    apply hy_ne_zero
    apply octImAction_injective (pcGenerator i)
    rw [hzero, octImAction_zero]
  · intro hbase
    apply hy_ne_base
    apply octImAction_injective (pcGenerator i)
    calc
      octImAction (pcGenerator i) y = nativeBasePoint := hbase
      _ = octImAction (pcGenerator i) nativeBasePoint :=
        (pcGenerator_fix i).symm
  · simpa [pcGenerator_fix i] using
      (native_multiplication_zero_iff (pcGenerator i) nativeBasePoint y).mpr hy_mul

theorem kernelCandidate_action_of_fix
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : OctImF2) (hy : y ∈ candidates) :
    octImAction g y ∈ candidates := by
  rcases Finset.mem_filter.mp hy with ⟨hy_univ, hy_ne_zero, hy_ne_base, hy_mul⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro hzero
    apply hy_ne_zero
    apply octImAction_injective g
    rw [hzero, octImAction_zero]
  · intro hbase
    apply hy_ne_base
    apply octImAction_injective g
    calc
      octImAction g y = nativeBasePoint := hbase
      _ = octImAction g nativeBasePoint := hg.symm
  · simpa [hg] using
      (native_multiplication_zero_iff g nativeBasePoint y).mpr hy_mul

theorem lineSet_action_mem_nativeLines (i : Fin 6) (y : OctImF2) (hy : y ∈ candidates) :
    (lineSet y).image (octImAction (pcGenerator i)) ∈ nativeLines := by
  rw [← lineSet_action (pcGenerator i) (pcGenerator_fix i) y]
  exact Finset.mem_image.mpr ⟨octImAction (pcGenerator i) y,
    kernelCandidate_action i y hy, rfl⟩

theorem lineSet_action_mem_nativeLines_of_fix
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : OctImF2) (hy : y ∈ candidates) :
    (lineSet y).image (octImAction g) ∈ nativeLines := by
  rw [← lineSet_action g hg y]
  exact Finset.mem_image.mpr ⟨octImAction g y,
    kernelCandidate_action_of_fix g hg y hy, rfl⟩

theorem nativeBasePoint_fix_inv
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    octImAction g⁻¹ nativeBasePoint = nativeBasePoint := by
  calc
    octImAction g⁻¹ nativeBasePoint =
        octImAction g⁻¹ (octImAction g nativeBasePoint) := by rw [hg]
    _ = nativeBasePoint := by
      rw [← octImAction_mul, inv_mul_cancel, octImAction_one]

def nativeLinesEquivOfFix
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    {L // L ∈ nativeLines} ≃ {L // L ∈ nativeLines} where
  toFun L := ⟨L.1.image (octImAction g), by
    rcases Finset.mem_image.mp L.2 with ⟨y, hy, hLy⟩
    rw [← hLy]
    exact lineSet_action_mem_nativeLines_of_fix g hg y hy⟩
  invFun L := ⟨L.1.image (octImAction g⁻¹), by
    have hginv := nativeBasePoint_fix_inv g hg
    rcases Finset.mem_image.mp L.2 with ⟨y, hy, hLy⟩
    rw [← hLy]
    exact lineSet_action_mem_nativeLines_of_fix g⁻¹ hginv y hy⟩
  left_inv L := by
    apply Subtype.ext
    change Finset.image (octImAction g⁻¹)
        (Finset.image (octImAction g) L.1) = L.1
    rw [Finset.image_image]
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
      have hwx' : w = x := by
        simpa [← octImAction_mul, inv_mul_cancel,
          octImAction_one] using hwx
      simpa [hwx'] using hw
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, by
        simp [Function.comp_def, ← octImAction_mul, inv_mul_cancel,
          octImAction_one]⟩
  right_inv L := by
    apply Subtype.ext
    change Finset.image (octImAction g)
        (Finset.image (octImAction g⁻¹) L.1) = L.1
    rw [Finset.image_image]
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
      have hwx' : w = x := by
        simpa [← octImAction_mul, mul_inv_cancel,
          octImAction_one] using hwx
      simpa [hwx'] using hw
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, by
        simp [Function.comp_def, ← octImAction_mul, mul_inv_cancel,
          octImAction_one]⟩

theorem candidates_card : candidates.card = 6 := by
  native_decide

theorem nativeLines_card : nativeLines.card = 3 := by
  native_decide

theorem lineSet_card (y : OctImF2) (hy : y ∈ candidates) :
    (lineSet y).card = 3 := by
  native_decide +revert

theorem lineSet_mem_nativeLines (y : OctImF2) (hy : y ∈ candidates) :
    lineSet y ∈ nativeLines := by
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

theorem nativeBasePoint_mem_lineSet (y : OctImF2) :
    nativeBasePoint ∈ lineSet y := by
  simp [lineSet]

/-! The canonical Borel-fixed line is the root line generated by the
third native coordinate.  It is written explicitly, rather than selected
from the finite pencil, so its carrier alignment is transparent. -/

def baseLineVector : OctImF2 := fun i => if i = 3 then 1 else 0

theorem baseLineVector_mem_candidates : baseLineVector ∈ candidates := by
  native_decide +revert

def nativeBaseLineWitness : Finset OctImF2 := lineSet baseLineVector

theorem nativeBaseLineWitness_mem_nativeLines :
    nativeBaseLineWitness ∈ nativeLines := by
  exact Finset.mem_image.mpr ⟨baseLineVector, baseLineVector_mem_candidates, rfl⟩

theorem pc1_fixes_nativeBaseLineWitness :
    nativeBaseLineWitness.image (octImAction (pcGenerator 0)) = nativeBaseLineWitness := by
  native_decide +revert

theorem pc2_fixes_nativeBaseLineWitness :
    nativeBaseLineWitness.image (octImAction (pcGenerator 1)) = nativeBaseLineWitness := by
  native_decide +revert

theorem pc3_fixes_nativeBaseLineWitness :
    nativeBaseLineWitness.image (octImAction (pcGenerator 2)) = nativeBaseLineWitness := by
  native_decide +revert

theorem pc4_fixes_nativeBaseLineWitness :
    nativeBaseLineWitness.image (octImAction (pcGenerator 3)) = nativeBaseLineWitness := by
  native_decide +revert

theorem pc5_fixes_nativeBaseLineWitness :
    nativeBaseLineWitness.image (octImAction (pcGenerator 4)) = nativeBaseLineWitness := by
  native_decide +revert

theorem pc6_fixes_nativeBaseLineWitness :
    nativeBaseLineWitness.image (octImAction (pcGenerator 5)) = nativeBaseLineWitness := by
  native_decide +revert

theorem prod_fixes_nativeBaseLineWitness (L : List SplitOctF2Aut)
    (hL : ∀ g ∈ L,
      octImAction g nativeBasePoint = nativeBasePoint ∧
      nativeBaseLineWitness.image (octImAction g) = nativeBaseLineWitness) :
    nativeBaseLineWitness.image (octImAction L.prod) = nativeBaseLineWitness := by
  induction L with
  | nil =>
      simp only [List.prod_nil]
      have hone : octImAction (1 : SplitOctF2Aut) = id := by
        funext x
        exact octImAction_one x
      rw [hone]
      simp
  | cons g gs ih =>
      rw [List.prod_cons]
      have hg := hL g (List.mem_cons_self)
      have hgs : ∀ x ∈ gs,
          octImAction x nativeBasePoint = nativeBasePoint ∧
          nativeBaseLineWitness.image (octImAction x) = nativeBaseLineWitness := by
        intro x hx
        exact hL x (List.mem_cons_of_mem g hx)
      have htail := ih hgs
      have hcomp : octImAction (g * gs.prod) =
          octImAction g ∘ octImAction gs.prod := by
        funext x
        exact octImAction_mul g gs.prod x
      rw [hcomp, ← Finset.image_image, htail]
      exact hg.2

theorem pcWord_fixes_nativeBaseLineWitness (e : Fin 6 → Bool) :
    nativeBaseLineWitness.image
        (octImAction (G2TwoSylowPCAutomorphisms.pcWord e)) =
      nativeBaseLineWitness := by
  unfold G2TwoSylowPCAutomorphisms.pcWord
  apply prod_fixes_nativeBaseLineWitness
  intro g hg
  rw [List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  by_cases h : e i
  · simp only [h, ↓reduceIte]
    fin_cases i
    · exact ⟨pcGenerator_fix 0, pc1_fixes_nativeBaseLineWitness⟩
    · exact ⟨pcGenerator_fix 1, pc2_fixes_nativeBaseLineWitness⟩
    · exact ⟨pcGenerator_fix 2, pc3_fixes_nativeBaseLineWitness⟩
    · exact ⟨pcGenerator_fix 3, pc4_fixes_nativeBaseLineWitness⟩
    · exact ⟨pcGenerator_fix 4, pc5_fixes_nativeBaseLineWitness⟩
    · exact ⟨pcGenerator_fix 5, pc6_fixes_nativeBaseLineWitness⟩
  · simp only [h]
    exact ⟨by simp [octImAction_one], by
      have hone : octImAction (1 : SplitOctF2Aut) = id := by
        funext x
        exact octImAction_one x
      change Finset.image (octImAction (1 : SplitOctF2Aut))
        nativeBaseLineWitness = nativeBaseLineWitness
      rw [hone]
      simp⟩

/- The native PC word fixes the selected point and the selected line fibre
   simultaneously.  This is the honest generator-level flag statement; it
   does not identify the native fibre with the exported 63-line certificate. -/
theorem pcWord_fixes_native_base_flag (e : Fin 6 → Bool) :
    octImAction (G2TwoSylowPCAutomorphisms.pcWord e) nativeBasePoint =
        nativeBasePoint ∧
      nativeBaseLineWitness.image
          (octImAction (G2TwoSylowPCAutomorphisms.pcWord e)) =
        nativeBaseLineWitness := by
  exact ⟨pcWord_fix e, pcWord_fixes_nativeBaseLineWitness e⟩

theorem unipotentSubgroup_fixes_native_base_flag
    (u : SplitOctF2Aut) (hu :
      u ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) :
    octImAction u nativeBasePoint = nativeBasePoint ∧
      nativeBaseLineWitness.image (octImAction u) = nativeBaseLineWitness := by
  change u ∈ Set.range G2TwoSylowSubgroup.pcWord at hu
  obtain ⟨e, rfl⟩ := hu
  exact pcWord_fixes_native_base_flag e

end InfoGeometry.Algebra.Zorn.G2NativeLineFiber
