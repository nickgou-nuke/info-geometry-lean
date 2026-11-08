/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
import InfoGeometry.Topology.KleinBottleCliffordGlide
import InfoGeometry.Clifford.Cl11CliffordMapIsometryBridge
import InfoGeometry.Clifford.Cl55WittOrthogonalReflections
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import Mathlib.RingTheory.Flat.Basic

/-!
# The split tangent plane mapped into the native `Cl(5,5)` carrier

The plane is mapped using one positive and one negative Witt coordinate, so
the restricted quadratic form is exactly the canonical `Cl(1,1)` form. The
Mathlib Clifford lift gives an algebra homomorphism into `Cl(5,5)`, and the
positive-coordinate reflection intertwines with the Klein glide convention
used by `KleinBottleExteriorOrientationBridge`. This is a one-way sector map;
it does not assert an algebra equivalence or a Pin-group witness.
-/

namespace InfoGeometry.Clifford.KleinGlideQ55ReflectionBridge

open InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
open InfoGeometry.Topology.KleinBottleCliffordGlide
open InfoGeometry.Topology.KleinBottleTangentHolonomy
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.CliffordTower
open scoped DirectSum

/-- The split tangent plane mapped to the first positive and negative Witt
coordinates of `V55`. -/
def vec11ToV55Linear : Vec11 →ₗ[ℝ] V55 where
  toFun v :=
    (fun i => if i = 0 then v.1 else 0,
      fun i => if i = 0 then v.2 else 0)
  map_add' u v := by
    apply Prod.ext
    · funext i
      by_cases h : i = 0 <;> simp [h]
    · funext i
      by_cases h : i = 0 <;> simp [h]
  map_smul' c v := by
    apply Prod.ext
    · funext i
      by_cases h : i = 0 <;> simp [h]
    · funext i
      by_cases h : i = 0 <;> simp [h]

/-- The covering-plane coordinates embedded into the selected split Witt
plane. -/
def planeToV55 (x : PlaneVector) : V55 :=
  vec11ToV55Linear (x 0, x 1)

@[simp] theorem Q55_vec11ToV55 (v : Vec11) :
    Q55 (vec11ToV55Linear v) = q11 v := by
  rcases v with ⟨x, y⟩
  simp [vec11ToV55Linear, Q55_apply, q11_apply]

/-- The selected positive and negative Witt coordinates recover the split
plane coordinates, so the linear map is injective. -/
theorem vec11ToV55Linear_injective : Function.Injective vec11ToV55Linear := by
  intro u v h
  rcases u with ⟨uPos, uNeg⟩
  rcases v with ⟨vPos, vNeg⟩
  have hPos := congrArg (fun w : V55 => w.1 0) h
  have hNeg := congrArg (fun w : V55 => w.2 0) h
  simp [vec11ToV55Linear] at hPos hNeg
  exact Prod.ext hPos hNeg

/-- The covering-plane coordinates are recovered from the selected Witt
coordinates, so `planeToV55` is injective. -/
theorem planeToV55_injective : Function.Injective planeToV55 := by
  intro x y h
  have hxy : (x 0, x 1) = (y 0, y 1) :=
    vec11ToV55Linear_injective h
  apply funext
  intro i
  fin_cases i
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

/-- The native `Cl(5,5)` generator restricted to the split tangent plane. -/
noncomputable def splitPlaneGenerator : Vec11 →ₗ[ℝ] Cl55 :=
  (CliffordAlgebra.ι Q55).comp vec11ToV55Linear

theorem splitPlaneGenerator_sq (v : Vec11) :
    splitPlaneGenerator v * splitPlaneGenerator v =
      algebraMap ℝ Cl55 (q11 v) := by
  change CliffordAlgebra.ι Q55 (vec11ToV55Linear v) *
      CliffordAlgebra.ι Q55 (vec11ToV55Linear v) = _
  rw [CliffordAlgebra.ι_sq_scalar, Q55_vec11ToV55]

/-- The native Clifford-algebra homomorphism selecting the split tangent
plane inside `Cl(5,5)`. -/
noncomputable def cl11Sector : CliffordAlgebra q11 →ₐ[ℝ] Cl55 :=
  CliffordAlgebra.lift q11 ⟨splitPlaneGenerator, splitPlaneGenerator_sq⟩

@[simp] theorem cl11Sector_ι (v : Vec11) :
    cl11Sector (CliffordAlgebra.ι q11 v) =
      CliffordAlgebra.ι Q55 (vec11ToV55Linear v) := by
  rw [cl11Sector, CliffordAlgebra.lift_ι_apply]
  rfl

/-- The selected Witt plane is the head `Cl(1,1)` factor in the existing
`Cl(5,5) ≃ Cl(1,1) ᵍ⊗ Cl(4,4)` decomposition. -/
theorem q55ToSplit5_vec11ToV55 (v : Vec11) :
    q55ToSplit5 (vec11ToV55Linear v) = headPair 4 v := by
  rcases v with ⟨x, y⟩
  have hv : vec11ToV55Linear (x, y) =
      x • cl55WittBasisFin 0 + y • cl55WittBasisFin 5 := by
    apply Prod.ext
    · funext i
      by_cases hi : i = 0 <;>
        simp [vec11ToV55Linear, cl55WittBasisFin, wittBasis,
          e_pos, f_neg, hi]
    · funext i
      by_cases hi : i = 0 <;>
        simp [vec11ToV55Linear, cl55WittBasisFin, wittBasis,
          e_pos, f_neg, hi]
  rw [hv, map_add, map_smul, map_smul,
    q55ToSplit5_wittBasis, q55ToSplit5_wittBasis,
    vec55SplitEquiv_basis0, vec55SplitEquiv_basis5]
  simp [headPair]

/-- The native `Cl(5,5)` comparison reads the selected sector map as the
graded head-factor inclusion. -/
theorem cl11Sector_tensor_readback :
    AlgHom.comp cl55ToCl11TensorCl44.toAlgHom cl11Sector =
      AlgHom.comp (GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit 4)))
        q11ToSplitClifford.toAlgHom := by
  apply CliffordAlgebra.hom_ext (Q := q11)
  apply LinearMap.ext
  intro v
  change cl55ToCl11TensorCl44
      (cl11Sector (CliffordAlgebra.ι q11 v)) =
    GradedTensorProduct.includeLeft
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (Qsplit 4))
      (q11ToSplitClifford (CliffordAlgebra.ι q11 v))
  rw [cl11Sector_ι]
  change splitCl55_headCl11TensorCl44Equiv
      (cl55ToSplitCl55
        (CliffordAlgebra.ι Q55 (vec11ToV55Linear v))) = _
  rw [cl55ToSplitCl55_map_ι, q55ToSplit5_vec11ToV55,
    splitCl55_headFactor, q11ToSplitClifford_ι]
  rfl

/-- The graded head-factor inclusion of the native `Cl(1,1)` algebra into
the `Cl(1,1) ᵍ⊗ Cl(4,4)` tensor stage is injective. -/
theorem cl11HeadTensor_injective :
    Function.Injective
      (GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit 4))) := by
  classical
  let A : Type := ⨁ i,
    CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 i
  let B : Type := ⨁ i, CliffordAlgebra.evenOdd (Qsplit 4) i
  have hB : Function.Injective (algebraMap ℝ B) := by
    intro r s h
    have h' := congrArg
      ((DirectSum.decomposeAlgEquiv
        (CliffordAlgebra.evenOdd (Qsplit 4))).symm) h
    have h'' :
        (algebraMap ℝ (CliffordAlgebra (Qsplit 4))) r =
          (algebraMap ℝ (CliffordAlgebra (Qsplit 4))) s := by
      simpa [B] using h'
    letI : Nontrivial (CliffordAlgebra (Qsplit 4)) :=
      (CliffordAlgebra.equivExterior (Qsplit 4)).symm.injective.nontrivial
    letI : Module.Free ℝ (CliffordAlgebra (Qsplit 4)) := by infer_instance
    exact (FaithfulSMul.algebraMap_injective ℝ
      (CliffordAlgebra (Qsplit 4))) h''
  letI : Module.Free ℝ A := by infer_instance
  have hTensor : Function.Injective
      (fun a : CliffordAlgebra InfoGeometry.CliffordTower.Q11 =>
        Algebra.TensorProduct.includeLeft (R := ℝ) (S := ℝ) (A := A) (B := B)
          ((DirectSum.decomposeAlgEquiv
            (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)) a)) := by
    exact Function.Injective.comp
      (Algebra.TensorProduct.includeLeft_injective
        (R := ℝ) (S := ℝ) (A := A) (B := B) hB)
      (DirectSum.decomposeAlgEquiv
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)).injective
  intro a b h
  apply hTensor
  simpa [A, B, GradedTensorProduct.includeLeft,
    GradedTensorProduct.auxEquiv_tmul] using
    congrArg
      (GradedTensorProduct.auxEquiv ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit 4))) h

/-- The `Cl(1,1)` algebra map into the native `Cl(5,5)` carrier is injective. -/
theorem cl11Sector_injective : Function.Injective cl11Sector := by
  intro a b h
  have ht := congrArg cl55ToCl11TensorCl44 h
  have ha := congrArg (fun f : CliffordAlgebra q11 →ₐ[ℝ]
      GradedTensorProduct ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit 4)) => f a) cl11Sector_tensor_readback
  have hb := congrArg (fun f : CliffordAlgebra q11 →ₐ[ℝ]
      GradedTensorProduct ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit 4)) => f b) cl11Sector_tensor_readback
  have hhead :
      GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
          (CliffordAlgebra.evenOdd (Qsplit 4))
          (q11ToSplitClifford a) =
        GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
          (CliffordAlgebra.evenOdd (Qsplit 4))
          (q11ToSplitClifford b) := by
    exact ha.symm.trans (ht.trans hb)
  exact q11ToSplitClifford.injective (cl11HeadTensor_injective hhead)

/-- The split-plane inclusion intertwines the first-coordinate reflection
with the corresponding positive Witt reflection. This is the
`KleinBottleExteriorOrientationBridge` convention `(-x,y)`; the actual
covering-glide derivative `(x,-y)` is handled by
`cl11Sector_coverGlide_equivariant` below. -/
theorem positiveReflection_vec11ToV55 (v : Vec11) :
    positiveReflection 0 (vec11ToV55Linear v) =
      vec11ToV55Linear (splitReflectionFirstCoordinate v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · funext i
    by_cases h : i = 0 <;> simp [vec11ToV55Linear,
      positiveReflection, splitReflectionFirstCoordinate, h]
  · funext i
    by_cases h : i = 0 <;> simp [vec11ToV55Linear,
      positiveReflection, splitReflectionFirstCoordinate, h]

/-- The first negative Witt reflection restricts to the canonical
`Cl(1,1)` reflection `(x,y) ↦ (x,-y)`, which is the derivative of the
affine glide on the covering plane. -/
theorem negativeReflection_vec11ToV55 (v : Vec11) :
    negativeReflection 0 (vec11ToV55Linear v) =
      vec11ToV55Linear (splitReflection v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · funext i
    by_cases h : i = 0 <;>
      simp [negativeReflection, vec11ToV55Linear, splitReflection, h]
  · funext i
    by_cases h : i = 0 <;>
      simp [negativeReflection, vec11ToV55Linear, splitReflection, h]

/-- The ambient negative Witt reflection restricts to the actual derivative
of `KleinBrillouinBase.glide`, using the already-proved equality between the
canonical `Cl(1,1)` reflection and that derivative. -/
theorem negativeReflection_vec11ToV55_glideDerivative (v : Vec11) :
    negativeReflection 0 (vec11ToV55Linear v) =
      vec11ToV55Linear (glideLinearPart v) := by
  rw [negativeReflection_vec11ToV55, splitReflection_eq_glideLinearPart]

/-- On each embedded Clifford generator, the ambient negative reflection
acts by the actual derivative of the affine Klein glide. -/
theorem negativeReflectionAlg_glideGenerator (v : Vec11) :
    negativeReflectionAlg 0
        (cl11Sector (CliffordAlgebra.ι q11 v)) =
      CliffordAlgebra.ι Q55 (vec11ToV55Linear (glideLinearPart v)) := by
  rw [cl11Sector_ι, negativeReflectionAlg_apply_ι,
    negativeReflection_vec11ToV55_glideDerivative]

/-- The coordinate-swapped exterior-orientation convention for the Klein
linear map is the restriction of the native positive Witt reflection. This
is distinct from the actual covering-glide derivative, which is the
negative-Witt-reflection case above. -/
theorem positiveReflection_planeToV55 (x : PlaneVector) :
    positiveReflection 0 (planeToV55 x) = planeToV55 (glideLinear x) := by
  have hx : x = x 0 • firstAxis + x 1 • secondAxis := by
    ext i
    fin_cases i <;> simp [firstAxis, secondAxis]
  have hglide : glideLinear x = fun i => if i = 0 then -x 0 else x 1 := by
    rw [hx]
    simp only [map_add, map_smul, glideLinear_firstAxis,
      glideLinear_secondAxis]
    ext i
    fin_cases i <;> simp [firstAxis, secondAxis]
  rw [hglide]
  change positiveReflection 0 (vec11ToV55Linear (x 0, x 1)) =
    vec11ToV55Linear (-x 0, x 1)
  rw [positiveReflection_vec11ToV55]
  apply congrArg vec11ToV55Linear
  apply Prod.ext
  · simp [splitReflectionFirstCoordinate]
  · rfl

/-- On the tangent plane, the `Cl(5,5)` quadratic form restricts to the
canonical split `Cl(1,1)` quadratic form. -/
theorem Q55_planeToV55 (x : PlaneVector) :
    Q55 (planeToV55 x) = q11 (x 0, x 1) :=
  Q55_vec11ToV55 (x 0, x 1)

/-- The native `Cl(5,5)` automorphism acts on tangent-plane Clifford
generators by the exterior-orientation convention `(-x,y)`. The differential
of the affine covering glide is `(x,-y)` and is proved separately below. -/
theorem positiveReflectionAlg_generator_plane (x : PlaneVector) :
    positiveReflectionAlg 0 (CliffordAlgebra.ι Q55 (planeToV55 x)) =
      CliffordAlgebra.ι Q55 (planeToV55 (glideLinear x)) := by
  rw [positiveReflectionAlg_apply_ι, positiveReflection_planeToV55]

/-- The split Clifford-sector homomorphism intertwines the two native
Clifford automorphisms on every algebra element for the
`KleinBottleExteriorOrientationBridge` coordinate convention. For the actual
covering-glide derivative, use `cl11Sector_coverGlide_equivariant`. -/
theorem cl11Sector_glide_equivariant (a : CliffordAlgebra q11) :
    cl11Sector (splitReflectionFirstCoordinateCliffordAuto a) =
      positiveReflectionAlg 0 (cl11Sector a) := by
  let lhs : CliffordAlgebra q11 →ₐ[ℝ] Cl55 :=
    cl11Sector.comp
      (splitReflectionFirstCoordinateCliffordAuto :
        CliffordAlgebra q11 →ₐ[ℝ] CliffordAlgebra q11)
  let rhs : CliffordAlgebra q11 →ₐ[ℝ] Cl55 :=
    (positiveReflectionAlg 0 : Cl55 →ₐ[ℝ] Cl55).comp cl11Sector
  have h : lhs = rhs := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change cl11Sector
        (splitReflectionFirstCoordinateCliffordAuto
          (CliffordAlgebra.ι q11 v)) =
      positiveReflectionAlg 0 (cl11Sector (CliffordAlgebra.ι q11 v))
    simp only [splitReflectionFirstCoordinateCliffordAuto_ι,
      cl11Sector_ι, positiveReflectionAlg_apply_ι,
      positiveReflection_vec11ToV55]
  exact DFunLike.congr_fun h a

/-- The split Clifford-sector map intertwines the actual covering-glide
derivative with the first negative Witt reflection on the ambient `Cl(5,5)`
algebra. The affine translation remains a base action and is not included in
this fibre-algebra statement. -/
theorem cl11Sector_coverGlide_equivariant (a : CliffordAlgebra q11) :
    cl11Sector (splitReflectionCliffordAuto a) =
      negativeReflectionAlg 0 (cl11Sector a) := by
  let lhs : CliffordAlgebra q11 →ₐ[ℝ] Cl55 :=
    cl11Sector.comp
      (splitReflectionCliffordAuto :
        CliffordAlgebra q11 →ₐ[ℝ] CliffordAlgebra q11)
  let rhs : CliffordAlgebra q11 →ₐ[ℝ] Cl55 :=
    (negativeReflectionAlg 0 : Cl55 →ₐ[ℝ] Cl55).comp cl11Sector
  have h : lhs = rhs := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change cl11Sector
        (splitReflectionCliffordAuto (CliffordAlgebra.ι q11 v)) =
      negativeReflectionAlg 0 (cl11Sector (CliffordAlgebra.ι q11 v))
    rw [splitReflectionCliffordAuto_ι, cl11Sector_ι,
      splitReflection_eq_glideLinearPart]
    exact (negativeReflectionAlg_glideGenerator v).symm
  exact DFunLike.congr_fun h a

/-- The ambient Clifford-algebra action of the actual glide differential is
involutive. This lifts the already-proved vector reflection law to the whole
Clifford carrier by generator extensionality. -/
theorem negativeReflectionAlg_involutive (a : Cl55) :
    negativeReflectionAlg 0 (negativeReflectionAlg 0 a) = a := by
  have h :
      (negativeReflectionAlg 0 : Cl55 ≃ₐ[ℝ] Cl55).toAlgHom.comp
          (negativeReflectionAlg 0 : Cl55 ≃ₐ[ℝ] Cl55).toAlgHom =
        AlgHom.id ℝ Cl55 := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change negativeReflectionAlg 0
        (negativeReflectionAlg 0 (CliffordAlgebra.ι Q55 v)) = _
    simp [negativeReflectionAlg_apply_ι, negativeReflection_involutive]
  exact DFunLike.congr_fun h a

/-- The actual covering-glide differential induces an involution on the
`Cl(1,1)` sector, not merely an intertwining map into `Cl(5,5)`. -/
theorem splitReflectionCliffordAuto_involutive (a : CliffordAlgebra q11) :
    splitReflectionCliffordAuto (splitReflectionCliffordAuto a) = a := by
  apply cl11Sector_injective
  calc
    cl11Sector (splitReflectionCliffordAuto (splitReflectionCliffordAuto a)) =
        negativeReflectionAlg 0
          (cl11Sector (splitReflectionCliffordAuto a)) :=
      cl11Sector_coverGlide_equivariant _
    _ = negativeReflectionAlg 0 (negativeReflectionAlg 0 (cl11Sector a)) := by
      rw [cl11Sector_coverGlide_equivariant]
    _ = cl11Sector a := negativeReflectionAlg_involutive _

end InfoGeometry.Clifford.KleinGlideQ55ReflectionBridge
