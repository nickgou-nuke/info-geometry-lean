import InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport

/-!
# Native action map on the full flag carrier

This owner packages the already proved point action and native line-fibre
transport.  It deliberately exposes only the carrier map: the group-action
composition law is a separate theorem and is not assumed here.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def nativeFlagMap
    (g : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut)
    (F : NativeFlag) : NativeFlag :=
  let p' := octImPointPerm g F.1
  have hp : p'.1 = octImAction g F.1.1 := by
    rfl
  ⟨p', cast (congrArg NativeLinesThroughPoint hp.symm)
    (nativeLineFiberMap g F.1.1 F.2)⟩

theorem nativePointPerm_val_eq_action
    (g : SplitOctF2Aut)
    (p : InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint) :
    (octImPointPerm g p).1 = octImAction g p.1 :=
  rfl

theorem nativeFlagMap_fst
    (g : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut)
    (F : NativeFlag) :
    (nativeFlagMap g F).1 = octImPointPerm g F.1 :=
  by simp [nativeFlagMap]

theorem nativeFlagMap_snd
    (g : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut)
    (F : NativeFlag) :
    (nativeFlagMap g F).2 =
      cast (congrArg NativeLinesThroughPoint
        (show (octImPointPerm g F.1).1 = octImAction g F.1.1 by rfl).symm)
        (nativeLineFiberMap g F.1.1 F.2) :=
  by simp [nativeFlagMap]

theorem nativeLineFiberMap_apply_val
    (g : SplitOctF2Aut)
    (x : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2)
    (L : G2NativeBaseFiber.NativeLinesThroughPoint x) :
    (nativeLineFiberMap g x L).1 = L.1.image (octImAction g) := by
  rfl

theorem nativeLineFiberMap_apply_val_mul
    (g h : SplitOctF2Aut)
    (x : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2)
    (L : G2NativeBaseFiber.NativeLinesThroughPoint x) :
    (nativeLineFiberMap (g * h) x L).1 =
      ((nativeLineFiberMap h x L).1).image (octImAction g) := by
  rw [nativeLineFiberMap_apply_val, nativeLineFiberMap_apply_val]
  rw [Finset.image_image]
  simp [Function.comp_def, ← octImAction_mul]

theorem nativeRawLine_transport_val
    {x y : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2}
    (hxy : x = y)
    (L : NativeLinesThroughPoint x) :
    (cast (congrArg NativeLinesThroughPoint hxy) L).1 = L.1 := by
  cases hxy
  rfl

theorem nativeLineFiberMap_mul
    (g h : SplitOctF2Aut)
    (x : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2)
    (L : G2NativeBaseFiber.NativeLinesThroughPoint x) :
    nativeLineFiberMap (g * h) x L =
      cast (congrArg NativeLinesThroughPoint (octImAction_mul g h x).symm)
        (nativeLineFiberMap g (octImAction h x) (nativeLineFiberMap h x L)) := by
  apply Subtype.ext
  rw [nativeRawLine_transport_val (octImAction_mul g h x).symm]
  exact nativeLineFiberMap_apply_val_mul g h x L

theorem nativeLineFiberMap_one_apply_val
    (x : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2)
    (L : NativeLinesThroughPoint x) :
    (nativeLineFiberMap (1 : SplitOctF2Aut) x L).1 = L.1 := by
  rw [nativeLineFiberMap_apply_val]
  have haction : octImAction (1 : SplitOctF2Aut) = fun v => v := by
    funext v
    exact G2NativeLineFiber.octImAction_one v
  rw [haction]
  simp

theorem nativeFlagMap_fst_mul
    (g h : SplitOctF2Aut) (F : NativeFlag) :
    (nativeFlagMap (g * h) F).1 =
      (nativeFlagMap g (nativeFlagMap h F)).1 := by
  simp [nativeFlagMap_fst, octImPointPerm_mul]

theorem nativeFlagMap_point_val_mul
    (g h : SplitOctF2Aut) (F : NativeFlag) :
    ((nativeFlagMap (g * h) F).1 : OctImIsotropicPoint).1 =
      ((nativeFlagMap g (nativeFlagMap h F)).1 : OctImIsotropicPoint).1 := by
  exact congrArg Subtype.val (nativeFlagMap_fst_mul g h F)

theorem nativeFlagMap_snd_val
    (g : SplitOctF2Aut) (F : NativeFlag) :
    (nativeFlagMap g F).2.1 = F.2.1.image (octImAction g) := by
  simpa [nativeFlagMap] using
    (nativeLineFiberMap_apply_val g F.1.1 F.2)

theorem nativeFlagMap_snd_val_mul
    (g h : SplitOctF2Aut) (F : NativeFlag) :
    (nativeFlagMap (g * h) F).2.1 =
      (nativeFlagMap g (nativeFlagMap h F)).2.1 := by
  rw [nativeFlagMap_snd_val, nativeFlagMap_snd_val, nativeFlagMap_snd_val]
  rw [Finset.image_image]
  simp [Function.comp_def, ← octImAction_mul]

theorem nativeLine_transport_val
    {p q : OctImIsotropicPoint} (hp : p = q)
    (L : NativeLinesThroughPoint p.1) :
    (cast (congrArg NativeLinesThroughPoint
      (congrArg Subtype.val hp)) L).1 = L.1 := by
  cases hp
  rfl



theorem nativeLineFamily_transport_heq
    {p q : OctImIsotropicPoint} (hp : p = q)
    (L : NativeLinesThroughPoint p.1) :
    HEq
      (cast (congrArg NativeLinesThroughPoint
        (congrArg Subtype.val hp)) L)
      L := by
  cases hp
  rfl

theorem nativeLineFamily_cast_eq_rec
    {x y : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2}
    (hxy : x = y)
    (L : NativeLinesThroughPoint x) :
    cast (congrArg NativeLinesThroughPoint hxy) L =
      Eq.rec L hxy := by
  cases hxy
  rfl

theorem nativeLineFamily_cast_eq_recOn
    {x y : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2}
    (hxy : x = y)
    (L : NativeLinesThroughPoint x) :
    cast (congrArg NativeLinesThroughPoint hxy) L =
      Eq.recOn hxy L := by
  cases hxy
  rfl

theorem nativeLine_transport_heq_of_val_eq
    {x y : InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier.OctImF2}
    (hxy : x = y)
    (Lx : NativeLinesThroughPoint x)
    (Ly : NativeLinesThroughPoint y)
    (hval : Lx.1 = Ly.1) :
    HEq (cast (congrArg NativeLinesThroughPoint hxy) Lx) Ly := by
  cases hxy
  apply heq_of_eq
  apply Subtype.ext
  exact hval

theorem nativeFlagMap_one
    (F : NativeFlag) :
    nativeFlagMap (1 : SplitOctF2Aut) F = F := by
  have hp : (nativeFlagMap (1 : SplitOctF2Aut) F).1 = F.1 := by
    simp [nativeFlagMap_fst, octImPointPerm_one]
  apply Sigma.ext_iff.mpr
  constructor
  · exact hp
  · have hxy : (nativeFlagMap (1 : SplitOctF2Aut) F).1.1 = F.1.1 :=
      congrArg Subtype.val hp
    have hval : (nativeFlagMap (1 : SplitOctF2Aut) F).2.1 = F.2.1 := by
      simpa [nativeFlagMap] using
        (nativeLineFiberMap_one_apply_val F.1.1 F.2)
    have hline := nativeLine_transport_heq_of_val_eq hxy
      (nativeFlagMap (1 : SplitOctF2Aut) F).2 F.2 hval
    rw [nativeLineFamily_cast_eq_recOn hxy
      (nativeFlagMap (1 : SplitOctF2Aut) F).2] at hline
    exact (eqRec_heq hxy (nativeFlagMap (1 : SplitOctF2Aut) F).2).symm.trans hline

theorem nativeFlagMap_mul
    (g h : SplitOctF2Aut) (F : NativeFlag) :
    nativeFlagMap (g * h) F =
      nativeFlagMap g (nativeFlagMap h F) := by
  have hp := nativeFlagMap_fst_mul g h F
  apply Sigma.ext_iff.mpr
  constructor
  · exact hp
  · have hp' : (nativeFlagMap (g * h) F).1.1 =
        (nativeFlagMap g (nativeFlagMap h F)).1.1 :=
      congrArg Subtype.val hp
    have hline := nativeLine_transport_heq_of_val_eq hp'
      (nativeFlagMap (g * h) F).2
      (nativeFlagMap g (nativeFlagMap h F)).2
      (nativeFlagMap_snd_val_mul g h F)
    have hrec : Eq.recOn hp' (nativeFlagMap (g * h) F).2 =
        (nativeFlagMap g (nativeFlagMap h F)).2 := by
      simpa [nativeLineFamily_cast_eq_rec, eqRec_eq_cast] using hline
    exact (eqRec_heq hp' (nativeFlagMap (g * h) F).2).symm.trans
      (heq_of_eq hrec)

noncomputable instance : MulAction SplitOctF2Aut NativeFlag where
  smul := nativeFlagMap
  one_smul := nativeFlagMap_one
  mul_smul := nativeFlagMap_mul

@[simp] theorem smul_nativeFlag
    (g : SplitOctF2Aut) (F : NativeFlag) :
    g • F = nativeFlagMap g F := rfl

theorem nativeFlag_mem_orbit_iff
    (F₀ F : NativeFlag) :
    F ∈ MulAction.orbit SplitOctF2Aut F₀ ↔
      ∃ g : SplitOctF2Aut, nativeFlagMap g F₀ = F := by
  rw [MulAction.mem_orbit_iff]
  simp [smul_nativeFlag]

theorem nativeFlagMap_injective (g : SplitOctF2Aut) :
    Function.Injective (nativeFlagMap g) := by
  intro F G hFG
  have h := congrArg (nativeFlagMap g⁻¹) hFG
  simpa [← nativeFlagMap_mul, nativeFlagMap_one] using h

theorem nativeFlagMap_surjective (g : SplitOctF2Aut) :
    Function.Surjective (nativeFlagMap g) := by
  intro F
  refine ⟨nativeFlagMap g⁻¹ F, ?_⟩
  simp [← nativeFlagMap_mul, nativeFlagMap_one]

theorem nativeFlagMap_bijective (g : SplitOctF2Aut) :
    Function.Bijective (nativeFlagMap g) :=
  ⟨nativeFlagMap_injective g, nativeFlagMap_surjective g⟩

noncomputable def nativeFlagPerm (g : SplitOctF2Aut) :
    Equiv.Perm NativeFlag :=
  Equiv.ofBijective (nativeFlagMap g) (nativeFlagMap_bijective g)

@[simp] theorem nativeFlagPerm_apply (g : SplitOctF2Aut) (F : NativeFlag) :
    nativeFlagPerm g F = nativeFlagMap g F :=
  rfl

theorem nativeFlagPerm_mul (g h : SplitOctF2Aut) :
    nativeFlagPerm (g * h) = nativeFlagPerm g * nativeFlagPerm h := by
  ext F
  simp [nativeFlagPerm_apply, nativeFlagMap_mul]

end InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
