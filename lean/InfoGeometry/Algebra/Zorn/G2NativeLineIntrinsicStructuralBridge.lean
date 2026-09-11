import InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeLineSetIsotropicBridge
import InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
import InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicFiberEquiv
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2NativePointTransitivity
import InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction

/-!
# Explicit native-to-intrinsic line construction and action equivariance

The map below is defined from a native line by extracting a native candidate
whose line-set is that line, then applying the already proved intrinsic
construction.  Its definition therefore records membership and independence
from the chosen candidate at the quotient level; it is not obtained merely
from a cardinality equality.

Furthermore, this module proves the canonical base-fiber action equivariance:
`nativeLineToIntrinsicLine (nativeLineAction g hg L) = cast ... (intrinsicLineMap g (nativeLineToIntrinsicLine L))`
establishing the exact incidence-preserving compatibility between native and intrinsic lines.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicStructuralBridge

open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicFiberEquiv
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativePointTransitivity
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagAction
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def nativeLineToIntrinsicLine
    (L : NativeLine) : IntrinsicLine nativeBaseIsotropicPoint :=
  nativeLineQuotientToIntrinsicLine (quotientOfNativeLine L)

theorem intrinsicLine_eq_of_val_eq
    {p : OctImIsotropicPoint}
    {L₁ L₂ : IntrinsicLine p}
    (h : L₁.1 = L₂.1) : L₁ = L₂ := by
  exact Subtype.ext h

theorem intrinsicLine_eq_of_val_image_eq
    {p : OctImIsotropicPoint}
    {L₁ L₂ : IntrinsicLine p}
    (h : L₁.1.image Subtype.val = L₂.1.image Subtype.val) : L₁ = L₂ := by
  apply Subtype.ext
  apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
  simp only [Finset.map_eq_image]
  exact h

theorem nativeLineToIntrinsicLine_eq_candidate
    (L : NativeLine) :
    nativeLineToIntrinsicLine L =
      intrinsicLineOfNativeCandidate
        (nativeCandidateOfLine L).1
        ((Finset.mem_filter.mp (nativeCandidateOfLine L).2).2) := by
  rw [nativeLineToIntrinsicLine]
  exact nativeLineQuotientToIntrinsicLine_mk (nativeCandidateOfLine L)

theorem nativeLineToIntrinsicLine_val_image
    (L : NativeLine) :
    (nativeLineToIntrinsicLine L).1.image Subtype.val = L.1 := by
  rw [nativeLineToIntrinsicLine_eq_candidate]
  rw [intrinsicLineOfNativeCandidate_val_image_eq_lineSet]
  exact nativeCandidateOfLine_spec L

theorem nativeLineToIntrinsicLine_mem
    (L : NativeLine) :
    (nativeLineToIntrinsicLine L).1 ∈
      zornZeroTriples := by
  simp only [zornZeroTriples, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(nativeLineToIntrinsicLine L).2.2.1, ?_⟩
  intro u hu v hv huv
  exact (nativeLineToIntrinsicLine L).2.2.2 hu hv huv

theorem nativeLineToIntrinsicLine_base_mem
    (L : NativeLine) :
    nativeBaseIsotropicPoint ∈ (nativeLineToIntrinsicLine L).1 := by
  exact (nativeLineToIntrinsicLine L).2.1

theorem nativeLineToIntrinsicLine_eq_equiv (L : NativeLine) :
    nativeLineToIntrinsicLine L = nativeLineToIntrinsicLineEquiv L := by
  dsimp [nativeLineToIntrinsicLine, nativeLineToIntrinsicLineEquiv]
  rfl

/-- Structural surjectivity: explicit preimage via the geometric equivalence inverse. -/
theorem nativeLineToIntrinsicLine_surjective_structural :
    ∀ L : IntrinsicLine nativeBaseIsotropicPoint,
      ∃ N : NativeLine, nativeLineToIntrinsicLine N = L := by
  intro L
  refine ⟨nativeLineToIntrinsicLineEquiv.symm L, ?_⟩
  rw [nativeLineToIntrinsicLine_eq_equiv]
  exact nativeLineToIntrinsicLineEquiv.apply_symm_apply L

theorem nativeLineToIntrinsicLine_injective :
    Function.Injective nativeLineToIntrinsicLine := by
  intro L₁ L₂ h
  apply Subtype.ext
  have h1 := congrArg (fun L : IntrinsicLine nativeBaseIsotropicPoint => L.1.image Subtype.val) h
  dsimp at h1
  rw [nativeLineToIntrinsicLine_val_image L₁, nativeLineToIntrinsicLine_val_image L₂] at h1
  exact h1

theorem nativeLineToIntrinsicLine_surjective :
    Function.Surjective nativeLineToIntrinsicLine := by
  intro L
  obtain ⟨q, hq⟩ := nativeLineQuotientToIntrinsicLine_surjective L
  refine ⟨lineSetQuotientToNativeLines q, ?_⟩
  change nativeLineQuotientToIntrinsicLine
      (quotientOfNativeLine (lineSetQuotientToNativeLines q)) = L
  rw [show quotientOfNativeLine (lineSetQuotientToNativeLines q) = q by
    exact lineSetQuotientToNativeLines.symm_apply_apply q]
  exact hq

noncomputable def nativeLineToIntrinsicLineStructuralEquiv :
    NativeLine ≃ IntrinsicLine nativeBaseIsotropicPoint :=
  Equiv.ofBijective nativeLineToIntrinsicLine
    ⟨nativeLineToIntrinsicLine_injective,
      nativeLineToIntrinsicLine_surjective⟩

/-- THEOREM: Canonical base-fiber action equivariance for the structural native-to-intrinsic map. -/
theorem nativeLineToIntrinsicLine_action_eq_cast
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint = nativeBaseIsotropicPoint)
    (L : NativeLine) :
    nativeLineToIntrinsicLine (nativeLineAction g hg L) =
      cast (congrArg IntrinsicLine hgp)
        (intrinsicLineMap g (nativeLineToIntrinsicLine L)) := by
  apply Subtype.ext
  apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
  simp only [Finset.map_eq_image]
  change (nativeLineToIntrinsicLine (nativeLineAction g hg L)).1.image Subtype.val =
    (cast (congrArg IntrinsicLine hgp)
      (intrinsicLineMap g (nativeLineToIntrinsicLine L))).1.image Subtype.val
  rw [nativeLineToIntrinsicLine_val_image]
  rw [cast_intrinsicLine_val_image hgp, intrinsicLineMap_val, zornZeroTripleMap_val_image]
  calc
    (nativeLineAction g hg L).1 = L.1.image (octImAction g) := by
      rfl
    _ = ((nativeLineToIntrinsicLine L).1.image Subtype.val).image (octImAction g) := by
      rw [nativeLineToIntrinsicLine_val_image]
    _ = (nativeLineToIntrinsicLine L).1.image (fun v => octImAction g v.1) := by
      rw [Finset.image_image]
      rfl

noncomputable def nativeLineFiberEquivOfTransport
    (p : OctImIsotropicPoint)
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = p.1)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint = p) :
    NativeLinesThroughPoint p.1 ≃ IntrinsicLine p := by
  let hn : NativeLinesThroughPoint (octImAction g nativeBasePoint) ≃
      NativeLinesThroughPoint p.1 :=
    Equiv.cast (congrArg NativeLinesThroughPoint hg)
  let hi : IntrinsicLine (octImPointPerm g nativeBaseIsotropicPoint) ≃
      IntrinsicLine p :=
    Equiv.cast (congrArg IntrinsicLine hgp)
  exact ((nativeLineFiberMap g nativeBasePoint).trans hn).symm.trans
    (nativeLineToIntrinsicLineEquiv.trans
      ((intrinsicLineMapEquiv g nativeBaseIsotropicPoint).trans hi))

theorem nativeLineFiberEquivOfTransport_apply_base
    (p : OctImIsotropicPoint)
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = p.1)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint = p)
    (L : NativeLinesThroughPoint p.1) :
    nativeLineFiberEquivOfTransport p g hg hgp L =
      (Equiv.cast (congrArg IntrinsicLine hgp))
        ((intrinsicLineMapEquiv g nativeBaseIsotropicPoint)
          (nativeLineToIntrinsicLineEquiv
            (((nativeLineFiberMap g nativeBasePoint).trans
              (Equiv.cast (congrArg NativeLinesThroughPoint hg))).symm L))) := by
  rfl

theorem nativeLineFiberEquivOfTransport_val_image
    (p : OctImIsotropicPoint)
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = p.1)
    (hgp : octImPointPerm g nativeBaseIsotropicPoint = p)
    (L : NativeLinesThroughPoint p.1) :
    (nativeLineFiberEquivOfTransport p g hg hgp L).1.image Subtype.val = L.1 := by
  dsimp [nativeLineFiberEquivOfTransport]
  rw [cast_intrinsicLine_val_image hgp]
  dsimp [intrinsicLineMapEquiv, intrinsicLineMap]
  rw [zornZeroTripleMap_val_image]
  rw [show (fun v : OctImIsotropicPoint => octImAction g v.1) = (octImAction g) ∘ Subtype.val from rfl]
  rw [← Finset.image_image]
  rw [nativeLineToIntrinsicLineEquiv_val_image]
  let L₀ : NativeLine :=
    (((nativeLineFiberMap g nativeBasePoint).trans
      (Equiv.cast (congrArg NativeLinesThroughPoint hg))).symm L)
  have htrans : (nativeLineFiberMap g nativeBasePoint L₀).1 =
      L₀.1.image (octImAction g) := rfl
  have htrans' :
      (Equiv.cast (congrArg NativeLinesThroughPoint hg)
        (nativeLineFiberMap g nativeBasePoint L₀)).1 = L.1 := by
    have hsymm :=
      ((nativeLineFiberMap g nativeBasePoint).trans
        (Equiv.cast (congrArg NativeLinesThroughPoint hg))).apply_symm_apply L
    exact congrArg (fun x : NativeLinesThroughPoint p.1 => x.1) hsymm
  dsimp [Equiv.cast] at htrans'
  have hcast := nativeRawLine_transport_val hg
    (nativeLineFiberMap g nativeBasePoint L₀)
  rw [hcast] at htrans'
  rw [htrans] at htrans'
  exact htrans'

/-- Canonical base-point transporter into `p`. -/
noncomputable def pointTransporter (p : OctImIsotropicPoint) : SplitOctF2Aut :=
  Classical.choose (octImPointPerm_base_surjective p)

theorem pointTransporter_spec (p : OctImIsotropicPoint) :
    octImPointPerm (pointTransporter p) nativeBaseIsotropicPoint = p :=
  Classical.choose_spec (octImPointPerm_base_surjective p)

theorem pointTransporter_val_spec (p : OctImIsotropicPoint) :
    octImAction (pointTransporter p) nativeBasePoint = p.1 :=
  congrArg Subtype.val (pointTransporter_spec p)

/-- Canonical point-dependent geometric fiber equivalence constructed from transport. -/
noncomputable def nativeLineFiberEquiv
    (p : OctImIsotropicPoint) :
    NativeLinesThroughPoint p.1 ≃ IntrinsicLine p :=
  nativeLineFiberEquivOfTransport p (pointTransporter p)
    (pointTransporter_val_spec p) (pointTransporter_spec p)

/- Transport a native line between arbitrary point fibres. -/
noncomputable def nativeLineFiberEquivFrom
    (a p : OctImIsotropicPoint)
    (g : SplitOctF2Aut)
    (hgp : octImPointPerm g a = p) :
    NativeLinesThroughPoint a.1 ≃ IntrinsicLine p := by
  let hi : IntrinsicLine (octImPointPerm g a) ≃ IntrinsicLine p :=
    Equiv.cast (congrArg IntrinsicLine hgp)
  exact (nativeLineFiberEquiv a).trans
    ((intrinsicLineMapEquiv g a).trans hi)

theorem nativeLineFiberEquivFrom_endpoint_mul
    (a p q : OctImIsotropicPoint)
    (g h : SplitOctF2Aut)
    (hgp : octImPointPerm g a = p)
    (hhq : octImPointPerm h p = q) :
    octImPointPerm (h * g) a = q := by
  have hmul : octImPointPerm (h * g) = octImPointPerm h * octImPointPerm g :=
    octImPointPerm_mul h g
  have happ : octImPointPerm (h * g) a = (octImPointPerm h * octImPointPerm g) a := by
    rw [hmul]
  rw [happ, Equiv.Perm.mul_apply, hgp, hhq]

noncomputable def nativeLineFiberTransportCast
    {a p : OctImIsotropicPoint} (h : a = p) :
    NativeLinesThroughPoint a.1 ≃ NativeLinesThroughPoint p.1 :=
  Equiv.cast (congrArg NativeLinesThroughPoint (congrArg Subtype.val h))

theorem nativeLineFiberTransportCast_apply_val
    {a p : OctImIsotropicPoint} (h : a = p)
    (L : NativeLinesThroughPoint a.1) :
    (nativeLineFiberTransportCast h L).1 = L.1 := by
  cases h
  rfl

theorem nativeLineFiberTransportCast_comp
    {a p q : OctImIsotropicPoint}
    (h₁ : a = p) (h₂ : p = q)
    (L : NativeLinesThroughPoint a.1) :
    nativeLineFiberTransportCast h₂
        (nativeLineFiberTransportCast h₁ L) =
      nativeLineFiberTransportCast (h₁.trans h₂) L := by
  cases h₁
  cases h₂
  rfl

theorem nativeLineFiberTransportCast_symm
    {a p : OctImIsotropicPoint}
    (h : a = p)
    (L : NativeLinesThroughPoint a.1) :
    nativeLineFiberTransportCast h.symm
        (nativeLineFiberTransportCast h L) = L := by
  cases h
  rfl

noncomputable def nativeLineFiberTransportCastOfAction
    {a p : OctImIsotropicPoint}
    (g : SplitOctF2Aut)
    (hgp : octImPointPerm g a = p) :
    NativeLinesThroughPoint (octImAction g a.1) ≃
      NativeLinesThroughPoint p.1 :=
  Equiv.cast (congrArg NativeLinesThroughPoint (congrArg Subtype.val hgp))

theorem nativeLineFiberTransportCastOfAction_apply_val
    {a p : OctImIsotropicPoint}
    (g : SplitOctF2Aut)
    (hgp : octImPointPerm g a = p)
    (L : NativeLinesThroughPoint (octImAction g a.1)) :
    (nativeLineFiberTransportCastOfAction g hgp L).1 = L.1 := by
  dsimp [nativeLineFiberTransportCastOfAction, Equiv.cast]
  exact nativeRawLine_transport_val (congrArg Subtype.val hgp) L

theorem nativeLineActionTransport_comp
    (a p q : OctImIsotropicPoint)
    (g h : SplitOctF2Aut)
    (hgp : octImPointPerm g a = p)
    (hhq : octImPointPerm h p = q)
    (L : NativeLinesThroughPoint a.1) :
    (nativeLineFiberTransportCastOfAction h hhq
        (nativeLineFiberMap h p.1
          (nativeLineFiberTransportCastOfAction g hgp
            (nativeLineFiberMap g a.1 L)))).1 =
      (nativeLineFiberTransportCastOfAction
        (h * g) (nativeLineFiberEquivFrom_endpoint_mul a p q g h hgp hhq)
        (nativeLineFiberMap (h * g) a.1 L)).1 := by
  rw [nativeLineFiberTransportCastOfAction_apply_val]
  rw [nativeLineFiberTransportCastOfAction_apply_val]
  rw [nativeLineFiberMap_apply_val]
  rw [nativeLineFiberTransportCastOfAction_apply_val]
  rw [nativeLineFiberMap_apply_val]
  rw [nativeLineFiberMap_apply_val]
  rw [Finset.image_image]
  simp [Function.comp_def, ← octImAction_mul]

theorem nativeLineFiberEquivFrom_apply
    (a p : OctImIsotropicPoint)
    (g : SplitOctF2Aut)
    (hgp : octImPointPerm g a = p)
    (L : NativeLinesThroughPoint a.1) :
    nativeLineFiberEquivFrom a p g hgp L =
      (Equiv.cast (congrArg IntrinsicLine hgp))
        ((intrinsicLineMapEquiv g a) (nativeLineFiberEquiv a L)) := by
  rfl

/-- THEOREM: The geometric fiber equivalence preserves the underlying line set in `OctImF2`. -/
theorem nativeLineFiberEquiv_val_image
    (p : OctImIsotropicPoint)
    (L : NativeLinesThroughPoint p.1) :
    (nativeLineFiberEquiv p L).1.image Subtype.val = L.1 :=
  nativeLineFiberEquivOfTransport_val_image p (pointTransporter p)
    (pointTransporter_val_spec p) (pointTransporter_spec p) L

end InfoGeometry.Algebra.Zorn.G2NativeLineIntrinsicStructuralBridge
