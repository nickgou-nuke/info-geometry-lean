import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness

/-!
# Surjectivity of the transported native line fibre

The native fibre equivalence has a dependent target: it transports the fibre
through the image of the base point.  This theorem exposes its universal
surjectivity without pretending that the two fibres are definitionally equal.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction

theorem nativePointStabilizer_fixes_base_point
    {g : SplitOctF2Aut}
    (hg : g ∈ nativePointStabilizer) :
    octImAction g nativeBasePoint = nativeBasePoint := by
  change g • nativeBasePointData = nativeBasePointData at hg
  have hp := congrArg
    (fun p : G2ImaginaryPointAction.Point => imaginaryToOctIm p.1) hg
  change imaginaryToOctIm (g • octImToImaginary nativeBasePoint) =
    imaginaryToOctIm (octImToImaginary nativeBasePoint) at hp
  unfold octImAction
  rw [hp]
  exact imaginaryOctImEquiv.right_inv nativeBasePoint

theorem nativePointStabilizer_lineFiber_surjective
    (g : SplitOctF2Aut)
    (_hg : octImAction g nativeBasePoint = nativeBasePoint) :
    Function.Surjective (nativeLineFiberMap g nativeBasePoint) :=
  (nativeLineFiberMap g nativeBasePoint).surjective

/- The transport equivalence is surjective without assuming that `g` fixes
   the base point.  Its codomain is the fibre over the transported point. -/
theorem nativeLineFiberMap_surjective
    (g : SplitOctF2Aut) (x : G2ParabolicLineCarrier.OctImF2) :
    Function.Surjective (nativeLineFiberMap g x) :=
  (nativeLineFiberMap g x).surjective

theorem nativePointStabilizer_lineAction_surjective
    (g : nativePointStabilizer) :
    Function.Surjective
    (fun L : NativeLine =>
        nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2) L) := by
  intro L
  let L' : NativeLinesThroughPoint (octImAction g.1 nativeBasePoint) :=
    ⟨L.1, by
      rw [nativePointStabilizer_fixes_base_point g.2]
      exact L.2⟩
  obtain ⟨L₀, hL₀⟩ :=
    (nativeLineFiberMap g.1 nativeBasePoint).surjective L'
  refine ⟨L₀, ?_⟩
  apply Subtype.ext
  change ((nativeLineFiberMap g.1 nativeBasePoint) L₀).1 = L.1
  exact congrArg Subtype.val hL₀

theorem nativePointStabilizer_reaches_lineInfinity :
    ∃ g : nativePointStabilizer,
      nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
          lineZero = lineInfinity := by
  refine ⟨⟨parabolicReflection, parabolicReflection_mem⟩, ?_⟩
  exact (parabolicReflection_lineZero).symm

theorem exists_nativeLine_distinct_from_lineZero_lineInfinity :
    ∃ L : NativeLine, L ≠ lineZero ∧ L ≠ lineInfinity := by
  let S : Finset NativeLine := (Finset.univ.erase lineZero).erase lineInfinity
  have hzero : lineZero ≠ lineInfinity := by
    intro h
    exact (InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness.lineZero_ne_lineInfinity)
      h
  have hcard : S.card = 1 := by
    have huniv : (Finset.univ : Finset NativeLine).card = 3 := by
      simpa using
        InfoGeometry.Algebra.Zorn.G2NativeLineFiber.nativeBaseLine_card
    have hmemInf : lineInfinity ∈
        (Finset.univ : Finset NativeLine).erase lineZero := by
      exact Finset.mem_erase.mpr ⟨hzero.symm, Finset.mem_univ _⟩
    change (((Finset.univ : Finset NativeLine).erase lineZero).erase lineInfinity).card = 1
    calc
      (((Finset.univ : Finset NativeLine).erase lineZero).erase lineInfinity).card =
          (Finset.univ.erase lineZero).card - 1 :=
        Finset.card_erase_of_mem hmemInf
      _ = (Finset.univ.card - 1) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ lineZero)]
      _ = 1 := by rw [huniv]
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hcard
    simp at hcard
  rcases hne with ⟨L, hL⟩
  simp only [S, Finset.mem_erase, Finset.mem_univ] at hL
  exact ⟨L, hL.2.1, hL.1⟩

theorem baseLine_orbit_surjective_of_three_witnesses
    (Lthird : NativeLine)
    (hcover : ∀ L : NativeLine,
      L = lineZero ∨ L = lineInfinity ∨ L = Lthird)
    (hzero : ∃ g : nativePointStabilizer,
      nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
          lineZero = lineZero)
    (hinfinity : ∃ g : nativePointStabilizer,
      nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
          lineZero = lineInfinity)
    (hthird : ∃ g : nativePointStabilizer,
      nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
          lineZero = Lthird) :
    Function.Surjective
      (fun g : nativePointStabilizer =>
        nativeLineAction g.1 (nativePointStabilizer_fixes_base_point g.2)
          lineZero) := by
  intro L
  rcases hcover L with rfl | rfl | rfl
  · exact hzero
  · exact hinfinity
  · exact hthird

end InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
