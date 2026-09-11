import InfoGeometry.Algebra.Zorn.G2NativeLineFiberIdentity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberThirdWitness
import InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus

/-! # Assembly of the native base-line orbit -/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiberOrbitAssembly

open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberIdentity
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberThirdWitness
open InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

theorem baseNativeLine_three_cover :
    ∀ L : NativeLine,
      L = lineZero ∨ L = lineInfinity ∨ L = thirdFiberLineLeanOrder := by
  intro L
  let S : Finset NativeLine := {lineZero, lineInfinity, thirdFiberLineLeanOrder}
  have hzero : lineZero ≠ lineInfinity := lineZero_ne_lineInfinity
  have hthirdZero : thirdFiberLineLeanOrder ≠ lineZero :=
    thirdFiberLineLeanOrder_ne_lineZero
  have hthirdInf : thirdFiberLineLeanOrder ≠ lineInfinity :=
    thirdFiberLineLeanOrder_ne_lineInfinity
  have hS : S.card = 3 := by
    change ({lineZero, lineInfinity, thirdFiberLineLeanOrder} :
      Finset NativeLine).card = 3
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · simp
      · simpa using (Ne.symm hthirdInf)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzero, Ne.symm hthirdZero⟩
  have hcard : S.card = Fintype.card NativeLine := by
    rw [hS]
    exact nativeBaseLine_card.symm
  have huniv : S = Finset.univ := Finset.eq_univ_of_card S hcard
  have hL : L ∈ S := by
    rw [huniv]
    exact Finset.mem_univ L
  simpa [S] using hL

theorem baseIntrinsicLine_orbit_surjective :
    Function.Surjective
      (fun g : G2NativeOnePointStabilizer.nativePointStabilizer =>
        nativeLineAction g.1
          (nativePointStabilizer_fixes_base_point g.2) lineZero) := by
  apply baseLine_orbit_surjective_of_three_witnesses
    thirdFiberLineLeanOrder baseNativeLine_three_cover
  · exact ⟨⟨1, by simp⟩, by simpa using nativeLineAction_one lineZero⟩
  · exact nativePointStabilizer_reaches_lineInfinity
  · exact ⟨⟨thirdFiberWitnessLeanOrder,
        thirdFiberWitnessLeanOrder_mem_nativePointStabilizer⟩, rfl⟩

end InfoGeometry.Algebra.Zorn.G2NativeLineFiberOrbitAssembly
