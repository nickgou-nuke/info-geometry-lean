import InfoGeometry.Algebra.Zorn.G2CASNativePointAction
import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

namespace InfoGeometry.Algebra.Zorn.G2CASPointOrbit

open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev PointWord := List (Fin 8)

def pointGeneratorRaw (k : Fin 8) (i : Fin 63) : Fin 63 :=
  if h : k.val < 6 then
    casPointPermRaw ⟨k.val, by omega⟩ i
  else if k.val = 6 then
    casPointPermRaw 6 i
  else
    correctedTPointPermRaw i

noncomputable def pointGenerator (k : Fin 8) : SplitOctF2Aut :=
  if h : k.val < 6 then
    pcGenerator ⟨k.val, by omega⟩
  else if k.val = 6 then
    swap01Aut
  else
    correctedT

noncomputable def pointWordProd : PointWord → SplitOctF2Aut
  | [] => 1
  | k :: ks => pointWordProd ks * pointGenerator k

theorem pointGenerator_intertwines (k : Fin 8) (i : Fin 63) :
    casPoint (pointGeneratorRaw k i) =
      octImAction (pointGenerator k) (casPoint i) := by
  fin_cases k
  · exact casPoint_pc_action 0 i
  · exact casPoint_pc_action 1 i
  · exact casPoint_pc_action 2 i
  · exact casPoint_pc_action 3 i
  · exact casPoint_pc_action 4 i
  · exact casPoint_pc_action 5 i
  · exact casPoint_swap_action i
  · exact correctedTPointPerm_intertwines i

def evalPointWord : PointWord → Fin 63 → Fin 63
  | [], i => i
  | k :: ks, i => evalPointWord ks (pointGeneratorRaw k i)

theorem evalPointWord_native (w : PointWord) (i : Fin 63) :
    casPoint (evalPointWord w i) =
      octImAction (pointWordProd w) (casPoint i) := by
  induction w generalizing i with
  | nil =>
      simp [evalPointWord, pointWordProd, octImAction_one]
  | cons k ks ih =>
      rw [evalPointWord, ih, pointWordProd, octImAction_mul]
      exact congrArg (octImAction (pointWordProd ks))
        (pointGenerator_intertwines k i)

/- The words are produced by BFS over the already verified eight finite action
rows.  Their only role here is to provide explicit orbit witnesses. -/
def orbitWord (i : Fin 63) : PointWord := match i.val with
  | 0 => []
  | 1 => [7, 6, 7]
  | 2 => [7, 6, 7, 6, 7]
  | 3 => [7, 6, 7, 0]
  | 4 => [7, 6, 7, 1]
  | 5 => [7, 6, 1, 7]
  | 6 => [7, 6, 7, 6]
  | 7 => [7, 6]
  | 8 => [7, 6, 7, 6, 7, 0]
  | 9 => [7, 0, 6, 7, 6, 7, 2]
  | 10 => [7, 0, 6, 7, 6, 7, 1]
  | 11 => [7, 6, 7, 6, 7, 3]
  | 12 => [7, 6, 7, 6, 7, 1]
  | 13 => [7, 6, 1, 7, 6, 7]
  | 14 => [7, 6, 1, 7, 0]
  | 15 => [7, 6, 7, 0, 2]
  | 16 => [7, 0, 6, 7, 0]
  | 17 => [7, 6, 7, 0, 6]
  | 18 => [7, 6, 7, 6, 1, 2]
  | 19 => [7, 6, 7, 6, 7, 2]
  | 20 => [7, 0, 6, 7]
  | 21 => [7, 6, 7, 1, 6]
  | 22 => [7, 6, 7, 6, 7, 0, 7]
  | 23 => [7, 6, 1, 7, 6]
  | 24 => [7, 6, 7, 1, 6, 1]
  | 25 => [7, 6, 1, 7, 6, 1]
  | 26 => [7, 0, 6, 7, 0, 6]
  | 27 => [7, 0, 6, 7, 6]
  | 28 => [7]
  | 29 => [7, 6, 1]
  | 30 => [7, 0, 6]
  | 31 => [7, 6, 7, 6, 1, 7, 0]
  | 32 => [7, 6, 7, 6, 7, 2, 0]
  | 33 => [7, 0, 6, 7, 6, 7, 6]
  | 34 => [7, 6, 7, 6, 2, 7, 6]
  | 35 => [7, 6, 1, 7, 6, 7, 0]
  | 36 => [7, 6, 7, 1, 6, 7]
  | 37 => [7, 0, 6, 1]
  | 38 => [7, 6, 7, 6, 7, 2, 6]
  | 39 => [7, 0, 6, 7, 6, 7]
  | 40 => [7, 6, 7, 0, 6, 7]
  | 41 => [7, 0, 6, 7, 6, 7, 0]
  | 42 => [7, 6, 7, 6, 7, 0, 2]
  | 43 => [7, 6, 7, 6, 2, 7]
  | 44 => [7, 6, 7, 0, 6, 7, 0]
  | 45 => [7, 0, 6, 7, 6, 1, 2]
  | 46 => [7, 0, 6, 7, 6, 2, 7]
  | 47 => [7, 0, 6, 7, 6, 1, 7]
  | 48 => [7, 6, 7, 6, 7, 1, 0]
  | 49 => [7, 0, 6, 7, 0, 6, 7]
  | 50 => [7, 0, 6, 7, 6, 2]
  | 51 => [7, 6, 7, 6, 2]
  | 52 => [7, 6, 7, 1, 6, 7, 0]
  | 53 => [7, 6, 7, 6, 7, 0, 1]
  | 54 => [7, 6, 7, 0, 6, 1]
  | 55 => [7, 6, 7, 6, 1]
  | 56 => [7, 6, 7, 6, 1, 0]
  | 57 => [7, 0, 6, 7, 6, 1]
  | 58 => [7, 0, 6, 7, 6, 1, 7, 0]
  | 59 => [7, 6, 7, 6, 2, 7, 0]
  | 60 => [7, 0]
  | 61 => [7, 6, 7, 6, 1, 7]
  | 62 => [7, 0, 6, 7, 6, 7, 3]
  | _ => []

theorem orbitWord_eval (i : Fin 63) :
    evalPointWord (orbitWord i) 0 = i := by
  fin_cases i <;> decide

theorem orbitWord_native_eval (i : Fin 63) :
    octImAction (pointWordProd (orbitWord i)) (casPoint 0) = casPoint i := by
  rw [← evalPointWord_native, orbitWord_eval]

theorem native_point_orbit_cover :
    ∀ v : OctImIsotropicPoint, ∃ w : PointWord,
      octImAction (pointWordProd w) nativeBasePoint = v.1 := by
  intro v
  obtain ⟨i, rfl⟩ := casPointEnum.surjective v
  refine ⟨orbitWord i, ?_⟩
  have h := orbitWord_native_eval i
  rw [casPoint_zero_eq_nativeBasePoint] at h
  simpa [casPointEnum_apply] using h

theorem point_orbit_cover :
    ∀ i : Fin 63, ∃ w : PointWord, evalPointWord w 0 = i := by
  intro i
  exact ⟨orbitWord i, orbitWord_eval i⟩

end InfoGeometry.Algebra.Zorn.G2CASPointOrbit
