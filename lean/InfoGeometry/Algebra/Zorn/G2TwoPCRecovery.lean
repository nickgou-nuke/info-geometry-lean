import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas

set_option maxHeartbeats 2000000

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

abbrev PCWordExp := Fin 6 → Bool

def pcTermFun (i : Fin 6) (b : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if b then
    match i with
    | 0 => pc1Fun X
    | 1 => pc2Fun X
    | 2 => pc3Fun X
    | 3 => pc4Fun X
    | 4 => pc5Fun X
    | 5 => pc6Fun X
  else X

def pcWordFun (e : PCWordExp) (X : SplitOctF2) : SplitOctF2 :=
  pcTermFun 5 (e 5) (pcTermFun 4 (e 4) (pcTermFun 3 (e 3)
    (pcTermFun 2 (e 2) (pcTermFun 1 (e 1) (pcTermFun 0 (e 0) X)))))

lemma bitToF2_map_ite (p : Bool) (x y : SplitOctF2)
    (q : SplitOctF2 → Bool) :
    bitToF2 (q (if p then x else y)) =
      bitToF2 p * bitToF2 (q x) + (1 + bitToF2 p) * bitToF2 (q y) := by
  cases p <;> simp [bitToF2] <;> ring

def wordEntry (e : PCWordExp) (i j : Fin 8) : F2 :=
  carrierToVec (pcWordFun e (basis8 j)) i

def recover0 (M : Matrix (Fin 8) (Fin 8) F2) : F2 :=
  M 0 1 + M 0 2 + M 1 1 + M 1 2 + M 1 3 + M 2 6 + M 2 7 + M 3 7 +
    M 0 0 * M 0 5 + M 0 0 * M 0 6 + M 0 0 * M 1 1 + M 0 0 * M 1 4 +
    M 0 1 * M 0 3 + M 0 1 * M 0 4 + M 0 2 * M 0 3 + M 0 2 * M 0 4 +
    M 0 2 * M 0 5 + M 0 2 * M 0 6 + M 0 2 * M 1 1 + M 0 2 * M 1 4

theorem recover0_word (e : PCWordExp) :
    recover0 (fun i j => wordEntry e i j) = bitToF2 (e 0) := by
  dsimp [recover0, wordEntry, pcWordFun, pcTermFun]
  simp only [carrierToVec_zero, carrierToVec_one, carrierToVec_x0,
    carrierToVec_x1, carrierToVec_x2, carrierToVec_y0,
    carrierToVec_y1, carrierToVec_y2]
  simp only [pc1Fun, pc2Fun, pc3Fun, pc4Fun, pc5Fun, pc6Fun]
  simp only [bitToF2_map_ite, bitToF2_xor, bitToF2_and]
  ring

def recover1 (M : Matrix (Fin 8) (Fin 8) F2) : F2 :=
  1 + M 0 0 + M 0 2 + M 1 1 + M 1 4 + M 1 7 + M 2 1 + M 2 2 + M 2 3 +
    M 2 4 + M 2 6 + M 2 7 + M 3 6 + M 3 7 +
    M 0 0 * M 0 1 + M 0 0 * M 0 2 + M 0 0 * M 0 3 + M 0 0 * M 0 5 +
    M 0 0 * M 1 2 + M 0 0 * M 1 3 + M 0 0 * M 1 5 + M 0 0 * M 1 7 +
    M 0 0 * M 2 1 + M 0 0 * M 2 2 + M 0 0 * M 2 4 + M 0 0 * M 3 3 +
    M 0 0 * M 3 4 + M 0 1 * M 0 2 + M 0 1 * M 0 4 + M 0 1 * M 0 5 +
    M 0 1 * M 1 1 + M 0 1 * M 1 5 + M 0 1 * M 1 7 + M 0 1 * M 3 1 +
    M 0 1 * M 3 2 + M 0 1 * M 3 3 + M 0 2 * M 0 3 + M 0 2 * M 0 4 +
    M 0 2 * M 1 1 + M 0 2 * M 1 2 + M 0 2 * M 1 3 + M 0 2 * M 2 1 +
    M 0 2 * M 2 2 + M 0 2 * M 2 4 + M 0 2 * M 3 1 + M 0 2 * M 3 2 +
    M 0 2 * M 3 4

theorem recover1_word (e : PCWordExp) :
    recover1 (fun i j => wordEntry e i j) = bitToF2 (e 1) := by
  dsimp [recover1, wordEntry, pcWordFun, pcTermFun]
  simp only [carrierToVec_zero, carrierToVec_one, carrierToVec_x0,
    carrierToVec_x1, carrierToVec_x2, carrierToVec_y0,
    carrierToVec_y1, carrierToVec_y2]
  simp only [pc1Fun, pc2Fun, pc3Fun, pc4Fun, pc5Fun, pc6Fun]
  simp only [bitToF2_map_ite, bitToF2_xor, bitToF2_and]
  ring

def recover2 (M : Matrix (Fin 8) (Fin 8) F2) : F2 :=
  M 0 1 + M 0 2 + M 0 4 + M 0 6 + M 1 2 + M 1 4 + M 2 1 + M 2 7 +
    M 3 5 + M 3 7 + M 0 0 * M 0 2 + M 0 0 * M 0 3 + M 0 0 * M 0 4 +
    M 0 1 * M 0 3 + M 0 2 * M 0 4

theorem recover2_word (e : PCWordExp) :
    recover2 (fun i j => wordEntry e i j) = bitToF2 (e 2) := by
  dsimp [recover2, wordEntry, pcWordFun, pcTermFun]
  simp only [carrierToVec_zero, carrierToVec_one, carrierToVec_x0,
    carrierToVec_x1, carrierToVec_x2, carrierToVec_y0,
    carrierToVec_y1, carrierToVec_y2]
  simp only [pc1Fun, pc2Fun, pc3Fun, pc4Fun, pc5Fun, pc6Fun]
  simp only [bitToF2_map_ite, bitToF2_xor, bitToF2_and]
  ring

end InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
