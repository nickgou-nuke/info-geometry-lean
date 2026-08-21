import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

abbrev PCExponent := Fin 6 → Bool
abbrev PCMatrix := Matrix (Fin 8) (Fin 8) F2

/-! The CAS-derived flag pivots, expressed over the existing matrix owner. -/

def flagRecover0 (M : PCMatrix) : F2 := M 2 7
def flagRecover1 (M : PCMatrix) : F2 := M 3 2
def flagRecover2 (M : PCMatrix) : F2 := M 0 2
def flagRecover4 (M : PCMatrix) : F2 :=
  M 0 7 + (M 2 7 * M 0 2) + M 3 2 + M 0 2
def flagRecover3 (M : PCMatrix) : F2 :=
  M 4 3 + (M 2 7 * M 0 2) + M 2 7 + M 3 2 + M 0 2 + flagRecover4 M
def flagRecover5 (M : PCMatrix) : F2 :=
  M 4 2 + (M 3 2 * flagRecover3 M) + (M 3 2 * flagRecover4 M)

def flagRecover (k : Fin 6) (M : PCMatrix) : F2 :=
  match k with
  | 0 => flagRecover0 M
  | 1 => flagRecover1 M
  | 2 => flagRecover2 M
  | 3 => flagRecover3 M
  | 4 => flagRecover4 M
  | 5 => flagRecover5 M

def pcMatrix (e : PCExponent) : PCMatrix := autMatrix (pcWord e)

theorem pcMatrix_eq_of_word_eq {e f : PCExponent}
    (h : pcWord e = pcWord f) : pcMatrix e = pcMatrix f := by
  exact congrArg autMatrix h

theorem pcWord_injective_of_matrix_recoveries
    (recover : Fin 6 → PCMatrix → F2)
    (hrecover : ∀ (k : Fin 6) (e : PCExponent),
      recover k (pcMatrix e) = bitToF2 (e k)) :
    Function.Injective pcWord := by
  intro e f h
  have hm : pcMatrix e = pcMatrix f := pcMatrix_eq_of_word_eq h
  funext k
  apply (bitToF2_eq_iff (e k) (f k)).mp
  rw [← hrecover k e, ← hrecover k f, hm]

theorem pcWord_range_card_of_matrix_recoveries
    (recover : Fin 6 → PCMatrix → F2)
    (hrecover : ∀ (k : Fin 6) (e : PCExponent),
      recover k (pcMatrix e) = bitToF2 (e k)) :
    Nat.card (Set.range pcWord) = 64 := by
  rw [Nat.card_range_of_injective
    (pcWord_injective_of_matrix_recoveries recover hrecover)]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

theorem pcWord_injective_of_flag_recoveries
    (hrecover : ∀ (k : Fin 6) (e : PCExponent),
      flagRecover k (pcMatrix e) = bitToF2 (e k)) :
    Function.Injective pcWord := by
  exact pcWord_injective_of_matrix_recoveries flagRecover hrecover

theorem conjugate_injective {α β : Type*} [Group α]
    (w : α) (f : β → α) (hf : Function.Injective f) :
    Function.Injective (fun x => w * f x * w⁻¹) := by
  intro x y h
  apply hf
  have h' : (w * f x) * w⁻¹ = (w * f y) * w⁻¹ := by
    simpa only using h
  have h'' : w * f x = w * f y := mul_right_cancel h'
  exact mul_left_cancel h''

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
