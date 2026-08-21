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

def pcMatrix (e : PCExponent) : PCMatrix := autMatrix (pcWord e)

def peeledAut (p w : SplitOctF2Aut) : SplitOctF2Aut := p⁻¹ * w

theorem autMatrix_peeled (p w : SplitOctF2Aut) :
    autMatrix (peeledAut p w) = autMatrix w * autMatrix p⁻¹ := by
  exact autMatrix_mul p⁻¹ w

theorem peeledAut_reconstruct (p w : SplitOctF2Aut) :
    p * peeledAut p w = w := by
  simp [peeledAut]

def peelPc2 (w : SplitOctF2Aut) : SplitOctF2Aut := pc2Aut⁻¹ * w

def peelPc3 (w : SplitOctF2Aut) : SplitOctF2Aut := pc3Aut⁻¹ * w

theorem peelPc2_reconstruct (w : SplitOctF2Aut) :
    pc2Aut * peelPc2 w = w := by
  simp [peelPc2]

theorem peelPc3_reconstruct (w : SplitOctF2Aut) :
    pc3Aut * peelPc3 w = w := by
  simp [peelPc3]

/-! The CAS inverse row transported through `autMatrix`, whose multiplication
    convention reverses composition. -/

theorem autMatrix_pc2Aut_inv :
    autMatrix pc2Aut⁻¹ = autMatrix pc2Aut * autMatrix pc6Aut := by
  rw [pc2Aut_inv_eq, autMatrix_mul]

theorem autMatrix_pc3Aut_inv :
    autMatrix pc3Aut⁻¹ = autMatrix pc3Aut * autMatrix pc6Aut := by
  rw [pc3Aut_inv_eq, autMatrix_mul]

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
