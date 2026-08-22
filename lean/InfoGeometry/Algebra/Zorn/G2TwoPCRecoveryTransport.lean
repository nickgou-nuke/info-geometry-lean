import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

abbrev PCExponent := Fin 6 → Bool
abbrev PCMatrix := Matrix (Fin 8) (Fin 8) F2

def pcMatrix (e : PCExponent) : PCMatrix :=
  autMatrix (G2TwoSylowSubgroup.pcWord e)

theorem pcMatrix_entry_x0 (e : PCExponent) :
    pcMatrix e 2 7 = bitToF2 (extractBit0 (G2TwoSylowSubgroup.pcWord e)) := by
  rfl

theorem pcMatrix_entry_x0_recovered (e : PCExponent) :
    pcMatrix e 2 7 = bitToF2 (e 0) := by
  rw [pcMatrix_entry_x0, extractBit0_pcWord]

theorem pcWord_autMatrix_entry_two_two (e : PCExponent) :
    autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 = 1 := by
  rw [autMatrix_entry_x0, G2TwoSylowSubgroup.pcWord_apply]
  change bitToF2 ((pcWordFun e (basis8 2)).x0) = 1
  rw [pcWordFun_x0_basis8_2]
  rfl

def pcRecover0 (M : PCMatrix) : F2 := M 2 7

theorem pcRecover0_pcMatrix (e : PCExponent) :
    pcRecover0 (pcMatrix e) = bitToF2 (e 0) := by
  exact pcMatrix_entry_x0_recovered e

def pcPeel0Matrix (M : PCMatrix) : PCMatrix :=
  M * autMatrix
    (if f2ToBit (pcRecover0 M) then pc1Aut else 1)

theorem pcPeel0Matrix_pcMatrix (e : PCExponent) :
    pcPeel0Matrix (pcMatrix e) =
      autMatrix (peel0 (G2TwoSylowSubgroup.pcWord e)) := by
  rw [pcPeel0Matrix, pcRecover0_pcMatrix, f2ToBit_bitToF2]
  dsimp [pcMatrix, peel0]
  split
  · rename_i h0
    have hbit :
        ((G2TwoSylowSubgroup.pcWord e).1 (basis8 7)).x0 = true := by
      change extractBit0 (G2TwoSylowSubgroup.pcWord e) = true
      rw [extractBit0_pcWord]
      exact h0
    simp [hbit, autMatrix_mul]
  · rename_i h0
    have hbit :
        ¬(((G2TwoSylowSubgroup.pcWord e).1 (basis8 7)).x0 = true) := by
      intro hbit
      apply h0
      change extractBit0 (G2TwoSylowSubgroup.pcWord e) = true at hbit
      rw [extractBit0_pcWord] at hbit
      exact hbit
    rw [if_neg hbit, autMatrix_one]
    simp

def pcPeel1Matrix (M : PCMatrix) : PCMatrix :=
  M * autMatrix
    (if f2ToBit (M 3 2) then pc6Aut * pc2Aut else 1)

theorem pcPeel1Matrix_pcMatrix (e : PCExponent) :
    pcPeel1Matrix (pcPeel0Matrix (pcMatrix e)) =
      autMatrix (peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))) := by
  rw [pcPeel1Matrix, pcPeel0Matrix_pcMatrix]
  have hbit :
      ((peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 2)).x1 =
        extractBit1 (G2TwoSylowSubgroup.pcWord e) := by
    rfl
  rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_x1]
  rw [hbit, extractBit1_pcWord, f2ToBit_bitToF2]
  dsimp [peel1]
  split
  · rename_i h1
    have hc :
        ((peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 2)).x1 = true := by
      rw [hbit, extractBit1_pcWord]
      exact h1
    simp only [if_pos hc]
    rw [autMatrix_mul, autMatrix_mul]
    rw [← autMatrix_mul pc6Aut pc2Aut]
  · rename_i h1
    have hc :
        ¬(((peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 2)).x1 = true) := by
      intro hc
      apply h1
      rw [hbit, extractBit1_pcWord] at hc
      exact hc
    rw [if_neg hc, autMatrix_one]
    simp

def pcPeel2Matrix (M : PCMatrix) : PCMatrix :=
  M * autMatrix
    (if f2ToBit (M 3 7) then pc6Aut * pc3Aut else 1)

theorem pcPeel2Matrix_pcMatrix (e : PCExponent) :
    pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix (pcMatrix e))) =
      autMatrix
        (peel2 (peel1 (peel0 (G2TwoSylowSubgroup.pcWord e)))) := by
  rw [pcPeel2Matrix, pcPeel1Matrix_pcMatrix]
  have hbit :
      ((peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))).1 (basis8 7)).x1 =
        extractBit2 (G2TwoSylowSubgroup.pcWord e) := by
    rfl
  rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_x1]
  rw [hbit, InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2.extractBit2_pcWord,
    f2ToBit_bitToF2]
  dsimp [peel2]
  split
  · rename_i h2
    have hc :
        ((peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))).1
            (basis8 7)).x1 = true := by
      rw [hbit, InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.extractBit2_pcWord]
      exact h2
    simp only [if_pos hc]
    rw [autMatrix_mul, autMatrix_mul]
    rw [← autMatrix_mul pc6Aut pc3Aut]
  · rename_i h2
    have hc :
        ¬(((peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))).1
            (basis8 7)).x1 = true) := by
      intro hc
      apply h2
      rw [hbit, InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.extractBit2_pcWord] at hc
      exact hc
    rw [if_neg hc, autMatrix_one]
    simp

def pcPivot4 (M : PCMatrix) : Bool := f2ToBit (M 6 2)

def pcPivot3 (M : PCMatrix) : Bool :=
  f2ToBit (M 4 3 + bitToF2 (pcPivot4 M))

theorem pcPivot4_pcPeel2Matrix (e : PCExponent) :
    pcPivot4 (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix (pcMatrix e)))) =
      extractBit4 (G2TwoSylowSubgroup.pcWord e) := by
  rw [pcPivot4, pcPeel2Matrix_pcMatrix]
  rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_y1]
  rw [f2ToBit_bitToF2]
  rfl

theorem pcPivot3_pcPeel2Matrix (e : PCExponent) :
    pcPivot3 (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix (pcMatrix e)))) =
      extractBit3 (G2TwoSylowSubgroup.pcWord e) := by
  rw [pcPivot3, pcPivot4_pcPeel2Matrix]
  rw [pcPeel2Matrix_pcMatrix]
  rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_x2]
  have hbool (a b : Bool) :
      f2ToBit (bitToF2 a + bitToF2 b) = (a ^^ b) := by
    cases a <;> cases b <;> rfl
  dsimp [extractBit3, extractBit4]
  exact hbool _ _

def pcPeel34Matrix (M : PCMatrix) : PCMatrix :=
  M * autMatrix (if pcPivot3 M then pc4Aut else 1) *
    autMatrix (if pcPivot4 M then pc5Aut else 1)

theorem pcPeel34Matrix_factor (M : PCMatrix) :
    pcPeel34Matrix M =
      M * autMatrix
        ((if pcPivot4 M then pc5Aut else 1) *
          (if pcPivot3 M then pc4Aut else 1)) := by
  rw [pcPeel34Matrix, autMatrix_mul]
  rw [mul_assoc]

theorem bool_eq_iff_xor_false (a b : Bool) :
    (a = b) ↔ (a ^^ b = false) := by
  cases a <;> cases b <;> simp

theorem pcPeel34Matrix_pcMatrix (e : PCExponent) :
    pcPeel34Matrix
        (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix (pcMatrix e)))) =
      autMatrix
        (peel34 (peel2 (peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))))) := by
  rw [pcPeel34Matrix_factor, pcPivot4_pcPeel2Matrix,
    pcPivot3_pcPeel2Matrix, pcPeel2Matrix_pcMatrix]
  cases h4 :
      ((peel2 (peel1 (peel0 (G2TwoSylowSubgroup.pcWord e)))).1
        (basis8 2)).y1 <;>
    cases h3 :
      ((peel2 (peel1 (peel0 (G2TwoSylowSubgroup.pcWord e)))).1
        (basis8 3)).x2 <;>
      simp [extractBit3, extractBit4, peel34, h3, h4, autMatrix_mul,
        autMatrix_one]

def pcPeel5Matrix (M : PCMatrix) : PCMatrix :=
  M * autMatrix (if f2ToBit (M 4 2) then pc6Aut else 1)

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
  rw [G2TwoSylowPCAutomorphisms.pc2Aut_inv_eq, autMatrix_mul]

theorem autMatrix_pc3Aut_inv :
    autMatrix pc3Aut⁻¹ = autMatrix pc3Aut * autMatrix pc6Aut := by
  rw [G2TwoSylowPCAutomorphisms.pc3Aut_inv_eq, autMatrix_mul]

theorem autMatrix_pc1Aut_inv :
    autMatrix pc1Aut⁻¹ = autMatrix pc1Aut := by
  rw [G2TwoSylowPCAutomorphisms.pc1Aut_inv_eq]

theorem autMatrix_pc4Aut_inv :
    autMatrix pc4Aut⁻¹ = autMatrix pc4Aut := by
  rw [G2TwoSylowPCAutomorphisms.pc4Aut_inv_eq]

theorem autMatrix_pc5Aut_inv :
    autMatrix pc5Aut⁻¹ = autMatrix pc5Aut := by
  rw [G2TwoSylowPCAutomorphisms.pc5Aut_inv_eq]

theorem autMatrix_pc6Aut_inv :
    autMatrix pc6Aut⁻¹ = autMatrix pc6Aut := by
  rw [G2TwoSylowPCAutomorphisms.pc6Aut_inv_eq]

theorem pcMatrix_eq_of_word_eq {e f : PCExponent}
    (h : G2TwoSylowSubgroup.pcWord e = G2TwoSylowSubgroup.pcWord f) :
    pcMatrix e = pcMatrix f := by
  exact congrArg autMatrix h

theorem pcWord_injective_of_matrix_recoveries
    (recover : Fin 6 → PCMatrix → F2)
    (hrecover : ∀ (k : Fin 6) (e : PCExponent),
      recover k (pcMatrix e) = bitToF2 (e k)) :
    Function.Injective G2TwoSylowSubgroup.pcWord := by
  intro e f h
  have hm : pcMatrix e = pcMatrix f := pcMatrix_eq_of_word_eq h
  funext k
  apply (bitToF2_eq_iff (e k) (f k)).mp
  rw [← hrecover k e, ← hrecover k f, hm]

theorem pcWord_range_card_of_matrix_recoveries
    (recover : Fin 6 → PCMatrix → F2)
    (hrecover : ∀ (k : Fin 6) (e : PCExponent),
      recover k (pcMatrix e) = bitToF2 (e k)) :
    Nat.card (Set.range G2TwoSylowSubgroup.pcWord) = 64 := by
  rw [Nat.card_range_of_injective
    (pcWord_injective_of_matrix_recoveries recover hrecover)]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

theorem sylowTwoSubgroup_card_ge_64_of_matrix_recoveries
    (recover : Fin 6 → PCMatrix → F2)
    (hrecover : ∀ (k : Fin 6) (e : PCExponent),
      recover k (pcMatrix e) = bitToF2 (e k)) :
    64 ≤ Nat.card G2TwoSylowSubgroup.sylowTwoSubgroup := by
  let f : PCExponent →
      {x : SplitOctF2Aut // x ∈ G2TwoSylowSubgroup.sylowTwoSubgroup} := fun e =>
    ⟨G2TwoSylowSubgroup.pcWord e, G2TwoSylowSubgroup.pcWord_mem_sylow e⟩
  have hf : Function.Injective f := by
    intro e g h
    apply pcWord_injective_of_matrix_recoveries recover hrecover
    exact congrArg Subtype.val h
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card,
    G2TwoSylowSubgroup.pcWordExp_card] at hc
  exact hc

theorem conjugate_injective {α β : Type*} [Group α]
    (w : α) (f : β → α) (hf : Function.Injective f) :
    Function.Injective (fun x => w * f x * w⁻¹) := by
  intro x y h
  apply hf
  have h' : (w * f x) * w⁻¹ = (w * f y) * w⁻¹ := by
    simpa only using h
  have h'' : w * f x = w * f y := mul_right_cancel h'
  exact mul_left_cancel h''


def pcPivot5 (M : PCMatrix) : Bool := f2ToBit (M 4 2)

theorem pcPivot5_pcPeel34Matrix (e : PCExponent) :
    pcPivot5 (pcPeel34Matrix (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix (pcMatrix e))))) =
      extractBit5 (G2TwoSylowSubgroup.pcWord e) := by
  rw [pcPivot5, pcPeel34Matrix_pcMatrix]
  rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_x2]
  rw [f2ToBit_bitToF2]
  rfl

def matrixRecover (k : Fin 6) (M : PCMatrix) : F2 :=
  match k with
  | 0 => pcRecover0 M
  | 1 => (pcPeel0Matrix M) 3 2
  | 2 => (pcPeel1Matrix (pcPeel0Matrix M)) 3 7
  | 3 => bitToF2 (pcPivot3 (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix M))))
  | 4 => bitToF2 (pcPivot4 (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix M))))
  | 5 => bitToF2 (pcPivot5 (pcPeel34Matrix (pcPeel2Matrix (pcPeel1Matrix (pcPeel0Matrix M)))))

theorem matrixRecover_pcMatrix (k : Fin 6) (e : PCExponent) :
    matrixRecover k (pcMatrix e) = bitToF2 (e k) := by
  fin_cases k
  · exact pcRecover0_pcMatrix e
  · dsimp [matrixRecover]
    rw [pcPeel0Matrix_pcMatrix]
    rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_x1]
    change bitToF2 (extractBit1 (G2TwoSylowSubgroup.pcWord e)) = _
    rw [extractBit1_pcWord]
  · dsimp [matrixRecover]
    rw [pcPeel1Matrix_pcMatrix]
    rw [InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier.autMatrix_entry_x1]
    change bitToF2 (extractBit2 (G2TwoSylowSubgroup.pcWord e)) = _
    rw [InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.extractBit2_pcWord]
  · dsimp [matrixRecover]
    rw [pcPivot3_pcPeel2Matrix]
    rw [extractBit3_pcWord]
  · dsimp [matrixRecover]
    rw [pcPivot4_pcPeel2Matrix]
    rw [extractBit4_pcWord]
  · dsimp [matrixRecover]
    rw [pcPivot5_pcPeel34Matrix]
    rw [extractBit5_pcWord]

theorem pcWord_injective_concrete :
    Function.Injective G2TwoSylowSubgroup.pcWord :=
  pcWord_injective_of_matrix_recoveries matrixRecover matrixRecover_pcMatrix

theorem pcWord_range_card_concrete :
    Nat.card (Set.range G2TwoSylowSubgroup.pcWord) = 64 :=
  pcWord_range_card_of_matrix_recoveries matrixRecover matrixRecover_pcMatrix

theorem sylowTwoSubgroup_card_ge_64_concrete :
    64 ≤ Nat.card G2TwoSylowSubgroup.sylowTwoSubgroup :=
  sylowTwoSubgroup_card_ge_64_of_matrix_recoveries matrixRecover matrixRecover_pcMatrix

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
