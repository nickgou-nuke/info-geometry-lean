import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import InfoGeometry.Algebra.Zorn.G2TwoPCConjugation

namespace InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication

open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCConjugation
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

theorem pcWord_oneAt_zero_mul_oneAt_zero :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 0) (oneAt 0)) := by
  rw [pcWord_oneAt_eq_generator]
  have hzero : pcCombine (oneAt 0) (oneAt 0) = (fun _ => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [hzero, pcWord_zero_eq_one]
  change pcGenerator 0 * pcGenerator 0 = 1
  change G2TwoSylowPCAutomorphisms.pc1Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut = 1
  have h : G2TwoSylowPCAutomorphisms.pc1Aut⁻¹ *
      G2TwoSylowPCAutomorphisms.pc1Aut = 1 := inv_mul_cancel _
  simpa [pc1Aut_inv_eq] using h

theorem pcWord_oneAt_one_mul_oneAt_one :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 1) (oneAt 1)) := by
  rw [pcWord_oneAt_eq_generator]
  have htarget : pcCombine (oneAt 1) (oneAt 1) = oneAt 5 := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc2Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
      G2TwoSylowPCAutomorphisms.pc6Aut
  exact pc2Aut_sq_eq_pc6Aut

theorem pcWord_oneAt_two_mul_oneAt_two :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 2)) := by
  rw [pcWord_oneAt_eq_generator]
  have htarget : pcCombine (oneAt 2) (oneAt 2) = oneAt 5 := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut =
      G2TwoSylowPCAutomorphisms.pc6Aut
  exact pc3Aut_sq_eq_pc6Aut

/- CAS-certified commuting coordinate step: the third and second PC factors
  commute, and their product is the corresponding normal-form word. -/
theorem pcWord_oneAt_two_mul_oneAt_one :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 1)) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
    G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 1))
  have h : G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc3Aut :=
    pc2Aut_comm_pc3Aut.symm
  rw [h]
  have hword :
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 1)) =
        G2TwoSylowPCAutomorphisms.pc2Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut := by
    dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm,
      pcCombine, oneAt, pcGenerator]
    simp
  exact hword.symm

/- CAS-certified adjacent commuting coordinate step. -/
theorem pcWord_oneAt_three_mul_oneAt_two :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 2)) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut =
    G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 2))
  rw [pc3Aut_comm_pc4Aut.symm]
  have hword :
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 2)) =
        G2TwoSylowPCAutomorphisms.pc3Aut *
          G2TwoSylowPCAutomorphisms.pc4Aut := by
    dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm,
      pcCombine, oneAt, pcGenerator]
    simp
  exact hword.symm

/- CAS-certified adjacent commuting coordinate step. -/
theorem pcWord_oneAt_four_mul_oneAt_three :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 3)) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut =
    G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 3))
  rw [pc4Aut_comm_pc5Aut.symm]
  have hword :
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 3)) =
        G2TwoSylowPCAutomorphisms.pc4Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
    dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm,
      pcCombine, oneAt, pcGenerator]
    simp
  exact hword.symm

/- CAS-certified adjacent commuting coordinate step. -/
theorem pcWord_oneAt_five_mul_oneAt_four :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 4)) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut =
    G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 4))
  rw [pc5Aut_comm_pc6Aut.symm]
  have hword :
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 4)) =
        G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut := by
    dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm,
      pcCombine, oneAt, pcGenerator]
    simp
  exact hword.symm

/- CAS-certified noncommutative coordinate step.  The target exponent
   `(true,true,true,true,false,true)` is the symbolic GF(2) product of the
   two input words; its proof below is only transport through the concrete
   coordinate maps, not a finite enumeration. -/
theorem pcWord_oneAt_one_mul_oneAt_zero :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => true
        | 2 => true
        | 3 => true
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  change pc1Fun (pc2Fun X) =
    pc6Fun (pc4Fun (pc3Fun (pc2Fun (pc1Fun X))))
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc1Fun, pc2Fun, pc3Fun, pc4Fun, pc6Fun]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pcWord_oneAt_one_mul_oneAt_zero_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 1) (oneAt 0)) := by
  have htarget : pcCombine (oneAt 1) (oneAt 0) = (fun i =>
        match i with
        | 0 => true
        | 1 => true
        | 2 => true
        | 3 => true
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_one_mul_oneAt_zero

/- CAS-certified product for the coordinate rows
   g₂ = e₂ + e₁ f₀ + f₂ and
   g₅ = e₂ f₀ + e₅ + f₅ in this specialization. -/
theorem pcWord_oneAt_two_mul_oneAt_zero :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, pcTermFun]
  simp [G2TwoSylowSubgroup.pcWordFun, G2TwoSylowSubgroup.pcTermFun]
  change pc1Fun (pc3Fun X) =
    pc6Fun (pc3Fun (pc1Fun X))
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [pc1Fun, pc3Fun, pc6Fun]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pcWord_oneAt_two_mul_oneAt_zero_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 0)) := by
  have htarget : pcCombine (oneAt 2) (oneAt 0) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_two_mul_oneAt_zero

theorem pcWord_oneAt_three_mul_oneAt_zero :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut = _
  rw [pc1Aut_comm_pc4Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_three_mul_oneAt_zero_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 0)) := by
  have htarget : pcCombine (oneAt 3) (oneAt 0) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_three_mul_oneAt_zero

theorem pcWord_oneAt_four_mul_oneAt_zero :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => true
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut = _
  have hconj := pc5Aut_conj_pc1Aut
  rw [pc5Aut_inv_eq] at hconj
  have hsq : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  have hmove : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut =
      G2TwoSylowPCAutomorphisms.pc1Aut *
        G2TwoSylowPCAutomorphisms.pc4Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
    calc
      _ = (G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc1Aut *
            G2TwoSylowPCAutomorphisms.pc5Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
            rw [mul_assoc]
            rw [hsq, mul_one]
      _ = _ := by rw [hconj]
  rw [hmove]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_four_mul_oneAt_zero_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 0)) := by
  have htarget : pcCombine (oneAt 4) (oneAt 0) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => true
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_four_mul_oneAt_zero

theorem pcWord_oneAt_five_mul_oneAt_zero :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut = _
  rw [pc1Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_five_mul_oneAt_zero_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 0) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 0)) := by
  have htarget : pcCombine (oneAt 5) (oneAt 0) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_five_mul_oneAt_zero

theorem pcWord_oneAt_four_mul_oneAt_one :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut = _
  have hconj := pc5Aut_conj_pc2Aut
  rw [pc5Aut_inv_eq] at hconj
  have hsq : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  have hmove : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
    calc
      _ = (G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc2Aut *
            G2TwoSylowPCAutomorphisms.pc5Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
            rw [mul_assoc, hsq, mul_one]
      _ = (G2TwoSylowPCAutomorphisms.pc2Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by rw [hconj]
  rw [hmove]
  rw [mul_assoc, pc5Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_four_mul_oneAt_one_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 1)) := by
  have htarget : pcCombine (oneAt 4) (oneAt 1) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_four_mul_oneAt_one

theorem pcWord_oneAt_four_mul_oneAt_two :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => true
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut = _
  have hconj := pc5Aut_conj_pc3Aut
  rw [pc5Aut_inv_eq] at hconj
  have hsq : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  have hmove : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut =
      G2TwoSylowPCAutomorphisms.pc3Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
    calc
      _ = (G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut *
            G2TwoSylowPCAutomorphisms.pc5Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
            rw [mul_assoc, hsq, mul_one]
      _ = (G2TwoSylowPCAutomorphisms.pc3Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by rw [hconj]
  rw [hmove, mul_assoc, pc5Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_four_mul_oneAt_two_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 2)) := by
  have htarget : pcCombine (oneAt 4) (oneAt 2) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => true
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_four_mul_oneAt_two

theorem pcWord_oneAt_five_mul_oneAt_one :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut = _
  rw [pc2Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_five_mul_oneAt_one_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 1)) := by
  have htarget : pcCombine (oneAt 5) (oneAt 1) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_five_mul_oneAt_one

theorem pcWord_oneAt_three_mul_oneAt_one :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut = _
  have hconj := pc4Aut_conj_pc2Aut
  rw [pc4Aut_inv_eq] at hconj
  have hsq : G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = 1 := by
    rw [← pc4Aut_inv_eq]
    exact inv_mul_cancel _
  have hmove : G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc4Aut := by
    calc
      _ = (G2TwoSylowPCAutomorphisms.pc4Aut *
          G2TwoSylowPCAutomorphisms.pc2Aut *
            G2TwoSylowPCAutomorphisms.pc4Aut) *
          G2TwoSylowPCAutomorphisms.pc4Aut := by
            rw [mul_assoc, hsq, mul_one]
      _ = (G2TwoSylowPCAutomorphisms.pc2Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut) *
          G2TwoSylowPCAutomorphisms.pc4Aut := by rw [hconj]
  rw [hmove, mul_assoc, pc4Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_three_mul_oneAt_one_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 1)) := by
  have htarget : pcCombine (oneAt 3) (oneAt 1) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_three_mul_oneAt_one

theorem pcWord_oneAt_five_mul_oneAt_two :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut = _
  rw [pc3Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_five_mul_oneAt_two_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 2)) := by
  have htarget : pcCombine (oneAt 5) (oneAt 2) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_five_mul_oneAt_two

theorem pcWord_oneAt_five_mul_oneAt_three :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = _
  rw [pc4Aut_comm_pc6Aut.symm]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_five_mul_oneAt_three_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 3)) := by
  have htarget : pcCombine (oneAt 5) (oneAt 3) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_five_mul_oneAt_three

theorem pcWord_oneAt_five_mul_oneAt_four_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 4)) := by
  have htarget : pcCombine (oneAt 5) (oneAt 4) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_five_mul_oneAt_four

theorem pcWord_oneAt_five_mul_oneAt_five :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (fun _ => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = _
  have hsq : G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = 1 := by
    rw [← pc6Aut_inv_eq]
    exact inv_mul_cancel _
  rw [hsq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_five_mul_oneAt_five_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 5) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 5)) := by
  have htarget : pcCombine (oneAt 5) (oneAt 5) = (fun _ => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_five_mul_oneAt_five

theorem pcWord_oneAt_three_mul_oneAt_five :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_three_mul_oneAt_five_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 5)) := by
  have htarget : pcCombine (oneAt 3) (oneAt 5) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_three_mul_oneAt_five

theorem pcWord_oneAt_two_mul_oneAt_five :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_two_mul_oneAt_five_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 5)) := by
  have htarget : pcCombine (oneAt 2) (oneAt 5) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_two_mul_oneAt_five

theorem pcWord_oneAt_one_mul_oneAt_five :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc2Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_one_mul_oneAt_five_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 1) (oneAt 5)) := by
  have htarget : pcCombine (oneAt 1) (oneAt 5) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_one_mul_oneAt_five

theorem pcWord_oneAt_zero_mul_oneAt_five :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc1Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_zero_mul_oneAt_five_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 0) (oneAt 5)) := by
  have htarget : pcCombine (oneAt 0) (oneAt 5) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_zero_mul_oneAt_five

theorem pcWord_oneAt_zero_mul_oneAt_four :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc1Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_zero_mul_oneAt_four_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 0) (oneAt 4)) := by
  have htarget : pcCombine (oneAt 0) (oneAt 4) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_zero_mul_oneAt_four

theorem pcWord_oneAt_zero_mul_oneAt_three :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc1Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_zero_mul_oneAt_three_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 0) (oneAt 3)) := by
  have htarget : pcCombine (oneAt 0) (oneAt 3) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_zero_mul_oneAt_three

theorem pcWord_oneAt_zero_mul_oneAt_two :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc1Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_zero_mul_oneAt_two_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 0) (oneAt 2)) := by
  have htarget : pcCombine (oneAt 0) (oneAt 2) = (fun i =>
        match i with
        | 0 => true
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_zero_mul_oneAt_two

theorem pcWord_oneAt_zero_mul_oneAt_one :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => true
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc1Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_zero_mul_oneAt_one_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 0) *
        G2TwoSylowSubgroup.pcWord (oneAt 1) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 0) (oneAt 1)) := by
  have htarget : pcCombine (oneAt 0) (oneAt 1) = (fun i =>
        match i with
        | 0 => true
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_zero_mul_oneAt_one

theorem pcWord_oneAt_one_mul_oneAt_four :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc2Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_one_mul_oneAt_four_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 1) (oneAt 4)) := by
  have htarget : pcCombine (oneAt 1) (oneAt 4) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_one_mul_oneAt_four

theorem pcWord_oneAt_one_mul_oneAt_three :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc2Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_one_mul_oneAt_three_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 1) (oneAt 3)) := by
  have htarget : pcCombine (oneAt 1) (oneAt 3) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => false
        | 3 => true
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_one_mul_oneAt_three

theorem pcWord_oneAt_one_mul_oneAt_two :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc2Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_one_mul_oneAt_two_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 1) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 1) (oneAt 2)) := by
  have htarget : pcCombine (oneAt 1) (oneAt 2) = (fun i =>
        match i with
        | 0 => false
        | 1 => true
        | 2 => true
        | 3 => false
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_one_mul_oneAt_two

theorem pcWord_oneAt_two_mul_oneAt_four :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => true
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_two_mul_oneAt_four_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 4)) := by
  have htarget : pcCombine (oneAt 2) (oneAt 4) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => false
        | 4 => true
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_two_mul_oneAt_four

theorem pcWord_oneAt_two_mul_oneAt_three :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => true
        | 4 => false
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_two_mul_oneAt_three_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 2) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 2) (oneAt 3)) := by
  have htarget : pcCombine (oneAt 2) (oneAt 3) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => true
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_two_mul_oneAt_three

theorem pcWord_oneAt_three_mul_oneAt_two_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 2) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 2)) := by
  have htarget : pcCombine (oneAt 3) (oneAt 2) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => true
        | 3 => true
        | 4 => false
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_three_mul_oneAt_two

theorem pcWord_oneAt_three_mul_oneAt_four :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => true
        | 5 => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_three_mul_oneAt_four_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 4)) := by
  have htarget : pcCombine (oneAt 3) (oneAt 4) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => true
        | 4 => true
        | 5 => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_three_mul_oneAt_four

theorem pcWord_oneAt_four_mul_oneAt_five :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => true) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = _
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_four_mul_oneAt_five_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 5) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 5)) := by
  have htarget : pcCombine (oneAt 4) (oneAt 5) = (fun i =>
        match i with
        | 0 => false
        | 1 => false
        | 2 => false
        | 3 => false
        | 4 => true
        | 5 => true) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_four_mul_oneAt_five

theorem pcWord_oneAt_four_mul_oneAt_four :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (fun _ => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = _
  have hsq : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  rw [hsq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_four_mul_oneAt_four_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 4) *
        G2TwoSylowSubgroup.pcWord (oneAt 4) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 4) (oneAt 4)) := by
  have htarget : pcCombine (oneAt 4) (oneAt 4) = (fun _ => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_four_mul_oneAt_four

theorem pcWord_oneAt_three_mul_oneAt_three :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (fun _ => false) := by
  rw [pcWord_oneAt_eq_generator]
  change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = _
  have hsq : G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut = 1 := by
    rw [← pc4Aut_inv_eq]
    exact inv_mul_cancel _
  rw [hsq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [pcWord_apply]
  dsimp [pcGenerator, G2TwoSylowSubgroup.pcWord,
    G2TwoSylowSubgroup.pcTerm, G2TwoSylowSubgroup.pcWordFun,
    pcTermFun]
  rfl

theorem pcWord_oneAt_three_mul_oneAt_three_pcCombine :
    G2TwoSylowSubgroup.pcWord (oneAt 3) *
        G2TwoSylowSubgroup.pcWord (oneAt 3) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 3) (oneAt 3)) := by
  have htarget : pcCombine (oneAt 3) (oneAt 3) = (fun _ => false) := by
    funext i
    fin_cases i <;> simp [pcCombine, oneAt]
  rw [htarget]
  exact pcWord_oneAt_three_mul_oneAt_three

theorem pcWord_oneAt_mul_self (i : Fin 6) :
    G2TwoSylowSubgroup.pcWord (oneAt i) *
        G2TwoSylowSubgroup.pcWord (oneAt i) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt i) (oneAt i)) := by
  fin_cases i
  · exact pcWord_oneAt_zero_mul_oneAt_zero
  · exact pcWord_oneAt_one_mul_oneAt_one
  · exact pcWord_oneAt_two_mul_oneAt_two
  · exact pcWord_oneAt_three_mul_oneAt_three
  · exact pcWord_oneAt_four_mul_oneAt_four
  · exact pcWord_oneAt_five_mul_oneAt_five

theorem pcWord_oneAt_mul (i j : Fin 6) :
    G2TwoSylowSubgroup.pcWord (oneAt i) *
        G2TwoSylowSubgroup.pcWord (oneAt j) =
      G2TwoSylowSubgroup.pcWord (pcCombine (oneAt i) (oneAt j)) := by
  fin_cases i <;> fin_cases j
  · exact pcWord_oneAt_zero_mul_oneAt_zero
  · exact pcWord_oneAt_zero_mul_oneAt_one_pcCombine
  · exact pcWord_oneAt_zero_mul_oneAt_two_pcCombine
  · exact pcWord_oneAt_zero_mul_oneAt_three_pcCombine
  · exact pcWord_oneAt_zero_mul_oneAt_four_pcCombine
  · exact pcWord_oneAt_zero_mul_oneAt_five_pcCombine
  · exact pcWord_oneAt_one_mul_oneAt_zero_pcCombine
  · exact pcWord_oneAt_one_mul_oneAt_one
  · exact pcWord_oneAt_one_mul_oneAt_two_pcCombine
  · exact pcWord_oneAt_one_mul_oneAt_three_pcCombine
  · exact pcWord_oneAt_one_mul_oneAt_four_pcCombine
  · exact pcWord_oneAt_one_mul_oneAt_five_pcCombine
  · exact pcWord_oneAt_two_mul_oneAt_zero_pcCombine
  · exact pcWord_oneAt_two_mul_oneAt_one
  · exact pcWord_oneAt_two_mul_oneAt_two
  · exact pcWord_oneAt_two_mul_oneAt_three_pcCombine
  · exact pcWord_oneAt_two_mul_oneAt_four_pcCombine
  · exact pcWord_oneAt_two_mul_oneAt_five_pcCombine
  · exact pcWord_oneAt_three_mul_oneAt_zero_pcCombine
  · exact pcWord_oneAt_three_mul_oneAt_one_pcCombine
  · exact pcWord_oneAt_three_mul_oneAt_two_pcCombine
  · exact pcWord_oneAt_three_mul_oneAt_three
  · exact pcWord_oneAt_three_mul_oneAt_four_pcCombine
  · exact pcWord_oneAt_three_mul_oneAt_five_pcCombine
  · exact pcWord_oneAt_four_mul_oneAt_zero_pcCombine
  · exact pcWord_oneAt_four_mul_oneAt_one_pcCombine
  · exact pcWord_oneAt_four_mul_oneAt_two_pcCombine
  · exact pcWord_oneAt_four_mul_oneAt_three
  · exact pcWord_oneAt_four_mul_oneAt_four
  · exact pcWord_oneAt_four_mul_oneAt_five_pcCombine
  · exact pcWord_oneAt_five_mul_oneAt_zero_pcCombine
  · exact pcWord_oneAt_five_mul_oneAt_one_pcCombine
  · exact pcWord_oneAt_five_mul_oneAt_two_pcCombine
  · exact pcWord_oneAt_five_mul_oneAt_three_pcCombine
  · exact pcWord_oneAt_five_mul_oneAt_four_pcCombine
  · exact pcWord_oneAt_five_mul_oneAt_five

theorem pcWord_oneAtBit_mul (i j : Fin 6) (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit i b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit j c) =
      G2TwoSylowSubgroup.pcWord
        (pcCombine (oneAtBit i b) (oneAtBit j c)) := by
  cases b
  · cases c
    · dsimp [oneAtBit]
      rw [pcWord_zeroPC_eq_one, one_mul, pcCombine_zero_left, pcWord_zeroPC_eq_one]
    · dsimp [oneAtBit]
      rw [pcWord_zeroPC_eq_one, one_mul, pcCombine_zero_left]
  · cases c
    · dsimp [oneAtBit]
      rw [pcWord_zeroPC_eq_one, mul_one, pcCombine_zero_right]
    · dsimp [oneAtBit]
      exact pcWord_oneAt_mul i j

end InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication
