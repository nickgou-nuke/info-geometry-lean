import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

namespace InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector

open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication
open InfoGeometry.Algebra.Zorn.G2TwoPCConjugation
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

theorem swap_nested_product {G : Type*} [Group G]
    (a b c d : G) (h : b * c = c * b) :
    a * (b * (c * d)) = a * (c * (b * d)) := by
  rw [← mul_assoc b c d, h, mul_assoc]

private def toggleLast (e : PCExponent) (c : Bool) : PCExponent :=
  fun i => if i = 5 then e i ^^ c else e i

private def toggleZero (e : PCExponent) (c : Bool) : PCExponent :=
  fun i =>
    match i with
    | 0 => e 0 ^^ c
    | 1 => e 1
    | 2 => e 2 ^^ (e 1 && c)
    | 3 => e 3 ^^ (e 1 && c) ^^ (e 4 && c)
    | 4 => e 4
    | 5 => e 5 ^^ (e 1 && e 2 && c) ^^ (e 1 && c) ^^ (e 2 && c)

private theorem pcCombine_oneAtBit_zero (e : PCExponent) (c : Bool) :
    pcCombine e (oneAtBit 0 c) = toggleZero e c := by
  funext i
  fin_cases i <;>
    dsimp [toggleZero, pcCombine, oneAtBit] <;>
    cases c <;> cases e 1 <;> cases e 2 <;> cases e 4 <;>
    simp [oneAt, zeroPC]

private def pcPrefix (e : PCExponent) :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut :=
  G2TwoSylowSubgroup.pcWord (oneAtBit 0 (e 0)) *
    G2TwoSylowSubgroup.pcWord (oneAtBit 1 (e 1)) *
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2)) *
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4))

private theorem pcWord_eq_prefix_mul_last (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e =
      pcPrefix e * G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
  rw [pcWord_factorized]
  simp only [pcPrefix]

theorem pcWord_mul_oneAtBit_five (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e * G2TwoSylowSubgroup.pcWord (oneAtBit 5 c) =
      G2TwoSylowSubgroup.pcWord (toggleLast e c) := by
  rw [pcWord_eq_prefix_mul_last]
  rw [mul_assoc,
    InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
  rw [pcWord_eq_prefix_mul_last (toggleLast e c)]
  have hbits :
      pcCombine (oneAtBit 5 (e 5)) (oneAtBit 5 c) =
        oneAtBit 5 (toggleLast e c 5) := by
    funext i
    fin_cases i <;> cases he : e 5 <;> cases hc : c <;>
      simp [toggleLast, pcCombine, oneAtBit, oneAt, zeroPC, he, hc]
  have hp : pcPrefix e = pcPrefix (toggleLast e c) := by
    dsimp [pcPrefix]
    congr 1 <;> simp [toggleLast]
  rw [hp]
  rw [hbits]

theorem pcWord_mul_oneAtBit_zero (e : PCExponent) (j : Fin 6) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit j false) =
      G2TwoSylowSubgroup.pcWord e := by
  rw [pcWord_oneAtBit]
  simp

private def toggleThree (e : PCExponent) (c : Bool) : PCExponent :=
  fun i => if i = 3 then e i ^^ c else e i

theorem pcWord_mul_oneAtBit_three (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 c) =
      G2TwoSylowSubgroup.pcWord (toggleThree e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have h : toggleThree e false = e := by
      funext i
      fin_cases i <;> simp [toggleThree]
    rw [h]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleThree e true)]
    simp only [mul_assoc]
    have hswap53 :
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
      rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      have h : pcCombine (oneAtBit 5 (e 5)) (oneAtBit 3 true) =
          pcCombine (oneAtBit 3 true) (oneAtBit 5 (e 5)) := by
        funext i
        fin_cases i <;> cases he : e 5 <;>
          simp [pcCombine, oneAtBit, oneAt, zeroPC, he]
      rw [h]
    have hswap43 :
        G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) := by
      rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      have h : pcCombine (oneAtBit 4 (e 4)) (oneAtBit 3 true) =
          pcCombine (oneAtBit 3 true) (oneAtBit 4 (e 4)) := by
        funext i
        fin_cases i <;> cases he : e 4 <;>
          simp [pcCombine, oneAtBit, oneAt, zeroPC, he]
      rw [h]
    have htail :
        G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) := by
      simpa using swap_nested_product 1 _ _ _ hswap43
    rw [hswap53, htail]
    have hcollect :
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
                G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)))) =
          G2TwoSylowSubgroup.pcWord
              (pcCombine (oneAtBit 3 (e 3)) (oneAtBit 3 true)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) := by
      rw [← mul_assoc, InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
    rw [hcollect]
    cases he : e 3
    · simp [toggleThree, oneAtBit, oneAt, zeroPC, he,
        pcCombine_zero_left]
    · simp [toggleThree, oneAtBit, oneAt, zeroPC, he]
      have h : pcCombine (oneAt 3) (oneAt 3) = zeroPC := by
        funext i
        fin_cases i <;> simp [pcCombine, oneAt, zeroPC]
      rw [h]

private def toggleFour (e : PCExponent) (c : Bool) : PCExponent :=
  fun i => if i = 4 then e i ^^ c else e i

theorem pcWord_mul_oneAtBit_four (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 4 c) =
      G2TwoSylowSubgroup.pcWord (toggleFour e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have h : toggleFour e false = e := by
      funext i
      fin_cases i <;> simp [toggleFour]
    rw [h]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleFour e true)]
    simp only [mul_assoc]
    have hswap54 :
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
      rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      have h : pcCombine (oneAtBit 5 (e 5)) (oneAtBit 4 true) =
          pcCombine (oneAtBit 4 true) (oneAtBit 5 (e 5)) := by
        funext i
        fin_cases i <;> cases he : e 5 <;>
          simp [pcCombine, oneAtBit, oneAt, zeroPC, he]
      rw [h]
    rw [hswap54]
    have hcollect :
        G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) =
          G2TwoSylowSubgroup.pcWord
              (pcCombine (oneAtBit 4 (e 4)) (oneAtBit 4 true)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
      rw [← mul_assoc, InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
    rw [hcollect]
    cases he : e 4
    · simp [toggleFour, oneAtBit, oneAt, zeroPC, he,
        pcCombine_zero_left]
    · simp [toggleFour, oneAtBit, oneAt, zeroPC, he]
      have h : pcCombine (oneAt 4) (oneAt 4) = zeroPC := by
        funext i
        fin_cases i <;> simp [pcCombine, oneAt, zeroPC]
      rw [h]

theorem pcWord_oneAtBit_five_comm_two (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
    InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
  have h : pcCombine (oneAtBit 5 b) (oneAtBit 2 c) =
      pcCombine (oneAtBit 2 c) (oneAtBit 5 b) := by
    funext i
    fin_cases i <;> cases b <;> cases c <;>
      simp [pcCombine, oneAtBit, oneAt, zeroPC]
  rw [h]

/-
private def toggleTwo (e : PCExponent) (c : Bool) : PCExponent :=
  fun i =>
    if i = 2 then e i ^^ c
    else if i = 5 then e i ^^ (c && e 2) ^^ (c && e 4)
    else e i

theorem pcWord_mul_oneAtBit_two (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord (toggleTwo e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have h : toggleTwo e false = e := by
      funext i
      fin_cases i <;> simp [toggleTwo]
    rw [h]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleTwo e true)]
    simp only [mul_assoc]
    have hswap52 :
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
      exact pcWord_oneAtBit_five_comm_two (e 5) true
    rw [hswap52]
    cases he4 : e 4
    · have hswap32 :
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) =
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) := by
        rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
          InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
        have h : pcCombine (oneAtBit 3 (e 3)) (oneAtBit 2 true) =
            pcCombine (oneAtBit 2 true) (oneAtBit 3 (e 3)) := by
          funext i
          fin_cases i <;> cases he : e 3 <;>
            simp [pcCombine, oneAtBit, oneAt, zeroPC, he]
        rw [h]
      rw [hswap32]
      rw [← mul_assoc,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      cases he2 : e 2 <;>
        simp [toggleTwo, oneAtBit, oneAt, zeroPC, he2, he4,
          pcCombine_zero_left]
    · have h4 :=
          InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAt_four_mul_oneAt_two
      rw [h4]
      rw [← mul_assoc,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAt_mul]
      cases he2 : e 2 <;>
        simp [toggleTwo, oneAtBit, oneAt, zeroPC, he2, he4]
 -/

theorem pcWord_oneAtBit_four_mul_two (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord
        (pcCombine (oneAtBit 4 b) (oneAtBit 2 c)) := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]

/-
private def toggleTwoCore (e : PCExponent) (c : Bool) : PCExponent :=
  fun i =>
    if i = 2 then e i ^^ c
    else if i = 5 then e i ^^ (c && e 2) ^^ (c && e 4)
    else e i

theorem pcWord_mul_oneAtBit_two (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord (toggleTwoCore e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have h : toggleTwoCore e false = e := by
      funext i
      fin_cases i <;> simp [toggleTwoCore]
    rw [h]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleTwoCore e true)]
    simp only [mul_assoc]
    have hswap53 :
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
      exact pcWord_oneAtBit_five_comm_two (e 5) true
    rw [hswap53]
    have hswap32 :
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) := by
      rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      have h : pcCombine (oneAtBit 3 (e 3)) (oneAtBit 2 true) =
          pcCombine (oneAtBit 2 true) (oneAtBit 3 (e 3)) := by
        funext i
        fin_cases i <;> cases he : e 3 <;>
          simp [pcCombine, oneAtBit, oneAt, zeroPC, he]
      rw [h]
    cases he4 : e 4
    · have h4zero :
          G2TwoSylowSubgroup.pcWord (oneAtBit 4 false) = 1 := by
        rw [pcWord_oneAtBit]
        simp
      rw [h4zero, one_mul]
      have htail := swap_nested_product 1
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)))
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true))
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) hswap32
      rw [htail]
      rw [← mul_assoc,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      cases he2 : e 2 <;>
        simp [toggleTwoCore, oneAtBit, oneAt, zeroPC, he2, he4,
          pcCombine_zero_left]
    · have htail :
          G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
                G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) =
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
                G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5))) := by
        calc
          _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 2 true)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
                rw [← mul_assoc]
          _ = G2TwoSylowSubgroup.pcWord (pcCombine (oneAtBit 4 true)
                (oneAtBit 2 true)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5)) := by
                rw [pcWord_oneAtBit_four_mul_two]
          _ = _ := by
            rw [← mul_assoc]
            exact (swap_nested_product 1 _ _ _ hswap32).symm
      rw [htail]
      rw [← mul_assoc,
        InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
      cases he2 : e 2 <;>
        simp [toggleTwoCore, oneAtBit, oneAt, zeroPC, he2, he4]
 -/

/-
theorem pcWord_four_two_five_tail (b d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) := by
  cases b
  · have hzero : G2TwoSylowSubgroup.pcWord (oneAtBit 4 false) = 1 := by
      rw [pcWord_oneAtBit]
      simp
    rw [hzero, one_mul]
  · calc
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 true)) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d) := by
            rw [← mul_assoc]
      _ = G2TwoSylowSubgroup.pcWord
          (pcCombine (oneAtBit 4 true) (oneAtBit 2 true)) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d) := by
            rw [pcWord_oneAtBit_four_mul_two]
      _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [pcWord_oneAtBit_mul]
 -/

theorem pcWord_oneAtBit_three_comm_two (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
    InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
  have h : pcCombine (oneAtBit 3 b) (oneAtBit 2 c) =
      pcCombine (oneAtBit 2 c) (oneAtBit 3 b) := by
    funext i
    fin_cases i <;> cases b <;> cases c <;>
      simp [pcCombine, oneAtBit, oneAt, zeroPC]
  rw [h]

/-
theorem pcWord_four_two_five_collect (b c d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ (b && c)))) := by
  cases b <;> cases c <;> cases d
  all_goals simp [pcWord_oneAtBit]
 -/

theorem pcWord_four_two_generator_transport :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) := by
  change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut =
    G2TwoSylowPCAutomorphisms.pc3Aut *
      (G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut)
  have hconj := pc5Aut_conj_pc3Aut
  rw [pc5Aut_inv_eq] at hconj
  have hsq : G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  calc
    _ = (G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc3Aut *
        G2TwoSylowPCAutomorphisms.pc5Aut) *
        G2TwoSylowPCAutomorphisms.pc5Aut := by
          rw [mul_assoc, hsq, mul_one]
    _ = (G2TwoSylowPCAutomorphisms.pc3Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut) *
        G2TwoSylowPCAutomorphisms.pc5Aut := by rw [hconj]
    _ = G2TwoSylowPCAutomorphisms.pc3Aut *
        (G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut) := by
          rw [mul_assoc, pc5Aut_comm_pc6Aut]

theorem pcWord_four_two_five_collect (b c d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ (b && c)))) := by
  cases b
  · rw [pcWord_oneAtBit]
    simp
  · cases c
    · have hzero2 :
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 false) = 1 := by
        rw [pcWord_oneAtBit]
        simp
      simp [hzero2]
    · cases d
      · simpa using pcWord_four_two_generator_transport
      · calc
          _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 2 true)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) := by
                rw [← mul_assoc]
          _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) *
                G2TwoSylowSubgroup.pcWord (oneAtBit 5 true))) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) := by
                rw [pcWord_four_two_generator_transport]
          _ = G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 4 true) := by
                have h5 :
                    G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) *
                        G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) = 1 := by
                  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
                  have hz : pcCombine (oneAtBit 5 true) (oneAtBit 5 true) = zeroPC := by
                    funext i
                    fin_cases i <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
                  rw [hz]
                  exact pcWord_zero_eq_one
                rw [← mul_assoc, mul_assoc, h5, mul_one]

theorem pcWord_two_two_bit (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 (b ^^ c)) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b && c)) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · rw [pcWord_oneAtBit, pcWord_oneAtBit, pcWord_oneAtBit, pcWord_oneAtBit]
    simp
  · rw [pcWord_oneAtBit, pcWord_oneAtBit, pcWord_oneAtBit, pcWord_oneAtBit]
    simp
  · simpa [oneAtBit, oneAt] using
      (InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAt_two_mul_oneAt_two)

theorem pcWord_oneAtBit_five_comm_three (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 3 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
    InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
  have h : pcCombine (oneAtBit 5 b) (oneAtBit 3 c) =
      pcCombine (oneAtBit 3 c) (oneAtBit 5 b) := by
    funext i
    fin_cases i <;> cases b <;> cases c <;>
      simp [pcCombine, oneAtBit, oneAt, zeroPC]
  rw [h]

theorem pcWord_oneAtBit_five_comm_four (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 4 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 4 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul,
    InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
  have h : pcCombine (oneAtBit 5 b) (oneAtBit 4 c) =
      pcCombine (oneAtBit 4 c) (oneAtBit 5 b) := by
    funext i
    fin_cases i <;> cases b <;> cases c <;>
      simp [pcCombine, oneAtBit, oneAt, zeroPC]
  rw [h]

theorem pcWord_oneAtBit_five_comm_one (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · calc
      _ = G2TwoSylowSubgroup.pcWord (pcCombine (oneAt 5) (oneAt 1)) :=
        pcWord_oneAt_five_mul_oneAt_one_pcCombine
      _ = _ :=
        pcWord_oneAt_one_mul_oneAt_five_pcCombine.symm
theorem pc5Aut_mul_pc2Aut_transport :
    G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut := by
  have hconj := pc5Aut_conj_pc2Aut
  rw [pc5Aut_inv_eq] at hconj
  have hsq :
      G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  calc
    _ = (G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut) *
            G2TwoSylowPCAutomorphisms.pc5Aut := by
      rw [mul_assoc, hsq, mul_one]
    _ = (G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by rw [hconj]
    _ = G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut := by
      rw [mul_assoc, ← pc5Aut_comm_pc6Aut, ← mul_assoc]

theorem pc5Aut_mul_pc1Aut_transport :
    G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc1Aut =
      G2TwoSylowPCAutomorphisms.pc1Aut *
        G2TwoSylowPCAutomorphisms.pc4Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut := by
  have hconj := pc5Aut_conj_pc1Aut
  rw [pc5Aut_inv_eq] at hconj
  have hsq :
      G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut = 1 := by
    rw [← pc5Aut_inv_eq]
    exact inv_mul_cancel _
  calc
    _ = (G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc1Aut *
          G2TwoSylowPCAutomorphisms.pc5Aut) *
            G2TwoSylowPCAutomorphisms.pc5Aut := by
      rw [mul_assoc, hsq, mul_one]
    _ = (G2TwoSylowPCAutomorphisms.pc1Aut *
        G2TwoSylowPCAutomorphisms.pc4Aut) *
          G2TwoSylowPCAutomorphisms.pc5Aut := by rw [hconj]
    _ = _ := by rw [mul_assoc]

theorem pcWord_oneAtBit_four_transport_zero (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (b && c)) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 4 b)) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut =
        G2TwoSylowPCAutomorphisms.pc1Aut *
          (G2TwoSylowPCAutomorphisms.pc4Aut *
            G2TwoSylowPCAutomorphisms.pc5Aut)
    exact pc5Aut_mul_pc1Aut_transport

theorem pcWord_oneAtBit_three_comm_zero (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut =
        G2TwoSylowPCAutomorphisms.pc1Aut *
          G2TwoSylowPCAutomorphisms.pc4Aut
    exact pc1Aut_comm_pc4Aut.symm

theorem pcWord_oneAtBit_five_comm_zero (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut =
        G2TwoSylowPCAutomorphisms.pc1Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut
    exact pc1Aut_comm_pc6Aut.symm

private theorem pcWord_oneAtBit_three_comm_four (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 4 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 4 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc5Aut =
        G2TwoSylowPCAutomorphisms.pc5Aut *
          G2TwoSylowPCAutomorphisms.pc4Aut
    exact pc4Aut_comm_pc5Aut

private theorem pcWord_four_to_six_transport_zero
    (d f c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 f) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 0 c)) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (d && c)) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 f))) := by
  rw [pcWord_oneAtBit_five_comm_zero f c]
  rw [← mul_assoc
    (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d))
    (G2TwoSylowSubgroup.pcWord (oneAtBit 0 c))
    (G2TwoSylowSubgroup.pcWord (oneAtBit 5 f))]
  rw [pcWord_oneAtBit_four_transport_zero d c]
  rw [mul_assoc]
  simp only [mul_assoc]

private theorem pcWord_three_tail_transport_zero
    (b d f c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 f) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 0 c))) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (b ^^ (d && c))) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 f))) := by
  rw [pcWord_four_to_six_transport_zero d f c]
  rw [← mul_assoc
    (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b))
    (G2TwoSylowSubgroup.pcWord (oneAtBit 0 c))
    (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (d && c)) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 f))),
    pcWord_oneAtBit_three_comm_zero b c,
    mul_assoc]
  have hbits :
      pcCombine (oneAtBit 3 b) (oneAtBit 3 (d && c)) =
        oneAtBit 3 (b ^^ (d && c)) := by
    funext i
    fin_cases i <;> cases b <;> cases d <;> cases c <;>
      simp [pcCombine, oneAtBit, oneAt, zeroPC]
  rw [← mul_assoc
    (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b))
    (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (d && c)))
    (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 5 f)))]
  rw [pcWord_oneAtBit_mul 3 3 b (d && c)]
  rw [hbits]

theorem pc3Aut_mul_pc1Aut_transport :
    G2TwoSylowPCAutomorphisms.pc3Aut *
        G2TwoSylowPCAutomorphisms.pc1Aut =
      G2TwoSylowPCAutomorphisms.pc1Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut := by
  have hconj := pc3Aut_conj_pc1Aut
  have hconj' := congrArg
      (fun z => G2TwoSylowPCAutomorphisms.pc3Aut * z) hconj
  change G2TwoSylowPCAutomorphisms.pc3Aut *
      (G2TwoSylowPCAutomorphisms.pc3Aut⁻¹ *
        G2TwoSylowPCAutomorphisms.pc1Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut) =
    G2TwoSylowPCAutomorphisms.pc3Aut *
      (G2TwoSylowPCAutomorphisms.pc1Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut) at hconj'
  have hleft :
      G2TwoSylowPCAutomorphisms.pc1Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut =
        G2TwoSylowPCAutomorphisms.pc3Aut *
          (G2TwoSylowPCAutomorphisms.pc1Aut *
            G2TwoSylowPCAutomorphisms.pc6Aut) := by
    rw [← mul_assoc
      G2TwoSylowPCAutomorphisms.pc3Aut
      (G2TwoSylowPCAutomorphisms.pc3Aut⁻¹ *
        G2TwoSylowPCAutomorphisms.pc1Aut)
      G2TwoSylowPCAutomorphisms.pc3Aut,
      ← mul_assoc G2TwoSylowPCAutomorphisms.pc3Aut
        G2TwoSylowPCAutomorphisms.pc3Aut⁻¹
        G2TwoSylowPCAutomorphisms.pc1Aut,
      mul_inv_cancel, one_mul] at hconj'
    exact hconj'
  have hleft' :
      G2TwoSylowPCAutomorphisms.pc1Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut =
        (G2TwoSylowPCAutomorphisms.pc3Aut *
          G2TwoSylowPCAutomorphisms.pc1Aut) *
            G2TwoSylowPCAutomorphisms.pc6Aut := by
    simpa [mul_assoc] using hleft
  have hsq :
      G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut = 1 := by
    rw [← pc6Aut_inv_eq]
    exact inv_mul_cancel _
  calc
    _ = (G2TwoSylowPCAutomorphisms.pc3Aut *
        G2TwoSylowPCAutomorphisms.pc1Aut) *
          G2TwoSylowPCAutomorphisms.pc6Aut *
            G2TwoSylowPCAutomorphisms.pc6Aut := by
      simp [mul_assoc, hsq]
    _ = (G2TwoSylowPCAutomorphisms.pc1Aut *
        G2TwoSylowPCAutomorphisms.pc3Aut) *
          G2TwoSylowPCAutomorphisms.pc6Aut := by
      rw [← hleft']
    _ = G2TwoSylowPCAutomorphisms.pc1Aut *
        (G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut) := by
      rw [mul_assoc, pc3Aut_comm_pc6Aut]

theorem pcWord_oneAtBit_two_transport_zero (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b && c)) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 b)) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut =
        G2TwoSylowPCAutomorphisms.pc1Aut *
          (G2TwoSylowPCAutomorphisms.pc6Aut *
            G2TwoSylowPCAutomorphisms.pc3Aut)
    exact pc3Aut_mul_pc1Aut_transport

theorem pcWord_oneAtBit_one_transport_zero (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 1 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 1 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 2 (b && c)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (b && c)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b && c))))) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc2Aut *
      G2TwoSylowPCAutomorphisms.pc1Aut =
        G2TwoSylowPCAutomorphisms.pc1Aut *
          (G2TwoSylowPCAutomorphisms.pc2Aut *
            (G2TwoSylowPCAutomorphisms.pc3Aut *
              (G2TwoSylowPCAutomorphisms.pc4Aut *
                G2TwoSylowPCAutomorphisms.pc6Aut)))
    have h := pcWord_oneAt_one_mul_oneAt_zero
    rw [pcWord_oneAt_eq_generator, pcWord_oneAt_eq_generator] at h
    change G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc1Aut =
      G2TwoSylowPCAutomorphisms.pc1Aut *
        (G2TwoSylowPCAutomorphisms.pc2Aut *
          (G2TwoSylowPCAutomorphisms.pc3Aut *
            (G2TwoSylowPCAutomorphisms.pc4Aut *
              G2TwoSylowPCAutomorphisms.pc6Aut))) at h
    exact h

theorem pc4Aut_mul_pc2Aut_transport :
    G2TwoSylowPCAutomorphisms.pc4Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc4Aut *
          G2TwoSylowPCAutomorphisms.pc6Aut := by
  have hconj := pc4Aut_conj_pc2Aut
  rw [pc4Aut_inv_eq] at hconj
  have hsq :
      G2TwoSylowPCAutomorphisms.pc4Aut *
          G2TwoSylowPCAutomorphisms.pc4Aut = 1 := by
    rw [← pc4Aut_inv_eq]
    exact inv_mul_cancel _
  calc
    _ = (G2TwoSylowPCAutomorphisms.pc4Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut *
          G2TwoSylowPCAutomorphisms.pc4Aut) *
            G2TwoSylowPCAutomorphisms.pc4Aut := by
      rw [mul_assoc, hsq, mul_one]
    _ = (G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut) *
          G2TwoSylowPCAutomorphisms.pc4Aut := by rw [hconj]
    _ = G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc4Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut := by
      rw [mul_assoc, pc4Aut_comm_pc6Aut.symm, ← mul_assoc]

theorem pcWord_oneAtBit_four_transport_one (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b && c))) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
        G2TwoSylowPCAutomorphisms.pc2Aut *
          (G2TwoSylowPCAutomorphisms.pc5Aut *
            G2TwoSylowPCAutomorphisms.pc6Aut)
    rw [pc5Aut_mul_pc2Aut_transport, mul_assoc]

theorem pcWord_oneAtBit_three_transport_one (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b && c))) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc4Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
        G2TwoSylowPCAutomorphisms.pc2Aut *
          (G2TwoSylowPCAutomorphisms.pc4Aut *
            G2TwoSylowPCAutomorphisms.pc6Aut)
    rw [pc4Aut_mul_pc2Aut_transport, mul_assoc]

theorem pcWord_oneAtBit_two_comm_one (b c : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) := by
  cases b <;> cases c
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc3Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut =
        G2TwoSylowPCAutomorphisms.pc2Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut
    exact pc2Aut_comm_pc3Aut.symm

private theorem pcWord_five_bit_mul (b d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 d) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b ^^ d)) := by
  cases b <;> cases d
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · simp [pcWord_oneAtBit]
  · change G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc6Aut = 1
    rw [← pc6Aut_inv_eq]
    exact inv_mul_cancel _

private theorem pcWord_four_tail_transport (b d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b))) := by
  rw [← mul_assoc, pcWord_oneAtBit_four_transport_one b true]
  simp only [Bool.and_true]
  rw [mul_assoc, mul_assoc, pcWord_five_bit_mul]
  simp [Bool.xor_comm]

private theorem pcWord_three_tail_transport (a b d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 d) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 1 true))) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b ^^ a)))) := by
  rw [pcWord_oneAtBit_five_comm_one d true]
  rw [pcWord_four_tail_transport b d]
  rw [← mul_assoc, pcWord_oneAtBit_three_transport_one a true]
  simp only [Bool.and_true]
  rw [mul_assoc, mul_assoc]
  rw [← mul_assoc
      (G2TwoSylowSubgroup.pcWord (oneAtBit 5 a))
      (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b))
      (G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b)))]
  rw [pcWord_oneAtBit_five_comm_four a b]
  rw [mul_assoc, pcWord_five_bit_mul]
  simp [Bool.xor_assoc, Bool.xor_comm]

private theorem pcWord_two_move_one (a : Bool) (x :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) * x) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) * x) := by
  rw [← mul_assoc, pcWord_oneAtBit_two_comm_one a true, mul_assoc]

private theorem pcWord_five_across_prefix (x a b d y : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 x) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 y)))) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (x ^^ y)))) := by
  have h2 := pcWord_oneAtBit_five_comm_two x a
  have h3 := pcWord_oneAtBit_five_comm_three x b
  have h4 := pcWord_oneAtBit_five_comm_four x d
  calc
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 x) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 y)))) := by
      simpa using swap_nested_product 1 _ _ _ h2
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 x) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 y)))) := by
      simpa using swap_nested_product
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 a)) _ _ _ h3
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 x) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 y)))) := by
      rw [← mul_assoc
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 a))
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 b))]
      rw [swap_nested_product
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 a) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 b))
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 x))
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 d))
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 y)) h4]
      rw [mul_assoc]
    _ = _ := by
      rw [pcWord_five_bit_mul]

private def toggleOneFinal (e : PCExponent) (c : Bool) : PCExponent :=
  fun i =>
    if i = 1 then e i ^^ c
    else if i = 5 then e i ^^ (c && e 1) ^^ (c && e 3) ^^ (c && e 4)
    else e i

theorem pcWord_mul_oneAtBit_one_full (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 1 c) =
      G2TwoSylowSubgroup.pcWord (toggleOneFinal e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have h : toggleOneFinal e false = e := by
      funext i
      fin_cases i <;> simp [toggleOneFinal]
    rw [h]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleOneFinal e true)]
    simp only [mul_assoc]
    rw [pcWord_three_tail_transport (e 3) (e 4) (e 5)]
    rw [pcWord_two_move_one (e 2)]
    have hcombine :
        G2TwoSylowSubgroup.pcWord (oneAtBit 1 (e 1)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 1 (e 1 ^^ true)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 1)) := by
      cases h : e 1
      · simp [h, pcWord_oneAtBit]
      · simpa [pcWord_oneAtBit, oneAtBit, oneAt, zeroPC] using
          pcWord_oneAt_one_mul_oneAt_one
    rw [← mul_assoc
      (G2TwoSylowSubgroup.pcWord (oneAtBit 1 (e 1)))
      (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true))]
    rw [hcombine]
    rw [mul_assoc]
    rw [pcWord_five_across_prefix
      (e 1) (e 2) (e 3) (e 4) (e 5 ^^ e 4 ^^ e 3)]
    simp [toggleOneFinal, oneAtBit, oneAt, zeroPC,
      Bool.xor_assoc, Bool.xor_comm]
    have hshape :
        (if e 1 = (e 3 ^^ (e 4 ^^ e 5)) then zeroPC else oneAt 5) =
          (if e 4 = (e 3 ^^ (e 1 ^^ e 5)) then zeroPC else oneAt 5) := by
      funext i
      fin_cases i <;>
        cases e1 : e 1 <;> cases e3 : e 3 <;>
          cases e4 : e 4 <;> cases e5 : e 5 <;>
            simp [e1, e3, e4, e5, Bool.xor_assoc, Bool.xor_comm]
    rw [hshape]

theorem pcWord_three_four_two_five_collect (a b d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 d) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true))) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b)))) := by
  have h52 := pcWord_oneAtBit_five_comm_two d true
  have h32 := pcWord_oneAtBit_three_comm_two a true
  calc
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 d))) := by
          rw [h52]
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b)))) := by
          rw [pcWord_four_two_five_collect b true d]
          simp only [Bool.and_true]
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b)))) := by
          exact swap_nested_product 1
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 a))
            (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true))
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (d ^^ b))) h32

theorem pcWord_five_transport_three_four (a b c d : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 c) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 d))) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (c ^^ d))) := by
  have h53 := pcWord_oneAtBit_five_comm_three c a
  have h54 := pcWord_oneAtBit_five_comm_four c b
  calc
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 c) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 d))) := by
          simpa using swap_nested_product 1
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 c))
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 a))
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) h53
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 c) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 d))) := by
          congr 1
          simpa using swap_nested_product 1
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 c))
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b))
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 d)) h54
    _ = G2TwoSylowSubgroup.pcWord (oneAtBit 3 a) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 b) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (c ^^ d))) := by
          rw [pcWord_oneAtBit_mul]
          have h : pcCombine (oneAtBit 5 c) (oneAtBit 5 d) =
              oneAtBit 5 (c ^^ d) := by
            funext i
            fin_cases i <;> cases c <;> cases d <;>
              simp [pcCombine, oneAtBit, oneAt, zeroPC]
          rw [h]

private def toggleTwoFinal (e : PCExponent) (c : Bool) : PCExponent :=
  fun i =>
    if i = 2 then e i ^^ c
    else if i = 5 then e i ^^ (c && e 2) ^^ (c && e 4)
    else e i

theorem pcWord_mul_oneAtBit_two_full (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 c) =
      G2TwoSylowSubgroup.pcWord (toggleTwoFinal e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have h : toggleTwoFinal e false = e := by
      funext i
      fin_cases i <;> simp [toggleTwoFinal]
    rw [h]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleTwoFinal e true)]
    simp only [mul_assoc]
    have hcombine :
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
                (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
                  G2TwoSylowSubgroup.pcWord
                    (oneAtBit 5 (e 5 ^^ e 4))))) =
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2 ^^ true)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
                G2TwoSylowSubgroup.pcWord
                  (oneAtBit 5 (e 5 ^^ e 4 ^^ e 2)))) := by
      calc
        _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
                G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5 ^^ e 4)))) := by
              rw [mul_assoc]
        _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2 ^^ true)) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 2))) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
                G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5 ^^ e 4)))) := by
              rw [pcWord_two_two_bit]
              simp only [Bool.and_true]
        _ = G2TwoSylowSubgroup.pcWord (oneAtBit 2 (e 2 ^^ true)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 2)) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e 3)) *
                (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (e 4)) *
                  G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e 5 ^^ e 4))))) := by
              rw [mul_assoc]
        _ = _ := by
              rw [pcWord_five_transport_three_four]
              cases h2 : e 2 <;> cases h4 : e 4 <;> cases h5 : e 5 <;>
                simp [h2, h4, h5]
    rw [pcWord_three_four_two_five_collect (e 3) (e 4) (e 5)]
    rw [← mul_assoc, hcombine]
    cases he2 : e 2 <;> cases he4 : e 4 <;> cases he5 : e 5 <;>
      simp [toggleTwoFinal, he2, he4, he5, mul_assoc]

/- CAS-certified flag-transport step for the nontrivial zero coordinate. -/

private theorem pcWord_move_two_zero_tail_structural
    (b : Bool) (X : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 0 true) * X) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) * X)) := by
  calc
    _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 2 b) *
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 true)) * X := by rw [mul_assoc]
    _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 0 true) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 5 b) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 2 b))) * X := by
      simpa [Bool.and_true] using
        congrArg (fun z => z * X) (pcWord_oneAtBit_two_transport_zero b true)
    _ = _ := by simp only [mul_assoc]

private theorem pcWord_move_one_zero_tail_structural
    (b : Bool) (X : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 1 b) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 0 true) * X) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 true) *
        ((G2TwoSylowSubgroup.pcWord (oneAtBit 1 b) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 2 (b && true)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (b && true)) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 (b && true))))) * X) := by
  simpa [mul_assoc] using congrArg (fun z => z * X)
    (pcWord_oneAtBit_one_transport_zero b true)

theorem pcCombine_oneAtBit_zero_concrete (a b : Bool) :
    pcCombine (oneAtBit 0 a) (oneAtBit 0 b) =
      oneAtBit 0 (a ^^ b) := by
  cases a <;> cases b
  · simpa [oneAtBit, zeroPC] using (pcCombine_zero_left zeroPC)
  · simpa [oneAtBit, zeroPC] using (pcCombine_zero_left (oneAt 0))
  · simpa [oneAtBit, zeroPC] using (pcCombine_zero_right (oneAt 0))
  · change pcCombine (oneAt 0) (oneAt 0) = zeroPC
    funext i
    fin_cases i <;> simp [pcCombine, oneAt, zeroPC]

private theorem pcWord_zero_mul_zero (a b : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 0 a) *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 b) =
      G2TwoSylowSubgroup.pcWord (oneAtBit 0 (a ^^ b)) := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCConcreteMultiplication.pcWord_oneAtBit_mul]
  congr 1
  exact pcCombine_oneAtBit_zero_concrete a b

theorem pcWord_zero_tail_false (e2 e3 e4 e5 : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 5 e2) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 2 e2) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5)))) =
    G2TwoSylowSubgroup.pcWord (oneAtBit 2 e2) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 (e5 ^^ e2)))) := by
  cases e2
  · have hzero5 : G2TwoSylowSubgroup.pcWord (oneAtBit 5 false) = 1 := by
      dsimp [oneAtBit]; exact pcWord_zero_eq_one
    have hzero2 : G2TwoSylowSubgroup.pcWord (oneAtBit 2 false) = 1 := by
      dsimp [oneAtBit]; exact pcWord_zero_eq_one
    rw [hzero5, hzero2, one_mul, one_mul, one_mul]
    simp only [Bool.xor_false]
  · have h52 := pcWord_oneAtBit_five_comm_two true true
    have h53 := pcWord_oneAtBit_five_comm_three true (e3 ^^ e4)
    have h54 := pcWord_oneAtBit_five_comm_four true e4
    have hz5 : pcCombine (oneAtBit 5 true) (oneAtBit 5 e5) = oneAtBit 5 (e5 ^^ true) := by
      funext i; fin_cases i <;> cases e5 <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
    calc
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5))) := by
        rw [← mul_assoc, h52]
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4)) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5)) := by
        simp only [mul_assoc]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h53]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h54]
      _ = _ := by
        rw [pcWord_oneAtBit_mul 5 5 true e5]
        rw [hz5]
        simp only [mul_assoc]

theorem pcWord_zero_tail_true (e2 e3 e4 e5 : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 e2) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 2 e2) *
                (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
                  (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
                    G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5)))))))) =
    G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
      (G2TwoSylowSubgroup.pcWord (oneAtBit 2 (!e2)) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (!e3 ^^ e4)) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 5 (!e5))))) := by
  cases e2
  · have h53 := pcWord_oneAtBit_five_comm_three true (e3 ^^ e4)
    have h54 := pcWord_oneAtBit_five_comm_four true e4
    have hz3 : pcCombine (oneAtBit 3 true) (oneAtBit 3 (e3 ^^ e4)) = oneAtBit 3 (! (e3 ^^ e4)) := by
      funext i; fin_cases i <;> cases e3 <;> cases e4 <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
    have hz5 : pcCombine (oneAtBit 5 true) (oneAtBit 5 e5) = oneAtBit 5 (! e5) := by
      funext i; fin_cases i <;> cases e5 <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
    have hzero5 : G2TwoSylowSubgroup.pcWord (oneAtBit 5 false) = 1 := by
      dsimp [oneAtBit]; exact pcWord_zero_eq_one
    have hzero2 : G2TwoSylowSubgroup.pcWord (oneAtBit 2 false) = 1 := by
      dsimp [oneAtBit]; exact pcWord_zero_eq_one
    have hnot : (! (e3 ^^ e4)) = (!e3 ^^ e4) := by cases e3 <;> cases e4 <;> rfl
    have hnot2 : (!false) = true := rfl
    calc
      _ = G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
        (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
                (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
                  G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5)))))) := by
        rw [hzero5, hzero2, one_mul, one_mul]
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4))) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5))) := by
        simp only [mul_assoc]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h53]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h54]
      _ = _ := by
        rw [mul_assoc (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) * G2TwoSylowSubgroup.pcWord (oneAtBit 2 true))]
        rw [pcWord_oneAtBit_mul 3 3 true (e3 ^^ e4), hz3]
        rw [pcWord_oneAtBit_mul 5 5 true e5, hz5]
        rw [hnot, hnot2]
        simp only [mul_assoc]
  · have h55 : G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) * G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) = 1 := by
      rw [pcWord_oneAtBit_mul 5 5 true true]
      have hz : pcCombine (oneAtBit 5 true) (oneAtBit 5 true) = zeroPC := by
        funext i; fin_cases i <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
      rw [hz]
      exact pcWord_zero_eq_one
    have h22 : G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) * G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) =
        G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) := by
      have h := pcWord_oneAt_two_mul_oneAt_two
      have hz : pcCombine (oneAt 2) (oneAt 2) = oneAt 5 := by
        funext i; fin_cases i <;> simp [pcCombine, oneAt]
      rw [hz] at h
      exact h
    have h32 := pcWord_oneAtBit_three_comm_two true true
    have h53_3 := pcWord_oneAtBit_five_comm_three true true
    have h53 := pcWord_oneAtBit_five_comm_three true (e3 ^^ e4)
    have h54 := pcWord_oneAtBit_five_comm_four true e4
    have hz3 : pcCombine (oneAtBit 3 true) (oneAtBit 3 (e3 ^^ e4)) = oneAtBit 3 (! (e3 ^^ e4)) := by
      funext i; fin_cases i <;> cases e3 <;> cases e4 <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
    have hz5 : pcCombine (oneAtBit 5 true) (oneAtBit 5 e5) = oneAtBit 5 (! e5) := by
      funext i; fin_cases i <;> cases e5 <;> simp [pcCombine, oneAtBit, oneAt, zeroPC]
    have hnot : (! (e3 ^^ e4)) = (!e3 ^^ e4) := by cases e3 <;> cases e4 <;> rfl
    have hnot2 : (!true) = false := rfl
    have hzero2 : G2TwoSylowSubgroup.pcWord (oneAtBit 2 false) = 1 := by
      dsimp [oneAtBit]; exact pcWord_zero_eq_one
    calc
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 true)) *
          ((G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) * G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
              (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
                (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
                  G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5))))) := by
        simp only [mul_assoc]
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 2 true) *
            G2TwoSylowSubgroup.pcWord (oneAtBit 2 true)) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 true)) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (e3 ^^ e4)) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5))) := by
        rw [h55, one_mul]
        simp only [mul_assoc]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 3 true)) _ _ h32]
      _ = (G2TwoSylowSubgroup.pcWord (oneAtBit 1 true) *
          G2TwoSylowSubgroup.pcWord (oneAtBit 3 (! (e3 ^^ e4)))) *
          (G2TwoSylowSubgroup.pcWord (oneAtBit 4 e4) *
            (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true) *
              G2TwoSylowSubgroup.pcWord (oneAtBit 5 e5))) := by
        rw [h22]
        simp only [mul_assoc]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h53_3]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h53]
        rw [swap_nested_product _ (G2TwoSylowSubgroup.pcWord (oneAtBit 5 true)) _ _ h54]
        rw [← mul_assoc (G2TwoSylowSubgroup.pcWord (oneAtBit 3 true))]
        rw [pcWord_oneAtBit_mul 3 3 true (e3 ^^ e4), hz3]
      _ = _ := by
        rw [pcWord_oneAtBit_mul 5 5 true e5, hz5]
        rw [hnot, hnot2, hzero2]
        simp only [one_mul, mul_assoc]

theorem pcWord_mul_oneAtBit_zero_full (e : PCExponent) (c : Bool) :
    G2TwoSylowSubgroup.pcWord e *
        G2TwoSylowSubgroup.pcWord (oneAtBit 0 c) =
      G2TwoSylowSubgroup.pcWord (toggleZero e c) := by
  cases c
  · rw [pcWord_mul_oneAtBit_zero]
    have hz : toggleZero e false = e := by
      funext i
      fin_cases i <;> simp [toggleZero]
    rw [hz]
  · rw [pcWord_factorized]
    rw [pcWord_factorized (toggleZero e true)]
    simp only [mul_assoc]
    rw [pcWord_three_tail_transport_zero (e 3) (e 4) (e 5) true]
    rw [pcWord_move_two_zero_tail_structural]
    rw [pcWord_move_one_zero_tail_structural]
    simp only [mul_assoc]
    rw [← mul_assoc, pcWord_zero_mul_zero]
    congr 1
    cases h1 : e 1
    · have hz1 : toggleZero e true 1 = false := h1
      have hz2 : toggleZero e true 2 = e 2 := by
        dsimp [toggleZero]; rw [h1]; cases e 2 <;> rfl
      have hz3 : toggleZero e true 3 = (e 3 ^^ e 4) := by
        dsimp [toggleZero]; rw [h1]; cases e 3 <;> cases e 4 <;> rfl
      have hz4 : toggleZero e true 4 = e 4 := rfl
      have hz5 : toggleZero e true 5 = (e 5 ^^ e 2) := by
        dsimp [toggleZero]; rw [h1]; cases e 2 <;> cases e 5 <;> rfl
      rw [hz1, hz2, hz3, hz4, hz5]
      simp only [Bool.false_and, Bool.and_true]
      have h0 (i : Fin 6) : G2TwoSylowSubgroup.pcWord (oneAtBit i false) = 1 := by
        change G2TwoSylowSubgroup.pcWord zeroPC = 1
        exact pcWord_zero_eq_one
      rw [h0 1, h0 2, h0 3, h0 5]
      rw [one_mul, one_mul, one_mul, one_mul, one_mul]
      exact pcWord_zero_tail_false (e 2) (e 3) (e 4) (e 5)
    · have hz1 : toggleZero e true 1 = true := h1
      have hz2 : toggleZero e true 2 = (!e 2) := by
        dsimp [toggleZero]; rw [h1]; cases e 2 <;> rfl
      have hz3 : toggleZero e true 3 = (!e 3 ^^ e 4) := by
        dsimp [toggleZero]; rw [h1]; cases e 3 <;> cases e 4 <;> rfl
      have hz4 : toggleZero e true 4 = e 4 := rfl
      have hz5 : toggleZero e true 5 = (!e 5) := by
        dsimp [toggleZero]; rw [h1]; cases e 2 <;> cases e 5 <;> rfl
      rw [hz1, hz2, hz3, hz4, hz5]
      simp only [Bool.and_true]
      exact pcWord_zero_tail_true (e 2) (e 3) (e 4) (e 5)

private theorem stepExp_apply_zero (e f : PCExponent) :
    toggleLast (toggleFour (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3)) (f 4)) (f 5) 0 =
      pcCombine e f 0 := rfl

private theorem stepExp_apply_one (e f : PCExponent) :
    toggleLast (toggleFour (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3)) (f 4)) (f 5) 1 =
      pcCombine e f 1 := rfl

private theorem stepExp_apply_two (e f : PCExponent) :
    toggleLast (toggleFour (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3)) (f 4)) (f 5) 2 =
      pcCombine e f 2 := by
  dsimp [toggleLast, toggleFour, toggleThree, toggleTwoFinal, toggleOneFinal, toggleZero, pcCombine]
  cases f 0 <;> cases e 1 <;> cases e 2 <;> cases f 2 <;> rfl

private theorem stepExp_apply_three (e f : PCExponent) :
    toggleLast (toggleFour (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3)) (f 4)) (f 5) 3 =
      pcCombine e f 3 := by
  dsimp [toggleLast, toggleFour, toggleThree, toggleTwoFinal, toggleOneFinal, toggleZero, pcCombine]
  cases f 0 <;> cases e 1 <;> cases e 3 <;> cases e 4 <;> cases f 3 <;> rfl

private theorem stepExp_apply_four (e f : PCExponent) :
    toggleLast (toggleFour (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3)) (f 4)) (f 5) 4 =
      pcCombine e f 4 := rfl

private theorem stepExp_apply_five (e f : PCExponent) :
    toggleLast (toggleFour (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3)) (f 4)) (f 5) 5 =
      pcCombine e f 5 := by
  dsimp [toggleLast, toggleFour, toggleThree, toggleTwoFinal, toggleOneFinal, toggleZero, pcCombine]
  cases e 1 <;> cases e 2 <;> cases e 3 <;> cases e 4 <;> cases e 5 <;>
    cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> cases f 5 <;> rfl

theorem pcWord_mul_pcWord (e f : PCExponent) :
    G2TwoSylowSubgroup.pcWord e * G2TwoSylowSubgroup.pcWord f =
      G2TwoSylowSubgroup.pcWord (pcCombine e f) := by
  rw [pcWord_factorized f]
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  rw [← mul_assoc (G2TwoSylowSubgroup.pcWord e) (G2TwoSylowSubgroup.pcWord (oneAtBit 0 (f 0)))]
  rw [pcWord_mul_oneAtBit_zero_full]
  rw [← mul_assoc (G2TwoSylowSubgroup.pcWord (toggleZero e (f 0))) (G2TwoSylowSubgroup.pcWord (oneAtBit 1 (f 1)))]
  rw [pcWord_mul_oneAtBit_one_full]
  rw [← mul_assoc (G2TwoSylowSubgroup.pcWord (toggleOneFinal (toggleZero e (f 0)) (f 1))) (G2TwoSylowSubgroup.pcWord (oneAtBit 2 (f 2)))]
  rw [pcWord_mul_oneAtBit_two_full]
  rw [← mul_assoc (G2TwoSylowSubgroup.pcWord (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2))) (G2TwoSylowSubgroup.pcWord (oneAtBit 3 (f 3)))]
  rw [pcWord_mul_oneAtBit_three]
  rw [← mul_assoc (G2TwoSylowSubgroup.pcWord (toggleThree (toggleTwoFinal (toggleOneFinal (toggleZero e (f 0)) (f 1)) (f 2)) (f 3))) (G2TwoSylowSubgroup.pcWord (oneAtBit 4 (f 4)))]
  rw [pcWord_mul_oneAtBit_four]
  rw [pcWord_mul_oneAtBit_five]
  congr 1
  funext i
  fin_cases i
  · exact stepExp_apply_zero e f
  · exact stepExp_apply_one e f
  · exact stepExp_apply_two e f
  · exact stepExp_apply_three e f
  · exact stepExp_apply_four e f
  · exact stepExp_apply_five e f

end InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector
