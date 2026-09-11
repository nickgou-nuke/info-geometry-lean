import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2PCWeylReadoutSeparation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

/-!
Structural separation of the PC carrier from the Weyl representatives using
matrix entries.  This owner deliberately avoids enumeration of `PCExponent`.
-/

theorem pcWord_ne_concreteWeylElement_two (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 2 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 2) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e,
    concreteWeylElement_two_entry_two_two] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_four (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 4 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 3 3) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 3 3 =
    autMatrix (concreteWeylElement 4) 3 3 at he
  rw [autMatrix_pcWord_entry_three_three e,
    concreteWeylElement_four_entry_three_three] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_six (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 6 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 6) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e,
    concreteWeylElement_six_entry_two_two] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_eight (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 8 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 8) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e,
    concreteWeylElement_eight_entry_two_two] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_one (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 1 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 1) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e] at he
  have hzero : autMatrix (concreteWeylElement 1) 2 2 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_three (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 3 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 3) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e] at he
  have hzero : autMatrix (concreteWeylElement 3) 2 2 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_five (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 5 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 5) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e] at he
  have hzero : autMatrix (concreteWeylElement 5) 2 2 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_seven (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 7 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 7) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e] at he
  have hzero : autMatrix (concreteWeylElement 7) 2 2 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_nine (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 9 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 9) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e] at he
  have hzero : autMatrix (concreteWeylElement 9) 2 2 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_ten (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 10 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 3 3) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 3 3 =
    autMatrix (concreteWeylElement 10) 3 3 at he
  rw [autMatrix_pcWord_entry_three_three e] at he
  have hzero : autMatrix (concreteWeylElement 10) 3 3 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_eleven (e : PCExponent) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement 11 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 =
    autMatrix (concreteWeylElement 11) 2 2 at he
  rw [autMatrix_pcWord_entry_two_two e] at he
  have hzero : autMatrix (concreteWeylElement 11) 2 2 = 0 := rfl
  rw [hzero] at he
  exact zero_ne_one he.symm

theorem pcWord_ne_concreteWeylElement_of_ne_zero
    (e : PCExponent) {i : Fin 12} (hi : i ≠ 0) :
    G2TwoSylowSubgroup.pcWord e ≠ concreteWeylElement i := by
  fin_cases i
  · exact (hi rfl).elim
  · exact pcWord_ne_concreteWeylElement_one e
  · exact pcWord_ne_concreteWeylElement_two e
  · exact pcWord_ne_concreteWeylElement_three e
  · exact pcWord_ne_concreteWeylElement_four e
  · exact pcWord_ne_concreteWeylElement_five e
  · exact pcWord_ne_concreteWeylElement_six e
  · exact pcWord_ne_concreteWeylElement_seven e
  · exact pcWord_ne_concreteWeylElement_eight e
  · exact pcWord_ne_concreteWeylElement_nine e
  · exact pcWord_ne_concreteWeylElement_ten e
  · exact pcWord_ne_concreteWeylElement_eleven e

end InfoGeometry.Algebra.Zorn.G2PCWeylReadoutSeparation
