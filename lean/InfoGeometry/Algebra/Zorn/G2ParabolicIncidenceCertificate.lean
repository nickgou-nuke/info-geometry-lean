import Mathlib.Data.Fin.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

namespace InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

/-- The three lines incident with each of the 63 parabolic points. -/
def incidence : Fin 63 → Finset (Fin 63)
  | ⟨0, _⟩ => {0, 1, 2}
  | ⟨1, _⟩ => {9, 10, 11}
  | ⟨2, _⟩ => {3, 4, 5}
  | ⟨3, _⟩ => {4, 10, 16}
  | ⟨4, _⟩ => {18, 55, 56}
  | ⟨5, _⟩ => {0, 3, 6}
  | ⟨6, _⟩ => {6, 43, 44}
  | ⟨7, _⟩ => {13, 47, 48}
  | ⟨8, _⟩ => {1, 9, 12}
  | ⟨9, _⟩ => {16, 25, 26}
  | ⟨10, _⟩ => {25, 44, 48}
  | ⟨11, _⟩ => {20, 37, 38}
  | ⟨12, _⟩ => {19, 49, 50}
  | ⟨13, _⟩ => {17, 61, 62}
  | ⟨14, _⟩ => {26, 32, 34}
  | ⟨15, _⟩ => {2, 15, 18}
  | ⟨16, _⟩ => {12, 31, 32}
  | ⟨17, _⟩ => {11, 35, 36}
  | ⟨18, _⟩ => {15, 16, 17}
  | ⟨19, _⟩ => {15, 53, 54}
  | ⟨20, _⟩ => {7, 33, 34}
  | ⟨21, _⟩ => {29, 50, 57}
  | ⟨22, _⟩ => {30, 44, 55}
  | ⟨23, _⟩ => {5, 13, 19}
  | ⟨24, _⟩ => {2, 51, 52}
  | ⟨25, _⟩ => {31, 43, 54}
  | ⟨26, _⟩ => {36, 48, 51}
  | ⟨27, _⟩ => {9, 29, 30}
  | ⟨28, _⟩ => {8, 57, 58}
  | ⟨29, _⟩ => {22, 31, 37}
  | ⟨30, _⟩ => {37, 39, 62}
  | ⟨31, _⟩ => {14, 59, 60}
  | ⟨32, _⟩ => {12, 13, 14}
  | ⟨33, _⟩ => {35, 40, 59}
  | ⟨34, _⟩ => {38, 41, 60}
  | ⟨35, _⟩ => {34, 46, 52}
  | ⟨36, _⟩ => {5, 45, 46}
  | ⟨37, _⟩ => {7, 11, 20}
  | ⟨38, _⟩ => {32, 42, 56}
  | ⟨39, _⟩ => {30, 46, 62}
  | ⟨40, _⟩ => {18, 19, 20}
  | ⟨41, _⟩ => {24, 43, 49}
  | ⟨42, _⟩ => {33, 47, 53}
  | ⟨43, _⟩ => {6, 7, 8}
  | ⟨44, _⟩ => {3, 41, 42}
  | ⟨45, _⟩ => {36, 42, 61}
  | ⟨46, _⟩ => {35, 45, 54}
  | ⟨47, _⟩ => {23, 56, 58}
  | ⟨48, _⟩ => {21, 55, 59}
  | ⟨49, _⟩ => {26, 40, 50}
  | ⟨50, _⟩ => {10, 23, 24}
  | ⟨51, _⟩ => {29, 41, 53}
  | ⟨52, _⟩ => {4, 21, 22}
  | ⟨53, _⟩ => {0, 39, 40}
  | ⟨54, _⟩ => {24, 52, 60}
  | ⟨55, _⟩ => {28, 45, 58}
  | ⟨56, _⟩ => {27, 49, 61}
  | ⟨57, _⟩ => {22, 51, 57}
  | ⟨58, _⟩ => {21, 27, 33}
  | ⟨59, _⟩ => {1, 27, 28}
  | ⟨60, _⟩ => {23, 39, 47}
  | ⟨61, _⟩ => {25, 28, 38}
  | ⟨62, _⟩ => {8, 14, 17}
  | _ => ∅

theorem incidence_card (p : Fin 63) : (incidence p).card = 3 := by
  fin_cases p <;> native_decide

theorem incidence_edge_card : (Finset.univ.biUnion incidence).card = 63 := by
  native_decide

theorem incidence_flag_card : (∑ p : Fin 63, (incidence p).card) = 189 := by
  native_decide

end InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate
