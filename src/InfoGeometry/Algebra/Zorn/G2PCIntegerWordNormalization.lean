import InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

namespace InfoGeometry.Algebra.Zorn.G2PCIntegerWordNormalization

open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev IntegerPCWord := List (Fin 6 × Int)

noncomputable def eval : IntegerPCWord → SplitOctF2Aut
  | [] => 1
  | (i, n) :: w => (pcGenerator i) ^ n * eval w

theorem eval_nil : eval [] = (1 : SplitOctF2Aut) := rfl

theorem eval_cons (i : Fin 6) (n : Int) (w : IntegerPCWord) :
    eval ((i, n) :: w) = (pcGenerator i) ^ n * eval w := rfl

theorem eval_append (u v : IntegerPCWord) :
    eval (u ++ v) = eval u * eval v := by
  induction u with
  | nil => simp [eval]
  | cons t u ih =>
      simp only [List.cons_append, eval]
      rw [ih]
      simp [mul_assoc]

def inverseWord (w : IntegerPCWord) : IntegerPCWord :=
  (w.reverse.map (fun t => (t.1, -t.2)))

theorem eval_inverseWord (w : IntegerPCWord) :
    eval (inverseWord w) = (eval w)⁻¹ := by
  induction w with
  | nil => simp [inverseWord, eval]
  | cons t w ih =>
      simp only [inverseWord, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.map_reverse]
      rw [← List.map_reverse]
      rw [eval_append]
      change eval (inverseWord w) * (pcGenerator t.1) ^ (-t.2) =
        ((pcGenerator t.1) ^ t.2 * eval w)⁻¹
      rw [ih]
      simp [mul_inv_rev]

theorem collect_eq_eval (w : FactorWord) :
    collect w = eval w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
      simp only [collect, eval]
      rw [ih]
      rfl

theorem eval_eq_collect (w : FactorWord) :
    eval w = collect w := (collect_eq_eval w).symm

theorem collect_inverseWord (w : FactorWord) :
    eval (inverseWord w) = (collect w)⁻¹ := by
  rw [eval_inverseWord, collect_eq_eval]

end InfoGeometry.Algebra.Zorn.G2PCIntegerWordNormalization
