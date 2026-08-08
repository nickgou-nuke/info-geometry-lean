theory TypeIIOrientifolds
  imports Main
begin

section ‹Type II Orientifolds and Discrete Parity Inversions›

text ‹
  We formalize the exact orientifold projections (Type IIA vs IIB)
  based on discrete parity inversions (world-sheet parity and spacetime parity).
›

datatype string_theory_type = TypeIIA | TypeIIB

record parity_inversions =
  worldsheet_parity :: "bool" 
  left_fermion_parity :: "bool"
  spacetime_parity :: "bool"

definition orientifold_projection :: "parity_inversions ⇒ string_theory_type ⇒ bool" where
  "orientifold_projection P T ≡ 
    case T of
      TypeIIA ⇒ (worldsheet_parity P = True) ∧ (left_fermion_parity P = True) ∧ (spacetime_parity P = True)
    | TypeIIB ⇒ (worldsheet_parity P = True) ∧ (left_fermion_parity P = False) ∧ (spacetime_parity P = False)"

lemma type_IIA_projection_exact:
  assumes "worldsheet_parity P = True"
  assumes "left_fermion_parity P = True"
  assumes "spacetime_parity P = True"
  shows "orientifold_projection P TypeIIA = True"
  using assms by (simp add: orientifold_projection_def)

lemma type_IIB_projection_exact:
  assumes "worldsheet_parity P = True"
  assumes "left_fermion_parity P = False"
  assumes "spacetime_parity P = False"
  shows "orientifold_projection P TypeIIB = True"
  using assms by (simp add: orientifold_projection_def)

lemma mutually_exclusive_orientifolds:
  assumes "orientifold_projection P TypeIIA"
  shows "¬ orientifold_projection P TypeIIB"
  using assms unfolding orientifold_projection_def by auto

end
