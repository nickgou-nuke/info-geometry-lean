theory AndreevReflection
  imports Main Complex_Main
begin

(* Formulate the chiral parity inversion matrices *)

record 'a matrix2x2 =
  m11 :: 'a
  m12 :: 'a
  m21 :: 'a
  m22 :: 'a

definition chiral_parity_inversion :: "complex matrix2x2" where
  "chiral_parity_inversion = \<lparr> m11 = 0, m12 = 1, m21 = 1, m22 = 0 \<rparr>"

lemma inversion_symmetry:
  "m12 chiral_parity_inversion = m21 chiral_parity_inversion"
  by (simp add: chiral_parity_inversion_def)

end
