theory WarehamNullBasis55 imports Complex_Main begin

type_synonym pair = "rat × rat"
definition q11 :: "pair ⇒ rat" where "q11 x = fst x * fst x - snd x * snd x"
definition bil11 :: "pair ⇒ pair ⇒ rat" where "bil11 x y = fst x * fst y - snd x * snd y"
definition reflectE :: "pair ⇒ pair" where "reflectE x = (- fst x, snd x)"
definition n :: pair where "n = (1,1)"
definition nbar :: pair where "nbar = (1,-1)"

theorem n_null: "q11 n = 0" by (simp add:q11_def n_def)
theorem nbar_null: "q11 nbar = 0" by (simp add:q11_def nbar_def)
theorem n_dot_nbar: "bil11 n nbar = 2" by (simp add:bil11_def n_def nbar_def)
theorem reflect_n: "reflectE n = (-1,1)" by (simp add:reflectE_def n_def)
theorem reflect_nbar: "reflectE nbar = (-1,-1)" by (simp add:reflectE_def nbar_def)
theorem mass_split: "((1/4::rat)+(1/25))-((1/4)-(1/25)) = 2/25" by simp

end
