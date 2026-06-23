import sys

out = ""
for g in range(8):
    out += f"""
lemma weylD5CrossSection_latticeEmbed_commutation_{g} (t : Z2) :
    matVec5 (weylD5CrossSection {g}) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 {g} t) := by
  rcases t with ⟨u, v⟩
  ext i
  rw [eval_matVec5]
  fin_cases i <;> dsimp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection] <;> push_cast <;> ring
"""

out += """
/-- 
LEMMA: The 5D Weyl representation of the `D₄` action precisely matches the 
embedded 2D geometric action on the lattice.
`W(g) * latticeEmbed(t) = latticeEmbed(g(t))`
-/
theorem weylD5CrossSection_latticeEmbed_commutation (g : Fin 8) (t : Z2) :
    matVec5 (weylD5CrossSection g) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 g t) := by
  match g with
  | 0 => exact weylD5CrossSection_latticeEmbed_commutation_0 t
  | 1 => exact weylD5CrossSection_latticeEmbed_commutation_1 t
  | 2 => exact weylD5CrossSection_latticeEmbed_commutation_2 t
  | 3 => exact weylD5CrossSection_latticeEmbed_commutation_3 t
  | 4 => exact weylD5CrossSection_latticeEmbed_commutation_4 t
  | 5 => exact weylD5CrossSection_latticeEmbed_commutation_5 t
  | 6 => exact weylD5CrossSection_latticeEmbed_commutation_6 t
  | 7 => exact weylD5CrossSection_latticeEmbed_commutation_7 t
"""
print(out)
