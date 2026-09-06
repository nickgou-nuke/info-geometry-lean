/-- The correct D5 lift that genuinely preserves the `latticeEmbed` subspace.
It acts as `A \oplus A \oplus 1`, which perfectly commutes with `latticeEmbed`. -/
def weylD5CrossSection2 : Fin 8 → Mat5Q
  | 0 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 1 => !![0, -1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  | 2 => !![-1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 1]
  | 3 => !![0, 1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 1]
  | 5 => !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  | 6 => !![-1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 7 => !![0, -1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1]

theorem weylD5CrossSection2_is_homomorphism (a b : Fin 8) :
    weylD5CrossSection2 a * weylD5CrossSection2 b = weylD5CrossSection2 (d4_comp a b) := by
  fin_cases a <;> fin_cases b <;> native_decide
