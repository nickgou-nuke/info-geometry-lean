import proofs.SixStateGeneralizedPauliBasis

/-!
  The Weyl multiplication laws are owned by
  `SixStateGeneralizedPauliBasis`.  This file is the small compatibility
  surface used by older proof imports; it contains no generated case split.
-/

open SixStateGeneralizedPauliBasis

theorem colorWeyl_mul_explicit (c d c' d' : ZMod 3) :
    colorWeyl c d * colorWeyl c' d' =
      ((ω3 : ℂ) ^ ((d.val : ℕ) * (c'.val : ℕ))) •
        colorWeyl (c + c') (d + d') := by
  exact colorWeyl_mul c d c' d'

theorem sheetWeyl_mul_explicit (a b c d : ZMod 2) :
    sheetWeyl a b * sheetWeyl c d =
      ((if (b.val : ℕ) * (c.val : ℕ) = 1 then (-1 : ℂ) else (1 : ℂ)) : ℂ) •
        sheetWeyl (a + c) (b + d) := by
  exact sheetWeyl_mul a b c d
