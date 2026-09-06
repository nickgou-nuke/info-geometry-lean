import proofs.SplitOctonionCircularChiralClosure

noncomputable section
namespace SplitOctonionWittSl2Slice

open SplitOctonionChiralClosure
open SplitOctonionCircularChiralClosure

abbrev SO := SplitOctonionChiralClosure.Zorn

def spatialU (i : Fin 3) : SO :=
  sub (sM (axis i)) (sP (axis i))

def nullPlus (i : Fin 3) : SO :=
  add (spatialU i) (mul ell (spatialU i))

def nullMinus (i : Fin 3) : SO :=
  sub (spatialU i) (mul ell (spatialU i))

def H : SO := ell

def E (i : Fin 3) : SO :=
  smul (1 / 2 : ℂ) (nullPlus i)

def F (i : Fin 3) : SO :=
  smul (-(1 / 2 : ℂ)) (nullMinus i)

-- Preferred intermediate theorems
theorem spatialU_sq (i : Fin 3) : mul (spatialU i) (spatialU i) = smul (-1 : ℂ) unit := by
  fin_cases i <;> { simp [spatialU, unit]; zorn_coords }
theorem spatialU_ell_anticommute (i : Fin 3) : mul (spatialU i) ell = smul (-1 : ℂ) (mul ell (spatialU i)) := by
  fin_cases i <;> { simp [spatialU]; zorn_coords }

theorem nullPlus_eq (i : Fin 3) : nullPlus i = smul (-2 : ℂ) (sP (axis i)) := by
  fin_cases i <;> { simp [nullPlus, spatialU, sP]; zorn_coords }
theorem nullMinus_eq (i : Fin 3) : nullMinus i = smul (2 : ℂ) (sM (axis i)) := by
  fin_cases i <;> { simp [nullMinus, spatialU, sM]; zorn_coords }

theorem nullPlus_sq_zero (i : Fin 3) : mul (nullPlus i) (nullPlus i) = zero := by
  fin_cases i <;> { simp [nullPlus, spatialU]; zorn_coords }
theorem nullMinus_sq_zero (i : Fin 3) : mul (nullMinus i) (nullMinus i) = zero := by
  fin_cases i <;> { simp [nullMinus, spatialU]; zorn_coords }

theorem comm_ell_nullPlus (i : Fin 3) : comm ell (nullPlus i) = smul (2 : ℂ) (nullPlus i) := by
  fin_cases i <;> { simp [nullPlus, spatialU]; zorn_coords }
theorem comm_ell_nullMinus (i : Fin 3) : comm ell (nullMinus i) = smul (-2 : ℂ) (nullMinus i) := by
  fin_cases i <;> { simp [nullMinus, spatialU]; zorn_coords }
theorem comm_nullPlus_nullMinus (i : Fin 3) : comm (nullPlus i) (nullMinus i) = smul (-4 : ℂ) ell := by
  fin_cases i <;> { simp [nullPlus, nullMinus, spatialU]; zorn_coords <;> ring }

theorem sl2_H_E (i : Fin 3) : comm H (E i) = smul (2 : ℂ) (E i) := by
  fin_cases i <;> { simp [H, E, nullPlus, spatialU]; zorn_coords <;> ring }
theorem sl2_H_F (i : Fin 3) : comm H (F i) = smul (-2 : ℂ) (F i) := by
  fin_cases i <;> { simp [H, F, nullMinus, spatialU]; zorn_coords <;> ring }
theorem sl2_E_F (i : Fin 3) : comm (E i) (F i) = H := by
  fin_cases i <;> { simp [H, E, F, nullPlus, nullMinus, spatialU]; zorn_coords <;> ring }

end SplitOctonionWittSl2Slice
end noncomputable section
