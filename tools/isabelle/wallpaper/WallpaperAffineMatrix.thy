theory WallpaperAffineMatrix
  imports Complex_Main
begin

definition p2_square :: real where "p2_square = (-1) * (-1)"
definition pm_square :: real where "pm_square = (-1) * (-1)"
definition pg_shift :: real where "pg_shift = (1/2) + (1/2)"

theorem p2_square_eq_one : "p2_square = 1"
  by (simp add: p2_square_def)

theorem pm_square_eq_one : "pm_square = 1"
  by (simp add: pm_square_def)

theorem pg_shift_eq_one : "pg_shift = 1"
  by (simp add: pg_shift_def)

theorem pm_conjugates_y_translation_example :
  "(-1::real) * (3 + 1) = ((-1::real) * 3) - 1"
  by algebra

end
