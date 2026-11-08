/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.GrandUnification.AlgebraicSouriauTomita
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Checks — Algebraic Souriau–Tomita Four-Pillar Synthesis

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.GrandUnification.AlgebraicSouriauTomita`.
- BUCKET 2 (Deconfabulation):
  * Signature verification for the wrapper-free Souriau–Tomita theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `#check` verification module.
-/

namespace InfoGeometry.GrandUnification.Checks

#check InfoGeometry.GrandUnification.h1_diagonal_volume_cocycle_det_exp
#check InfoGeometry.GrandUnification.massieu_potential_zero_ne_volume_cocycle_log
#check InfoGeometry.GrandUnification.finite_commuting_connes_phase_cocycle_law
#check InfoGeometry.GrandUnification.normal_ordered_car_matrix_unit_wick_commutator
#check InfoGeometry.GrandUnification.algebraic_souriau_tomita_four_pillar_synthesis

end InfoGeometry.GrandUnification.Checks
