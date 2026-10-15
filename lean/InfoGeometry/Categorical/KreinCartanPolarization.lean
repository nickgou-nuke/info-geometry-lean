/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Categorical Krein-Cartan Polarization

This module defines the categorical Krein polarization structure `KreinPolarizationData`
in an ambient preadditive category `C`.

All properties are proved via standalone definitions, lemmas, and theorems.
-/

namespace InfoGeometry.Categorical

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Categorical Krein polarization data: an ambient space `K` equipped with a
fundamental symmetry involution `J` and section/retraction pairs into positive
and negative subspaces `K_plus` and `K_minus`. -/
structure KreinPolarizationData where
  K         : C
  J         : K ⟶ K
  K_plus    : C
  K_minus   : C
  i_plus    : K_plus ⟶ K
  p_plus    : K ⟶ K_plus
  i_minus   : K_minus ⟶ K
  p_minus   : K ⟶ K_minus
  J_sq      : J ≫ J = 𝟙 K
  id_plus   : i_plus ≫ p_plus = 𝟙 K_plus
  id_minus  : i_minus ≫ p_minus = 𝟙 K_minus
  orthog_pm : i_plus ≫ p_minus = 0
  orthog_mp : i_minus ≫ p_plus = 0
  decomp_id : p_plus ≫ i_plus + p_minus ≫ i_minus = 𝟙 K
  decomp_J  : p_plus ≫ i_plus - p_minus ≫ i_minus = J

end InfoGeometry.Categorical
