/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG, Apache-2.0. Module and namespace paths are
adapted for this repository's Lean 4.34.1 / mathlib pin.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyStrings
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyParameterAddition
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCheck
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyStringCheck

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

theorem upTransport (τ : Tag) : UpTransport τ := by
  intro i α hα hne hne' k hk
  obtain ⟨-, -, htr⟩ := root_string_transport hα i hne hne'
  obtain ⟨h1, h2, h3, h4, h5⟩ := htr k (by omega) (by exact_mod_cast hk)
  exact ⟨h1, h2, h3, by omega, by omega⟩

theorem downTransport (τ : Tag) : DownTransport τ := by
  intro i α hα hne hne' k hk
  obtain ⟨-, -, htr⟩ := root_string_transport hα i hne hne'
  have hkk : α - (k : ℤ) • Pi.single i 1 = α + (-(k : ℤ)) • Pi.single i 1 := by
    rw [neg_smul, sub_eq_add_neg]
  obtain ⟨h1, h2, h3, h4, h5⟩ := htr (-(k : ℤ)) (by omega) (by omega)
  rw [hkk]
  exact ⟨h1, h2, h3, by omega, by omega⟩

theorem simple_root_parameter_addition_of_tag (τ : Tag) (R : Type*) [CommRing R]
    (i : Fin τ.rank) :
    (∀ c d : R, xOp τ R i c * xOp τ R i d = xOp τ R i (c + d)) ∧
      (∀ c d : R, yOp τ R i c * yOp τ R i d = yOp τ R i (c + d)) ∧
      xOp τ R i 0 = 1 ∧ yOp τ R i 0 = 1 ∧
      (∀ c : R, xOp τ R i c * xOp τ R i (-c) = 1 ∧ xOp τ R i (-c) * xOp τ R i c = 1) ∧
      (∀ c : R, yOp τ R i c * yOp τ R i (-c) = 1 ∧ yOp τ R i (-c) * yOp τ R i c = 1) ∧
      Function.Injective (xOp τ R i) ∧ Function.Injective (yOp τ R i) :=
  simple_root_parameter_addition τ R (upTransport τ) (downTransport τ) i

end InfoGeometry.Exceptional.CFSGPort.Chevalley
