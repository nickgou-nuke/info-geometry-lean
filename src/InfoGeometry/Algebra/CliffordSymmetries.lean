/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Clifford chiral symmetry on even generator products

This file records the ring-level centralizer consequence of a chiral
operator: if an operator anticommutes with every generator, it commutes with
each length-two generator word. The statement is valid over any unital
associative ring. It does not assert Bott periodicity, a Clifford reduction
isomorphism, or a KO-spectrum classification.
-/

namespace InfoGeometry.Algebra.CliffordSymmetries

/-- An operator that anticommutes with each generator commutes with every
length-two word in those generators. This is the even-degree centralizer
law, with multiplication order retained. -/
theorem chiral_operator_commutes_with_even_generator_products
    {B : Type*} [Ring B] {ι : Type*} (C : B) (e : ι → B)
    (hC : ∀ i, C * e i = -(e i * C)) (i j : ι) :
    C * (e i * e j) = (e i * e j) * C := by
  calc
    C * (e i * e j) = (C * e i) * e j := by rw [mul_assoc]
    _ = (-(e i * C)) * e j := by rw [hC i]
    _ = -(e i * (C * e j)) := by noncomm_ring
    _ = -(e i * (-(e j * C))) := by rw [hC j]
    _ = (e i * e j) * C := by noncomm_ring

end InfoGeometry.Algebra.CliffordSymmetries
