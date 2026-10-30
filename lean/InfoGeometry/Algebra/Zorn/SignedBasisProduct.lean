/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.BasisTable

/-!
# Faithful signed-basis multiplication with zero

Contract: use the existing integer Zorn cells and their existing multiplication
table. The signed basis together with zero is closed under that product, and
its readout is injective. This is a finite nonassociative multiplication
carrier, not a twisted group algebra with unit-valued structure constants.
Dependency order: basis table → signed product → faithful readout → unique
product readback. No associative replacement of the Zorn product is made.
-/
namespace InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8.SignedBasis

def flip : SignedBasis → SignedBasis
  | zero => zero
  | pos a => neg a
  | neg a => pos a

def product : SignedBasis → SignedBasis → SignedBasis
  | zero, _ => zero
  | _, zero => zero
  | pos a, pos b => mulTable a b
  | pos a, neg b => flip (mulTable a b)
  | neg a, pos b => flip (mulTable a b)
  | neg a, neg b => mulTable a b

theorem cell_injective : Function.Injective cell := by
  intro a b
  cases a <;> cases b <;> (try casesm* Basis8) <;> decide

theorem product_cell (a b : SignedBasis) :
    cell (product a b) = cell a * cell b := by
  cases a <;> cases b <;> (try casesm* Basis8) <;> decide

theorem unique_product_readback (a b : SignedBasis) :
    ∃! c : SignedBasis, cell c = cell a * cell b := by
  refine ⟨product a b, product_cell a b, ?_⟩
  intro c hc
  exact cell_injective (hc.trans (product_cell a b).symm)

theorem product_eq_zero_iff (a b : SignedBasis) :
    product a b = zero ↔ cell a * cell b = cell zero := by
  rw [← product_cell]
  exact cell_injective.eq_iff.symm

theorem product_noncommutative :
    product (pos u1) (pos u2) ≠ product (pos u2) (pos u1) := by
  decide

theorem product_nonassociative :
    product (product (pos e11) (pos u1)) (pos u2) ≠
      product (pos e11) (product (pos u1) (pos u2)) := by
  decide

end InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8.SignedBasis
