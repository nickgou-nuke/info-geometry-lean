/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Quantum.KrausBoundaryDuality

/-!
# Commutator energy and finite Kraus fixed points

For the Heisenberg map `X ↦ ∑ i, star (K i) * X * K i`, unitality
gives an exact identity for the sum of commutator Gram matrices. At a fixed
point this is the Schwarz defect of its adjoint square.
Native positivity and finite trace then give a fixed-square criterion.
The second completeness equation makes the map trace preserving and removes
the square-fixed hypothesis. All operators act on the full matrix algebra.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Quantum.Choi

open scoped BigOperators ComplexOrder

variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A finite sum of matrix Gram traces vanishes exactly when every matrix
vanishes. The scalar positivity here is inherited from native matrix PSD. -/
theorem trace_sum_star_mul_self_eq_zero_iff (C : ι → Matrix n n ℂ) :
    Matrix.trace (∑ i, star (C i) * C i) = 0 ↔ ∀ i, C i = 0 := by
  rw [Matrix.trace_sum]
  have hn (i : ι) : 0 ≤ Matrix.trace (star (C i) * C i) :=
    (Matrix.posSemidef_conjTranspose_mul_self (C i)).trace_nonneg
  constructor
  · intro h i
    have hz : Matrix.trace (star (C i) * C i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp h i (Finset.mem_univ i)
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
  · intro h
    simp [h]

/-- Exact noncommutative commutator-energy identity for a unital Heisenberg
Kraus map. No commutation or fixed-point hypothesis is used in its expansion. -/
theorem krausMap_adjoint_commutator_gram
    (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hcomplete : (∑ i, star (K i) * K i) = 1) :
    (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) =
      krausMap (fun i => star (K i)) (star X * X) -
        krausMap (fun i => star (K i)) (star X) * X -
        star X * krausMap (fun i => star (K i)) X + star X * X := by
  change (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) =
    (∑ i, star (K i) * (star X * X) * star (star (K i))) -
      (∑ i, star (K i) * star X * star (star (K i))) * X -
      star X * (∑ i, star (K i) * X * star (star (K i))) + star X * X
  simp only [star_star]
  calc
    (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) =
        ∑ i, (star (K i) * (star X * X) * K i -
          (star (K i) * star X * K i) * X -
          star X * (star (K i) * X * K i) +
          star X * (star (K i) * K i) * X) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [star_sub, star_mul]
      noncomm_ring
    _ = (∑ i, star (K i) * (star X * X) * K i) -
          (∑ i, star (K i) * star X * K i) * X -
          star X * (∑ i, star (K i) * X * K i) +
          star X * (∑ i, star (K i) * K i) * X := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
    _ = _ := by rw [hcomplete, mul_one]

/-- Commutation with each Kraus coefficient gives both fixedness and
fixedness of the adjoint square under the unital Heisenberg action. -/
theorem krausMap_adjoint_fixed_and_square_of_commute
    (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hcomplete : (∑ i, star (K i) * K i) = 1)
    (hcomm : ∀ i, X * K i = K i * X) :
    krausMap (fun i => star (K i)) X = X ∧
      krausMap (fun i => star (K i)) (star X * X) = star X * X := by
  have hstar (i : ι) : star (K i) * star X = star X * star (K i) := by
    simpa only [star_mul] using congrArg star (hcomm i)
  constructor
  · change (∑ i, star (K i) * X * star (star (K i))) = X
    simp only [star_star]
    calc
      (∑ i, star (K i) * X * K i) = ∑ i, (star (K i) * K i) * X := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc, hcomm i, ← mul_assoc]
      _ = X := by rw [← Finset.sum_mul, hcomplete, one_mul]
  · change (∑ i, star (K i) * (star X * X) * star (star (K i))) = star X * X
    simp only [star_star]
    calc
      (∑ i, star (K i) * (star X * X) * K i) =
          ∑ i, star X * (star (K i) * K i) * X := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          star (K i) * (star X * X) * K i =
              (star (K i) * star X) * (X * K i) := by noncomm_ring
          _ = (star X * star (K i)) * (K i * X) := by rw [hstar i, hcomm i]
          _ = star X * (star (K i) * K i) * X := by noncomm_ring
      _ = star X * X := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hcomplete, mul_one]

/-- A fixed operator whose adjoint square is also fixed commutes with every
Kraus coefficient. The converse needs only the same unitality equation. -/
theorem krausMap_adjoint_fixed_and_square_iff_commute
    (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hcomplete : (∑ i, star (K i) * K i) = 1) :
    (krausMap (fun i => star (K i)) X = X ∧
      krausMap (fun i => star (K i)) (star X * X) = star X * X) ↔
      ∀ i, X * K i = K i * X := by
  constructor
  · rintro ⟨hx, hxx⟩
    have hxs : krausMap (fun i => star (K i)) (star X) = star X := by
      rw [← star_krausMap, hx]
    have hz : (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) = 0 := by
      rw [krausMap_adjoint_commutator_gram K X hcomplete, hx, hxs, hxx]
      noncomm_ring
    have htr : Matrix.trace
        (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) = 0 := by
      rw [hz, Matrix.trace_zero]
    intro i
    exact sub_eq_zero.mp
      ((trace_sum_star_mul_self_eq_zero_iff (fun i => X * K i - K i * X)).mp htr i)
  · exact krausMap_adjoint_fixed_and_square_of_commute K X hcomplete

/-- With both ordered completeness equations, finite trace positivity makes
every fixed operator commute with all Kraus coefficients. -/
theorem krausMap_adjoint_fixed_iff_commute_of_bistochastic
    (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hright : (∑ i, star (K i) * K i) = 1)
    (hleft : (∑ i, K i * star (K i)) = 1) :
    krausMap (fun i => star (K i)) X = X ↔
      ∀ i, X * K i = K i * X := by
  constructor
  · intro hx
    have hxs : krausMap (fun i => star (K i)) (star X) = star X := by
      rw [← star_krausMap, hx]
    have htrace : Matrix.trace (krausMap (fun i => star (K i)) (star X * X)) =
        Matrix.trace (star X * X) := by
      apply trace_krausMap_of_completeness
      simpa only [star_star] using hleft
    have htr : Matrix.trace
        (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) = 0 := by
      rw [krausMap_adjoint_commutator_gram K X hright, hx, hxs,
        Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htrace]
      abel
    intro i
    exact sub_eq_zero.mp
      ((trace_sum_star_mul_self_eq_zero_iff (fun i => X * K i - K i * X)).mp htr i)
  · intro hcomm
    exact (krausMap_adjoint_fixed_and_square_of_commute K X hright hcomm).1

/-- Fixedness of a self-adjoint idempotent supplies the square-fixed
hypothesis without trace preservation of the Heisenberg map. -/
theorem commute_of_krausMap_adjoint_fixed_projection
    (K : ι → Matrix n n ℂ) (E : Matrix n n ℂ)
    (hcomplete : (∑ i, star (K i) * K i) = 1)
    (hstar : star E = E) (hsquare : E * E = E)
    (hfixed : krausMap (fun i => star (K i)) E = E) :
    ∀ i, E * K i = K i * E := by
  apply (krausMap_adjoint_fixed_and_square_iff_commute K E hcomplete).mp
  refine ⟨hfixed, ?_⟩
  simpa only [hstar, hsquare] using hfixed

/-- An explicit quadratic relation makes a fixed self-adjoint observable
square-fixed, hence commuting, for any unital finite Heisenberg Kraus map. -/
theorem commute_of_krausMap_adjoint_fixed_quadratic
    (K : ι → Matrix n n ℂ) (E : Matrix n n ℂ) (a b : ℂ)
    (hcomplete : (∑ i, star (K i) * K i) = 1)
    (hstar : star E = E) (hsquare : E * E = a • E + b • (1 : Matrix n n ℂ))
    (hfixed : krausMap (fun i => star (K i)) E = E) :
    ∀ i, E * K i = K i * E := by
  have hone : krausMap (fun i => star (K i)) (1 : Matrix n n ℂ) = 1 := by
    simpa only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, star_star, mul_one] using hcomplete
  apply (krausMap_adjoint_fixed_and_square_iff_commute K E hcomplete).mp
  refine ⟨hfixed, ?_⟩
  rw [hstar, hsquare, map_add, map_smul, map_smul, hfixed, hone]

end InfoGeometry.Quantum.Choi
