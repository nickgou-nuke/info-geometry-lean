/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornE6Simplicity
import Mathlib.Algebra.Lie.SerreConstruction

/-!
# Serre presentation map for the split Albert `E₆` stabilizer

The local Albert owner has a 78-dimensional Chevalley basis. This file evaluates
Mathlib's free Lie algebra on its six simple triples, verifies all six families
of Cartan--Serre relations, and descends the evaluation to a Lie homomorphism
from the Serre-quotient `LieAlgebra.e₆`. The map sends the quotient generators
to the corresponding Albert stabilizer elements and is proved bijective, yielding
a Lie algebra equivalence `LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.propDecidable

/-- Evaluate the six Cartan, positive-root, and negative-root generators in
the already constructed split Albert cubic stabilizer. -/
def h3zornE6SerreGenerator
    (g : CartanMatrix.Generators (Fin 6)) : h3zornCubicStabilizer :=
  match g with
  | .H i => e6SimpleH i
  | .E i => e6SimpleE i
  | .F i => e6SimpleF i

/-- The universal Lie homomorphism from the free Lie algebra on the E₆ Serre
generators to the split Albert cubic stabilizer. -/
def h3zornE6FreeSerreEval :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 6)) →ₗ⁅ℝ⁆
      h3zornCubicStabilizer :=
  FreeLieAlgebra.lift ℝ h3zornE6SerreGenerator

@[simp] theorem h3zornE6FreeSerreEval_H (i : Fin 6) :
    h3zornE6FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = e6SimpleH i := by
  simp [h3zornE6FreeSerreEval, h3zornE6SerreGenerator]

@[simp] theorem h3zornE6FreeSerreEval_E (i : Fin 6) :
    h3zornE6FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = e6SimpleE i := by
  simp [h3zornE6FreeSerreEval, h3zornE6SerreGenerator]

@[simp] theorem h3zornE6FreeSerreEval_F (i : Fin 6) :
    h3zornE6FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = e6SimpleF i := by
  simp [h3zornE6FreeSerreEval, h3zornE6SerreGenerator]

/-- The local and Mathlib E₆ Cartan matrices agree. -/
theorem h3zornE6_cartan_eq_mathlib :
    (fun i j : Fin 6 => Tag.cartan .E6 i j) = CartanMatrix.E 6 := by
  change Tag.cartan .E6 = CartanMatrix.E 6
  exact Tag.cartan_E6_eq_mathlib

/-- The free-Lie evaluation kills the Cartan-generator commutation relations. -/
theorem h3zornE6FreeSerreEval_HH (i j : Fin 6) :
    h3zornE6FreeSerreEval
      (CartanMatrix.Relations.HH ℝ (i, j)) = 0 := by
  change h3zornE6FreeSerreEval
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0
  rw [LieHom.map_lie, h3zornE6FreeSerreEval_H, h3zornE6FreeSerreEval_H]
  exact e6SimpleH_comm i j

/-- The free-Lie evaluation kills the simple positive/negative root relations. -/
theorem h3zornE6FreeSerreEval_EF (i j : Fin 6) :
    h3zornE6FreeSerreEval
      (CartanMatrix.Relations.EF ℝ (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair]
    change h3zornE6FreeSerreEval
      (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0
    rw [map_sub, LieHom.map_lie, h3zornE6FreeSerreEval_E,
      h3zornE6FreeSerreEval_F, h3zornE6FreeSerreEval_H]
    rw [e6Simple_bracket_EF_same]
    simp
  · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte]
    change h3zornE6FreeSerreEval
      ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0
    rw [LieHom.map_lie, h3zornE6FreeSerreEval_E, h3zornE6FreeSerreEval_F]
    exact e6Simple_bracket_EF_ne hij

/-- The free-Lie evaluation kills the `H,E` Cartan relations. -/
theorem h3zornE6FreeSerreEval_HE (i j : Fin 6) :
    h3zornE6FreeSerreEval
      (CartanMatrix.Relations.HE ℝ (CartanMatrix.E 6) (i, j)) = 0 := by
  simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair]
  simp only [Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  rw [map_sub, LieHom.map_lie, h3zornE6FreeSerreEval_H,
    h3zornE6FreeSerreEval_E, map_smul, h3zornE6FreeSerreEval_E]
  rw [e6Simple_bracket_HE]
  have hcartan := h3zornE6_cartan_eq_mathlib
  have hentry := congrFun (congrFun hcartan i) j
  rw [← congrArg (fun z : ℤ => (z : ℝ)) hentry]
  simp

/-- The free-Lie evaluation kills the `H,F` Cartan relations. -/
theorem h3zornE6FreeSerreEval_HF (i j : Fin 6) :
    h3zornE6FreeSerreEval
      (CartanMatrix.Relations.HF ℝ (CartanMatrix.E 6) (i, j)) = 0 := by
  simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair]
  simp only [Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  rw [map_add, LieHom.map_lie, h3zornE6FreeSerreEval_H,
    h3zornE6FreeSerreEval_F, map_smul, h3zornE6FreeSerreEval_F]
  rw [e6Simple_bracket_HF]
  have hcartan := h3zornE6_cartan_eq_mathlib
  have hentry := congrFun (congrFun hcartan i) j
  rw [← congrArg (fun z : ℤ => (z : ℝ)) hentry]
  simp

/-- Lie homomorphisms commute with iterated adjoint actions. -/
private theorem map_iterate_ad {R L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (x y : L) (n : ℕ) :
    f (Nat.iterate (fun z => ⁅x, z⁆) n y) =
      Nat.iterate (fun z => ⁅f x, z⁆) n (f y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', LieHom.map_lie, ih]

/-- Powers of the adjoint endomorphism are iterated brackets. -/
private theorem ad_pow_apply_eq_iterate {R L : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] (x y : L) (n : ℕ) :
    ((LieAlgebra.ad R L x) ^ n) y = Nat.iterate (fun z => ⁅x, z⁆) n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change (LieAlgebra.ad R L x) (((LieAlgebra.ad R L x) ^ n) y) = _
      rw [ih]
      simp only [LieAlgebra.ad_apply, Function.iterate_succ_apply']

/-- Off-diagonal E₆ Cartan entries are nonpositive, so the two Serre
exponent conventions agree after accounting for the initial bracket. -/
private theorem e6_cartan_offdiag_nonpos {i j : Fin 6} (hij : i ≠ j) :
    Tag.cartan .E6 i j ≤ 0 := by
  simp only [Tag.cartan, Tag.cartanE, hij, ↓reduceIte]
  split_ifs <;> omega

private theorem e6_serre_exponent {i j : Fin 6} (hij : i ≠ j) :
    (-Tag.cartan .E6 i j).toNat + 1 = (1 - Tag.cartan .E6 i j).toNat := by
  have h0 : 0 ≤ -Tag.cartan .E6 i j := neg_nonneg.mpr (e6_cartan_offdiag_nonpos hij)
  have h1 : 0 ≤ 1 - Tag.cartan .E6 i j := by
    have := e6_cartan_offdiag_nonpos hij
    omega
  omega

/-- The free-Lie evaluation kills the positive-root Serre relations. -/
theorem h3zornE6FreeSerreEval_adE (i j : Fin 6) :
    h3zornE6FreeSerreEval
      (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 6) (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [CartanMatrix.Relations.adE, Function.uncurry_apply_pair]
  · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair,
      Function.comp_apply]
    rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
      h3zornE6FreeSerreEval_E, h3zornE6FreeSerreEval_E,
      ← Function.iterate_succ_apply]
    have hcartan := h3zornE6_cartan_eq_mathlib
    rw [Nat.succ_eq_add_one, ← congrFun (congrFun hcartan i) j,
      e6_serre_exponent hij]
    exact e6Simple_serre_E hij

/-- The free-Lie evaluation kills the negative-root Serre relations. -/
theorem h3zornE6FreeSerreEval_adF (i j : Fin 6) :
    h3zornE6FreeSerreEval
      (CartanMatrix.Relations.adF ℝ (CartanMatrix.E 6) (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [CartanMatrix.Relations.adF, Function.uncurry_apply_pair]
  · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair,
      Function.comp_apply]
    rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
      h3zornE6FreeSerreEval_F, h3zornE6FreeSerreEval_F,
      ← Function.iterate_succ_apply]
    have hcartan := h3zornE6_cartan_eq_mathlib
    rw [Nat.succ_eq_add_one, ← congrFun (congrFun hcartan i) j,
      e6_serre_exponent hij]
    exact e6Simple_serre_F hij

/-- The evaluation kernel contains the full Lie ideal generated by all E₆
Cartan--Serre relations. -/
theorem h3zornE6FreeSerreEval_serreIdeal :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6) ≤
      h3zornE6FreeSerreEval.ker := by
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with hx | hAdF
  · rcases hx with hx | hAdE
    · rcases hx with hx | hHF
      · rcases hx with hx | hHE
        · rcases hx with hHH | hEF
          · rcases hHH with ⟨⟨i, j⟩, rfl⟩
            exact h3zornE6FreeSerreEval_HH i j
          · rcases hEF with ⟨⟨i, j⟩, rfl⟩
            exact h3zornE6FreeSerreEval_EF i j
        · rcases hHE with ⟨⟨i, j⟩, rfl⟩
          exact h3zornE6FreeSerreEval_HE i j
      · rcases hHF with ⟨⟨i, j⟩, rfl⟩
        exact h3zornE6FreeSerreEval_HF i j
    · rcases hAdE with ⟨⟨i, j⟩, rfl⟩
      exact h3zornE6FreeSerreEval_adE i j
  · rcases hAdF with ⟨⟨i, j⟩, rfl⟩
    exact h3zornE6FreeSerreEval_adF i j

private theorem h3zornE6FreeSerreEval_serreIdeal_submodule :
    (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)).toSubmodule ≤
      LinearMap.ker h3zornE6FreeSerreEval.toLinearMap := by
  exact h3zornE6FreeSerreEval_serreIdeal

/-- The free-Lie evaluation descends to Mathlib's Serre-quotient carrier. -/
noncomputable def h3zornE6SerreQuotientMap :
    LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ h3zornCubicStabilizer := by
  let I := CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)
  have hI : I.toSubmodule ≤ LinearMap.ker h3zornE6FreeSerreEval.toLinearMap := by
    exact h3zornE6FreeSerreEval_serreIdeal
  refine
    { I.toSubmodule.liftQ h3zornE6FreeSerreEval.toLinearMap hI with
      map_lie' := ?_ }
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          change h3zornE6FreeSerreEval ⁅x, y⁆ =
            ⁅h3zornE6FreeSerreEval x, h3zornE6FreeSerreEval y⁆
          exact LieHom.map_lie h3zornE6FreeSerreEval x y

@[simp] theorem h3zornE6SerreQuotientMap_H (i : Fin 6) :
    h3zornE6SerreQuotientMap
      (Submodule.Quotient.mk
        (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))) = e6SimpleH i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)).toSubmodule.liftQ
    h3zornE6FreeSerreEval.toLinearMap h3zornE6FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [h3zornE6FreeSerreEval_H]

@[simp] theorem h3zornE6SerreQuotientMap_E (i : Fin 6) :
    h3zornE6SerreQuotientMap
      (Submodule.Quotient.mk
        (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))) = e6SimpleE i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)).toSubmodule.liftQ
    h3zornE6FreeSerreEval.toLinearMap h3zornE6FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [h3zornE6FreeSerreEval_E]

@[simp] theorem h3zornE6SerreQuotientMap_F (i : Fin 6) :
    h3zornE6SerreQuotientMap
      (Submodule.Quotient.mk
        (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))) = e6SimpleF i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)).toSubmodule.liftQ
    h3zornE6FreeSerreEval.toLinearMap h3zornE6FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [h3zornE6FreeSerreEval_F]

/-- The descended Serre map is surjective: the root-chain certificates show
that the simple Cartan and root generators generate the full Albert stabilizer. -/
theorem h3zornE6SerreQuotientMap_surjective :
    Function.Surjective h3zornE6SerreQuotientMap := by
  apply (LieHom.range_eq_top h3zornE6SerreQuotientMap).mp
  apply h3zornE6_simple_generators_generate h3zornE6SerreQuotientMap.range
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)),
      h3zornE6SerreQuotientMap_H i⟩
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)),
      h3zornE6SerreQuotientMap_E i⟩
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)),
      h3zornE6SerreQuotientMap_F i⟩

/-- A linear section obtained by lifting the 78 Chevalley basis vectors through
the surjective Serre map. -/
noncomputable def h3zornE6SerreQuotientSection :
    h3zornCubicStabilizer →ₗ[ℝ] LieAlgebra.e₆ ℝ :=
  e6ChevalleyBasis.constr ℝ fun i =>
    Classical.choose (h3zornE6SerreQuotientMap_surjective (e6ChevalleyBasis i))

/-- The section lifts each Cartan and root vector to the Serre quotient. -/
theorem h3zornE6SerreQuotientMap_section_basis (i : Fin 6 ⊕ Fin 72) :
    h3zornE6SerreQuotientMap
      (h3zornE6SerreQuotientSection (e6ChevalleyBasis i)) = e6ChevalleyBasis i := by
  rw [h3zornE6SerreQuotientSection, e6ChevalleyBasis.constr_basis]
  exact Classical.choose_spec
    (h3zornE6SerreQuotientMap_surjective (e6ChevalleyBasis i))

/-- The lifted basis splits the Serre map on the entire Albert stabilizer. -/
theorem h3zornE6SerreQuotientMap_section_leftInverse :
    h3zornE6SerreQuotientMap.toLinearMap.comp h3zornE6SerreQuotientSection =
      LinearMap.id := by
  apply e6ChevalleyBasis.ext
  intro i
  simp [LinearMap.comp_apply, h3zornE6SerreQuotientMap_section_basis]

/-- In particular, the 78 Chevalley directions embed linearly into the Serre
quotient; the remaining dimension problem is an upper bound on that quotient. -/
theorem h3zornE6SerreQuotientSection_injective :
    Function.Injective h3zornE6SerreQuotientSection := by
  intro x y hxy
  have h := congrArg h3zornE6SerreQuotientMap.toLinearMap hxy
  change (h3zornE6SerreQuotientMap.toLinearMap.comp
    h3zornE6SerreQuotientSection) x =
      (h3zornE6SerreQuotientMap.toLinearMap.comp
        h3zornE6SerreQuotientSection) y at h
  rw [h3zornE6SerreQuotientMap_section_leftInverse,
    LinearMap.id_apply, LinearMap.id_apply] at h
  exact h

/-- If the Serre quotient is finite-dimensional, its dimension is at least 78:
the target Chevalley basis embeds through the constructed section. -/
theorem h3zornE6SerreQuotient_finrank_lower_bound
    [FiniteDimensional ℝ (LieAlgebra.e₆ ℝ)] :
    78 ≤ Module.finrank ℝ (LieAlgebra.e₆ ℝ) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := h3zornE6SerreQuotientSection)
    h3zornE6SerreQuotientSection_injective
  rw [finrank_h3zornCubicStabilizer] at h
  exact h

/-- The Serre presentation is isomorphic to the Albert stabilizer once its
finite-dimensional dimension is established as 78. This theorem exposes the
remaining classical Serre-dimension calculation as the only hypothesis needed
to upgrade the verified generator map to an equivalence. -/
noncomputable def h3zornE6SerreQuotientEquivOfFinrank
    [FiniteDimensional ℝ (LieAlgebra.e₆ ℝ)]
    (hdim : Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78) :
    LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer := by
  letI : FiniteDimensional ℝ h3zornCubicStabilizer :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_h3zornCubicStabilizer]; decide)
  have hdim' : Module.finrank ℝ (LieAlgebra.e₆ ℝ) =
      Module.finrank ℝ h3zornCubicStabilizer := by
    rw [hdim, finrank_h3zornCubicStabilizer]
  have hsurj : Function.Surjective
      (h3zornE6SerreQuotientMap.toLinearMap) :=
    h3zornE6SerreQuotientMap_surjective
  have hinj : Function.Injective
      (h3zornE6SerreQuotientMap.toLinearMap) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').2 hsurj
  exact LieEquiv.ofBijective h3zornE6SerreQuotientMap ⟨hinj, hsurj⟩

/-! ### Serre quotient finite-dimensionality (78D Chevalley span) and isomorphism closure -/

private def e6SerreMk :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 6)) →ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ where
  toLinearMap := (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)).toSubmodule.mkQ
  map_lie' := fun {_ _} => rfl

/-- The simple Cartan generators inside Mathlib's `LieAlgebra.e₆ ℝ`. -/
def e6SerreH (i : Fin 6) : LieAlgebra.e₆ ℝ :=
  e6SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))

/-- The simple positive root generators inside Mathlib's `LieAlgebra.e₆ ℝ`. -/
def e6SerreE (i : Fin 6) : LieAlgebra.e₆ ℝ :=
  e6SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))

/-- The simple negative root generators inside Mathlib's `LieAlgebra.e₆ ℝ`. -/
def e6SerreF (i : Fin 6) : LieAlgebra.e₆ ℝ :=
  e6SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))

/-- Any Lie subalgebra of `LieAlgebra.e₆ ℝ` containing the 18 Chevalley generators
equals the whole Lie algebra. -/
theorem e6Serre_generators_generate (S : LieSubalgebra ℝ (LieAlgebra.e₆ ℝ))
    (hH : ∀ i, e6SerreH i ∈ S)
    (hE : ∀ i, e6SerreE i ∈ S)
    (hF : ∀ i, e6SerreF i ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let g : CartanMatrix.Generators (Fin 6) → S := fun gen =>
    match gen with
    | .H i => ⟨e6SerreH i, hH i⟩
    | .E i => ⟨e6SerreE i, hE i⟩
    | .F i => ⟨e6SerreF i, hF i⟩
  have hcomp : S.incl.comp (FreeLieAlgebra.lift ℝ g) = e6SerreMk := by
    apply FreeLieAlgebra.hom_ext
    intro gen
    cases gen with
    | H i => simp [g, e6SerreH]
    | E i => simp [g, e6SerreE]
    | F i => simp [g, e6SerreF]
  have hy : e6SerreMk y = S.incl (FreeLieAlgebra.lift ℝ g y) := by
    rw [← hcomp]
    rfl
  change e6SerreMk y ∈ S
  rw [hy]
  exact (FreeLieAlgebra.lift ℝ g y).2

private theorem e6SerreMk_mem_ideal_zero
    {x : FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 6))}
    (hx : x ∈ CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6)) :
    e6SerreMk x = 0 := by
  change LieSubmodule.Quotient.mk x = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan hx

private theorem e6SerreH_comm (i j : Fin 6) : ⁅e6SerreH i, e6SerreH j⁆ = 0 := by
  have hx : CartanMatrix.Relations.HH ℝ (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩))))
  have h := e6SerreMk_mem_ideal_zero hx
  change e6SerreMk
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0 at h
  simpa [LieHom.map_lie, e6SerreH] using h

private theorem e6Serre_bracket_EF_same (i : Fin 6) :
    ⁅e6SerreE i, e6SerreF i⁆ = e6SerreH i := by
  have hx : CartanMatrix.Relations.EF ℝ (i, i) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i), rfl⟩))))
  have h := e6SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte] at h
  change e6SerreMk
    (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0 at h
  rw [map_sub, LieHom.map_lie] at h
  exact sub_eq_zero.mp h

private theorem e6Serre_bracket_EF_ne {i j : Fin 6} (hij : i ≠ j) :
    ⁅e6SerreE i, e6SerreF j⁆ = 0 := by
  have hx : CartanMatrix.Relations.EF ℝ (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))))
  have h := e6SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte] at h
  change e6SerreMk
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0 at h
  simpa [LieHom.map_lie, e6SerreE, e6SerreF] using h

private theorem e6Serre_bracket_HE (i j : Fin 6) :
    ⁅e6SerreH i, e6SerreE j⁆ = ((Tag.cartan .E6 i j : ℤ) : ℝ) • e6SerreE j := by
  have hx : CartanMatrix.Relations.HE ℝ (CartanMatrix.E 6) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩)))
  have h := e6SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair,
    Function.comp_apply] at h
  rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, map_smul] at h
  have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
  rw [← hentry] at h
  exact sub_eq_zero.mp h

private theorem e6Serre_bracket_HF (i j : Fin 6) :
    ⁅e6SerreH i, e6SerreF j⁆ = (-(Tag.cartan .E6 i j : ℤ) : ℝ) • e6SerreF j := by
  have hx : CartanMatrix.Relations.HF ℝ (CartanMatrix.E 6) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))
  have h := e6SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair,
    Function.comp_apply] at h
  rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, map_smul] at h
  have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
  rw [← hentry] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

private theorem e6Serre_adE_iter {i j : Fin 6} (hij : i ≠ j) :
    Nat.iterate (fun x => ⁅e6SerreE i, x⁆)
      (1 - Tag.cartan .E6 i j).toNat (e6SerreE j) = 0 := by
  have hx : CartanMatrix.Relations.adE ℝ (CartanMatrix.E 6) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inl (Or.inr ⟨(i, j), rfl⟩)
  have h := e6SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair,
    Function.comp_apply] at h
  rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
    ← Function.iterate_succ_apply] at h
  have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
  rw [Nat.succ_eq_add_one, ← hentry, e6_serre_exponent hij] at h
  exact h

private theorem e6Serre_adF_iter {i j : Fin 6} (hij : i ≠ j) :
    Nat.iterate (fun x => ⁅e6SerreF i, x⁆)
      (1 - Tag.cartan .E6 i j).toNat (e6SerreF j) = 0 := by
  have hx : CartanMatrix.Relations.adF ℝ (CartanMatrix.E 6) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 6) :=
    Or.inr ⟨(i, j), rfl⟩
  have h := e6SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair,
    Function.comp_apply] at h
  rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
    ← Function.iterate_succ_apply] at h
  have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
  rw [Nat.succ_eq_add_one, ← hentry, e6_serre_exponent hij] at h
  exact h

private theorem e6Serre_adE_zero {i j : Fin 6} (hc : Tag.cartan .E6 i j = 0) :
    ⁅e6SerreE i, e6SerreE j⁆ = 0 := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hd : Tag.cartan .E6 i i = 2 := by
      simp [Tag.cartan, Tag.cartanE]
    omega
  have h := e6Serre_adE_iter hij
  rw [hc] at h
  simpa using h

private theorem e6Serre_adE_negOne {i j : Fin 6} (hc : Tag.cartan .E6 i j = -1) :
    ⁅e6SerreE i, ⁅e6SerreE i, e6SerreE j⁆⁆ = 0 := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hd : Tag.cartan .E6 i i = 2 := by
      simp [Tag.cartan, Tag.cartanE]
    omega
  have h := e6Serre_adE_iter hij
  rw [hc] at h
  simpa using h

private theorem e6_cartan_offdiag_cases {i j : Fin 6} (hij : i ≠ j) :
    Tag.cartan .E6 i j = 0 ∨ Tag.cartan .E6 i j = -1 := by
  simp only [Tag.cartan, Tag.cartanE, hij, ↓reduceIte]
  split_ifs <;> simp

private theorem e6Serre_adE_sq_gen (i j : Fin 6) :
    ⁅e6SerreE i, ⁅e6SerreE i, e6SerreE j⁆⁆ = 0 := by
  by_cases hij : i = j
  · subst hij
    simp [lie_self]
  · rcases e6_cartan_offdiag_cases hij with h0 | h1
    · rw [e6Serre_adE_zero h0, lie_zero]
    · exact e6Serre_adE_negOne h1

/-! #### Chevalley involution on `LieAlgebra.e₆ ℝ` -/

private def e6SerreChevalleyGen
    (g : CartanMatrix.Generators (Fin 6)) : LieAlgebra.e₆ ℝ :=
  match g with
  | .H i => -e6SerreH i
  | .E i => e6SerreF i
  | .F i => e6SerreE i

private noncomputable def e6SerreChevalleyFree :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 6)) →ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ :=
  FreeLieAlgebra.lift ℝ e6SerreChevalleyGen

private theorem e6SerreChevalleyFree_serreIdeal :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6) ≤
      e6SerreChevalleyFree.ker := by
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
      ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · change e6SerreChevalleyFree
      ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0
    simp [e6SerreChevalleyFree, e6SerreChevalleyGen, e6SerreH_comm]
  · change e6SerreChevalleyFree (CartanMatrix.Relations.EF ℝ (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte]
      change e6SerreChevalleyFree
        (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0
      simp only [map_sub, LieHom.map_lie, e6SerreChevalleyFree,
        FreeLieAlgebra.lift_of_apply, e6SerreChevalleyGen]
      rw [← lie_skew (e6SerreF i) (e6SerreE i), e6Serre_bracket_EF_same, sub_neg_eq_add,
        neg_add_cancel]
    · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte]
      change e6SerreChevalleyFree
        ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0
      simp only [LieHom.map_lie, e6SerreChevalleyFree, FreeLieAlgebra.lift_of_apply,
        e6SerreChevalleyGen]
      rw [← lie_skew (e6SerreF i) (e6SerreE j), e6Serre_bracket_EF_ne (Ne.symm hij), neg_zero]
  · change e6SerreChevalleyFree
      (CartanMatrix.Relations.HE ℝ (CartanMatrix.E 6) (i, j)) = 0
    simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair,
      Function.comp_apply]
    rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, map_smul]
    simp only [e6SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e6SerreChevalleyGen,
      neg_lie, e6Serre_bracket_HF]
    have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
    rw [← hentry, neg_smul, neg_neg, sub_self]
  · change e6SerreChevalleyFree
      (CartanMatrix.Relations.HF ℝ (CartanMatrix.E 6) (i, j)) = 0
    simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair,
      Function.comp_apply]
    rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, map_smul]
    simp only [e6SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e6SerreChevalleyGen,
      neg_lie, e6Serre_bracket_HE]
    have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
    rw [← hentry, neg_add_cancel]
  · change e6SerreChevalleyFree
      (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 6) (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.Relations.adE, Function.uncurry_apply_pair]
    · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair,
        Function.comp_apply]
      rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
        ← Function.iterate_succ_apply]
      simp only [e6SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e6SerreChevalleyGen]
      have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
      rw [Nat.succ_eq_add_one, ← hentry, e6_serre_exponent hij]
      exact e6Serre_adF_iter hij
  · change e6SerreChevalleyFree
      (CartanMatrix.Relations.adF ℝ (CartanMatrix.E 6) (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.Relations.adF, Function.uncurry_apply_pair]
    · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair,
        Function.comp_apply]
      rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
        ← Function.iterate_succ_apply]
      simp only [e6SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e6SerreChevalleyGen]
      have hentry := congrFun (congrFun h3zornE6_cartan_eq_mathlib i) j
      rw [Nat.succ_eq_add_one, ← hentry, e6_serre_exponent hij]
      exact e6Serre_adE_iter hij

private noncomputable def e6SerreChevalleyHom :
    LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ :=
  { (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 6)).toSubmodule.liftQ
      e6SerreChevalleyFree.toLinearMap e6SerreChevalleyFree_serreIdeal with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
              change e6SerreChevalleyFree ⁅x, y⁆ =
                ⁅e6SerreChevalleyFree x, e6SerreChevalleyFree y⁆
              exact LieHom.map_lie e6SerreChevalleyFree x y }

@[simp] private theorem e6SerreChevalleyHom_H (i : Fin 6) :
    e6SerreChevalleyHom (e6SerreH i) = -e6SerreH i := by
  change e6SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = _
  simp [e6SerreChevalleyFree, e6SerreChevalleyGen]

@[simp] private theorem e6SerreChevalleyHom_E (i : Fin 6) :
    e6SerreChevalleyHom (e6SerreE i) = e6SerreF i := by
  change e6SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = _
  simp [e6SerreChevalleyFree, e6SerreChevalleyGen]

@[simp] private theorem e6SerreChevalleyHom_F (i : Fin 6) :
    e6SerreChevalleyHom (e6SerreF i) = e6SerreE i := by
  change e6SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = _
  simp [e6SerreChevalleyFree, e6SerreChevalleyGen]

private theorem e6SerreChevalleyHom_involutive (x : LieAlgebra.e₆ ℝ) :
    e6SerreChevalleyHom (e6SerreChevalleyHom x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hcomp : (e6SerreChevalleyHom.comp e6SerreChevalleyHom).comp e6SerreMk = e6SerreMk := by
    apply FreeLieAlgebra.hom_ext
    intro gen
    cases gen with
    | H i =>
        change e6SerreChevalleyHom (e6SerreChevalleyHom (e6SerreH i)) = e6SerreH i
        simp
    | E i =>
        change e6SerreChevalleyHom (e6SerreChevalleyHom (e6SerreE i)) = e6SerreE i
        simp
    | F i =>
        change e6SerreChevalleyHom (e6SerreChevalleyHom (e6SerreF i)) = e6SerreF i
        simp
  exact congrArg (fun f => f y) hcomp

/-- The Chevalley involution on `LieAlgebra.e₆ ℝ`, swapping `E_i ↔ F_i` and negating `H_i`. -/
noncomputable def e6SerreChevalleyInv :
    LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ :=
  LieEquiv.ofBijective e6SerreChevalleyHom
    ⟨Function.LeftInverse.injective e6SerreChevalleyHom_involutive,
      Function.RightInverse.surjective e6SerreChevalleyHom_involutive⟩

@[simp] private theorem e6SerreChevalleyInv_H (i : Fin 6) :
    e6SerreChevalleyInv (e6SerreH i) = -e6SerreH i :=
  e6SerreChevalleyHom_H i

@[simp] private theorem e6SerreChevalleyInv_E (i : Fin 6) :
    e6SerreChevalleyInv (e6SerreE i) = e6SerreF i :=
  e6SerreChevalleyHom_E i

@[simp] private theorem e6SerreChevalleyInv_F (i : Fin 6) :
    e6SerreChevalleyInv (e6SerreF i) = e6SerreE i :=
  e6SerreChevalleyHom_F i

/-! #### 36 positive root vectors in `LieAlgebra.e₆ ℝ` -/

private def simplePosIdx (i : Fin 6) : Fin 36 :=
  match i.val with
  | 0 => 5 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 4 | _ => 5

private def simpleOfPos (p : Fin 36) : Fin 6 :=
  match p.val with
  | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 5 | 5 => 0 | _ => 0

private def e6PosHeight (p : Fin 36) : ℕ :=
  match p.val with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1
  | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | 10 => 2
  | 11 => 3 | 12 => 3 | 13 => 3 | 14 => 3 | 15 => 3
  | 16 => 4 | 17 => 4 | 18 => 4 | 19 => 4 | 20 => 4
  | 21 => 5 | 22 => 5 | 23 => 5 | 24 => 5
  | 25 => 6 | 26 => 6 | 27 => 6
  | 28 => 7 | 29 => 7 | 30 => 7
  | 31 => 8 | 32 => 8
  | 33 => 9
  | 34 => 10
  | 35 => 11
  | _ => 1

private def e6PosParent (p : Fin 36) : Option (Fin 6 × Fin 36) :=
  match p.val with
  | 6 => some (1, 1) | 7 => some (3, 2) | 8 => some (2, 1)
  | 9 => some (0, 3) | 10 => some (4, 4) | 11 => some (2, 7)
  | 12 => some (1, 7) | 13 => some (1, 8) | 14 => some (0, 8)
  | 15 => some (3, 10) | 16 => some (1, 11) | 17 => some (0, 13)
  | 18 => some (1, 15) | 19 => some (2, 15) | 20 => some (0, 11)
  | 21 => some (0, 19) | 22 => some (3, 16) | 23 => some (1, 19)
  | 24 => some (0, 16) | 25 => some (0, 23) | 26 => some (3, 23)
  | 27 => some (0, 22) | 28 => some (0, 26) | 29 => some (2, 27)
  | 30 => some (4, 26) | 31 => some (0, 30) | 32 => some (2, 28)
  | 33 => some (2, 31) | 34 => some (3, 33) | 35 => some (1, 34)
  | _ => none

private theorem e6PosParent_lt {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) : p₀.val < p.val := by
  revert p k p₀ hp
  decide

/-- The 36 positive root vectors inside `LieAlgebra.e₆ ℝ`, built inductively
by height from the six simple positive generators `e6SerreE i`. -/
noncomputable def e6SerrePosVec (p : Fin 36) : LieAlgebra.e₆ ℝ :=
  match hp : e6PosParent p with
  | none => e6SerreE (simpleOfPos p)
  | some (k, p₀) =>
      have _ : p₀.val < p.val := e6PosParent_lt hp
      ⁅e6SerreE k, e6SerrePosVec p₀⁆
termination_by p.val

private theorem e6_ht_le_one_simple {p : Fin 36} (hp : e6PosParent p = none) :
    e6SerrePosVec p = e6SerreE (simpleOfPos p) := by
  rw [e6SerrePosVec]
  split
  · rfl
  · next h => exact absurd (hp.symm.trans h) (by simp)

private theorem e6SerrePosVec_simple (i : Fin 6) :
    e6SerrePosVec (simplePosIdx i) = e6SerreE i := by
  fin_cases i <;>
    · rw [e6_ht_le_one_simple rfl]
      rfl

private theorem e6SerrePosVec_parent {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) :
    e6SerrePosVec p = ⁅e6SerreE k, e6SerrePosVec p₀⁆ := by
  rw [e6SerrePosVec]
  split
  · next h => exact absurd (hp.symm.trans h) (by simp)
  · next k' p₀' h =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans h))
      rfl

private def e6Cartan (i j : Fin 6) : ℤ :=
  if i = j then 2
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨ (i.val = 1 ∧ j.val = 3) ∨
      (i.val = 3 ∧ j.val = 1) ∨ (2 ≤ i.val ∧ j.val = i.val + 1) ∨
      (2 ≤ j.val ∧ i.val = j.val + 1) then -1
  else 0

private lemma e6Cartan_eq (i j : Fin 6) : Tag.cartan .E6 i j = e6Cartan i j := rfl

/-- Next positive root entry `(positiveSign, target)` for `⁅e6SerreE i, e6SerrePosVec p⁆`. -/
private def e6PosUp (i : Fin 6) (p : Fin 36) : Option (Bool × Fin 36) :=
  match i.val, p.val with
  | 0, 3 => some (true, 9) | 0, 8 => some (true, 14) | 0, 11 => some (true, 20)
  | 0, 13 => some (true, 17) | 0, 16 => some (true, 24) | 0, 19 => some (true, 21)
  | 0, 22 => some (true, 27) | 0, 23 => some (true, 25) | 0, 26 => some (true, 28)
  | 0, 30 => some (true, 31)
  | 1, 1 => some (true, 6) | 1, 7 => some (true, 12) | 1, 8 => some (true, 13)
  | 1, 11 => some (true, 16) | 1, 14 => some (true, 17) | 1, 15 => some (true, 18)
  | 1, 19 => some (true, 23) | 1, 20 => some (true, 24) | 1, 21 => some (true, 25)
  | 1, 34 => some (true, 35)
  | 2, 1 => some (true, 8) | 2, 5 => some (false, 9) | 2, 6 => some (true, 13)
  | 2, 7 => some (true, 11) | 2, 12 => some (true, 16) | 2, 15 => some (true, 19)
  | 2, 18 => some (true, 23) | 2, 27 => some (true, 29) | 2, 28 => some (true, 32)
  | 2, 31 => some (true, 33)
  | 3, 0 => some (false, 6) | 3, 2 => some (true, 7) | 3, 3 => some (false, 8)
  | 3, 9 => some (false, 14) | 3, 10 => some (true, 15) | 3, 16 => some (true, 22)
  | 3, 23 => some (true, 26) | 3, 24 => some (true, 27) | 3, 25 => some (true, 28)
  | 3, 33 => some (true, 34)
  | 4, 1 => some (false, 7) | 4, 4 => some (true, 10) | 4, 6 => some (false, 12)
  | 4, 8 => some (false, 11) | 4, 13 => some (false, 16) | 4, 14 => some (false, 20)
  | 4, 17 => some (false, 24) | 4, 26 => some (true, 30) | 4, 28 => some (true, 31)
  | 4, 32 => some (true, 33)
  | 5, 2 => some (false, 10) | 5, 7 => some (false, 15) | 5, 11 => some (false, 19)
  | 5, 12 => some (false, 18) | 5, 16 => some (false, 23) | 5, 20 => some (false, 21)
  | 5, 22 => some (false, 26) | 5, 24 => some (false, 25) | 5, 27 => some (false, 28)
  | 5, 29 => some (false, 32)
  | _, _ => none

private def isSelfParent (i : Fin 6) (p : Fin 36) : Bool :=
  match e6PosUp i p with
  | some (true, q) => e6PosParent q == some (i, p)
  | _ => false

private noncomputable def evalPosUp : Option (Bool × Fin 36) → LieAlgebra.e₆ ℝ
  | none => 0
  | some (true, q) => e6SerrePosVec q
  | some (false, q) => -e6SerrePosVec q

private lemma two_smul_bracket_eq_ad_sq {x z y : LieAlgebra.e₆ ℝ}
    (hxz : ⁅x, ⁅x, z⁆⁆ = 0) (hxy : ⁅x, ⁅x, y⁆⁆ = 0) :
    (2 : ℝ) • ⁅x, ⁅z, ⁅x, y⁆⁆⁆ = ⁅x, ⁅x, ⁅z, y⁆⁆⁆ := by
  have h1 : ⁅x, ⁅x, ⁅z, y⁆⁆⁆ =
      ⁅x, ⁅⁅x, z⁆, y⁆⁆ + ⁅x, ⁅z, ⁅x, y⁆⁆⁆ := by
    rw [leibniz_lie x z y, lie_add]
  have h2 : ⁅x, ⁅⁅x, z⁆, y⁆⁆ = ⁅⁅x, z⁆, ⁅x, y⁆⁆ := by
    rw [leibniz_lie x ⁅x, z⁆ y, hxz, zero_lie, zero_add]
  have h3 : ⁅⁅x, z⁆, ⁅x, y⁆⁆ = ⁅x, ⁅z, ⁅x, y⁆⁆⁆ := by
    rw [lie_lie x z ⁅x, y⁆, hxy, lie_zero, sub_zero]
  rw [h1, h2, h3, two_smul]

private lemma two_smul_comm_ad_eq_zero {a b w : LieAlgebra.e₆ ℝ}
    (hab : ⁅a, b⁆ = 0) (haw : ⁅w, ⁅a, w⁆⁆ = 0) (hbw : ⁅w, ⁅b, w⁆⁆ = 0) :
    ⁅⁅a, w⁆, ⁅b, w⁆⁆ = 0 := by
  have hL : ⁅⁅a, w⁆, ⁅b, w⁆⁆ = -⁅w, ⁅a, ⁅b, w⁆⁆⁆ := by
    rw [lie_lie a w ⁅b, w⁆, hbw, lie_zero, zero_sub]
  have hR : ⁅⁅b, w⁆, ⁅a, w⁆⁆ = -⁅w, ⁅b, ⁅a, w⁆⁆⁆ := by
    rw [lie_lie b w ⁅a, w⁆, haw, lie_zero, zero_sub]
  have hcomm : ⁅a, ⁅b, w⁆⁆ = ⁅b, ⁅a, w⁆⁆ := by
    rw [leibniz_lie a b w, hab, zero_lie, zero_add]
  have h2 : (2 : ℝ) • ⁅⁅a, w⁆, ⁅b, w⁆⁆ = 0 := by
    rw [two_smul]
    calc ⁅⁅a, w⁆, ⁅b, w⁆⁆ + ⁅⁅a, w⁆, ⁅b, w⁆⁆
        = ⁅⁅a, w⁆, ⁅b, w⁆⁆ - ⁅⁅b, w⁆, ⁅a, w⁆⁆ := by
            rw [← lie_skew ⁅b, w⁆ ⁅a, w⁆, sub_neg_eq_add]
      _ = -⁅w, ⁅a, ⁅b, w⁆⁆⁆ - -⁅w, ⁅b, ⁅a, w⁆⁆⁆ := by rw [hL, hR]
      _ = 0 := by rw [hcomm, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

private lemma e6PosParent_ht_lt_bool :
    ∀ p : Fin 36, (match e6PosParent p with
      | some (_, p₀) => decide (e6PosHeight p₀ < e6PosHeight p)
      | none => true) = true := by decide

private lemma e6PosParent_ht_lt {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) : e6PosHeight p₀ < e6PosHeight p := by
  have h := e6PosParent_ht_lt_bool p
  rw [hp] at h
  exact of_decide_eq_true h

private lemma e6PosParent_ht_succ_bool :
    ∀ p : Fin 36, (match e6PosParent p with
      | some (_, p₀) => decide (e6PosHeight p = e6PosHeight p₀ + 1)
      | none => true) = true := by decide

private lemma e6PosParent_ht_succ {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) : e6PosHeight p = e6PosHeight p₀ + 1 := by
  have h := e6PosParent_ht_succ_bool p
  rw [hp] at h
  exact of_decide_eq_true h

private lemma e6PosUp_ht_le_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosUp i p with
      | some (_, q) => decide (e6PosHeight q ≤ e6PosHeight p + 1)
      | none => true) = true := by decide

private lemma e6PosUp_ht_le {i : Fin 6} {p : Fin 36} {s : Bool} {q : Fin 36}
    (hu : e6PosUp i p = some (s, q)) : e6PosHeight q ≤ e6PosHeight p + 1 := by
  have h := e6PosUp_ht_le_bool i p
  rw [hu] at h
  exact of_decide_eq_true h

private lemma e6PosHeight_pos (p : Fin 36) : 1 ≤ e6PosHeight p := by
  revert p; decide

private lemma e6PosHeight_le_11 (p : Fin 36) : e6PosHeight p ≤ 11 := by
  revert p; decide

private lemma e6_adSq_mid_up_none_bool :
    ∀ p : Fin 36, (match e6PosParent p with
      | some (k, p₀) => match e6PosParent p₀ with
        | some (m, p₁) =>
            if decide (e6Cartan k m ≠ 0 ∧ k ≠ m) then e6PosUp k p₁ == none else true
        | none => true
      | none => true) = true := by decide

private lemma e6_adSq_mid_up_none {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    {m : Fin 6} {p₁ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hp₀ : e6PosParent p₀ = some (m, p₁))
    (hkm : e6Cartan k m ≠ 0) (hkmeq : k ≠ m) :
    e6PosUp k p₁ = none := by
  have h := e6_adSq_mid_up_none_bool p
  rw [hp] at h
  dsimp only at h
  rw [hp₀] at h
  simpa [hkm, hkmeq] using h

private lemma e6_adSq_end_up_none_bool :
    ∀ p : Fin 36, (match e6PosParent p with
      | some (k, p₀) => match e6PosParent p₀ with
        | some (_, p₁) => match e6PosUp k p₁ with
          | some (_, q) => e6PosUp k q == none
          | none => true
        | none => true
      | none => true) = true := by decide

private lemma e6_adSq_end_up_none {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    {m : Fin 6} {p₁ : Fin 36} {s : Bool} {q : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hp₀ : e6PosParent p₀ = some (m, p₁))
    (hup : e6PosUp k p₁ = some (s, q)) :
    e6PosUp k q = none := by
  have h := e6_adSq_end_up_none_bool p
  rw [hp] at h
  dsimp only at h
  rw [hp₀] at h
  dsimp only at h
  rw [hup] at h
  exact eq_of_beq h

private lemma e6_diag_up_none_bool :
    ∀ p : Fin 36, (match e6PosParent p with
      | some (k, _) => e6PosUp k p == none
      | none => true) = true := by decide

private lemma e6_diag_up_none {p : Fin 36} {k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) : e6PosUp k p = none := by
  have h := e6_diag_up_none_bool p
  rw [hp] at h
  exact eq_of_beq h

private lemma e6_comm_up_none_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e6Cartan i k = 0) && (e6PosUp i p₀ == none)
          then e6PosUp i p == none else true
      | none => true) = true := by decide

private lemma e6_comm_up_none {p : Fin 36} {i k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k = 0) (hup0 : e6PosUp i p₀ = none) :
    e6PosUp i p = none := by
  have h := e6_comm_up_none_bool i p
  rw [hp] at h
  simpa [hik, hcart, hup0] using h

private lemma e6_comm_up_self_parent_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e6Cartan i k = 0) && isSelfParent i p then
            match e6PosUp i p₀ with
            | some (s₀, _) => s₀ == true
            | none => true
          else true
      | none => true) = true := by decide

private lemma e6_comm_up_self_parent {p : Fin 36} {i k : Fin 6} {p₀ q₁ : Fin 36}
    {s₀ : Bool}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k = 0) (hup0 : e6PosUp i p₀ = some (s₀, q₁))
    (hself : isSelfParent i p = true) :
    s₀ = true := by
  have h := e6_comm_up_self_parent_bool i p
  rw [hp] at h
  simpa [hik, hcart, hself, hup0] using h

private lemma e6_comm_up_other_parent_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e6Cartan i k = 0) && !(isSelfParent i p) then
            match e6PosUp i p₀ with
            | some (s₀, q₁) => match e6PosUp i p with
              | some (s, q) => (s == s₀) && (e6PosParent q == some (k, q₁))
              | none => false
            | none => true
          else true
      | none => true) = true := by decide

private lemma e6_comm_up_other_parent {p : Fin 36} {i k : Fin 6} {p₀ q₁ : Fin 36}
    {s₀ : Bool}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k = 0) (hup0 : e6PosUp i p₀ = some (s₀, q₁))
    (hnot : isSelfParent i p = false) :
    ∃ q, e6PosUp i p = some (s₀, q) ∧ e6PosParent q = some (k, q₁) := by
  have h := e6_comm_up_other_parent_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at h
  rw [hup0] at h
  dsimp only at h
  cases hup : e6PosUp i p with
  | none => rw [hup] at h; dsimp only at h; contradiction
  | some sq =>
      rcases sq with ⟨s, q⟩
      rw [hup] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨q, by rw [h.1], h.2⟩

private lemma e6_cartan_symm_zero {i k : Fin 6}
    (h : e6Cartan i k = 0) : e6Cartan k i = 0 := by
  have hbool : ∀ a b : Fin 6, (if e6Cartan a b == 0 then e6Cartan b a == 0 else true) = true := by
    decide
  have ha := hbool i k
  simpa [h] using ha

private lemma e6_adj_up_none_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, _) =>
          if decide (i ≠ k ∧ e6Cartan i k ≠ 0) && !(isSelfParent i p)
          then e6PosUp i p == none else true
      | none => true) = true := by decide

private lemma e6_adj_up_none {p : Fin 36} {i k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k ≠ 0) (hnot : isSelfParent i p = false) :
    e6PosUp i p = none := by
  have h := e6_adj_up_none_bool i p
  rw [hp] at h
  simpa [hik, hcart, hnot] using h

private lemma e6_adj_ht2_simple_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e6Cartan i k ≠ 0) && !(isSelfParent i p) then
            match e6PosParent p₀ with
            | none => simpleOfPos p₀ == i
            | some _ => true
          else true
      | none => true) = true := by decide

private lemma e6_adj_ht2_simple {p : Fin 36} {i k : Fin 6} {p₀ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k ≠ 0) (hnot : isSelfParent i p = false)
    (hp₀ : e6PosParent p₀ = none) :
    simpleOfPos p₀ = i := by
  have h := e6_adj_ht2_simple_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  rw [hp₀] at h
  exact eq_of_beq h

private lemma e6_adj_mi_up_none_bool :
    ∀ (m : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (m ≠ k ∧ e6Cartan m k ≠ 0) && !(isSelfParent m p) then
            match e6PosParent p₀ with
            | some (m', p₁) =>
                if m' == m then (e6PosUp k p₁ == none) && (e6PosUp m p₀ == none) else true
            | none => true
          else true
      | none => true) = true := by decide

private lemma e6_adj_mi_up_none {p : Fin 36} {m k : Fin 6} {p₀ p₁ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hmk : m ≠ k)
    (hcart : e6Cartan m k ≠ 0) (hnot : isSelfParent m p = false)
    (hp₀ : e6PosParent p₀ = some (m, p₁)) :
    e6PosUp k p₁ = none ∧ e6PosUp m p₀ = none := by
  have h := e6_adj_mi_up_none_bool m p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hmk, hcart⟩, hnot] at h
  rw [hp₀] at h
  simpa using h

private lemma e6_adj_comm_m_witness_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e6Cartan i k ≠ 0) && !(isSelfParent i p) then
            match e6PosParent p₀ with
            | some (m, p₁) =>
                if decide (m ≠ i ∧ e6Cartan k m = 0 ∧ e6Cartan i m = 0) then
                  match e6PosUp k p₁ with
                  | some (_, q) => e6PosUp i q == none
                  | none => false
                else true
            | none => true
          else true
      | none => true) = true := by decide

private lemma e6_adj_comm_m_witness {p : Fin 36} {i k m : Fin 6} {p₀ p₁ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k ≠ 0) (hnot : isSelfParent i p = false)
    (hp₀ : e6PosParent p₀ = some (m, p₁)) (hmi : m ≠ i)
    (hcomm : e6Cartan k m = 0 ∧ e6Cartan i m = 0) :
    ∃ s q, e6PosUp k p₁ = some (s, q) ∧ e6PosUp i q = none := by
  have h := e6_adj_comm_m_witness_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at h
  rw [hp₀] at h
  dsimp only at h
  rw [decide_eq_true ⟨hmi, hcomm⟩] at h
  simp only [↓reduceIte] at h
  cases hupk : e6PosUp k p₁ with
  | none => rw [hupk] at h; dsimp only at h; contradiction
  | some sq =>
      rcases sq with ⟨s, q⟩
      rw [hupk] at h
      dsimp only at h
      exact ⟨s, q, rfl, eq_of_beq h⟩

private lemma e6_adj_rem_cases_bool :
    ∀ (i : Fin 6) (p : Fin 36), (match e6PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e6Cartan i k ≠ 0) && !(isSelfParent i p) then
            match e6PosParent p₀ with
            | some (m, _) =>
                if decide (m ≠ i ∧ ¬(e6Cartan k m = 0 ∧ e6Cartan i m = 0)) then
                  decide ((i.val = 3 ∧ p.val = 13) ∨ (i.val = 2 ∧ p.val = 22) ∨
                    (i.val = 4 ∧ p.val = 22) ∨ (i.val = 2 ∧ p.val = 26) ∨
                    (i.val = 3 ∧ p.val = 29) ∨ (i.val = 3 ∧ p.val = 32) ∨
                    (i.val = 5 ∧ p.val = 30) ∨ (i.val = 4 ∧ p.val = 34))
                else true
            | none => true
          else true
      | none => true) = true := by decide

private lemma e6_adj_rem_cases {p : Fin 36} {i k m : Fin 6} {p₀ p₁ : Fin 36}
    (hp : e6PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e6Cartan i k ≠ 0) (hnot : isSelfParent i p = false)
    (hp₀ : e6PosParent p₀ = some (m, p₁)) (hmi : m ≠ i)
    (hnc : ¬(e6Cartan k m = 0 ∧ e6Cartan i m = 0)) :
    (i.val = 3 ∧ p.val = 13) ∨ (i.val = 2 ∧ p.val = 22) ∨
    (i.val = 4 ∧ p.val = 22) ∨ (i.val = 2 ∧ p.val = 26) ∨
    (i.val = 3 ∧ p.val = 29) ∨ (i.val = 3 ∧ p.val = 32) ∨
    (i.val = 5 ∧ p.val = 30) ∨ (i.val = 4 ∧ p.val = 34) := by
  have h := e6_adj_rem_cases_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at h
  rw [hp₀] at h
  dsimp only at h
  rw [decide_eq_true (p := m ≠ i ∧ ¬(e6Cartan k m = 0 ∧ e6Cartan i m = 0)) ⟨hmi, hnc⟩] at h
  simp only [↓reduceIte] at h
  exact of_decide_eq_true h

private lemma e6_pos_base_ht1_simple (i j : Fin 6) :
    ⁅e6SerreE i, e6SerrePosVec (simplePosIdx j)⁆ = evalPosUp (e6PosUp i (simplePosIdx j)) := by
  by_cases hij : i = j
  · subst hij
    have hdiag : ∀ a : Fin 6, e6PosUp a (simplePosIdx a) = none := by decide
    rw [e6SerrePosVec_simple, hdiag i, evalPosUp, lie_self]
  · by_cases h0 : e6Cartan i j = 0
    · have hzero : e6PosUp i (simplePosIdx j) = none := by
        have hb : ∀ a b : Fin 6,
            (if decide (e6Cartan a b = 0) then e6PosUp a (simplePosIdx b) == none else true) =
              true := by decide
        have h' := hb i j
        simpa [h0] using h'
      rw [e6SerrePosVec_simple, hzero, evalPosUp]
      exact e6Serre_adE_zero (by rw [e6Cartan_eq]; exact h0)
    · have htrich : ∀ a b : Fin 6,
          (if decide (a ≠ b ∧ e6Cartan a b ≠ 0) then
            (match e6PosUp a (simplePosIdx b) with
              | some (true, q) => e6PosParent q == some (a, simplePosIdx b)
              | some (false, q) => e6PosParent q == some (b, simplePosIdx a)
              | none => false) else true) = true := by decide
      have ht := htrich i j
      rw [decide_eq_true ⟨hij, h0⟩] at ht
      simp only [↓reduceIte] at ht
      cases hup : e6PosUp i (simplePosIdx j) with
      | none => rw [hup] at ht; contradiction
      | some sq =>
          rcases sq with ⟨s, q⟩
          cases s
          · rw [hup] at ht
            rw [e6SerrePosVec_simple j, ← lie_skew, ← e6SerrePosVec_simple i]
            dsimp only [evalPosUp]
            exact congrArg Neg.neg (e6SerrePosVec_parent (eq_of_beq ht)).symm
          · rw [hup] at ht
            dsimp only [evalPosUp]
            exact (e6SerrePosVec_parent (eq_of_beq ht)).symm

private lemma e6_pos_base_ht1 (i : Fin 6) (p : Fin 36) (hp : e6PosParent p = none) :
    ⁅e6SerreE i, e6SerrePosVec p⁆ = evalPosUp (e6PosUp i p) := by
  have hbool : ∀ x : Fin 36, (match e6PosParent x with
      | none => x == simplePosIdx (simpleOfPos x)
      | some _ => true) = true := by decide
  have hsp : p = simplePosIdx (simpleOfPos p) := by
    have h := hbool p
    rw [hp] at h
    exact eq_of_beq h
  conv_lhs => rw [hsp]
  conv_rhs => rw [hsp]
  exact e6_pos_base_ht1_simple i (simpleOfPos p)

private lemma e6_ad_sq_posVec_eq_zero (n : ℕ)
    (ih : ∀ q : Fin 36, e6PosHeight q ≤ n → ∀ j : Fin 6,
      ⁅e6SerreE j, e6SerrePosVec q⁆ = evalPosUp (e6PosUp j q))
    (p : Fin 36) (hn : e6PosHeight p ≤ n + 1) (k : Fin 6) (p₀ : Fin 36)
    (hp : e6PosParent p = some (k, p₀)) :
    ⁅e6SerreE k, e6SerrePosVec p⁆ = 0 := by
  rw [e6SerrePosVec_parent hp]
  have hlt0 : e6PosHeight p₀ ≤ n :=
    Nat.le_of_lt_succ (lt_of_lt_of_le (e6PosParent_ht_lt hp) hn)
  cases hp₀ : e6PosParent p₀ with
  | none =>
      rw [e6_ht_le_one_simple hp₀]
      exact e6Serre_adE_sq_gen k (simpleOfPos p₀)
  | some kp1 =>
      rcases kp1 with ⟨m, p₁⟩
      have hlt1 : e6PosHeight p₁ < e6PosHeight p₀ := e6PosParent_ht_lt hp₀
      have hlt1n : e6PosHeight p₁ ≤ n := by omega
      rw [e6SerrePosVec_parent hp₀]
      have had : ⁅e6SerreE k, ⁅e6SerreE k, ⁅e6SerreE m, e6SerrePosVec p₁⁆⁆⁆ =
          ⁅⁅e6SerreE k, ⁅e6SerreE k, e6SerreE m⁆⁆, e6SerrePosVec p₁⁆ +
          (2 : ℝ) • ⁅⁅e6SerreE k, e6SerreE m⁆, ⁅e6SerreE k, e6SerrePosVec p₁⁆⁆ +
          ⁅e6SerreE m, ⁅e6SerreE k, ⁅e6SerreE k, e6SerrePosVec p₁⁆⁆⁆ := by
        rw [leibniz_lie (e6SerreE k) (e6SerreE m) (e6SerrePosVec p₁), lie_add]
        rw [leibniz_lie (e6SerreE k) ⁅e6SerreE k, e6SerreE m⁆ (e6SerrePosVec p₁)]
        rw [leibniz_lie (e6SerreE k) (e6SerreE m) ⁅e6SerreE k, e6SerrePosVec p₁⁆]
        rw [two_smul]
        abel
      rw [had, e6Serre_adE_sq_gen k m, zero_lie, zero_add]
      have hmid : ⁅⁅e6SerreE k, e6SerreE m⁆, ⁅e6SerreE k, e6SerrePosVec p₁⁆⁆ = 0 := by
        by_cases hkm : e6Cartan k m = 0
        · rw [e6Serre_adE_zero (by rw [e6Cartan_eq]; exact hkm), zero_lie]
        · by_cases hkm_eq : k = m
          · subst hkm_eq; simp [lie_self]
          · have hup := e6_adSq_mid_up_none hp hp₀ hkm hkm_eq
            rw [ih p₁ hlt1n k, hup, evalPosUp, lie_zero]
      have hend : ⁅e6SerreE k, ⁅e6SerreE k, e6SerrePosVec p₁⁆⁆ = 0 := by
        rw [ih p₁ hlt1n k]
        cases hup : e6PosUp k p₁ with
        | none => simp [evalPosUp]
        | some sq =>
            rcases sq with ⟨s, q⟩
            have hq_ht : e6PosHeight q ≤ e6PosHeight p₁ + 1 := e6PosUp_ht_le hup
            have hq_le : e6PosHeight q ≤ n := by
              have := e6PosParent_ht_succ hp₀
              omega
            have hup2 := e6_adSq_end_up_none hp hp₀ hup
            cases s <;> simp [evalPosUp, ih q hq_le k, hup2]
      rw [hmid, smul_zero, zero_add, hend, lie_zero]

private theorem e6Serre_adE_posVec :
    ∀ (n : ℕ) (p : Fin 36), e6PosHeight p ≤ n → ∀ i : Fin 6,
      ⁅e6SerreE i, e6SerrePosVec p⁆ = evalPosUp (e6PosUp i p) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have := e6PosHeight_pos p
      omega
  | succ n ih =>
      intro p hn i
      cases hp : e6PosParent p with
      | none => exact e6_pos_base_ht1 i p hp
      | some kp₀ =>
          rcases kp₀ with ⟨k, p₀⟩
          have hlt0 : e6PosHeight p₀ ≤ n := by
            have := e6PosParent_ht_succ hp
            omega
          by_cases hik : i = k
          · subst hik
            rw [e6_diag_up_none hp, evalPosUp]
            exact e6_ad_sq_posVec_eq_zero n ih p hn i p₀ hp
          · by_cases hcart : e6Cartan i k = 0
            · rw [e6SerrePosVec_parent hp]
              rw [leibniz_lie (e6SerreE i) (e6SerreE k) (e6SerrePosVec p₀)]
              rw [e6Serre_adE_zero (by rw [e6Cartan_eq]; exact hcart), zero_lie, zero_add]
              rw [ih p₀ hlt0 i]
              cases hup0 : e6PosUp i p₀ with
              | none =>
                  rw [e6_comm_up_none hp hik hcart hup0, evalPosUp, lie_zero]
              | some sq1 =>
                  rcases sq1 with ⟨s₀, q₁⟩
                  cases hself : isSelfParent i p
                  · rcases e6_comm_up_other_parent hp hik hcart hup0 hself with ⟨q, hup, hparq⟩
                    rw [hup]
                    cases s₀ <;> simp [evalPosUp, lie_neg, e6SerrePosVec_parent hparq]
                  · have hself' := hself
                    unfold isSelfParent at hself'
                    cases hup : e6PosUp i p with
                    | none => rw [hup] at hself'; contradiction
                    | some sq =>
                        rcases sq with ⟨s, q⟩
                        rw [hup] at hself'
                        cases s
                        · contradiction
                        · have hparq : e6PosParent q = some (i, p) := by
                            simpa using hself'
                          have hs1 := e6_comm_up_self_parent hp hik hcart hup0 hself
                          subst hs1
                          rw [evalPosUp, evalPosUp]
                          calc ⁅e6SerreE k, e6SerrePosVec q₁⁆
                              = ⁅e6SerreE k, ⁅e6SerreE i, e6SerrePosVec p₀⁆⁆ := by
                                  have := ih p₀ hlt0 i
                                  rw [hup0, evalPosUp] at this
                                  rw [this]
                            _ = ⁅e6SerreE i, ⁅e6SerreE k, e6SerrePosVec p₀⁆⁆ := by
                                  rw [leibniz_lie (e6SerreE k) (e6SerreE i) (e6SerrePosVec p₀)]
                                  rw [e6Serre_adE_zero (by rw [e6Cartan_eq]; exact e6_cartan_symm_zero hcart),
                                    zero_lie, zero_add]
                            _ = ⁅e6SerreE i, e6SerrePosVec p⁆ := by rw [e6SerrePosVec_parent hp]
                            _ = e6SerrePosVec q := (e6SerrePosVec_parent hparq).symm
            · have hcartTag : Tag.cartan .E6 i k ≠ 0 := by
                intro hzero
                apply hcart
                rw [← e6Cartan_eq]
                exact hzero
              have hcart1 : Tag.cartan .E6 i k = -1 :=
                (e6_cartan_offdiag_cases hik).resolve_left hcartTag
              cases hself : isSelfParent i p
              · have hup := e6_adj_up_none hp hik hcart hself
                rw [hup, evalPosUp]
                cases hp₀ : e6PosParent p₀ with
                | none =>
                    have hsi := e6_adj_ht2_simple hp hik hcart hself hp₀
                    rw [e6SerrePosVec_parent hp, e6_ht_le_one_simple hp₀, hsi]
                    rw [← lie_skew (e6SerreE k) (e6SerreE i), lie_neg,
                      e6Serre_adE_negOne hcart1, neg_zero]
                | some mp₁ =>
                    rcases mp₁ with ⟨m, p₁⟩
                    have hlt1n : e6PosHeight p₁ ≤ n := by
                      have := e6PosParent_ht_lt hp₀
                      omega
                    by_cases hmi : m = i
                    · subst hmi
                      obtain ⟨hup_kp1, hup_mp0⟩ :=
                        e6_adj_mi_up_none hp hik hcart hself hp₀
                      rw [e6SerrePosVec_parent hp, e6SerrePosVec_parent hp₀]
                      have h1 : ⁅e6SerreE m, ⁅e6SerreE m, e6SerrePosVec p₁⁆⁆ = 0 := by
                        rw [← e6SerrePosVec_parent hp₀, ih p₀ hlt0 m, hup_mp0, evalPosUp]
                      have h2 : ⁅e6SerreE m, ⁅e6SerreE m, ⁅e6SerreE k, e6SerrePosVec p₁⁆⁆⁆ = 0 := by
                        rw [ih p₁ hlt1n k, hup_kp1, evalPosUp, lie_zero, lie_zero]
                      have h2sm := two_smul_bracket_eq_ad_sq (e6Serre_adE_negOne hcart1) h1
                      rw [h2] at h2sm
                      exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                    · by_cases hcomm_km : e6Cartan k m = 0 ∧ e6Cartan i m = 0
                      · rw [e6SerrePosVec_parent hp, e6SerrePosVec_parent hp₀]
                        rw [leibniz_lie (e6SerreE k) (e6SerreE m) (e6SerrePosVec p₁),
                          e6Serre_adE_zero (by rw [e6Cartan_eq]; exact hcomm_km.1), zero_lie, zero_add]
                        rw [leibniz_lie (e6SerreE i) (e6SerreE m) ⁅e6SerreE k, e6SerrePosVec p₁⁆,
                          e6Serre_adE_zero (by rw [e6Cartan_eq]; exact hcomm_km.2), zero_lie, zero_add]
                        obtain ⟨s, q, hupk, hupi⟩ :=
                          e6_adj_comm_m_witness hp hik hcart hself hp₀ hmi hcomm_km
                        have hq_le : e6PosHeight q ≤ n := by
                          have hq_ht := e6PosUp_ht_le hupk
                          have hp0_ht := e6PosParent_ht_succ hp₀
                          omega
                        have hres : ⁅e6SerreE i, ⁅e6SerreE k, e6SerrePosVec p₁⁆⁆ = 0 := by
                          rw [ih p₁ hlt1n k, hupk]
                          cases s <;> simp [evalPosUp, lie_neg, ih q hq_le i, hupi]
                        rw [hres, lie_zero]
                      · have hcases :=
                          e6_adj_rem_cases hp hik hcart hself hp₀ hmi hcomm_km
                        rcases hcases with ⟨hi, hpv⟩ | ⟨hi, hpv⟩ | ⟨hi, hpv⟩ | ⟨hi, hpv⟩ |
                            ⟨hi, hpv⟩ | ⟨hi, hpv⟩ | ⟨hi, hpv⟩ | ⟨hi, hpv⟩
                        · -- (3, 13)
                          have hi' : i = 3 := Fin.ext hi
                          have hp' : p = 13 := Fin.ext hpv
                          subst hi' hp'
                          have h13 : e6SerrePosVec 13 = ⁅e6SerreE 1, ⁅e6SerreE 2, e6SerreE 3⁆⁆ := by
                            rw [e6SerrePosVec_parent (p := 13) (k := 1) (p₀ := 8) rfl,
                              e6SerrePosVec_parent (p := 8) (k := 2) (p₀ := 1) rfl,
                              e6_ht_le_one_simple (p := 1) rfl]
                            rfl
                          have hc12 : ⁅e6SerreE 1, e6SerreE 2⁆ = 0 :=
                            e6Serre_adE_zero (by rw [e6Cartan_eq]; decide)
                          have hc21 : ⁅e6SerreE 2, e6SerreE 1⁆ = 0 :=
                            e6Serre_adE_zero (by rw [e6Cartan_eq]; decide)
                          have hsw : e6SerrePosVec 13 = -⁅e6SerreE 2, ⁅e6SerreE 3, e6SerreE 1⁆⁆ := by
                            rw [h13, leibniz_lie (e6SerreE 1) (e6SerreE 2) (e6SerreE 3),
                              hc12, zero_lie, zero_add, ← lie_skew (e6SerreE 1) (e6SerreE 3),
                              lie_neg]
                          rw [hsw, lie_neg]
                          have h2sm := two_smul_bracket_eq_ad_sq
                            (e6Serre_adE_sq_gen 3 2) (e6Serre_adE_sq_gen 3 1)
                          rw [hc21, lie_zero, lie_zero] at h2sm
                          rw [(smul_eq_zero.mp h2sm).resolve_left (by norm_num), neg_zero]
                        · -- (2, 22)
                          have hi' : i = 2 := Fin.ext hi
                          have hp' : p = 22 := Fin.ext hpv
                          subst hi' hp'
                          have hn7 : e6PosHeight 7 ≤ n := by
                            have : e6PosHeight 22 = 5 := rfl
                            have : e6PosHeight 7 = 2 := rfl
                            omega
                          have hn12 : e6PosHeight 12 ≤ n := by
                            have : e6PosHeight 22 = 5 := rfl
                            have : e6PosHeight 12 = 3 := rfl
                            omega
                          have hn16 : e6PosHeight 16 ≤ n := by
                            have : e6PosHeight 22 = 5 := rfl
                            have : e6PosHeight 16 = 4 := rfl
                            omega
                          have h11 : e6SerrePosVec 11 = ⁅e6SerreE 2, e6SerrePosVec 7⁆ :=
                            e6SerrePosVec_parent (p := 11) rfl
                          have h16 : e6SerrePosVec 16 = ⁅e6SerreE 2, e6SerrePosVec 12⁆ := by
                            rw [e6SerrePosVec_parent (p := 16) rfl, h11,
                              leibniz_lie (e6SerreE 1) (e6SerreE 2) (e6SerrePosVec 7),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide), zero_lie, zero_add]
                            have h17 := ih 7 hn7 1
                            change ⁅e6SerreE 1, e6SerrePosVec 7⁆ = e6SerrePosVec 12 at h17
                            rw [h17]
                          have h22 : e6SerrePosVec 22 = ⁅e6SerreE 3, ⁅e6SerreE 2, e6SerrePosVec 12⁆⁆ := by
                            rw [e6SerrePosVec_parent (p := 22) rfl, h16]
                          have hsq : ⁅e6SerreE 2, ⁅e6SerreE 2, e6SerrePosVec 12⁆⁆ = 0 := by
                            rw [← h16]
                            have h2_16 := ih 16 hn16 2
                            change ⁅e6SerreE 2, e6SerrePosVec 16⁆ = 0 at h2_16
                            exact h2_16
                          have h3_12 : ⁅e6SerreE 3, e6SerrePosVec 12⁆ = 0 := by
                            have h3 := ih 12 hn12 3
                            change ⁅e6SerreE 3, e6SerrePosVec 12⁆ = 0 at h3
                            exact h3
                          rw [h22]
                          have h2sm := two_smul_bracket_eq_ad_sq (e6Serre_adE_sq_gen 2 3) hsq
                          rw [h3_12, lie_zero, lie_zero] at h2sm
                          exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                        · -- (4, 22)
                          have hi' : i = 4 := Fin.ext hi
                          have hp' : p = 22 := Fin.ext hpv
                          subst hi' hp'
                          have hn7 : e6PosHeight 7 ≤ n := by
                            have : e6PosHeight 22 = 5 := rfl; have : e6PosHeight 7 = 2 := rfl; omega
                          have hn11 : e6PosHeight 11 ≤ n := by
                            have : e6PosHeight 22 = 5 := rfl; have : e6PosHeight 11 = 3 := rfl; omega
                          have hn12 : e6PosHeight 12 ≤ n := by
                            have : e6PosHeight 22 = 5 := rfl; have : e6PosHeight 12 = 3 := rfl; omega
                          have h11_3 : ⁅e6SerreE 3, e6SerrePosVec 11⁆ = 0 := by
                            have h := ih 11 hn11 3
                            change ⁅e6SerreE 3, e6SerrePosVec 11⁆ = 0 at h; exact h
                          have h11_4 : ⁅e6SerreE 4, e6SerrePosVec 11⁆ = 0 := by
                            have h := ih 11 hn11 4
                            change ⁅e6SerreE 4, e6SerrePosVec 11⁆ = 0 at h; exact h
                          have h12_3 : ⁅e6SerreE 3, e6SerrePosVec 12⁆ = 0 := by
                            have h := ih 12 hn12 3
                            change ⁅e6SerreE 3, e6SerrePosVec 12⁆ = 0 at h; exact h
                          have h7_4 : ⁅e6SerreE 4, e6SerrePosVec 7⁆ = 0 := by
                            have h := ih 7 hn7 4
                            change ⁅e6SerreE 4, e6SerrePosVec 7⁆ = 0 at h; exact h
                          have h12_4 : ⁅e6SerreE 4, e6SerrePosVec 12⁆ = 0 := by
                            rw [e6SerrePosVec_parent (p := 12) rfl,
                              leibniz_lie (e6SerreE 4) (e6SerreE 1) (e6SerrePosVec 7),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide),
                              zero_lie, zero_add, h7_4, lie_zero]
                          have h12_eq : e6SerrePosVec 12 = ⁅e6SerreE 1, e6SerrePosVec 7⁆ :=
                            e6SerrePosVec_parent (p := 12) rfl
                          have h11_eq : e6SerrePosVec 11 = ⁅e6SerreE 2, e6SerrePosVec 7⁆ :=
                            e6SerrePosVec_parent (p := 11) rfl
                          have h7_eq : e6SerrePosVec 7 = ⁅e6SerreE 3, e6SerreE 4⁆ := by
                            rw [e6SerrePosVec_parent (p := 7) rfl,
                              e6_ht_le_one_simple (p := 2) rfl]
                            rfl
                          have h43 : ⁅e6SerreE 4, ⁅e6SerreE 3, e6SerreE 1⁆⁆ = e6SerrePosVec 12 := by
                            rw [leibniz_lie (e6SerreE 4) (e6SerreE 3) (e6SerreE 1),
                              e6Serre_adE_zero (i := 4) (j := 1) (by rw [e6Cartan_eq]; decide),
                              lie_zero, add_zero,
                              ← lie_skew (e6SerreE 4) (e6SerreE 3), ← h7_eq, neg_lie,
                              ← lie_skew (e6SerrePosVec 7) (e6SerreE 1), neg_neg, ← h12_eq]
                          have h7_12 : ⁅e6SerrePosVec 7, e6SerrePosVec 12⁆ = 0 := by
                            rw [h7_eq, lie_lie (e6SerreE 3) (e6SerreE 4) (e6SerrePosVec 12),
                              h12_4, lie_zero, h12_3, lie_zero, sub_self]
                          have h7_11 : ⁅e6SerrePosVec 7, e6SerrePosVec 11⁆ = 0 := by
                            rw [h7_eq, lie_lie (e6SerreE 3) (e6SerreE 4) (e6SerrePosVec 11),
                              h11_4, lie_zero, h11_3, lie_zero, sub_self]
                          have h22_eq : e6SerrePosVec 22 =
                              ⁅⁅e6SerreE 3, e6SerreE 1⁆, e6SerrePosVec 11⁆ := by
                            rw [e6SerrePosVec_parent (p := 22) rfl,
                              e6SerrePosVec_parent (p := 16) rfl,
                              leibniz_lie (e6SerreE 3) (e6SerreE 1) (e6SerrePosVec 11),
                              h11_3, lie_zero, add_zero]
                          rw [h22_eq, leibniz_lie (e6SerreE 4) ⁅e6SerreE 3, e6SerreE 1⁆
                              (e6SerrePosVec 11),
                            h11_4, lie_zero, add_zero, h43, h12_eq, h11_eq]
                          exact two_smul_comm_ad_eq_zero
                            (e6Serre_adE_zero (by rw [e6Cartan_eq]; decide))
                            (by rw [← h12_eq]; exact h7_12)
                            (by rw [← h11_eq]; exact h7_11)
                        · -- (2, 26)
                          have hi' : i = 2 := Fin.ext hi
                          have hp' : p = 26 := Fin.ext hpv
                          subst hi' hp'
                          have hn15 : e6PosHeight 15 ≤ n := by
                            have : e6PosHeight 26 = 6 := rfl; have : e6PosHeight 15 = 3 := rfl; omega
                          have hn18 : e6PosHeight 18 ≤ n := by
                            have : e6PosHeight 26 = 6 := rfl; have : e6PosHeight 18 = 4 := rfl; omega
                          have hn23 : e6PosHeight 23 ≤ n := by
                            have : e6PosHeight 26 = 6 := rfl; have : e6PosHeight 23 = 5 := rfl; omega
                          have h19 : e6SerrePosVec 19 = ⁅e6SerreE 2, e6SerrePosVec 15⁆ :=
                            e6SerrePosVec_parent (p := 19) rfl
                          have h23 : e6SerrePosVec 23 = ⁅e6SerreE 2, e6SerrePosVec 18⁆ := by
                            rw [e6SerrePosVec_parent (p := 23) rfl, h19,
                              leibniz_lie (e6SerreE 1) (e6SerreE 2) (e6SerrePosVec 15),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide), zero_lie, zero_add]
                            have h1_15 := ih 15 hn15 1
                            change ⁅e6SerreE 1, e6SerrePosVec 15⁆ = e6SerrePosVec 18 at h1_15
                            rw [h1_15]
                          have h26 : e6SerrePosVec 26 = ⁅e6SerreE 3, ⁅e6SerreE 2, e6SerrePosVec 18⁆⁆ := by
                            rw [e6SerrePosVec_parent (p := 26) rfl, h23]
                          have hsq : ⁅e6SerreE 2, ⁅e6SerreE 2, e6SerrePosVec 18⁆⁆ = 0 := by
                            rw [← h23]
                            have h2_23 := ih 23 hn23 2
                            change ⁅e6SerreE 2, e6SerrePosVec 23⁆ = 0 at h2_23
                            exact h2_23
                          have h3_18 : ⁅e6SerreE 3, e6SerrePosVec 18⁆ = 0 := by
                            have h3 := ih 18 hn18 3
                            change ⁅e6SerreE 3, e6SerrePosVec 18⁆ = 0 at h3
                            exact h3
                          rw [h26]
                          have h2sm := two_smul_bracket_eq_ad_sq (e6Serre_adE_sq_gen 2 3) hsq
                          rw [h3_18, lie_zero, lie_zero] at h2sm
                          exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                        · -- (3, 29)
                          have hi' : i = 3 := Fin.ext hi
                          have hp' : p = 29 := Fin.ext hpv
                          subst hi' hp'
                          have hn16 : e6PosHeight 16 ≤ n := by
                            have : e6PosHeight 29 = 7 := rfl; have : e6PosHeight 16 = 4 := rfl; omega
                          have hn24 : e6PosHeight 24 ≤ n := by
                            have : e6PosHeight 29 = 7 := rfl; have : e6PosHeight 24 = 5 := rfl; omega
                          have hn27 : e6PosHeight 27 ≤ n := by
                            have : e6PosHeight 29 = 7 := rfl; have : e6PosHeight 27 = 6 := rfl; omega
                          have h22 : e6SerrePosVec 22 = ⁅e6SerreE 3, e6SerrePosVec 16⁆ :=
                            e6SerrePosVec_parent (p := 22) rfl
                          have h27 : e6SerrePosVec 27 = ⁅e6SerreE 3, e6SerrePosVec 24⁆ := by
                            rw [e6SerrePosVec_parent (p := 27) rfl, h22,
                              leibniz_lie (e6SerreE 0) (e6SerreE 3) (e6SerrePosVec 16),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide), zero_lie, zero_add]
                            have h0_16 := ih 16 hn16 0
                            change ⁅e6SerreE 0, e6SerrePosVec 16⁆ = e6SerrePosVec 24 at h0_16
                            rw [h0_16]
                          have h29 : e6SerrePosVec 29 = ⁅e6SerreE 2, ⁅e6SerreE 3, e6SerrePosVec 24⁆⁆ := by
                            rw [e6SerrePosVec_parent (p := 29) rfl, h27]
                          have hsq : ⁅e6SerreE 3, ⁅e6SerreE 3, e6SerrePosVec 24⁆⁆ = 0 := by
                            rw [← h27]
                            have h3_27 := ih 27 hn27 3
                            change ⁅e6SerreE 3, e6SerrePosVec 27⁆ = 0 at h3_27
                            exact h3_27
                          have h2_24 : ⁅e6SerreE 2, e6SerrePosVec 24⁆ = 0 := by
                            have h2 := ih 24 hn24 2
                            change ⁅e6SerreE 2, e6SerrePosVec 24⁆ = 0 at h2
                            exact h2
                          rw [h29]
                          have h2sm := two_smul_bracket_eq_ad_sq (e6Serre_adE_sq_gen 3 2) hsq
                          rw [h2_24, lie_zero, lie_zero] at h2sm
                          exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                        · -- (3, 32)
                          have hi' : i = 3 := Fin.ext hi
                          have hp' : p = 32 := Fin.ext hpv
                          subst hi' hp'
                          have hn23 : e6PosHeight 23 ≤ n := by
                            have : e6PosHeight 32 = 8 := rfl; have : e6PosHeight 23 = 5 := rfl; omega
                          have hn25 : e6PosHeight 25 ≤ n := by
                            have : e6PosHeight 32 = 8 := rfl; have : e6PosHeight 25 = 6 := rfl; omega
                          have hn28 : e6PosHeight 28 ≤ n := by
                            have : e6PosHeight 32 = 8 := rfl; have : e6PosHeight 28 = 7 := rfl; omega
                          have h26 : e6SerrePosVec 26 = ⁅e6SerreE 3, e6SerrePosVec 23⁆ :=
                            e6SerrePosVec_parent (p := 26) rfl
                          have h28 : e6SerrePosVec 28 = ⁅e6SerreE 3, e6SerrePosVec 25⁆ := by
                            rw [e6SerrePosVec_parent (p := 28) rfl, h26,
                              leibniz_lie (e6SerreE 0) (e6SerreE 3) (e6SerrePosVec 23),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide), zero_lie, zero_add]
                            have h0_23 := ih 23 hn23 0
                            change ⁅e6SerreE 0, e6SerrePosVec 23⁆ = e6SerrePosVec 25 at h0_23
                            rw [h0_23]
                          have h32 : e6SerrePosVec 32 = ⁅e6SerreE 2, ⁅e6SerreE 3, e6SerrePosVec 25⁆⁆ := by
                            rw [e6SerrePosVec_parent (p := 32) rfl, h28]
                          have hsq : ⁅e6SerreE 3, ⁅e6SerreE 3, e6SerrePosVec 25⁆⁆ = 0 := by
                            rw [← h28]
                            have h3_28 := ih 28 hn28 3
                            change ⁅e6SerreE 3, e6SerrePosVec 28⁆ = 0 at h3_28
                            exact h3_28
                          have h2_25 : ⁅e6SerreE 2, e6SerrePosVec 25⁆ = 0 := by
                            have h2 := ih 25 hn25 2
                            change ⁅e6SerreE 2, e6SerrePosVec 25⁆ = 0 at h2
                            exact h2
                          rw [h32]
                          have h2sm := two_smul_bracket_eq_ad_sq (e6Serre_adE_sq_gen 3 2) hsq
                          rw [h2_25, lie_zero, lie_zero] at h2sm
                          exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                        · -- (5, 30)
                          have hi' : i = 5 := Fin.ext hi
                          have hp' : p = 30 := Fin.ext hpv
                          subst hi' hp'
                          have hn15 : e6PosHeight 15 ≤ n := by
                            have : e6PosHeight 30 = 7 := rfl; have : e6PosHeight 15 = 3 := rfl; omega
                          have hn18 : e6PosHeight 18 ≤ n := by
                            have : e6PosHeight 30 = 7 := rfl; have : e6PosHeight 18 = 4 := rfl; omega
                          have hn19 : e6PosHeight 19 ≤ n := by
                            have : e6PosHeight 30 = 7 := rfl; have : e6PosHeight 19 = 4 := rfl; omega
                          have hn23 : e6PosHeight 23 ≤ n := by
                            have : e6PosHeight 30 = 7 := rfl; have : e6PosHeight 23 = 5 := rfl; omega
                          have hn26 : e6PosHeight 26 ≤ n := by
                            have : e6PosHeight 30 = 7 := rfl; have : e6PosHeight 26 = 6 := rfl; omega
                          have h26_5 : ⁅e6SerreE 5, e6SerrePosVec 26⁆ = 0 := by
                            have h := ih 26 hn26 5; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h23_5 : ⁅e6SerreE 5, e6SerrePosVec 23⁆ = 0 := by
                            have h := ih 23 hn23 5; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h23_4 : ⁅e6SerreE 4, e6SerrePosVec 23⁆ = 0 := by
                            have h := ih 23 hn23 4; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h19_3 : ⁅e6SerreE 3, e6SerrePosVec 19⁆ = 0 := by
                            have h := ih 19 hn19 3; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h19_4 : ⁅e6SerreE 4, e6SerrePosVec 19⁆ = 0 := by
                            have h := ih 19 hn19 4; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h19_5 : ⁅e6SerreE 5, e6SerrePosVec 19⁆ = 0 := by
                            have h := ih 19 hn19 5; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h18_3 : ⁅e6SerreE 3, e6SerrePosVec 18⁆ = 0 := by
                            have h := ih 18 hn18 3; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h15_4 : ⁅e6SerreE 4, e6SerrePosVec 15⁆ = 0 := by
                            have h := ih 15 hn15 4; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h15_5 : ⁅e6SerreE 5, e6SerrePosVec 15⁆ = 0 := by
                            have h := ih 15 hn15 5; simp only [e6PosUp, evalPosUp] at h; exact h
                          have h18_4 : ⁅e6SerreE 4, e6SerrePosVec 18⁆ = 0 := by
                            rw [e6SerrePosVec_parent (p := 18) rfl,
                              leibniz_lie (e6SerreE 4) (e6SerreE 1) (e6SerrePosVec 15),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide),
                              zero_lie, zero_add, h15_4, lie_zero]
                          have h18_5 : ⁅e6SerreE 5, e6SerrePosVec 18⁆ = 0 := by
                            rw [e6SerrePosVec_parent (p := 18) rfl,
                              leibniz_lie (e6SerreE 5) (e6SerreE 1) (e6SerrePosVec 15),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide),
                              zero_lie, zero_add, h15_5, lie_zero]
                          have h10_eq : e6SerrePosVec 10 = ⁅e6SerreE 4, e6SerreE 5⁆ := by
                            rw [e6SerrePosVec_parent (p := 10) rfl,
                              e6_ht_le_one_simple (p := 4) rfl]; rfl
                          have h15_eq : e6SerrePosVec 15 = ⁅e6SerreE 3, e6SerrePosVec 10⁆ :=
                            e6SerrePosVec_parent (p := 15) rfl
                          have h18_eq : e6SerrePosVec 18 = ⁅e6SerreE 1, e6SerrePosVec 15⁆ :=
                            e6SerrePosVec_parent (p := 18) rfl
                          have h19_eq : e6SerrePosVec 19 = ⁅e6SerreE 2, e6SerrePosVec 15⁆ :=
                            e6SerrePosVec_parent (p := 19) rfl
                          have h10_19 : ⁅e6SerrePosVec 10, e6SerrePosVec 19⁆ = 0 := by
                            rw [h10_eq, lie_lie (e6SerreE 4) (e6SerreE 5) (e6SerrePosVec 19),
                              h19_5, lie_zero, h19_4, lie_zero, sub_self]
                          have h10_18 : ⁅e6SerrePosVec 10, e6SerrePosVec 18⁆ = 0 := by
                            rw [h10_eq, lie_lie (e6SerreE 4) (e6SerreE 5) (e6SerrePosVec 18),
                              h18_5, lie_zero, h18_4, lie_zero, sub_self]
                          have h15_19 : ⁅e6SerrePosVec 15, e6SerrePosVec 19⁆ = 0 := by
                            rw [h15_eq, lie_lie (e6SerreE 3) (e6SerrePosVec 10) (e6SerrePosVec 19),
                              h10_19, lie_zero, h19_3, lie_zero, sub_self]
                          have h15_18 : ⁅e6SerrePosVec 15, e6SerrePosVec 18⁆ = 0 := by
                            rw [h15_eq, lie_lie (e6SerreE 3) (e6SerrePosVec 10) (e6SerrePosVec 18),
                              h10_18, lie_zero, h18_3, lie_zero, sub_self]
                          have h10_23 : ⁅e6SerrePosVec 10, e6SerrePosVec 23⁆ = 0 := by
                            rw [h10_eq, lie_lie (e6SerreE 4) (e6SerreE 5) (e6SerrePosVec 23),
                              h23_5, lie_zero, h23_4, lie_zero, sub_self]
                          have h15_23 : ⁅e6SerrePosVec 15, e6SerrePosVec 23⁆ = 0 := by
                            have hE12 : ⁅e6SerreE 1, e6SerreE 2⁆ = 0 :=
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide)
                            have h18comm :
                                ⁅e6SerrePosVec 15,
                                  ⁅e6SerreE 1, e6SerrePosVec 15⁆⁆ = 0 := by
                              rw [← h18_eq]
                              exact h15_18
                            have h19comm :
                                ⁅e6SerrePosVec 15,
                                  ⁅e6SerreE 2, e6SerrePosVec 15⁆⁆ = 0 := by
                              rw [← h19_eq]
                              exact h15_19
                            rw [e6SerrePosVec_parent (p := 23) rfl,
                              leibniz_lie (e6SerrePosVec 15) (e6SerreE 1)
                                (e6SerrePosVec 19), h15_19, lie_zero, add_zero,
                              ← lie_skew (e6SerrePosVec 15) (e6SerreE 1), neg_lie,
                              ← h18_eq]
                            exact neg_eq_zero.mpr (by
                              simpa [h18_eq, h19_eq] using
                                two_smul_comm_ad_eq_zero hE12 h18comm h19comm)
                          rw [e6SerrePosVec_parent (p := 30) rfl,
                            leibniz_lie (e6SerreE 5) (e6SerreE 4) (e6SerrePosVec 26),
                            h26_5, lie_zero, add_zero,
                            ← lie_skew (e6SerreE 5) (e6SerreE 4), ← h10_eq, neg_lie,
                            e6SerrePosVec_parent (p := 26) rfl,
                            leibniz_lie (e6SerrePosVec 10) (e6SerreE 3) (e6SerrePosVec 23),
                            h10_23, lie_zero, add_zero,
                            ← lie_skew (e6SerrePosVec 10) (e6SerreE 3), ← h15_eq, neg_lie,
                            h15_23, neg_zero, neg_zero]
                        · -- (4, 34)
                          have hi' : i = 4 := Fin.ext hi
                          have hp' : p = 34 := Fin.ext hpv
                          subst hi' hp'
                          have hn32 : e6PosHeight 32 ≤ n := by
                            have : e6PosHeight 34 = 10 := rfl; have : e6PosHeight 32 = 8 := rfl; omega
                          have hn33 : e6PosHeight 33 ≤ n := by
                            have : e6PosHeight 34 = 10 := rfl; have : e6PosHeight 33 = 9 := rfl; omega
                          have h31 : e6SerrePosVec 31 = ⁅e6SerreE 4, e6SerrePosVec 28⁆ := by
                            rw [e6SerrePosVec_parent (p := 31) rfl,
                              e6SerrePosVec_parent (p := 30) rfl,
                              leibniz_lie (e6SerreE 0) (e6SerreE 4) (e6SerrePosVec 26),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide), zero_lie, zero_add,
                              ← e6SerrePosVec_parent (p := 28) rfl]
                          have h33 : e6SerrePosVec 33 = ⁅e6SerreE 4, e6SerrePosVec 32⁆ := by
                            rw [e6SerrePosVec_parent (p := 33) rfl, h31,
                              leibniz_lie (e6SerreE 2) (e6SerreE 4) (e6SerrePosVec 28),
                              e6Serre_adE_zero (by rw [e6Cartan_eq]; decide), zero_lie, zero_add,
                              ← e6SerrePosVec_parent (p := 32) rfl]
                          have h34 : e6SerrePosVec 34 = ⁅e6SerreE 3, ⁅e6SerreE 4, e6SerrePosVec 32⁆⁆ := by
                            rw [e6SerrePosVec_parent (p := 34) rfl, h33]
                          have hsq : ⁅e6SerreE 4, ⁅e6SerreE 4, e6SerrePosVec 32⁆⁆ = 0 := by
                            rw [← h33]
                            have h4_33 := ih 33 hn33 4
                            change ⁅e6SerreE 4, e6SerrePosVec 33⁆ = 0 at h4_33
                            exact h4_33
                          have h3_32 : ⁅e6SerreE 3, e6SerrePosVec 32⁆ = 0 := by
                            have h3 := ih 32 hn32 3
                            change ⁅e6SerreE 3, e6SerrePosVec 32⁆ = 0 at h3
                            exact h3
                          rw [h34]
                          have h2sm := two_smul_bracket_eq_ad_sq (e6Serre_adE_sq_gen 4 3) hsq
                          rw [h3_32, lie_zero, lie_zero] at h2sm
                          exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
              · unfold isSelfParent at hself
                cases hup : e6PosUp i p with
                | none => rw [hup] at hself; contradiction
                | some sq =>
                    rcases sq with ⟨s, q⟩
                    rw [hup] at hself
                    cases s
                    · contradiction
                    · have hparq : e6PosParent q = some (i, p) := by simpa using hself
                      rw [evalPosUp, e6SerrePosVec_parent hparq]

/-! #### 78-dimensional spanning submodule and triangular decomposition -/

private noncomputable def e6SerrePosSpan : Submodule ℝ (LieAlgebra.e₆ ℝ) :=
  Submodule.span ℝ (Set.range e6SerrePosVec)

private noncomputable def e6SerreCartan : Submodule ℝ (LieAlgebra.e₆ ℝ) :=
  Submodule.span ℝ (Set.range e6SerreH)

private noncomputable def e6SerreNegVec (p : Fin 36) : LieAlgebra.e₆ ℝ :=
  e6SerreChevalleyInv (e6SerrePosVec p)

private noncomputable def e6SerreNegSpan : Submodule ℝ (LieAlgebra.e₆ ℝ) :=
  Submodule.span ℝ (Set.range e6SerreNegVec)

private noncomputable def e6SerreSpan78 : Submodule ℝ (LieAlgebra.e₆ ℝ) :=
  e6SerreNegSpan ⊔ e6SerreCartan ⊔ e6SerrePosSpan

private theorem e6SerrePosVec_mem_posSpan (p : Fin 36) :
    e6SerrePosVec p ∈ e6SerrePosSpan :=
  Submodule.subset_span ⟨p, rfl⟩

private theorem e6SerreE_mem_posSpan (i : Fin 6) :
    e6SerreE i ∈ e6SerrePosSpan := by
  rw [← e6SerrePosVec_simple i]
  exact e6SerrePosVec_mem_posSpan _

private theorem e6SerreH_mem_cartan (i : Fin 6) :
    e6SerreH i ∈ e6SerreCartan :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem e6SerreF_mem_negSpan (i : Fin 6) :
    e6SerreF i ∈ e6SerreNegSpan := by
  have h : e6SerreF i = e6SerreNegVec (simplePosIdx i) := by
    simp [e6SerreNegVec, e6SerrePosVec_simple]
  rw [h]
  exact Submodule.subset_span ⟨simplePosIdx i, rfl⟩

private theorem evalPosUp_mem_posSpan (o : Option (Bool × Fin 36)) :
    evalPosUp o ∈ e6SerrePosSpan := by
  cases o with
  | none => exact e6SerrePosSpan.zero_mem
  | some bq =>
      rcases bq with ⟨b, q⟩
      cases b with
      | true => exact e6SerrePosVec_mem_posSpan q
      | false => exact e6SerrePosSpan.neg_mem (e6SerrePosVec_mem_posSpan q)

private theorem e6Serre_adE_posVec_mem (i : Fin 6) (p : Fin 36) :
    ⁅e6SerreE i, e6SerrePosVec p⁆ ∈ e6SerrePosSpan := by
  rw [e6Serre_adE_posVec 11 p (e6PosHeight_le_11 p) i]
  exact evalPosUp_mem_posSpan _

private theorem e6Serre_adE_posSpan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerrePosSpan) : ⁅e6SerreE i, y⁆ ∈ e6SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerrePosSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      exact e6Serre_adE_posVec_mem i p

private theorem e6Serre_adE_cartan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerreCartan) : ⁅e6SerreE i, y⁆ ∈ e6SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerrePosSpan.smul_mem c ha
  | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [← lie_skew (e6SerreE i) (e6SerreH j), e6Serre_bracket_HE, ← neg_smul]
      exact e6SerrePosSpan.smul_mem _ (e6SerreE_mem_posSpan i)

private theorem e6Serre_adH_posVec_mem (i : Fin 6) :
    ∀ p : Fin 36, ⁅e6SerreH i, e6SerrePosVec p⁆ ∈ e6SerrePosSpan := by
  intro p
  induction hp_val : p.val using Nat.strong_induction_on generalizing p with
  | h n ih =>
      subst hp_val
      cases hp : e6PosParent p with
      | none =>
          rw [e6_ht_le_one_simple hp, e6Serre_bracket_HE]
          exact e6SerrePosSpan.smul_mem _ (e6SerreE_mem_posSpan _)
      | some kp₀ =>
          rcases kp₀ with ⟨k, p₀⟩
          have hlt : p₀.val < p.val := e6PosParent_lt hp
          rw [e6SerrePosVec_parent hp,
            leibniz_lie (e6SerreH i) (e6SerreE k) (e6SerrePosVec p₀),
            e6Serre_bracket_HE, smul_lie]
          refine e6SerrePosSpan.add_mem ?_ ?_
          · exact e6SerrePosSpan.smul_mem _ (e6Serre_adE_posVec_mem k p₀)
          · exact e6Serre_adE_posSpan_mem k (ih p₀.val hlt p₀ rfl)

private theorem e6Serre_adF_posVec_mem (i : Fin 6) :
    ∀ (n : ℕ) (p : Fin 36), e6PosHeight p ≤ n →
      ⁅e6SerreF i, e6SerrePosVec p⁆ ∈ e6SerrePosSpan ⊔ e6SerreCartan := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have := e6PosHeight_pos p
      omega
  | succ n ih =>
      intro p hp
      cases hpar : e6PosParent p with
      | none =>
          rw [e6_ht_le_one_simple hpar, ← lie_skew (e6SerreF i) (e6SerreE (simpleOfPos p))]
          by_cases hij : simpleOfPos p = i
          · rw [hij, e6Serre_bracket_EF_same]
            exact Submodule.mem_sup_right (e6SerreCartan.neg_mem (e6SerreH_mem_cartan i))
          · rw [e6Serre_bracket_EF_ne hij, neg_zero]
            exact (e6SerrePosSpan ⊔ e6SerreCartan).zero_mem
      | some kp₀ =>
          rcases kp₀ with ⟨k, p₀⟩
          have hlt : e6PosHeight p₀ ≤ n := by
            have := e6PosParent_ht_succ hpar
            omega
          rw [e6SerrePosVec_parent hpar,
            leibniz_lie (e6SerreF i) (e6SerreE k) (e6SerrePosVec p₀)]
          refine (e6SerrePosSpan ⊔ e6SerreCartan).add_mem ?_ ?_
          · rw [← lie_skew (e6SerreF i) (e6SerreE k)]
            by_cases hik : k = i
            · rw [hik, e6Serre_bracket_EF_same, neg_lie]
              exact Submodule.mem_sup_left
                (e6SerrePosSpan.neg_mem (e6Serre_adH_posVec_mem i p₀))
            · rw [e6Serre_bracket_EF_ne hik, neg_zero, zero_lie]
              exact (e6SerrePosSpan ⊔ e6SerreCartan).zero_mem
          · have hih := ih p₀ hlt
            rw [Submodule.mem_sup] at hih
            rcases hih with ⟨u, hu, v, hv, huv⟩
            rw [← huv, lie_add]
            exact Submodule.mem_sup_left
              (e6SerrePosSpan.add_mem (e6Serre_adE_posSpan_mem k hu)
                (e6Serre_adE_cartan_mem k hv))

private def submoduleLieNormalizer (S : Submodule ℝ (LieAlgebra.e₆ ℝ)) :
    LieSubalgebra ℝ (LieAlgebra.e₆ ℝ) where
  carrier := { x | ∀ y ∈ S, ⁅x, y⁆ ∈ S }
  zero_mem' y _ := by simp
  add_mem' hx hy y hyS := by rw [add_lie]; exact S.add_mem (hx y hyS) (hy y hyS)
  smul_mem' c x hx y hyS := by rw [smul_lie]; exact S.smul_mem c (hx y hyS)
  lie_mem' hx₁ hx₂ y hyS := by
    rw [lie_lie]
    exact S.sub_mem (hx₁ _ (hx₂ y hyS)) (hx₂ _ (hx₁ y hyS))

private theorem chevalley_posSpan_mem_negSpan {x : LieAlgebra.e₆ ℝ}
    (hx : x ∈ e6SerrePosSpan) : e6SerreChevalleyInv x ∈ e6SerreNegSpan := by
  induction hx using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact e6SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [map_smul]; exact e6SerreNegSpan.smul_mem c ha
  | mem _ hq =>
      rcases hq with ⟨q, rfl⟩
      exact Submodule.subset_span ⟨q, rfl⟩

private theorem chevalley_mem_span78_of_pos_cartan {x : LieAlgebra.e₆ ℝ}
    (hx : x ∈ e6SerrePosSpan ⊔ e6SerreCartan) :
    e6SerreChevalleyInv x ∈ e6SerreSpan78 := by
  rw [Submodule.mem_sup] at hx
  rcases hx with ⟨u, hu, v, hv, rfl⟩
  rw [map_add]
  refine Submodule.mem_sup_left (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.mem_sup_left (chevalley_posSpan_mem_negSpan hu)
  · apply Submodule.mem_sup_right
    induction hv using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ha hb => rw [map_add]; exact e6SerreCartan.add_mem ha hb
    | smul c _ _ ha => rw [map_smul]; exact e6SerreCartan.smul_mem c ha
    | mem _ hj =>
        rcases hj with ⟨j, rfl⟩
        rw [e6SerreChevalleyInv_H]
        exact e6SerreCartan.neg_mem (e6SerreH_mem_cartan j)

private theorem e6Serre_adH_negSpan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerreNegSpan) : ⁅e6SerreH i, y⁆ ∈ e6SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerreNegSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have heq : ⁅e6SerreH i, e6SerreNegVec p⁆ =
          -e6SerreChevalleyInv ⁅e6SerreH i, e6SerrePosVec p⁆ := by
        rw [LieEquiv.map_lie, e6SerreChevalleyInv_H, neg_lie, neg_neg]
        rfl
      rw [heq]
      exact e6SerreNegSpan.neg_mem (chevalley_posSpan_mem_negSpan (e6Serre_adH_posVec_mem i p))

private theorem e6Serre_adH_cartan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerreCartan) : ⁅e6SerreH i, y⁆ ∈ e6SerreCartan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerreCartan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerreCartan.smul_mem c ha
  | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [e6SerreH_comm]
      exact e6SerreCartan.zero_mem

private theorem e6Serre_adH_posSpan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerrePosSpan) : ⁅e6SerreH i, y⁆ ∈ e6SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerrePosSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      exact e6Serre_adH_posVec_mem i p

private theorem e6Serre_adE_negSpan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerreNegSpan) : ⁅e6SerreE i, y⁆ ∈ e6SerreSpan78 := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerreSpan78.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerreSpan78.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have heq : ⁅e6SerreE i, e6SerreNegVec p⁆ =
          e6SerreChevalleyInv ⁅e6SerreF i, e6SerrePosVec p⁆ := by
        rw [LieEquiv.map_lie, e6SerreChevalleyInv_F]; rfl
      rw [heq]
      exact chevalley_mem_span78_of_pos_cartan
        (e6Serre_adF_posVec_mem i 11 p (e6PosHeight_le_11 p))

private theorem e6Serre_adF_negSpan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerreNegSpan) : ⁅e6SerreF i, y⁆ ∈ e6SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerreNegSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have heq : ⁅e6SerreF i, e6SerreNegVec p⁆ =
          e6SerreChevalleyInv ⁅e6SerreE i, e6SerrePosVec p⁆ := by
        rw [LieEquiv.map_lie, e6SerreChevalleyInv_E]; rfl
      rw [heq]
      exact chevalley_posSpan_mem_negSpan (e6Serre_adE_posVec_mem i p)

private theorem e6Serre_adF_cartan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerreCartan) : ⁅e6SerreF i, y⁆ ∈ e6SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerreNegSpan.smul_mem c ha
  | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [← lie_skew (e6SerreF i) (e6SerreH j), e6Serre_bracket_HF, ← neg_smul]
      exact e6SerreNegSpan.smul_mem _ (e6SerreF_mem_negSpan i)

private theorem e6Serre_adF_posSpan_mem (i : Fin 6) {y : LieAlgebra.e₆ ℝ}
    (hy : y ∈ e6SerrePosSpan) : ⁅e6SerreF i, y⁆ ∈ e6SerreSpan78 := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e6SerreSpan78.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e6SerreSpan78.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have hmem := e6Serre_adF_posVec_mem i 11 p (e6PosHeight_le_11 p)
      rw [Submodule.mem_sup] at hmem
      rcases hmem with ⟨u, hu, v, hv, huv⟩
      rw [← huv]
      exact e6SerreSpan78.add_mem (Submodule.mem_sup_right hu)
        (Submodule.mem_sup_left (Submodule.mem_sup_right hv))

private theorem e6Serre_span78_ad_invariant (x : LieAlgebra.e₆ ℝ)
    (hx : x ∈ (Set.range e6SerreH ∪ Set.range e6SerreE ∪ Set.range e6SerreF)) :
    x ∈ submoduleLieNormalizer e6SerreSpan78 := by
  intro y hy
  have hy' : y ∈ e6SerreNegSpan ⊔ e6SerreCartan ⊔ e6SerrePosSpan := hy
  rcases Submodule.mem_sup.mp hy' with ⟨y₁, hy₁, y₃, hy₃, rfl⟩
  rcases Submodule.mem_sup.mp hy₁ with ⟨y_neg, hy_neg, y_car, hy_car, rfl⟩
  rw [lie_add, lie_add]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact e6SerreSpan78.add_mem
      (e6SerreSpan78.add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e6Serre_adH_negSpan_mem i hy_neg)))
        (Submodule.mem_sup_left (Submodule.mem_sup_right (e6Serre_adH_cartan_mem i hy_car))))
      (Submodule.mem_sup_right (e6Serre_adH_posSpan_mem i hy₃))
  · exact e6SerreSpan78.add_mem
      (e6SerreSpan78.add_mem
        (e6Serre_adE_negSpan_mem i hy_neg)
        (Submodule.mem_sup_right (e6Serre_adE_cartan_mem i hy_car)))
      (Submodule.mem_sup_right (e6Serre_adE_posSpan_mem i hy₃))
  · exact e6SerreSpan78.add_mem
      (e6SerreSpan78.add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e6Serre_adF_negSpan_mem i hy_neg)))
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e6Serre_adF_cartan_mem i hy_car))))
      (e6Serre_adF_posSpan_mem i hy₃)

private theorem e6Serre_span78_eq_top : e6SerreSpan78 = ⊤ := by
  have hnorm : submoduleLieNormalizer e6SerreSpan78 = ⊤ := by
    apply e6Serre_generators_generate
    · intro i
      exact e6Serre_span78_ad_invariant _ (Or.inl (Or.inl ⟨i, rfl⟩))
    · intro i
      exact e6Serre_span78_ad_invariant _ (Or.inl (Or.inr ⟨i, rfl⟩))
    · intro i
      exact e6Serre_span78_ad_invariant _ (Or.inr ⟨i, rfl⟩)
  let S_lie : LieSubalgebra ℝ (LieAlgebra.e₆ ℝ) :=
    { e6SerreSpan78 with
      lie_mem' := fun {x y} _ hy => by
        have hx_norm : x ∈ submoduleLieNormalizer e6SerreSpan78 := by rw [hnorm]; trivial
        exact hx_norm y hy }
  have htop : S_lie = ⊤ := by
    apply e6Serre_generators_generate
    · intro i
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (e6SerreH_mem_cartan i))
    · intro i
      exact Submodule.mem_sup_right (e6SerreE_mem_posSpan i)
    · intro i
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (e6SerreF_mem_negSpan i))
  exact congrArg LieSubalgebra.toSubmodule htop

private noncomputable def e6SerreSpanVec :
    Fin 6 ⊕ Fin 36 ⊕ Fin 36 → LieAlgebra.e₆ ℝ :=
  Sum.elim e6SerreH (Sum.elim e6SerrePosVec e6SerreNegVec)

private theorem e6SerreSpanVec_span_eq_top :
    Submodule.span ℝ (Set.range e6SerreSpanVec) = ⊤ := by
  rw [← e6Serre_span78_eq_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨idx, rfl⟩
    rcases idx with i | p | p
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (e6SerreH_mem_cartan i))
    · exact Submodule.mem_sup_right (e6SerrePosVec_mem_posSpan p)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨p, rfl⟩))
  · refine sup_le (sup_le ?_ ?_) ?_
    · dsimp only [e6SerreNegSpan]
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr p), rfl⟩
    · dsimp only [e6SerreCartan]
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · dsimp only [e6SerrePosSpan]
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inl p), rfl⟩

/-- `LieAlgebra.e₆ ℝ` is finite-dimensional, spanned by the 78 Chevalley elements. -/
instance e6Serre_finiteDimensional : FiniteDimensional ℝ (LieAlgebra.e₆ ℝ) := by
  have : Module.Finite ℝ (Submodule.span ℝ (Set.range e6SerreSpanVec)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range e6SerreSpanVec)
  exact Module.Finite.equiv
    ((LinearEquiv.ofEq _ ⊤ e6SerreSpanVec_span_eq_top).trans Submodule.topEquiv)

/-- The Serre presentation of `E₆` over `ℝ` has dimension at most `78`. -/
theorem finrank_e6_serre_le : Module.finrank ℝ (LieAlgebra.e₆ ℝ) ≤ 78 := by
  have h := finrank_le_of_span_eq_top e6SerreSpanVec_span_eq_top
  simpa using h

/-- The descended Serre quotient homomorphism `LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ h3zornCubicStabilizer`
is injective. -/
theorem h3zornE6SerreQuotientMap_injective :
    Function.Injective h3zornE6SerreQuotientMap := by
  let f := h3zornE6SerreQuotientMap.toLinearMap
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr h3zornE6SerreQuotientMap_surjective
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, finrank_h3zornCubicStabilizer] at hrank
  have hle : Module.finrank ℝ (LieAlgebra.e₆ ℝ) ≤ 78 := finrank_e6_serre_le
  have hker0 : Module.finrank ℝ (LinearMap.ker f) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)

/-- **E₆ Serre Isomorphism**: Mathlib's Serre quotient `LieAlgebra.e₆ ℝ` is isomorphic
as a real Lie algebra to the split Albert cubic stabilizer `h3zornCubicStabilizer`. -/
noncomputable def h3zornE6SerreEquiv :
    LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer :=
  LieEquiv.ofBijective h3zornE6SerreQuotientMap
    ⟨h3zornE6SerreQuotientMap_injective, h3zornE6SerreQuotientMap_surjective⟩

/-- Mathlib's Serre presentation `LieAlgebra.e₆ ℝ` has exact dimension `78`. -/
theorem finrank_e6_serre : Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78 := by
  rw [LinearEquiv.finrank_eq h3zornE6SerreEquiv.toLinearEquiv,
    finrank_h3zornCubicStabilizer]

/-- Mathlib's Serre presentation `LieAlgebra.e₆ ℝ` is a simple real Lie algebra. -/
instance e6Serre_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₆ ℝ) where
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top
        (I.map (h3zornE6SerreEquiv : LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ h3zornCubicStabilizer)) with
      hbot | htop
    · exact Or.inl (LieIdeal.bot_of_map_eq_bot h3zornE6SerreEquiv.injective hbot)
    · right
      rw [eq_top_iff]
      intro x _
      have hx : (h3zornE6SerreEquiv : LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ h3zornCubicStabilizer) x ∈
          I.map (h3zornE6SerreEquiv : LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ h3zornCubicStabilizer) := by
        rw [htop]
        trivial
      obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective h3zornE6SerreEquiv.surjective hx
      have hyx : (y : LieAlgebra.e₆ ℝ) = x := h3zornE6SerreEquiv.injective hy
      rw [← hyx]
      exact y.2
  non_abelian := by
    rw [lie_abelian_iff_equiv_lie_abelian h3zornE6SerreEquiv]
    exact LieAlgebra.IsSimple.non_abelian ℝ

end InfoGeometry.Algebra
