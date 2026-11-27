/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FreedCliffordSuspension
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita
import InfoGeometry.Algebra.Grothendieck

/-!
# Native ABS restriction and the zero-step arithmetic cokernel

This focused owner contains the exact restriction and degree-zero arithmetic
constructions previously owned by `KahlerHestenesJWABSPrimary`. Their original
namespaces, declaration types and proofs are preserved. The synthesis module
imports this owner, while actual-module comparisons can depend on these native
constructions without importing the unrelated synthesis graph.

The categorical functor acts on actual graded modules. The zero-step arithmetic
monoid and Grothendieck cokernel are distinct declarations; their comparison
with an actual represented module requires an explicit theorem.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary.AtiyahBottShapiroPrimary

open CliffordAlgebra CategoryTheory
open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita
open scoped TensorProduct

/-- `S2-18` (ABS 1964 §5 p. 11; Freed `positiveForm`): Coordinate-free canonical inclusion
`i : CliffordAlgebra Q →ₐ[R] CliffordAlgebra (positiveForm Q)` where
`positiveForm Q = Q.prod (-QuadraticMap.sq)` extends `Q` by a negative-square vector (`R3.2`). -/
def absInclusion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra (positiveForm Q) :=
  CliffordAlgebra.map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq (R := R)))

/-- `S2-18` (ABS 1964 §5): `absInclusion Q` commutes with the `ℤ/2`-grade involution
`CliffordAlgebra.involute`, making `absInclusion Q` a graded algebra homomorphism. -/
theorem absInclusion_involute_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    absInclusion Q (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (absInclusion Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [AlgHom.commutes]
  | ι m =>
    simp [absInclusion, CliffordAlgebra.map_apply_ι, CliffordAlgebra.involute_ι]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `S2-18` (ABS 1964 §5): Category `M(Cl(Q))` of `ℤ/2`-graded `CliffordAlgebra Q`-modules
(built directly over `GradedModuleCat` from `GradedMatrixMorita.lean`). -/
abbrev absModuleCat {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :=
  GradedModuleCat (CliffordAlgebra.involuteEquiv (Q := Q)).toRingEquiv

/-- `S2-18` (ABS 1964 §5 p. 11): Categorical graded-module restriction functor
`i* : M(Cl(Q ⊕ ⟨-1⟩)) ⥤ M(Cl(Q))` induced by `absInclusion Q`. -/
def absRestrictionFunctor {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :
    absModuleCat (positiveForm Q) ⥤ absModuleCat Q :=
  InfoGeometry.OperatorAlgebra.GradedMatrixMorita.restrict
    (CliffordAlgebra.involuteEquiv (Q := Q)).toRingEquiv
    (CliffordAlgebra.involuteEquiv (Q := positiveForm Q)).toRingEquiv
    (absInclusion Q).toRingHom
    (fun x => absInclusion_involute_comm Q x)

/-- `S2-18` (ABS 1964 §5 Table 2, p. 12): The arithmetic diagonal monoid map
`k ↦ (k, k)` from `ℕ` to `ℕ × ℕ`. The theorem
`ABSZeroStepModuleComparison.restrictionSuperDimension_eq_diagonal` identifies
this map with the superdimension invariant of each actual finite represented
negative-line restriction. This definition alone does not identify a monoid
of module isomorphism classes with `ℕ`. -/
def absZeroStepRestrictMonoid : ℕ →+ ℕ × ℕ where
  toFun k := (k, k)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `S2-18` (ABS 1964 §5): The Grothendieck completion of the arithmetic
map `absZeroStepRestrictMonoid`, using `Algebra/Grothendieck.lean`. Categorical
restriction is separately constructed by `absRestrictionFunctor`; the
objectwise comparison for actual finite represented modules is proved in
`ABSZeroStepModuleComparison.restrictionClass_eq`. -/
def absZeroStepRestrictK0 : Grothendieck ℕ →+ Grothendieck (ℕ × ℕ) :=
  grothendieckFunctor absZeroStepRestrictMonoid

/-- `S2-18` (ABS 1964 §5): Arithmetic superdimension homomorphism
`Grothendieck (ℕ × ℕ) →+ ℤ`, sending
`[(a₀, a₁), (b₀, b₁)] ↦ (a₀ - a₁) - (b₀ - b₁)`. -/
def absSuperDimHom : Grothendieck (ℕ × ℕ) →+ ℤ :=
  grothendieckLift
    { toFun := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]
        ring }

/-- `S2-18` (ABS 1964 §5): `absSuperDimHom` is surjective onto `ℤ`. -/
theorem absSuperDimHom_surjective : Function.Surjective absSuperDimHom := by
  intro z
  refine ⟨grothendieckMap (ℕ × ℕ) (z.toNat, (-z).toNat), ?_⟩
  dsimp [absSuperDimHom]
  rw [grothendieckLift_comp]
  change (z.toNat : ℤ) - ((-z).toNat : ℤ) = z
  omega

/-- `S2-18` (ABS 1964 §5 Table 2): The kernel of arithmetic superdimension
is the range of the completed diagonal map `absZeroStepRestrictK0`.
This is exactness for the displayed arithmetic Grothendieck groups; it does
not assert an equivalence with Grothendieck groups of module classes. -/
theorem absSuperDimHom_ker_eq_range :
    absSuperDimHom.ker = absZeroStepRestrictK0.range := by
  apply le_antisymm
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rcases grothendieck_eq_sub x with ⟨a, b, rfl⟩
    have hdiff : ((a.1 : ℤ) - (a.2 : ℤ)) - ((b.1 : ℤ) - (b.2 : ℤ)) = 0 := by
      simpa [absSuperDimHom, grothendieckLift_comp] using hx
    have hnat : a.1 + b.2 = a.2 + b.1 := by omega
    refine ⟨grothendieckMap ℕ a.1 - grothendieckMap ℕ b.1, ?_⟩
    rw [map_sub, absZeroStepRestrictK0, grothendieckFunctor_map, grothendieckFunctor_map]
    rw [grothendieck_sub_mk, grothendieck_sub_mk]
    apply Quotient.sound
    refine ⟨(0, a.2 + b.1), ?_⟩
    ext <;> simp [absZeroStepRestrictMonoid] <;> omega
  · rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    rcases grothendieck_eq_sub y with ⟨m, n, rfl⟩
    rw [map_sub, absZeroStepRestrictK0, grothendieckFunctor_map, grothendieckFunctor_map]
    simp [absSuperDimHom, grothendieckLift_comp, absZeroStepRestrictMonoid]

/-- `S2-18` (ABS 1964 §5 Table 2, p. 12): The arithmetic cokernel
`Grothendieck (ℕ × ℕ) / range(absZeroStepRestrictK0)` is isomorphic to `ℤ`.
Its comparison with module-class or topological ABS groups is a separate
statement. `ABSZeroStepModuleComparison.restrictionClass_integer_zero` proves
that the invariant of every actual finite represented restriction maps to zero. -/
def absCokernelZeroEquivInt :
    (Grothendieck (ℕ × ℕ) ⧸ absZeroStepRestrictK0.range) ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq absSuperDimHom_ker_eq_range.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective absSuperDimHom absSuperDimHom_surjective)

/-- `S2-18` (ABS 1964 §5): Compatibility of the arithmetic cokernel
isomorphism `absCokernelZeroEquivInt` with
`Algebra/Grothendieck.grothendieckEquivInt` on `ℕ`-generators. -/
theorem absCokernelZero_compatible_with_grothendieckEquivInt (k : ℕ) :
    absCokernelZeroEquivInt
        (QuotientAddGroup.mk (grothendieckMap (ℕ × ℕ) (k, 0))) =
      grothendieckEquivInt (grothendieckMap ℕ k) := by
  change absSuperDimHom (grothendieckMap (ℕ × ℕ) (k, 0)) =
    grothendieckToInt (grothendieckMap ℕ k)
  dsimp [absSuperDimHom]
  rw [grothendieckLift_comp]
  change (k : ℤ) - (0 : ℤ) = to_int_raw (k, 0)
  simp [to_int_raw]

end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary.AtiyahBottShapiroPrimary
