/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Parity lowering on the even-translation Laurent module

The translation ring is the native additive group algebra
`(ZMod 2)[ℤ³]`. Its coefficient ring after blocking is the group algebra of
the subgroup of vectors whose coordinates are even. The coefficient action
is induced by the actual subgroup inclusion, so the coarse generator in a
coordinate acts as the square of the original translation generator.

The map `lowering j` sends a monomial `x^n` to
`(n_j : ZMod 2) x^(n-e_j)`. This formula includes negative exponents. Its
linearity over the coarse ring is proved from its Leibniz identity and the
vanishing of the derivative on even translation monomials.

The `difference j` operators multiply by `x_j - 1`. The identities
`lowering j * difference j + difference j * lowering j = 1` and off-axis
commutation take place in the noncommutative endomorphism ring of this
Laurent module. A same-carrier witness proves that lowering and its own
difference operator do not commute.

This is the coefficient-module construction in Appendix G, equations
G1--G3, of Hao Song, arXiv:2608.09913v1. It does not assert a Clifford-circuit
realization, a topological classification, or a superselection calculation.
-/

noncomputable section

namespace InfoGeometry.Quantum.EvenTranslationOperators

/-- Integer translation exponents in three spatial directions. -/
abbrev Lattice := Fin 3 → ℤ

/-- Coordinatewise reduction modulo two. -/
def parityHom : Lattice →+ (Fin 3 → ZMod 2) where
  toFun n j := n j
  map_zero' := by ext j; simp
  map_add' n m := by ext j; simp

/-- The actual even-translation subgroup of the integer lattice. -/
def evenLattice : AddSubgroup Lattice := parityHom.ker

/-- An exponent belonging to the even-translation subgroup. -/
abbrev EvenLattice := ↥evenLattice

theorem mem_evenLattice_iff (n : Lattice) :
    n ∈ evenLattice ↔ ∀ j, Even (n j) := by
  change parityHom n = 0 ↔ _
  constructor
  · intro h j
    apply ZMod.intCast_eq_zero_iff_even.mp
    exact congrFun h j
  · intro h
    funext j
    exact ZMod.intCast_eq_zero_iff_even.mpr (h j)

@[simp] theorem evenLattice_cast (n : EvenLattice) (j : Fin 3) :
    ((n : Lattice) j : ZMod 2) = 0 :=
  congrFun n.property j

/-- Finite-support Laurent polynomials on the original lattice. -/
abbrev TranslationRing := AddMonoidAlgebra (ZMod 2) Lattice

/-- Finite-support Laurent polynomials on the even sublattice. -/
abbrev CoarseRing := AddMonoidAlgebra (ZMod 2) EvenLattice

/-- The coefficient inclusion induced by the subgroup inclusion. -/
def coarseInclusion : CoarseRing →+* TranslationRing :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod 2) evenLattice.subtype

@[simp] theorem coarseInclusion_single (n : EvenLattice) (c : ZMod 2) :
    coarseInclusion (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (n : Lattice) c :=
  AddMonoidAlgebra.mapDomain_single

theorem coarseInclusion_injective : Function.Injective coarseInclusion :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- Restriction of scalars along the actual even-sublattice inclusion. -/
instance coarseAlgebra : Algebra CoarseRing TranslationRing :=
  coarseInclusion.toAlgebra

@[simp] theorem coarse_smul (a : CoarseRing) (r : TranslationRing) :
    a • r = coarseInclusion a * r := rfl

/-- The original binary coefficient action factors through the coarse ring. -/
instance coarseScalarTower : IsScalarTower (ZMod 2) CoarseRing TranslationRing :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change AddMonoidAlgebra.single (0 : Lattice) c =
      coarseInclusion (AddMonoidAlgebra.single (0 : EvenLattice) c)
    exact (coarseInclusion_single 0 c).symm

instance translationCharP : CharP TranslationRing 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2

instance coarseCharP : CharP CoarseRing 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2

/-- A unit translation exponent in a specified direction. -/
def unitStep (j : Fin 3) : Lattice := Pi.single j 1

@[simp] theorem unitStep_self (j : Fin 3) : unitStep j j = 1 := by
  simp [unitStep]

@[simp] theorem unitStep_of_ne {j l : Fin 3} (h : j ≠ l) :
    unitStep l j = 0 := by
  simp [unitStep, h]

/-- One translation step as an actual Laurent monomial. -/
def generator (j : Fin 3) : TranslationRing :=
  AddMonoidAlgebra.single (unitStep j) 1

/-- Two translation steps belong to the even sublattice. -/
def doubledStep (j : Fin 3) : EvenLattice :=
  ⟨unitStep j + unitStep j, by
    change parityHom (unitStep j + unitStep j) = 0
    funext l
    change (((unitStep j) l + (unitStep j) l : ℤ) : ZMod 2) = 0
    rw [Int.cast_add]
    exact CharTwo.add_self_eq_zero _⟩

/-- A unit coarse translation, corresponding to two original lattice steps. -/
def coarseGenerator (j : Fin 3) : CoarseRing :=
  AddMonoidAlgebra.single (doubledStep j) 1

/-- The coarse coefficient action is precisely `y_j ↦ x_j²`. -/
theorem coarseInclusion_coarseGenerator (j : Fin 3) :
    coarseInclusion (coarseGenerator j) = generator j ^ 2 := by
  simp [coarseGenerator, coarseInclusion_single, generator, pow_two,
    AddMonoidAlgebra.single_mul_single, doubledStep]

/-- The Laurent partial derivative, first constructed as a coefficient-linear map. -/
def lowerLinear (j : Fin 3) : TranslationRing →ₗ[ZMod 2] TranslationRing :=
  (Finsupp.lsum (ZMod 2) fun n : Lattice =>
    (n j : ZMod 2) •
      (AddMonoidAlgebra.lsingle (n - unitStep j) :
        ZMod 2 →ₗ[ZMod 2] TranslationRing)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap

/-- The defining monomial formula includes arbitrary integer exponents. -/
@[simp] theorem lowerLinear_single (j : Fin 3) (n : Lattice) (c : ZMod 2) :
    lowerLinear j (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (n - unitStep j) ((n j : ZMod 2) * c) := by
  change (Finsupp.lsum (ZMod 2) _)
      (Finsupp.single n c) = _
  rw [Finsupp.lsum_single]
  simp only [LinearMap.smul_apply, AddMonoidAlgebra.lsingle_apply,
    AddMonoidAlgebra.smul_single, smul_eq_mul]

/-- Leibniz holds for the convolution product on the actual group algebra. -/
theorem lowerLinear_mul (j : Fin 3) (r s : TranslationRing) :
    lowerLinear j (r * s) = lowerLinear j r * s + r * lowerLinear j s := by
  induction r using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add r t hr ht =>
      simp only [add_mul, map_add, hr, ht]
      abel
  | single n c =>
      induction s using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add s t hs ht =>
          simp only [mul_add, map_add, hs, ht]
          abel
      | single m d =>
          simp only [AddMonoidAlgebra.single_mul_single, lowerLinear_single,
            Pi.add_apply, Int.cast_add]
          have h₁ : n - unitStep j + m = n + m - unitStep j := by abel
          have h₂ : n + (m - unitStep j) = n + m - unitStep j := by abel
          rw [h₁, h₂, ← AddMonoidAlgebra.single_add]
          congr 1
          ring

@[simp] theorem lowerLinear_one (j : Fin 3) :
    lowerLinear j 1 = 0 := by
  change lowerLinear j (AddMonoidAlgebra.single 0 1) = 0
  simp

@[simp] theorem lowerLinear_generator (j : Fin 3) :
    lowerLinear j (generator j) = 1 := by
  simp [generator, lowerLinear_single, AddMonoidAlgebra.one_def]

@[simp] theorem lowerLinear_generator_of_ne {j l : Fin 3} (h : j ≠ l) :
    lowerLinear j (generator l) = 0 := by
  simp [generator, lowerLinear_single, unitStep_of_ne h]

/-- Every even-translation coefficient is killed by the Laurent derivative. -/
@[simp] theorem lowerLinear_coarseInclusion (j : Fin 3) (a : CoarseRing) :
    lowerLinear j (coarseInclusion a) = 0 := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single n c =>
      rw [coarseInclusion_single, lowerLinear_single, evenLattice_cast]
      simp

/-- This is the nontrivial linearity statement required by even blocking. -/
theorem lowerLinear_coarse_smul (j : Fin 3) (a : CoarseRing) (r : TranslationRing) :
    lowerLinear j (a • r) = a • lowerLinear j r := by
  rw [coarse_smul, coarse_smul, lowerLinear_mul, lowerLinear_coarseInclusion,
    zero_mul, zero_add]

/-- The parity-lowering map is a native endomorphism over the coarse ring. -/
def lowering (j : Fin 3) : Module.End CoarseRing TranslationRing where
  toFun := lowerLinear j
  map_add' := (lowerLinear j).map_add
  map_smul' := lowerLinear_coarse_smul j

@[simp] theorem lowering_apply (j : Fin 3) (r : TranslationRing) :
    lowering j r = lowerLinear j r := rfl

@[simp] theorem lowering_single (j : Fin 3) (n : Lattice) (c : ZMod 2) :
    lowering j (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (n - unitStep j) ((n j : ZMod 2) * c) :=
  lowerLinear_single j n c

@[simp] theorem lowering_one (j : Fin 3) : lowering j 1 = 0 :=
  lowerLinear_one j

/-- Multiplication by `x_j - 1`, regarded as a coarse-linear operator. -/
def difference (j : Fin 3) : Module.End CoarseRing TranslationRing :=
  LinearMap.mulLeft CoarseRing (generator j - 1)

@[simp] theorem difference_apply (j : Fin 3) (r : TranslationRing) :
    difference j r = (generator j - 1) * r := rfl

/-- The three translation differences commute with one another. -/
theorem difference_commute (j l : Fin 3) : Commute (difference j) (difference l) := by
  change difference j * difference l = difference l * difference j
  apply LinearMap.ext
  intro r
  change (generator j - 1) * ((generator l - 1) * r) =
    (generator l - 1) * ((generator j - 1) * r)
  ac_rfl

/-- Differentiating a same-axis translation difference gives the unit term. -/
theorem lowering_difference_apply (j : Fin 3) (r : TranslationRing) :
    lowering j (difference j r) = r + difference j (lowering j r) := by
  change lowerLinear j ((generator j - 1) * r) =
    r + (generator j - 1) * lowerLinear j r
  rw [lowerLinear_mul, map_sub, lowerLinear_generator, lowerLinear_one]
  simp

/-- The block-local contraction identity in the noncommutative endomorphism ring. -/
theorem lowering_mul_difference_add_difference_mul_lowering (j : Fin 3) :
    lowering j * difference j + difference j * lowering j = 1 := by
  apply LinearMap.ext
  intro r
  change lowering j (difference j r) + difference j (lowering j r) = r
  rw [lowering_difference_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Lowering commutes with every translation difference in another direction. -/
theorem lowering_commute_difference_of_ne {j l : Fin 3} (h : j ≠ l) :
    Commute (lowering j) (difference l) := by
  change lowering j * difference l = difference l * lowering j
  apply LinearMap.ext
  intro r
  change lowerLinear j ((generator l - 1) * r) =
    (generator l - 1) * lowerLinear j r
  rw [lowerLinear_mul, map_sub, lowerLinear_generator_of_ne h, lowerLinear_one]
  simp

/-- The same Laurent-module operators genuinely fail to commute on their own axis. -/
theorem lowering_difference_noncommute (j : Fin 3) :
    ¬ Commute (lowering j) (difference j) := by
  intro h
  have he := congrArg (fun f : Module.End CoarseRing TranslationRing => f 1) h.eq
  change lowering j (difference j 1) = difference j (lowering j 1) at he
  have h10 : (1 : TranslationRing) = 0 := by
    simpa only [lowering_difference_apply, lowering_one, map_zero, add_zero] using he
  exact one_ne_zero h10

end InfoGeometry.Quantum.EvenTranslationOperators
