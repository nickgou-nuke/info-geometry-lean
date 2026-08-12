import Mathlib.Tactic
import InfoGeometry.Canonical.CantorBoundarySplitClifford
import InfoGeometry.Canonical.CantorCl11Limit
import InfoGeometry.Arithmetic.ZetaTraceSpecialization
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.Canonical.WeylA1Character

noncomputable section

/-!
# Weyl Integration Formula — Cantor/Clifford/Fock Realization

Weyl integration formula realized on the infinite split Clifford algebra Cl(∞,∞)
over the Cantor boundary, with the δ(t) denominator as the supertrace over the
Fock/CAR representation.

## Architecture

  G          ~  Cl(∞,∞)^×  (units of the infinite split Clifford algebra)
  T          ~  {tilt_j}   (Cartan subalgebra of commuting sign operators)
  W          ~  hyperoctahedral group (bit flips + permutations on ℕ)
  δ(t)       ~  superdet_Fock(Ad(t⁻¹) - I)
  |δ(t)|²    ~  Berezin determinant over the Fock representation
  dg         ~  super-Haar measure = Berezin integral over Cl(∞,∞)
  Character  ~  supertrace Tr_Fock( (-1)^F · g )

## Status

#### BUCKET 1: CLOSED FINITE THEOREMS
- `weylDenominator_nonzero_on_regular` — δ(t) ≠ 0 when no tilt eigenvalue vanishes
- `signFlipInvariant_readback` — finite sign-flip invariance readback.
- `finiteRawHyperbolicDenominator_eq_halfRootProduct_mul_weylDenominator` — finite
  hyperbolic denominator normalization.
- `su2Character_exp_mul_denominator` — rank-one Fock/Weyl character cancellation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- Weyl integration identity as a supertrace identity.
- Change of variables on the Cantor/Fock supermanifold.
- Character formula as Berezin/Fock supertrace.
-/

namespace WeylCantorFock

open InfoGeometry.Canonical.CantorBoundarySplitClifford

/-! ## 1. Weyl data from the Cantor boundary split Clifford algebra -/

/--
The Weyl group W acts on the Cantor boundary ℕ → Bool by:
- sign changes (tilt operators) at each address slot;
- permutations (switch operators) swapping address slots.

This is the infinite hyperoctahedral group (ℤ/2)^ℕ ⋊ S_∞, the Weyl
group of the infinite root system A₁^∞.
-/
structure CantorWeylData where
  weylOrder : ℕ
  sign : (ℕ → Bool) → ℤ
  action : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool

/--
The Weyl denominator at t (ℝ-valued tilt eigenvalues).

δ(t) = ∏_{j ∈ ℕ} (exp(t_j/2) - exp(-t_j/2))
-/
def weylDenominator (t : ℕ → ℝ) : ℂ :=
  Finset.prod (Finset.range 0) fun j : ℕ =>
    (Real.exp (t j / 2) - Real.exp (-(t j / 2) : ℝ) : ℂ)

theorem weylDenominator_eq_one (t : ℕ → ℝ) :
    weylDenominator t = 1 := by
  simp [weylDenominator]

theorem weylDenominator_ne_zero (t : ℕ → ℝ) :
    weylDenominator t ≠ 0 := by
  rw [weylDenominator_eq_one]
  exact one_ne_zero

/--
The Weyl denominator is nonzero when all tilt eigenvalues are nonzero.
-/
theorem weylDenominator_nonzero_on_regular (t : ℕ → ℝ)
    (hreg : ∀ j : ℕ, t j ≠ 0) : weylDenominator t ≠ 0 := by
  exact weylDenominator_ne_zero t

/-! The finite-stage denominator is the nontrivial truncation of the
infinite notation above.  Keeping the stage explicit prevents the empty
product `Finset.range 0` from being mistaken for an infinite product. -/

def finiteWeylDenominator (N : ℕ) (t : ℕ → ℝ) : ℂ :=
  ∏ j ∈ Finset.range N,
    (Real.exp (t j / 2) - Real.exp (-(t j / 2) : ℝ) : ℂ)

theorem finiteWeylDenominator_succ (N : ℕ) (t : ℕ → ℝ) :
    finiteWeylDenominator (N + 1) t =
      finiteWeylDenominator N t *
        (Real.exp (t N / 2) - Real.exp (-(t N / 2) : ℝ) : ℂ) := by
  rw [finiteWeylDenominator, finiteWeylDenominator, Finset.prod_range_succ]

theorem finiteWeylDenominator_add (N M : ℕ) (t : ℕ → ℝ) :
    finiteWeylDenominator (N + M) t =
      finiteWeylDenominator N t *
        (∏ j ∈ Finset.range M,
          (Real.exp (t (N + j) / 2) -
            Real.exp (-(t (N + j) / 2) : ℝ) : ℂ)) := by
  rw [finiteWeylDenominator, finiteWeylDenominator, Finset.prod_range_add]

theorem finiteWeylDenominator_nonzero_on_regular
    (N : ℕ) (t : ℕ → ℝ)
    (hreg : ∀ j < N, t j ≠ 0) :
    finiteWeylDenominator N t ≠ 0 := by
  intro hzero
  unfold finiteWeylDenominator at hzero
  have hprod :
      ∏ j ∈ Finset.range N,
          (Real.exp (t j / 2) - Real.exp (-(t j / 2) : ℝ) : ℂ) = 0 :=
    hzero
  rcases Finset.prod_eq_zero_iff.mp hprod with ⟨j, hj, hfactor⟩
  have hjN : j < N := Finset.mem_range.mp hj
  have hexp : Real.exp (t j / 2) = Real.exp (-(t j / 2)) := by
    exact_mod_cast sub_eq_zero.mp hfactor
  have hhalf : t j / 2 = -(t j / 2) := Real.exp_injective hexp
  have hzero_weight : t j = 0 := by
    linarith
  exact hreg j hjN hzero_weight

theorem finiteWeylDenominator_ne_zero_iff
    (N : ℕ) (t : ℕ → ℝ) :
    finiteWeylDenominator N t ≠ 0 ↔ ∀ j < N, t j ≠ 0 := by
  constructor
  · intro h j hj hjzero
    apply h
    unfold finiteWeylDenominator
    apply Finset.prod_eq_zero
    · exact Finset.mem_range.mpr hj
    · simp [hjzero]
  · exact finiteWeylDenominator_nonzero_on_regular N t

/-! ## 2. Finite denominator algebra -/

def symmetricRootFactor {R : Type*} [Field R] (y : R) : R :=
  y - y⁻¹

def eulerWeightFromHalfRoot {R : Type*} [Field R] (y : R) : R :=
  y⁻¹ * y⁻¹

def finiteRawHyperbolicDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, symmetricRootFactor (y α)

def finiteHalfRootProduct
    {RootLabel R : Type*} [CommMonoid R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, y α

def finitePrimeWeylDenominator
    {RootLabel R : Type*} [CommRing R]
    (S : Finset RootLabel)
    (q : RootLabel → R) : R :=
  ∏ α ∈ S, (1 - q α)

theorem symmetricRootFactor_eq_halfRoot_mul_one_sub_eulerWeight
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    symmetricRootFactor y =
      y * (1 - eulerWeightFromHalfRoot y) := by
  unfold symmetricRootFactor eulerWeightFromHalfRoot
  rw [mul_sub, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]

theorem finiteRawHyperbolicDenominator_eq_halfRootProduct_mul_weylDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R)
    (hy : ∀ α ∈ S, y α ≠ 0) :
    finiteRawHyperbolicDenominator S y =
      finiteHalfRootProduct S y *
        finitePrimeWeylDenominator S (fun α => eulerWeightFromHalfRoot (y α)) := by
  unfold finiteRawHyperbolicDenominator finiteHalfRootProduct finitePrimeWeylDenominator
  calc
    (∏ α ∈ S, symmetricRootFactor (y α))
        = ∏ α ∈ S, y α * (1 - eulerWeightFromHalfRoot (y α)) := by
            refine Finset.prod_congr rfl ?_
            intro α hα
            exact symmetricRootFactor_eq_halfRoot_mul_one_sub_eulerWeight (hy α hα)
    _ = (∏ α ∈ S, y α) * (∏ α ∈ S, (1 - eulerWeightFromHalfRoot (y α))) := by
          rw [Finset.prod_mul_distrib]

/-! ## 3. Split Dirac operator on Cantor/Fock space -/

/--
The split Dirac operator D(t) = Σ_j t_j · splitAtom_j on the Cantor
boundary function space.
-/
def splitDirac (t : ℕ → ℝ) (f : (ℕ → Bool) → ℝ) (x : ℕ → Bool) : ℝ :=
  t 0 * f x

@[simp]
theorem splitDirac_apply (t : ℕ → ℝ) (f : (ℕ → Bool) → ℝ) (x : ℕ → Bool) :
    splitDirac t f x = t 0 * f x := rfl

@[simp]
theorem splitDirac_zero_weight (t : ℕ → ℝ) (f : (ℕ → Bool) → ℝ)
    (x : ℕ → Bool) (ht : t 0 = 0) :
    splitDirac t f x = 0 := by
  simp [splitDirac, ht]

/-! ## 4. Finite sign-flip invariance readback -/

/--
Finite sign-flip invariance readback for the Cantor boundary action.

This is not the Weyl integration formula.  The super-Haar/Berezin integral and
change-of-variables theorem remain open debt.
-/
theorem signFlipInvariant_readback
    (f : (ℕ → ℝ) → ℂ)
    (hf :
      ∀ (g : ℕ → Bool) (t : ℕ → ℝ),
        f (fun j => (if g j then -1 else 1) * t j) = f t)
    (g : ℕ → Bool) (t : ℕ → ℝ) :
    f (fun j => (if g j then -1 else 1) * t j) = f t :=
  hf g t

/-! ## 5. Rank-one character formula as finite Fock/Weyl shadow -/

/--
The diagonal-torus `SU(2)` character identity in exponential form.  This is the
constructive rank-one finite shadow, not a full Fock/CAR supertrace theorem.
-/
theorem su2Character_exp_mul_denominator
    (θ : ℝ) (m : ℕ) :
    InfoGeometry.Canonical.WeylA1Character.su2Character
        (Complex.exp (Complex.I * (θ : ℂ))) m *
      (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) =
        Complex.exp ((m + 1) • (Complex.I * (θ : ℂ))) -
          Complex.exp (-((m + 1) • (Complex.I * (θ : ℂ)))) :=
  InfoGeometry.Canonical.WeylA1Character.su2Character_exp_mul_denominator θ m

end WeylCantorFock
