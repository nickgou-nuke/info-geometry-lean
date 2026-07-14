import Mathlib

/-!
# Castro theta scaling bridge, finite owner surface

This module isolates a small theorem-backed fragment inspired by Castro's
scaling-operator and Gauss-Jacobi-theta strategy:

* a doubled carrier where modular swap exchanges the two scaling channels;
* a finite theta-weight readout whose `l ↔ -l`, `τ ↔ -τ` duality is explicit;
* a finite Kronecker resolution identity, the finite algebraic shadow of a
  completeness/trace formula.

#### BUCKET 1: CLOSED FINITE THEOREMS
The doubled-swap identities, finite theta duality, and finite Kronecker
resolution are proved outright.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
No Hilbert-Polya operator, self-adjointness theorem, Gauss-Jacobi modular
transformation theorem, analytic theta integral, spectral trace formula,
zeta-zero completeness theorem, or Riemann Hypothesis consequence is proved
here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CastroThetaScalingBridge

open scoped BigOperators

/-! ## Doubled scaling channels -/

/-- The modular swap on a doubled carrier. -/
def modularSwap {α : Type*} (x : α × α) : α × α :=
  (x.2, x.1)

/-- A diagonal doubled scaling action with two possibly different channels. -/
def doubledScaling {α : Type*} (D1 D2 : α → α) (x : α × α) : α × α :=
  (D1 x.1, D2 x.2)

@[simp]
theorem modularSwap_involutive {α : Type*} (x : α × α) :
    modularSwap (modularSwap x) = x := by
  cases x
  rfl

/--
The modular swap exchanges the two scaling channels.

This is the finite doubled-carrier core behind the informal dictionary
`D1 ↔ D2` under `t ↦ 1/t`.
-/
theorem modularSwap_doubledScaling_modularSwap
    {α : Type*} (D1 D2 : α → α) (x : α × α) :
    modularSwap (doubledScaling D1 D2 (modularSwap x)) =
      doubledScaling D2 D1 x := by
  cases x
  rfl

/-! ## Finite Gauss-Jacobi theta readout -/

/--
Finite theta weight in logarithmic coordinate `τ`.

This is only a finite scalar readout.  No infinite theta series or modular
Poisson summation theorem is asserted here.
-/
def thetaWeight (l τ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (l * τ))

lemma thetaWeight_pos (l τ : ℝ) (n : ℤ) :
    0 < thetaWeight l τ n := by
  unfold thetaWeight
  exact Real.exp_pos _

/-- Finite Gauss-Jacobi-style theta sum over a supplied finite index set. -/
def finiteTheta (S : Finset ℤ) (l τ : ℝ) : ℝ :=
  ∑ n ∈ S, thetaWeight l τ n

lemma finiteTheta_nonneg (S : Finset ℤ) (l τ : ℝ) :
    0 ≤ finiteTheta S l τ := by
  unfold finiteTheta
  exact Finset.sum_nonneg (fun n _hn => le_of_lt (thetaWeight_pos l τ n))

lemma finiteTheta_pos_of_nonempty {S : Finset ℤ} (hS : S.Nonempty) (l τ : ℝ) :
    0 < finiteTheta S l τ := by
  unfold finiteTheta
  rcases hS with ⟨n, hn⟩
  exact Finset.sum_pos'
    (fun m _hm => le_of_lt (thetaWeight_pos l τ m))
    ⟨n, hn, thetaWeight_pos l τ n⟩

/-- The finite theta weight is invariant under the paired duality `l,τ ↦ -l,-τ`. -/
theorem thetaWeight_dual (l τ : ℝ) (n : ℤ) :
    thetaWeight (-l) τ n = thetaWeight l (-τ) n := by
  unfold thetaWeight
  congr 1
  ring_nf

/-- The same paired duality after summing over any finite index set. -/
theorem finiteTheta_dual (S : Finset ℤ) (l τ : ℝ) :
    finiteTheta S (-l) τ = finiteTheta S l (-τ) := by
  unfold finiteTheta
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact thetaWeight_dual l τ n

/-! ## Finite trace/completeness shadow -/

/-- Kronecker delta as a real-valued finite kernel. -/
def kronecker {ι : Type*} [DecidableEq ι] (i j : ι) : ℝ :=
  if i = j then 1 else 0

@[simp]
theorem kronecker_self {ι : Type*} [DecidableEq ι] (i : ι) :
    kronecker i i = 1 := by
  simp [kronecker]

theorem kronecker_of_ne {ι : Type*} [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    kronecker i j = 0 := by
  simp [kronecker, h]

/--
Finite resolution of the identity for the Kronecker kernel.

This is the finite algebraic shadow of a completeness trace formula.  It does
not assert analytic completeness of Castro eigenfunctions.
-/
theorem finite_kronecker_resolution
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (∑ k : ι, kronecker k i * kronecker k j) = kronecker i j := by
  by_cases hij : i = j
  · subst j
    rw [kronecker_self]
    calc
      (∑ k : ι, kronecker k i * kronecker k i)
          = ∑ k : ι, kronecker k i := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hki : k = i
              · simp [kronecker, hki]
              · simp [kronecker, hki]
      _ = 1 := by
              rw [← kronecker_self i]
              exact Fintype.sum_eq_single i
                (by intro k hk; simp [kronecker, hk])
  · rw [kronecker_of_ne hij]
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hki : k = i
    · have hkj : k ≠ j := by
        intro h
        exact hij (hki.symm.trans h)
      simp [kronecker, hki, hij]
    · simp [kronecker, hki]

end InfoGeometry.Arithmetic.CastroThetaScalingBridge
