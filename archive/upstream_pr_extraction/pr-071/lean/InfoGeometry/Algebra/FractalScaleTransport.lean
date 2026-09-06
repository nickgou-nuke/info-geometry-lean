import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.FractalScaleTransport

Finite scale transport for fractal/operator inductive systems.

This file separates two finite-stage mechanisms:

* immutable readouts: quantities unchanged by one zoom/bonding step;
* scale cocycles: quantities whose change is additive at each step.

It also proves normalized log-determinant stability under doubling:

  logdet_{n+1} = 2 logdet_n,
  dim_{n+1}    = 2 dim_n

implies

  logdet_n / dim_n

is independent of depth.

No colimit.
No completion.
No Type III theorem.
No analytic continuation.
No Virasoro-origin theorem.
-/

namespace InfoGeometry.Algebra.FractalScaleTransport

open Finset

/-- Iterate a finite scale/zoom/bonding step. -/
def iter {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (iter step n x)

@[simp]
theorem iter_zero {X : Type*} (step : X → X) (x : X) :
    iter step 0 x = x := rfl

@[simp]
theorem iter_succ {X : Type*} (step : X → X) (n : Nat) (x : X) :
    iter step (n + 1) x = step (iter step n x) := rfl

/--
If a readout is invariant under one zoom step, it is invariant under every
finite number of zoom steps.
-/
theorem invariant_iter
    {X Y : Type*}
    (step : X → X)
    (I : X → Y)
    (hI : ∀ x : X, I (step x) = I x) :
    ∀ n : Nat, ∀ x : X, I (iter step n x) = I x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      calc
        I (iter step (n + 1) x)
            = I (step (iter step n x)) := rfl
        _ = I (iter step n x) := hI _
        _ = I x := ih x

/--
A potential with one-step additive scale defect has a finite telescoping law.

This is the finite algebraic form of a renormalization cocycle:
`F(step x) = F x + c x`.
-/
theorem potential_iter_eq_sum_cocycle
    {X A : Type*} [AddCommMonoid A]
    (step : X → X)
    (F : X → A)
    (c : X → A)
    (hF : ∀ x : X, F (step x) = F x + c x) :
    ∀ n : Nat, ∀ x : X,
      F (iter step n x) =
        F x + ∑ k ∈ range n, c (iter step k x) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [iter]
  | succ n ih =>
      intro x
      calc
        F (iter step (n + 1) x)
            = F (step (iter step n x)) := rfl
        _ = F (iter step n x) + c (iter step n x) := hF _
        _ =
          (F x + ∑ k ∈ range n, c (iter step k x)) +
            c (iter step n x) := by
              rw [ih x]
        _ =
          F x + ∑ k ∈ range (n + 1), c (iter step k x) := by
              rw [sum_range_succ]
              ac_rfl

/--
If the scale cocycle is identically zero, the potential is an invariant.
-/
theorem potential_iter_eq_of_zero_cocycle
    {X A : Type*} [AddCommMonoid A]
    (step : X → X)
    (F : X → A)
    (c : X → A)
    (hF : ∀ x : X, F (step x) = F x + c x)
    (hc : ∀ x : X, c x = 0) :
    ∀ n : Nat, ∀ x : X, F (iter step n x) = F x := by
  intro n x
  rw [potential_iter_eq_sum_cocycle step F c hF n x]
  simp [hc]

/--
A Cayley/Möbius/time-reversal style conjugated step preserves an invariant
when the readout is invariant under both the original step and the involution.

The conjugated step is:

  `x ↦ inv (step (inv x))`.
-/
theorem invariant_conjugated_step
    {X Y : Type*}
    (step inv : X → X)
    (I : X → Y)
    (hStep : ∀ x : X, I (step x) = I x)
    (hInv : ∀ x : X, I (inv x) = I x)
    (x : X) :
    I (inv (step (inv x))) = I x := by
  rw [hInv (step (inv x))]
  rw [hStep (inv x)]
  rw [hInv x]

/--
The conjugated scale step preserves the invariant at every finite depth.
-/
theorem invariant_iter_conjugated_step
    {X Y : Type*}
    (step inv : X → X)
    (I : X → Y)
    (hStep : ∀ x : X, I (step x) = I x)
    (hInv : ∀ x : X, I (inv x) = I x) :
    ∀ n : Nat, ∀ x : X,
      I (iter (fun x => inv (step (inv x))) n x) = I x :=
  invariant_iter
    (fun x => inv (step (inv x)))
    I
    (invariant_conjugated_step step inv I hStep hInv)

/--
A potential with additive scale defect under `step` transforms under the
conjugated step by the defect evaluated at the inverted point.
-/
theorem potential_conjugated_step
    {X A : Type*} [AddCommMonoid A]
    (step inv : X → X)
    (F : X → A)
    (c : X → A)
    (hStep : ∀ x : X, F (step x) = F x + c x)
    (hInv : ∀ x : X, F (inv x) = F x)
    (x : X) :
    F (inv (step (inv x))) = F x + c (inv x) := by
  rw [hInv (step (inv x))]
  rw [hStep (inv x)]
  rw [hInv x]

/--
If the cocycle is also invariant under the inversion, the conjugated step has
the same additive defect.
-/
theorem potential_conjugated_step_same_cocycle
    {X A : Type*} [AddCommMonoid A]
    (step inv : X → X)
    (F : X → A)
    (c : X → A)
    (hStep : ∀ x : X, F (step x) = F x + c x)
    (hInv : ∀ x : X, F (inv x) = F x)
    (hcInv : ∀ x : X, c (inv x) = c x)
    (x : X) :
    F (inv (step (inv x))) = F x + c x := by
  rw [potential_conjugated_step step inv F c hStep hInv x]
  rw [hcInv x]

/-! ## Normalized log-determinant stability under doubling -/

/--
One-step normalized log-determinant stability.

If the raw log-determinant doubles and the stage dimension doubles, then the
normalized log-determinant is unchanged.
-/
theorem normalizedLogDet_doubling
    (logdet logdetNext dim : ℝ)
    (hdim : dim ≠ 0)
    (hlog : logdetNext = 2 * logdet) :
    logdetNext / (2 * dim) = logdet / dim := by
  subst logdetNext
  have h2dim : (2 : ℝ) * dim ≠ 0 := by
    exact mul_ne_zero (by norm_num) hdim
  field_simp [hdim, h2dim]
  try ring

/--
Finite-depth normalized log-determinant invariant.

If

  `logdet (n+1) = 2 * logdet n`
  `dim    (n+1) = 2 * dim n`

and all dimensions are nonzero, then

  `logdet n / dim n`

is independent of the depth `n`.
-/
theorem normalizedLogDet_iter
    (logdet dim : Nat → ℝ)
    (hlog : ∀ n : Nat, logdet (n + 1) = 2 * logdet n)
    (hdim : ∀ n : Nat, dim (n + 1) = 2 * dim n)
    (hnez : ∀ n : Nat, dim n ≠ 0) :
    ∀ n : Nat, logdet n / dim n = logdet 0 / dim 0 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        logdet (n + 1) / dim (n + 1)
            = (2 * logdet n) / (2 * dim n) := by
              rw [hlog n, hdim n]
        _ = logdet n / dim n := by
              have h2dim : (2 : ℝ) * dim n ≠ 0 := by
                exact mul_ne_zero (by norm_num) (hnez n)
              field_simp [hnez n, h2dim]
              try ring
        _ = logdet 0 / dim 0 := ih

end InfoGeometry.Algebra.FractalScaleTransport
