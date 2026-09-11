import InfoGeometry.Clifford.ClNN
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

open scoped TensorProduct

/-!
# Split bilinear forms for the recursive `Cl(n,n)` tower

This file adds the bilinear-form readback for the existing split Clifford
tower:

* `Qsplit 1` is the split `Cl(1,1)` quadratic seed;
* `Qsplit (n+1) = Q11.prod (Qsplit n)` is the recursive `Cl(n,n)` carrier;
* `Bsplit n` is the corresponding split bilinear form;
* the Clifford anticommutator reads back to the bilinear form.

No witness packet is introduced here.  Every law is a theorem from the explicit
recursive definitions and mathlib's Clifford-algebra relations.
-/

namespace InfoGeometry.Clifford.ClNNBilinear

open InfoGeometry.Clifford
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN

/-- Hyperbolic split carrier alias: `n` copies of the split plane. -/
@[rep_depth krein] abbrev HyperbolicSpace (n : ℕ) := SplitSpace n

/-- Hyperbolic split quadratic form of signature `(n,n)`. -/
@[rep_depth krein] noncomputable abbrev hyperbolicQuadratic (n : ℕ) :
    QuadraticForm ℝ (HyperbolicSpace n) :=
  Qsplit n

/-- Recursive split bilinear form corresponding to `Qsplit`. -/
@[rep_depth krein]
noncomputable def Bsplit : (n : ℕ) → SplitSpace n →ₗ[ℝ] SplitSpace n →ₗ[ℝ] ℝ
  | 0 => 0
  | n + 1 =>
      letI : AddCommGroup (SplitSpace n) := splitSpaceAddCommGroup n
      letI : Module ℝ (SplitSpace n) := splitSpaceModule n
      {
        toFun := fun x =>
          {
            toFun := fun y => splitB11 x.1 y.1 + Bsplit n x.2 y.2
            map_add' := by
              intro y z
              change splitB11 x.1 (y.1 + z.1) + Bsplit n x.2 (y.2 + z.2)
                = (splitB11 x.1 y.1 + Bsplit n x.2 y.2)
                  + (splitB11 x.1 z.1 + Bsplit n x.2 z.2)
              rw [map_add]
              rw [map_add]
              simp
              ring
            map_smul' := by
              intro r y
              change splitB11 x.1 (r • y.1) + Bsplit n x.2 (r • y.2)
                = r • (splitB11 x.1 y.1 + Bsplit n x.2 y.2)
              rw [map_smul]
              rw [map_smul]
              simp
              ring
          }
        map_add' := by
          intro x y
          apply LinearMap.ext
          intro z
          change splitB11 (x.1 + y.1) z.1 + Bsplit n (x.2 + y.2) z.2
            = (splitB11 x.1 z.1 + Bsplit n x.2 z.2)
              + (splitB11 y.1 z.1 + Bsplit n y.2 z.2)
          rw [map_add]
          rw [map_add]
          simp
          ring
        map_smul' := by
          intro r x
          apply LinearMap.ext
          intro z
          change splitB11 (r • x.1) z.1 + Bsplit n (r • x.2) z.2
            = r • (splitB11 x.1 z.1 + Bsplit n x.2 z.2)
          rw [map_smul]
          rw [map_smul]
          simp
          ring
      }

@[rep_depth krein, simp] theorem Bsplit_zero_apply
    (x y : SplitSpace 0) :
    Bsplit 0 x y = 0 := by
  rfl

@[rep_depth krein, simp] theorem Bsplit_succ_apply
    (n : ℕ) (x y : ℝ × ℝ) (xs ys : SplitSpace n) :
    Bsplit (n + 1) (x, xs) (y, ys) = splitB11 x y + Bsplit n xs ys := by
  rfl

/-- Hyperbolic split bilinear form of signature `(n,n)`. -/
@[rep_depth krein] noncomputable abbrev hyperbolicBilinear (n : ℕ) :
    HyperbolicSpace n →ₗ[ℝ] HyperbolicSpace n →ₗ[ℝ] ℝ :=
  Bsplit n

@[rep_depth krein, simp] theorem hyperbolicQuadratic_zero_apply
    (x : HyperbolicSpace 0) :
    hyperbolicQuadratic 0 x = 0 := by
  exact Qsplit_zero_apply x

@[rep_depth krein, simp] theorem hyperbolicQuadratic_succ_apply
    (n : ℕ) (x : ℝ × ℝ) (xs : HyperbolicSpace n) :
    hyperbolicQuadratic (n + 1) (x, xs)
      = splitQ11 x + hyperbolicQuadratic n xs := by
  simp [hyperbolicQuadratic, Q11]

@[rep_depth krein, simp] theorem hyperbolicBilinear_succ_apply
    (n : ℕ) (x y : ℝ × ℝ) (xs ys : HyperbolicSpace n) :
    hyperbolicBilinear (n + 1) (x, xs) (y, ys)
      = splitB11 x y + hyperbolicBilinear n xs ys := by
  rfl

/-- `Bsplit` is symmetric. -/
@[rep_depth krein]
theorem Bsplit_symm
    (n : ℕ) (x y : SplitSpace n) :
    Bsplit n x y = Bsplit n y x := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rcases x with ⟨x, xs⟩
      rcases y with ⟨y, ys⟩
      simp [Bsplit_succ_apply, ih xs ys]
      ring

/-- The recursive quadratic form is the diagonal of the recursive bilinear form. -/
@[rep_depth krein]
theorem Qsplit_eq_Bsplit_diag
    (n : ℕ) (x : SplitSpace n) :
    Qsplit n x = Bsplit n x x := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rcases x with ⟨x, xs⟩
      simp [Qsplit_succ_apply, Bsplit_succ_apply, ih xs, Q11]

/-- The hyperbolic quadratic form is the diagonal of the hyperbolic bilinear form. -/
@[rep_depth krein]
theorem hyperbolicQuadratic_eq_hyperbolicBilinear_diag
    (n : ℕ) (x : HyperbolicSpace n) :
    hyperbolicQuadratic n x = hyperbolicBilinear n x x :=
  Qsplit_eq_Bsplit_diag n x

/-- The bilinear form polarizes `Qsplit` with mathlib's `QuadraticMap.polar`. -/
@[rep_depth krein]
theorem polar_Qsplit_eq_two_Bsplit
    (n : ℕ) (x y : SplitSpace n) :
    QuadraticMap.polar (Qsplit n) x y = 2 * Bsplit n x y := by
  induction n with
  | zero =>
      have hx : x = 0 := Subsingleton.elim _ _
      have hy : y = 0 := Subsingleton.elim _ _
      subst x
      subst y
      simp [QuadraticMap.polar, Qsplit, Bsplit]
  | succ n ih =>
      rcases x with ⟨x, xs⟩
      rcases y with ⟨y, ys⟩
      have htail :
          Qsplit n (xs + ys) - Qsplit n xs - Qsplit n ys = 2 * Bsplit n xs ys := by
        simpa [QuadraticMap.polar] using ih xs ys
      rw [QuadraticMap.polar]
      change
        Q11 (x + y) + Qsplit n (xs + ys) - (Q11 x + Qsplit n xs)
            - (Q11 y + Qsplit n ys)
          = 2 * (splitB11 x y + Bsplit n xs ys)
      have hhead : Q11 (x + y) - Q11 x - Q11 y = 2 * splitB11 x y := by
        simp [splitB11_apply]
        ring
      linarith

/-- Polarization of the hyperbolic quadratic form. -/
@[rep_depth krein]
theorem hyperbolic_polar_eq_two_bilinear
    (n : ℕ) (x y : HyperbolicSpace n) :
    QuadraticMap.polar (hyperbolicQuadratic n) x y
      = 2 * hyperbolicBilinear n x y :=
  polar_Qsplit_eq_two_Bsplit n x y

@[rep_depth krein, simp] theorem Bsplit_headPair_tailLift
    (n : ℕ) (x : ℝ × ℝ) (xs : SplitSpace n) :
    Bsplit (n + 1) (headPair n x) (tailLift n xs) = 0 := by
  simp [headPair, tailLift]

@[rep_depth krein, simp] theorem Bsplit_tailLift_headPair
    (n : ℕ) (xs : SplitSpace n) (x : ℝ × ℝ) :
    Bsplit (n + 1) (tailLift n xs) (headPair n x) = 0 := by
  rw [Bsplit_symm]
  exact Bsplit_headPair_tailLift n x xs

@[rep_depth krein, simp] theorem Bsplit_headPair_headPair
    (n : ℕ) (x y : ℝ × ℝ) :
    Bsplit (n + 1) (headPair n x) (headPair n y) = splitB11 x y := by
  simp [headPair]

@[rep_depth krein, simp] theorem Bsplit_tailLift_tailLift
    (n : ℕ) (xs ys : SplitSpace n) :
    Bsplit (n + 1) (tailLift n xs) (tailLift n ys) = Bsplit n xs ys := by
  simp [tailLift]

/--
The split `Cl(1,1)` head tensored with the split `Cl(n,n)` tail is the next
split tower stage `Cl(n+1,n+1)`.
-/
@[rep_depth krein]
noncomputable def cl11TensorClNNEquiv (n : ℕ) :
    CliffordAlgebra (Qsplit (n + 1))
      ≃ₐ[ℝ] (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) :=
  clsplit_succ_equiv n

/--
Clifford anticommutator readback: generators anticommute according to the split
bilinear form.
-/
@[rep_depth krein]
theorem clifford_ι_mul_ι_add_swap_eq_bilinear
    (n : ℕ) (x y : SplitSpace n) :
    CliffordAlgebra.ι (Qsplit n) x * CliffordAlgebra.ι (Qsplit n) y
      + CliffordAlgebra.ι (Qsplit n) y * CliffordAlgebra.ι (Qsplit n) x
        = algebraMap ℝ (CliffordAlgebra (Qsplit n)) (2 * Bsplit n x y) := by
  simpa [polar_Qsplit_eq_two_Bsplit] using
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := Qsplit n) x y)

@[rep_depth krein]
theorem clifford_head_tail_anticommute
    (n : ℕ) (x : ℝ × ℝ) (xs : SplitSpace n) :
    CliffordAlgebra.ι (Qsplit (n + 1)) (headPair n x)
        * CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n xs)
      + CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n xs)
        * CliffordAlgebra.ι (Qsplit (n + 1)) (headPair n x)
        = 0 := by
  simpa using
    (clifford_ι_mul_ι_add_swap_eq_bilinear (n + 1) (headPair n x) (tailLift n xs))

@[rep_depth krein, simp] theorem hyperbolic_headNullMinus_isotropic
    (n : ℕ) :
    hyperbolicQuadratic (n + 1) (headNullMinus n) = 0 := by
  exact headNullMinus_isotropic n

@[rep_depth krein, simp] theorem hyperbolic_headNullPlus_isotropic
    (n : ℕ) :
    hyperbolicQuadratic (n + 1) (headNullPlus n) = 0 := by
  exact headNullPlus_isotropic n

/-- The normalized null head vectors pair to `1/2` under the bilinear form. -/
@[rep_depth krein, simp] theorem hyperbolic_headNullMinus_headNullPlus_pairing
    (n : ℕ) :
    hyperbolicBilinear (n + 1) (headNullMinus n) (headNullPlus n) = 1 / 2 := by
  have hpolar := polar_Qsplit_eq_two_Bsplit (n + 1) (headNullMinus n) (headNullPlus n)
  rw [polar_headNullMinus_headNullPlus] at hpolar
  linarith

@[rep_depth krein, simp] theorem hyperbolic_headNullPlus_headNullMinus_pairing
    (n : ℕ) :
    hyperbolicBilinear (n + 1) (headNullPlus n) (headNullMinus n) = 1 / 2 := by
  rw [Bsplit_symm]
  exact hyperbolic_headNullMinus_headNullPlus_pairing n

/--
The head null CAR is the Clifford anticommutator readback of the hyperbolic
bilinear pairing.

This is the theorem-level bridge between the chiral causal-cone generators
`u_-`, `u_+` and the hyperbolic quadratic/bilinear form:

`u_- u_+ + u_+ u_- = 2 B(u_-,u_+) · 1`.
-/
@[rep_depth krein]
theorem gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap_eq_hyperbolic_pairing
    (n : ℕ) :
    gammaHeadNullMinus n * gammaHeadNullPlus n
      + gammaHeadNullPlus n * gammaHeadNullMinus n
        = algebraMap ℝ (Alg (n + 1))
            (2 * hyperbolicBilinear (n + 1) (headNullMinus n) (headNullPlus n)) := by
  simpa [gammaHeadNullMinus, gammaHeadNullPlus, hyperbolicBilinear] using
    (clifford_ι_mul_ι_add_swap_eq_bilinear
      (n + 1) (headNullMinus n) (headNullPlus n))

/--
The normalized head null generators satisfy the causal/chiral CAR
`u_- u_+ + u_+ u_- = 1`, derived from the hyperbolic bilinear pairing.
-/
@[rep_depth krein]
theorem gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap_from_hyperbolic_pairing
    (n : ℕ) :
    gammaHeadNullMinus n * gammaHeadNullPlus n
      + gammaHeadNullPlus n * gammaHeadNullMinus n = 1 := by
  rw [gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap_eq_hyperbolic_pairing]
  simp [hyperbolic_headNullMinus_headNullPlus_pairing]

end InfoGeometry.Clifford.ClNNBilinear
