import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.NonAssocDerivation
import Mathlib.Algebra.Jordan.Basic

/-!
# Inner derivations on the real split Albert algebra

Baez's description of the compact real `𝔣₄` identifies it with the derivation
algebra of the exceptional Jordan algebra `h₃(𝕆)`.  The carrier used here is
instead the real *split* Albert algebra `H3Zorn ℝ`; consequently this module
formalizes the universal Jordan-algebra derivation mechanism and its split-real
specialization, not an identification with the compact real form.

For any linear commutative Jordan algebra in which `2` is invertible, the
commutator `[L_a,L_b]` of left multiplication operators satisfies the Leibniz
rule.  Thus these operators are genuine elements of the native derivation Lie
subalgebra.  The proof uses Mathlib's fully linearized Jordan identity.
-/

namespace InfoGeometry.Algebra

section Operators

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocCommRing A] [Module R A]
  [SMulCommClass R A A]

/-- Left Jordan multiplication as an `R`-linear endomorphism. -/
def jordanLmul (a : A) : Module.End R A where
  toFun x := a * x
  map_add' x y := mul_add a x y
  map_smul' r x := mul_smul_comm r a x

@[simp] theorem jordanLmul_apply (a x : A) :
    jordanLmul (R := R) a x = a * x := rfl

/-- The commutator of two left Jordan multiplication operators. -/
def jordanInnerDerivation (a b : A) : Module.End R A :=
  ⁅jordanLmul (R := R) a, jordanLmul (R := R) b⁆

@[simp] theorem jordanInnerDerivation_apply (a b x : A) :
    jordanInnerDerivation (R := R) a b x = a * (b * x) - b * (a * x) := by
  rfl

/-- A Leibniz derivation acts on the left-multiplication sector by the
adjoint representation: `[D,L_a] = L_{D a}`. -/
theorem lie_derivation_jordanLmul
    (D : Module.End R A)
    (hD : NonAssocDerivation.IsLeibniz R A D)
    (a : A) :
    ⁅D, jordanLmul (R := R) a⁆ = jordanLmul (R := R) (D a) := by
  ext x
  simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
    jordanLmul_apply]
  rw [hD a x]
  abel

end Operators

section Jordan

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocCommRing A] [Module R A]
  [SMulCommClass R A A]

/-- In a commutative Jordan algebra in which two is invertible, commutators of
left multiplication operators obey the Leibniz rule. -/
theorem jordanInnerDerivation_isLeibniz
    [IsCommJordan A] [Invertible (2 : R)] (a b : A) :
    NonAssocDerivation.IsLeibniz R A (jordanInnerDerivation (R := R) a b) := by
  intro x y
  have h₁raw := congrArg (fun f : AddMonoid.End A => f b)
    (two_nsmul_lie_lmul_lmul_add_add_eq_zero a x y)
  have h₂raw := congrArg (fun f : AddMonoid.End A => f a)
    (two_nsmul_lie_lmul_lmul_add_add_eq_zero b x y)
  have h₁ : 2 • (a * ((x * y) * b) - (x * y) * (a * b) +
      (x * ((y * a) * b) - (y * a) * (x * b)) +
      (y * ((a * x) * b) - (a * x) * (y * b))) = 0 := by
    simpa [Ring.lie_def] using h₁raw
  have h₂ : 2 • (b * ((x * y) * a) - (x * y) * (b * a) +
      (x * ((y * b) * a) - (y * b) * (x * a)) +
      (y * ((b * x) * a) - (b * x) * (y * a))) = 0 := by
    simpa [Ring.lie_def] using h₂raw
  have h : 2 •
      (jordanInnerDerivation (R := R) a b (x * y) -
        (jordanInnerDerivation (R := R) a b x * y +
          x * jordanInnerDerivation (R := R) a b y)) = 0 := by
    simp only [jordanInnerDerivation_apply, two_nsmul]
    simp only [two_nsmul] at h₁ h₂
    rw [mul_comm (x * y) b, mul_comm (y * a) b, mul_comm (a * x) b,
      mul_comm (y * a) (x * b), mul_comm (a * x) (y * b)] at h₁
    rw [mul_comm (x * y) a, mul_comm b a, mul_comm (y * b) a,
      mul_comm (b * x) a, mul_comm (y * b) (x * a),
      mul_comm (b * x) (y * a)] at h₂
    have heq0 := sub_eq_zero.mpr (h₁.trans h₂.symm)
    simp only [sub_mul, mul_sub]
    simp only [mul_comm] at heq0 ⊢
    abel_nf at heq0 ⊢
    exact heq0
  rw [← Nat.cast_smul_eq_nsmul R] at h
  have hz : jordanInnerDerivation (R := R) a b (x * y) -
        (jordanInnerDerivation (R := R) a b x * y +
          x * jordanInnerDerivation (R := R) a b y) = 0 :=
    (isUnit_of_invertible (2 : R)).smul_left_cancel.mp (by simpa using h)
  exact sub_eq_zero.mp hz

/-- The bundled inner derivation associated to two elements of a linear
commutative Jordan algebra. -/
def jordanInnerDerivationBundled
    [IsScalarTower R A A] [IsCommJordan A] [Invertible (2 : R)] (a b : A) :
    NonAssocDerivation.derivations R A :=
  ⟨jordanInnerDerivation (R := R) a b,
    jordanInnerDerivation_isLeibniz (R := R) a b⟩

end Jordan

section SplitAlbert

open H3Zorn

/-- Scalar multiplication associates with the verified real split-Albert
Jordan product. -/
noncomputable instance h3ZornJordanIsScalarTower :
    IsScalarTower ℝ (H3Zorn ℝ) (H3Zorn ℝ) where
  smul_assoc r X Y := by
    change candidateJordanMul (r • X) Y = r • candidateJordanMul X Y
    exact candidateJordanMul_smul_left r X Y

/-- Real scalars commute across the verified split-Albert Jordan product. -/
noncomputable instance h3ZornJordanSMulCommClass :
    SMulCommClass ℝ (H3Zorn ℝ) (H3Zorn ℝ) where
  smul_comm r X Y := by
    change r • (X * Y) = X * (r • Y)
    rw [← candidateJordanMul_eq_mul X Y,
      ← candidateJordanMul_eq_mul X (r • Y), candidateJordanMul_smul_right]

/-- The native inner Jordan derivation `[L_a,L_b]` of the real split Albert
algebra, bundled in its derivation Lie subalgebra. -/
noncomputable def h3ZornJordanInnerDerivation (a b : H3Zorn ℝ) :
    NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
  jordanInnerDerivationBundled (R := ℝ) a b

@[simp] theorem h3ZornJordanInnerDerivation_apply
    (a b x : H3Zorn ℝ) :
    (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x =
      a * (b * x) - b * (a * x) := by
  rfl

/-- The split-Albert inner derivation satisfies the ordinary Leibniz rule. -/
theorem h3ZornJordanInnerDerivation_leibniz
    (a b x y : H3Zorn ℝ) :
    (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) (x * y) =
      (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x * y +
        x * (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) y :=
  (h3ZornJordanInnerDerivation a b).property x y

/-- On the verified split Albert carrier, every native Jordan derivation sends
left multiplication by `a` to left multiplication by `D a` under the Lie bracket. -/
theorem h3Zorn_derivation_lie_jordanLmul
    (D : NonAssocDerivation.derivations ℝ (H3Zorn ℝ))
    (a : H3Zorn ℝ) :
    ⁅(D : Module.End ℝ (H3Zorn ℝ)), jordanLmul (R := ℝ) a⁆ =
      jordanLmul (R := ℝ) (D a) :=
  lie_derivation_jordanLmul (R := ℝ) D D.property a

end SplitAlbert

end InfoGeometry.Algebra
