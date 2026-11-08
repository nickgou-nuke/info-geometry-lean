/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.SupercolorTripotentParity
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors
import InfoGeometry.Algebra.GrassmannianCartanTower
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral
import InfoGeometry.Canonical.RegularSupportSecondLaw

/-!
# Fréchet transport of the supercolor Grassmannian cut

The supercolor tetraktys constructs an idempotent zero-color cut. A continuous
Fréchet derivation differentiates that cut into a genuine Grassmannian tangent,
and its exponential flow preserves the idempotent cut. This is an algebraic
operator statement; it does not assert a Krein/Clifford realization or a
Maurer--Cartan identification. Its Erlangen reading is that the geometric
carrier is the operator algebra together with its distinguished Peirce data
and symmetry actions. Here `ℝ` is the central linearity base, while
operator-valued forms retain coefficients in the generally noncommutative
operator ring. A Cartan subalgebra is not assumed central in that ring; any
larger scalar base must be supplied by a central algebra action. Modular
automorphisms transport operators and forms, and fix individual observables
only when an additional invariance hypothesis is proved.
-/

namespace InfoGeometry.Synthesis.SupercolorFrechetGrassmannianBridge

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Physics.Algebra

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A]
variable {ι : Type*} {d b : ι → A}

omit [CompleteSpace A] in
/-- The zero-color cut built from two distinct supercolors is idempotent. -/
theorem supercolor_zeroCut_idempotent
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j) :
    (1 - colorBoson d b i i - colorBoson d b j j) *
        (1 - colorBoson d b i i - colorBoson d b j j) =
      1 - colorBoson d b i i - colorBoson d b j j := by
  let T := colorTripotent (colorBoson d b i i) (colorBoson d b j j)
  have hT : T * T * T = T := by
    simpa [T] using supercolor_colorTripotent_tripotent hS hij
  rw [← supercolor_projZero_colorTripotent hS hij]
  exact projZero_idempotent hT

omit [CompleteSpace A] in
/-- A Fréchet--Leibniz variation of the supercolor zero-cut is tangent to the
algebraic Grassmannian at that cut. -/
theorem supercolor_zeroCut_frechet_derivative_tangent
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j)
    (D : FrechetOperatorDerivation ℝ A) :
    IsGrassmannianTangent
      (1 - colorBoson d b i i - colorBoson d b j j)
      (D.toContinuousLinearMap
        (1 - colorBoson d b i i - colorBoson d b j j)) := by
  let p : A := 1 - colorBoson d b i i - colorBoson d b j j
  have hp : p * p = p := by
    simpa [p] using supercolor_zeroCut_idempotent hS hij
  unfold IsGrassmannianTangent InfoGeometry.Core.SuperGrassmannianSusy.jordanProd
  change p * D.toContinuousLinearMap p +
      D.toContinuousLinearMap p * p = D.toContinuousLinearMap p
  calc
    p * D.toContinuousLinearMap p + D.toContinuousLinearMap p * p =
        D.toContinuousLinearMap p * p + p * D.toContinuousLinearMap p := by
          exact add_comm _ _
    _ = D.toContinuousLinearMap (p * p) :=
      (D.leibniz p p).symm
    _ = D.toContinuousLinearMap p :=
      congrArg D.toContinuousLinearMap hp

omit [CompleteSpace A] in
/-- The Fréchet variation of the supercolor zero-cut is exactly its odd
five-grade component: the two grade `-1` and `+1` corners, with no even-grade
contribution. -/
theorem supercolor_zeroCut_frechet_derivative_eq_oddGrades
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j)
    (D : FrechetOperatorDerivation ℝ A) :
    gradeNegOneProjector (colorTripotent (colorBoson d b i i) (colorBoson d b j j))
        (D.toContinuousLinearMap (1 - colorBoson d b i i - colorBoson d b j j)) +
      gradePosOneProjector (colorTripotent (colorBoson d b i i) (colorBoson d b j j))
        (D.toContinuousLinearMap (1 - colorBoson d b i i - colorBoson d b j j)) =
      D.toContinuousLinearMap (1 - colorBoson d b i i - colorBoson d b j j) := by
  have ht := supercolor_zeroCut_frechet_derivative_tangent hS hij D
  have hcut := supercolor_projZero_colorTripotent hS hij
  rw [← hcut] at ht
  have hodd := (isGrassmannianTangent_iff_oddGrades_fixed
    (supercolor_colorTripotent_tripotent hS hij)
    (D.toContinuousLinearMap
      (projZero (colorTripotent (colorBoson d b i i) (colorBoson d b j j))))).mp ht
  simpa only [hcut] using hodd

/-- The intrinsic operator-valued two-form associated to the odd Peirce
grades. Its directions are operators in `A`, and its values remain in the
noncommutative ring `A`; only the multilinear structure uses the central real
algebra structure. -/
noncomputable def oddPeirceOperatorTwoForm (T : A) :
    InfoGeometry.OperatorAlgebra.General.OpForm ℝ A A 2 := by
  classical
  let minus := gradeNegOneProjector T
  let plus := gradePosOneProjector T
  let f : MultilinearMap ℝ (fun _ : Fin 2 => A) A :=
    { toFun := fun v => minus (v 0) * plus (v 1) - minus (v 1) * plus (v 0)
      map_update_add' := by
        intro _dec v i x y
        fin_cases i <;> simp [Function.update, minus, plus,
          LinearMap.map_add, sub_eq_add_neg, add_mul, mul_add] <;> abel
      map_update_smul' := by
        intro _dec v i r x
        fin_cases i <;> simp [Function.update, minus, plus,
          Algebra.smul_mul_assoc, smul_sub] }
  exact AlternatingMap.mk f (by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have hv : v 0 = v 1 := by simpa using hij
      simp [f, hv]
    · have hv : v 1 = v 0 := by simpa using hij
      simp [f, hv]
    · exact (hne rfl).elim)

omit [CompleteSpace A] [StarRing A] in
/-- Evaluating the operator-valued form gives the ordered odd-grade
commutator pairing, with no passage to a scalar-valued exterior carrier. -/
@[simp] theorem oddPeirceOperatorTwoForm_apply (T : A)
    (v : Fin 2 → A) :
    oddPeirceOperatorTwoForm T v =
      gradeNegOneProjector T (v 0) * gradePosOneProjector T (v 1) -
        gradeNegOneProjector T (v 1) * gradePosOneProjector T (v 0) := by
  rfl

omit [CompleteSpace A] [StarRing A] in
/-- An `ℝ`-algebra automorphism commutes with each polynomial Peirce
projector attached to an element. -/
theorem algebraEquiv_peirceProjector (e : A ≃ₐ[ℝ] A) (T : A)
    (s : InfoGeometry.Physics.Algebra.PeirceSign) :
    e (InfoGeometry.Physics.Algebra.peirceProjector T s) =
      InfoGeometry.Physics.Algebra.peirceProjector (e T) s := by
  cases s <;>
    simp [InfoGeometry.Physics.Algebra.peirceProjector,
      InfoGeometry.Physics.Algebra.projPos,
      InfoGeometry.Physics.Algebra.projZero,
      InfoGeometry.Physics.Algebra.projNeg, map_smul, map_mul, map_sub]

omit [CompleteSpace A] [StarRing A] in
/-- Joint left-right Peirce components are natural under real algebra
automorphisms. -/
theorem algebraEquiv_jointPeirceProjector (e : A ≃ₐ[ℝ] A) (T x : A)
    (left right : InfoGeometry.Physics.Algebra.PeirceSign) :
    e (InfoGeometry.Physics.Algebra.jointPeirceProjector T left right x) =
      InfoGeometry.Physics.Algebra.jointPeirceProjector (e T) left right (e x) := by
  rw [InfoGeometry.Physics.Algebra.jointPeirceProjector_apply,
    InfoGeometry.Physics.Algebra.jointPeirceProjector_apply,
    map_mul, map_mul,
    algebraEquiv_peirceProjector e T left,
    algebraEquiv_peirceProjector e T right]

omit [CompleteSpace A] [StarRing A] in
/-- Both odd five-grade projectors intertwine with the same algebra
automorphism, since they are sums of joint Peirce components. -/
theorem algebraEquiv_oddGradeProjectors (e : A ≃ₐ[ℝ] A) (T x : A) :
    e (gradeNegOneProjector T x) = gradeNegOneProjector (e T) (e x) ∧
      e (gradePosOneProjector T x) = gradePosOneProjector (e T) (e x) := by
  constructor
  · change e (InfoGeometry.Physics.Algebra.jointPeirceProjector T .zero .pos x +
        InfoGeometry.Physics.Algebra.jointPeirceProjector T .neg .zero x) =
      InfoGeometry.Physics.Algebra.jointPeirceProjector (e T) .zero .pos (e x) +
        InfoGeometry.Physics.Algebra.jointPeirceProjector (e T) .neg .zero (e x)
    rw [map_add, algebraEquiv_jointPeirceProjector,
      algebraEquiv_jointPeirceProjector]
  · change e (InfoGeometry.Physics.Algebra.jointPeirceProjector T .pos .zero x +
        InfoGeometry.Physics.Algebra.jointPeirceProjector T .zero .neg x) =
      InfoGeometry.Physics.Algebra.jointPeirceProjector (e T) .pos .zero (e x) +
        InfoGeometry.Physics.Algebra.jointPeirceProjector (e T) .zero .neg (e x)
    rw [map_add, algebraEquiv_jointPeirceProjector,
      algebraEquiv_jointPeirceProjector]

omit [CompleteSpace A] [StarRing A] in
/-- The odd-grade operator two-form is equivariant under every real algebra
automorphism. It transports the graded geometry without asserting the form is
fixed. -/
theorem oddPeirceOperatorTwoForm_equivariant (e : A ≃ₐ[ℝ] A) (T : A) :
    InfoGeometry.OperatorAlgebra.General.mapN 2 e.toAlgHom
      (InfoGeometry.OperatorAlgebra.General.pullbackN 2 e.symm.toLinearMap
        (oddPeirceOperatorTwoForm T)) =
      oddPeirceOperatorTwoForm (e T) := by
  ext v
  have h0 := algebraEquiv_oddGradeProjectors e T (e.symm (v 0))
  have h1 := algebraEquiv_oddGradeProjectors e T (e.symm (v 1))
  have hm0 : e (gradeNegOneProjector T (e.symm (v 0))) =
      gradeNegOneProjector (e T) (v 0) := by simpa using h0.1
  have hm1 : e (gradeNegOneProjector T (e.symm (v 1))) =
      gradeNegOneProjector (e T) (v 1) := by simpa using h1.1
  have hp0 : e (gradePosOneProjector T (e.symm (v 0))) =
      gradePosOneProjector (e T) (v 0) := by simpa using h0.2
  have hp1 : e (gradePosOneProjector T (e.symm (v 1))) =
      gradePosOneProjector (e T) (v 1) := by simpa using h1.2
  change e (oddPeirceOperatorTwoForm T (fun k => e.symm (v k))) =
    oddPeirceOperatorTwoForm (e T) v
  simp only [oddPeirceOperatorTwoForm_apply, map_sub, map_mul,
    hm0, hm1, hp0, hp1]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [StarRing A] in
/-- Integer-coefficient polynomial evaluation is natural under every ring
automorphism of the operator carrier. This is the reusable algebraic
invariance law behind nilpotence, idempotence, and cyclotomic constraints. -/
theorem ringEquiv_map_integerPolynomial_aeval (e : A ≃+* A)
    (p : Polynomial ℤ) (x : A) :
    e (Polynomial.aeval x p) = Polynomial.aeval (e x) p := by
  have hbase : (algebraMap ℤ A).comp (RingHom.id ℤ) =
      e.toRingHom.comp (algebraMap ℤ A) := by
    ext z
    simp
  simpa using Polynomial.map_aeval_eq_aeval_map hbase p x

omit [NormedAlgebra ℝ A] [CompleteSpace A] [StarRing A] in
/-- Polynomial root equations with integer coefficients are preserved and
reflected by the modular/Erlangen ring action. In particular, this applies to
the integer cyclotomic polynomial `Φ₆(X) = X² - X + 1`. -/
theorem ringEquiv_preserves_integerPolynomial_root (e : A ≃+* A)
    (p : Polynomial ℤ) (x : A) :
    Polynomial.aeval x p = 0 ↔ Polynomial.aeval (e x) p = 0 := by
  have heval := ringEquiv_map_integerPolynomial_aeval e p x
  constructor
  · intro hx
    rw [← heval, hx, map_zero]
  · intro hx
    apply e.injective
    rw [heval, hx, map_zero]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [StarRing A] in
/-- Nilpotence of any finite order is invariant along a modular/Erlangen
ring automorphism orbit. -/
theorem ringEquiv_preserves_nilpotence (e : A ≃+* A) (x : A) (n : ℕ) :
    x ^ n = 0 ↔ (e x) ^ n = 0 := by
  constructor
  · intro hx
    rw [← e.map_pow, hx, map_zero]
  · intro hx
    apply e.injective
    rw [map_pow, hx, map_zero]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [StarRing A] in
/-- Idempotence is invariant along a modular/Erlangen ring automorphism
orbit. -/
theorem ringEquiv_preserves_idempotence (e : A ≃+* A) (x : A) :
    x * x = x ↔ e x * e x = e x := by
  constructor
  · intro hx
    simpa only [map_mul] using congrArg e hx
  · intro hx
    apply e.injective
    simpa only [map_mul] using hx

omit [CompleteSpace A] in
/-- The Fréchet variation of the supercolor cut is the sum of its two
off-diagonal Peirce corners. -/
theorem supercolor_zeroCut_frechet_derivative_offDiagonal
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j)
    (D : FrechetOperatorDerivation ℝ A) :
    D.toContinuousLinearMap
        (1 - colorBoson d b i i - colorBoson d b j j) =
      (1 - colorBoson d b i i - colorBoson d b j j) *
          D.toContinuousLinearMap
            (1 - colorBoson d b i i - colorBoson d b j j) *
          (1 - (1 - colorBoson d b i i - colorBoson d b j j)) +
        (1 - (1 - colorBoson d b i i - colorBoson d b j j)) *
          D.toContinuousLinearMap
            (1 - colorBoson d b i i - colorBoson d b j j) *
          (1 - colorBoson d b i i - colorBoson d b j j) := by
  let p : A := 1 - colorBoson d b i i - colorBoson d b j j
  have hp : p * p = p := by
    simpa [p] using supercolor_zeroCut_idempotent hS hij
  simpa [p] using
    FrechetOperatorDerivation.map_idempotent_is_offDiagonal D hp

/-- The continuous Fréchet derivation flow transports the supercolor cut to
another idempotent at every real time. -/
theorem supercolor_zeroCut_flow_preserves_idempotent
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j)
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t
        (1 - colorBoson d b i i - colorBoson d b j j) *
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t
        (1 - colorBoson d b i i - colorBoson d b j j) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t
        (1 - colorBoson d b i i - colorBoson d b j j) := by
  let p : A := 1 - colorBoson d b i i - colorBoson d b j j
  have hp : p * p = p := by
    simpa [p] using supercolor_zeroCut_idempotent hS hij
  simpa [p] using FrechetOperatorDerivation.flow_preserves_idempotent D t hp

/-- Derivation flow transports the supercolor tetraktys curvature through its
Peirce corners, connecting the color and Chevalley--Eilenberg lanes. -/
theorem supercolor_tetraktys_CE_curvature_flow
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j)
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t
        (InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (colorBoson d b i j) (colorBoson d b j i)) =
      InfoGeometry.NCG.DerivationDifferential.curvature
        InfoGeometry.NCG.DerivationDifferential.innerSystem
        (fun x : A => x)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t (colorBoson d b i i))
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t (colorBoson d b i j)))
        (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t (colorBoson d b i i))
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t (colorBoson d b j i))) := by
  have hcorners :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.supercolor_tetraktys_corners hS hij
  have hcurvature :
      InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x) (colorBoson d b i j) (colorBoson d b j i) =
        InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
            (colorBoson d b i i) (colorBoson d b i j))
          (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
            (colorBoson d b i i) (colorBoson d b j i)) := by
    calc
      _ = InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
            (colorBoson d b i i) (colorBoson d b i j))
          (colorBoson d b j i) := by rw [hcorners.1]
      _ = _ := by rw [hcorners.2]
  rw [hcurvature]
  exact FrechetOperatorDerivation.flow_transports_peirce_tetraktys_CE_curvature
    D t (colorBoson d b i i) (colorBoson d b i j) (colorBoson d b j i)

end

end InfoGeometry.Synthesis.SupercolorFrechetGrassmannianBridge
