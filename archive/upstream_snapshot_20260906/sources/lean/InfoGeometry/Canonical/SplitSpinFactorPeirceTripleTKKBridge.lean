import Mathlib
import InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
import InfoGeometry.Canonical.SplitSpinFactorTKKSO66

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorPeirceTripleTKKBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
open InfoGeometry.Canonical.SplitSpinFactorTKKSO66

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ
abbrev V10 := SplitSpacetime10

/-- The explicit Jordan product on the fixed-`e1` Peirce-zero block
`H2(O_s) = R^2 ⊕ O_s`.  This definition is independent of the ambient H3
product. -/
noncomputable def spinJordanMul (x y : V10) : V10 :=
  let p := zornPolar x.2 y.2
  (((x.1.1 * y.1.1 + (1 / 2 : ℝ) * p),
    (x.1.2 * y.1.2 + (1 / 2 : ℝ) * p)),
    (1 / 2 : ℝ) •
      ((x.1.1 + x.1.2) • y.2 + (y.1.1 + y.1.2) • x.2))

/-- The Peirce-zero embedding is an algebraic soldering for the explicit
spin-factor Jordan product. -/
theorem peirceZeroEmbed_spinJordanMul (x y : V10) :
    peirceZeroEmbed (spinJordanMul x y) =
      candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y) := by
  rcases x with ⟨⟨x2, x3⟩, xb⟩
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  rw [candidateJordanMul_trace_formula]
  apply H3Zorn.ext_h3
  all_goals
    simp [spinJordanMul, peirceZeroEmbed, zornPolar,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
      H3Zorn.one_readback,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.trace_add,
      ZornVectorMatrix.norm, ZornVectorMatrix.trace,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.add, ZornVectorMatrix.sub,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> try ring <;> try module

/-- The standard Jordan triple on the ten-dimensional spin factor. -/
noncomputable def spinJordanTriple (x y z : V10) : V10 :=
  spinJordanMul (spinJordanMul x y) z +
    spinJordanMul (spinJordanMul z y) x -
      spinJordanMul (spinJordanMul x z) y

/-- Restriction theorem: the ambient Albert triple of three Peirce-zero
vectors is again Peirce-zero, and its coordinate representative is exactly
the independently defined spin-factor triple. -/
theorem peirceZeroEmbed_spinJordanTriple (x y z : V10) :
    peirceZeroEmbed (spinJordanTriple x y z) =
      jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y)
        (peirceZeroEmbed z) := by
  apply H3Zorn.ext_h3
  all_goals
    simp [spinJordanTriple, jordanTriple, peirceZeroEmbed_spinJordanMul,
      peirceZeroEmbed, H3Zorn.add_readback, H3Zorn.sub_readback,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg]

/-- Ambient formulation of Peirce-zero triple closure. -/
theorem jordanTriple_preserves_peirceZero
    {x y z : H3} (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) := by
  rw [eq_peirceZeroEmbed_of_mem hx, eq_peirceZeroEmbed_of_mem hy,
    eq_peirceZeroEmbed_of_mem hz]
  let x0 : V10 := ((x.α₂, x.α₃), x.b)
  let y0 : V10 := ((y.α₂, y.α₃), y.b)
  let z0 : V10 := ((z.α₂, z.α₃), z.b)
  rw [← peirceZeroEmbed_spinJordanTriple x0 y0 z0]
  exact peirceZeroEmbed_mem _

/-- The spin-factor trace reversal / quadratic adjoint on the rank-two
Jordan algebra.  This is the identification of the Jordan dual middle slot
with `V10` used by the conformal `B10` realization. -/
def spinTraceReverse (y : V10) : V10 :=
  ((y.1.2, y.1.1), -y.2)

@[simp] theorem spinTraceReverse_involutive (y : V10) :
    spinTraceReverse (spinTraceReverse y) = y := by
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  simp [spinTraceReverse]

/-- The determinant-polar conformal triple. -/
def conformalSpinTriple (x y z : V10) : V10 :=
  B10 x y • z + B10 y z • x - B10 x z • y

/-- The restricted Jordan triple becomes the standard orthogonal conformal
triple after trace reversal in the middle Jordan slot. -/
theorem spinJordanTriple_traceReverse_eq_conformal
    (x y z : V10) :
    spinJordanTriple x (spinTraceReverse y) z =
      conformalSpinTriple x y z := by
  rcases x with ⟨⟨x2, x3⟩, xb⟩
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  rcases z with ⟨⟨z2, z3⟩, zb⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [spinJordanTriple, spinJordanMul, spinTraceReverse,
        conformalSpinTriple, B10, zornPolar,
        ZornVectorMatrix.trace, ZornVectorMatrix.mul,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVec3.dot, Fin.sum_univ_three] <;> ring
  · apply ZornVectorMatrix.ext <;> try funext i <;> try fin_cases i <;>
      simp [spinJordanTriple, spinJordanMul, spinTraceReverse,
        conformalSpinTriple, B10, zornPolar,
        ZornVectorMatrix.trace, ZornVectorMatrix.mul,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVec3.dot, Fin.sum_univ_three] <;> ring

/-- Grade-zero orthogonal action generated by a translation/special-conformal
pair. -/
def conformalZeroAction (x y : V10) : Module.End ℝ V10 :=
  (-B10 x y) • LinearMap.id + rankTwoRotation x y

@[simp] theorem conformalZeroAction_apply (x y z : V10) :
    conformalZeroAction x y z = - conformalSpinTriple x y z := by
  simp [conformalZeroAction, conformalSpinTriple, rankTwoRotation,
    B10_symm]
  module

/-- The cross bracket already present in the D6 owner is exactly the
zero-grade operator attached to the trace-reversed restricted Jordan triple. -/
theorem translation_specialConformal_cross_bracket_triple
    (x y : V10) :
    commutator (translation x) (specialConformal y) =
      dilation (-B10 x y) + middleRotation (rankTwoRotation x y) :=
  translation_specialConformal_cross_bracket x y

/-- The TKK double bracket acts on translations by minus the restricted
Jordan triple with trace reversal in the middle slot. -/
theorem conformal_double_bracket_translation
    (x y z : V10) :
    commutator
        (commutator (translation x) (specialConformal y))
        (translation z) =
      - translation (spinJordanTriple x (spinTraceReverse y) z) := by
  rw [spinJordanTriple_traceReverse_eq_conformal]
  apply LinearMap.ext
  intro q
  rcases q with ⟨s, w, t⟩
  simp [commutator, translation, specialConformal, dilation,
    middleRotation, rankTwoRotation, conformalSpinTriple,
    B10_add_left, B10_add_right, B10_smul_left, B10_smul_right,
    B10_symm]
  ext <;> ring

/-- The same zero-grade cross bracket is visibly a dilation plus the native
rank-two `so(5,5)` rotation.  This is the precise `D(x,y)` readback needed by
the existing 66-dimensional conformal parameterization. -/
theorem restricted_triple_zero_grade_readback (x y : V10) :
    commutator (translation x) (specialConformal y) =
      dilation (-B10 x y) + middleRotation (rankTwoRotation x y) := by
  exact translation_specialConformal_cross_bracket x y

/-- Summary packet for the Peirce restriction and conformal TKK readback. -/
theorem peirce_triple_tkk_packet (x y z : V10) :
    InPeirceZero
        (jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y)
          (peirceZeroEmbed z)) ∧
    peirceZeroEmbed (spinJordanTriple x y z) =
      jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y)
        (peirceZeroEmbed z) ∧
    commutator
        (commutator (translation x) (specialConformal y))
        (translation z) =
      - translation (spinJordanTriple x (spinTraceReverse y) z) := by
  refine ⟨?_, peirceZeroEmbed_spinJordanTriple x y z,
    conformal_double_bracket_translation x y z⟩
  rw [← peirceZeroEmbed_spinJordanTriple]
  exact peirceZeroEmbed_mem _

end InfoGeometry.Canonical.SplitSpinFactorPeirceTripleTKKBridge
