import InfoGeometry.Lie.SplitOctonionEllCircularCAR
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

/-!
# Split-octonion and finite arithmetic chiral Hodge--Dirac readout

This owner records the common finite CAR packet behind two already existing
carriers.  On the native split-octonion carrier the opposite root channels are
square-zero and have the expected complementary products.  On the finite
prime-exterior carrier the creation and annihilation push-forwards satisfy the
same local relations.  Their sum is therefore a finite Hodge--Dirac operator.

The file deliberately does **not** assert an intertwiner between the two
carriers, nor an infinite Dirichlet operator or zeta functional calculus.  The
logarithmic arithmetic readout is imported separately from the finite
Dirichlet-shift owner.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.SplitOctonionChiralHodgeDiracBridge

open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
open InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

/-! ## Native split-octonion chiral CAR -/

/-- The native opposite-channel CAR packet in one colour direction.

The sum is intentionally recorded only as a formal readout here: the native
Zorn carrier has not been packaged with associative/distributive algebra
instances, so its operator square belongs to a separate multiplication
transport theorem rather than being silently derived by ring tactics.
-/
theorem splitOctonionChiralCAR (a : Fin 3) :
    rootPlus a * rootPlus a = 0 ∧
    rootMinus a * rootMinus a = 0 ∧
    rootPlus a * rootMinus a = uPlus ∧
    rootMinus a * rootPlus a = uMinus := by
  exact ⟨rootPlus_sq_zero a, rootMinus_sq_zero a,
    rootPlus_mul_rootMinus a, rootMinus_mul_rootPlus a⟩

theorem splitOctonionChiralCAR_anticommutator (a : Fin 3) :
    rootPlus a * rootMinus a + rootMinus a * rootPlus a = 1 := by
  rw [rootPlus_mul_rootMinus, rootMinus_mul_rootPlus, uPlus_add_uMinus]

/-! ## Finite prime-exterior chiral Hodge--Dirac -/

abbrev PrimeCutoff := InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff
abbrev PrimeMode (P : PrimeCutoff) :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeMode P
abbrev Vertex (P : PrimeCutoff) :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.Vertex P
abbrev CantorField (P : PrimeCutoff) :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.CantorField P

/-- Finite discrete exterior derivative on one prime axis. -/
def primeExteriorDerivative {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  creationPush p f S

/-- Finite discrete codifferential on one prime axis. -/
def primeCodifferential {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  annihilationPush p f S

/-- The one-axis finite chiral Hodge--Dirac operator `D_p = d_p + δ_p`. -/
def primeChiralHodgeDirac {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  primeExteriorDerivative p f S + primeCodifferential p f S

/-- The one-axis finite Hodge Laplacian `Δ_p = d_p δ_p + δ_p d_p`. -/
def primeChiralHodgeLaplacian {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  primeExteriorDerivative p (fun T => primeCodifferential p f T) S +
    primeCodifferential p (fun T => primeExteriorDerivative p f T) S

private theorem optionEval_add {P : PrimeCutoff}
    (f g : CantorField P) (o : Option (Vertex P)) :
    optionEval (fun T => f T + g T) o = optionEval f o + optionEval g o := by
  cases o <;> simp [optionEval]

private theorem creationPush_add {P : PrimeCutoff}
    (p : PrimeMode P) (f g : CantorField P) (S : Vertex P) :
    creationPush p (fun T => f T + g T) S =
      creationPush p f S + creationPush p g S := by
  exact optionEval_add f g
    (InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.create p S)

private theorem annihilationPush_add {P : PrimeCutoff}
    (p : PrimeMode P) (f g : CantorField P) (S : Vertex P) :
    annihilationPush p (fun T => f T + g T) S =
      annihilationPush p f S + annihilationPush p g S := by
  exact optionEval_add f g
    (InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.annihilate p S)

theorem primeExteriorDerivative_sq_zero {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    primeExteriorDerivative p (fun T => primeExteriorDerivative p f T) S = 0 := by
  exact creationPush_sq_zero p f S

theorem primeCodifferential_sq_zero {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    primeCodifferential p (fun T => primeCodifferential p f T) S = 0 := by
  exact annihilationPush_sq_zero p f S

theorem primeChiralHodgeLaplacian_apply {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    primeChiralHodgeLaplacian p f S = f S := by
  unfold primeChiralHodgeLaplacian primeExteriorDerivative primeCodifferential
  exact creation_annihilation_push_anticomm_identity p f S

theorem primeChiralHodgeDirac_sq {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    primeChiralHodgeDirac p
        (fun T => primeChiralHodgeDirac p f T) S =
      primeChiralHodgeLaplacian p f S := by
  unfold primeChiralHodgeDirac primeChiralHodgeLaplacian
    primeExteriorDerivative primeCodifferential
  rw [creationPush_add, annihilationPush_add]
  rw [creationPush_sq_zero, annihilationPush_sq_zero]
  ring

/-! ## Arithmetic logarithmic readout -/

/-- The weight attached to the finite prime Hodge mode is `log p`. -/
def primeHodgeLogWeight {P : PrimeCutoff} (p : PrimeMode P) : ℝ :=
  Real.log (p : ℝ)

@[simp] theorem primeHodgeLogWeight_eq_primeEnergy
    {P : PrimeCutoff} (p : PrimeMode P) :
    primeHodgeLogWeight p =
      InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.primeEnergy p := rfl

theorem finiteDirichlet_logarithmic_readout (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n => Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  exact finiteDirichletShift_exponentialTest N s t

end InfoGeometry.Canonical.SplitOctonionChiralHodgeDiracBridge

end noncomputable section
