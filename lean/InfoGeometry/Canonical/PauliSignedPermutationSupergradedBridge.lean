import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.CircularPauliCausalCone
import InfoGeometry.Canonical.ZornOrientationTwistedS3

noncomputable section

namespace InfoGeometry.Canonical.PauliSignedPermutationSupergradedBridge

open _root_.InfoGeometry.Quantum.CircularPauliCausalCone
open _root_.InfoGeometry.Canonical.ZornOrientationTwistedS3

abbrev Vec3 := InfoGeometry.Algebra.FiniteSpin.Vec3C

def signedPermVec (p : Equiv.Perm (Fin 3)) (x : Vec3) : Vec3 :=
  twistedVec p x

theorem signedPermVec_swap_dot (a b : Fin 3) (x y : Vec3) :
    orderedDot (twistedVec (Equiv.swap a b) x) (twistedVec (Equiv.swap a b) y) = orderedDot x y := by
  fin_cases a <;> fin_cases b <;>
    (simp [twistedVec, permutationSign, permuteVec, orderedDot, Equiv.swap_apply_def] <;>
     ring)

theorem signedPermVec_dot (p : Equiv.Perm (Fin 3)) (x y : Vec3) :
    orderedDot (signedPermVec p x) (signedPermVec p y) = orderedDot x y := by
  induction p using Equiv.Perm.swap_induction_on with
  | one => simp [signedPermVec]
  | swap_mul f a b _ ih =>
    dsimp [signedPermVec]
    rw [twistedVec_comp, twistedVec_comp, signedPermVec_swap_dot]
    exact ih

def signedZorn (p : Equiv.Perm (Fin 3))
    (X : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ :=
  zornAction p X

theorem signedZorn_mul (p : Equiv.Perm (Fin 3))
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    signedZorn p (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ X Y) =
      InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (signedZorn p X) (signedZorn p Y) :=
  zornAction_mulZ p X Y

theorem signedZorn_one (X : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    signedZorn 1 X = X := zornAction_one X

theorem signedZorn_comp (p q : Equiv.Perm (Fin 3))
    (X : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    signedZorn (p * q) X = signedZorn p (signedZorn q X) :=
  zornAction_comp p q X

theorem pauliScalarCorrelation_product (x y : Vec3) :
    pauliScalarCorrelation x y = orderedDot x y :=
  pauliScalarCorrelation_eq_orderedDot x y

theorem pauliVectorCorrelation_product (x y : Vec3) :
    pauliVectorCorrelation x y = fun k => Complex.I * orderedCross x y k :=
  pauliVectorCorrelation_eq_i_orderedCross x y

theorem permuteVec_comp (p q : Equiv.Perm (Fin 3)) (x : Vec3) :
    permuteVec (p * q) x = permuteVec p (permuteVec q x) := by
  ext i
  simp [permuteVec, mul_inv_rev, Equiv.Perm.coe_mul]

theorem permuteVec_one (x : Vec3) : permuteVec 1 x = x := by
  ext i
  simp [permuteVec]

theorem pauliVectorCorrelation_swap (a b : Fin 3) (x y : Vec3) :
    pauliVectorCorrelation (permuteVec (Equiv.swap a b) x) (permuteVec (Equiv.swap a b) y) =
      permutationSign (Equiv.swap a b) • permuteVec (Equiv.swap a b) (pauliVectorCorrelation x y) := by
  rw [pauliVectorCorrelation_product, pauliVectorCorrelation_product]
  funext i
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    (simp [permuteVec, permutationSign, orderedCross, Equiv.swap_apply_def] <;>
     ring)

theorem pauliVectorCorrelation_permuteVec
    (p : Equiv.Perm (Fin 3)) (x y : Vec3) :
    pauliVectorCorrelation (permuteVec p x) (permuteVec p y) =
      permutationSign p • permuteVec p (pauliVectorCorrelation x y) := by
  induction p using Equiv.Perm.swap_induction_on with
  | one =>
    simp [permuteVec_one, permutationSign]
  | swap_mul f a b _ ih =>
    rw [permuteVec_comp, permuteVec_comp, pauliVectorCorrelation_swap, ih]
    rw [permuteVec_comp]
    ext i
    simp only [permuteVec, permutationSign, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, mul_smul, Pi.smul_apply]

def koszulSign (px py : Bool) : Bool := px && py

def superBracket {A : Type*} [Ring A]
    (px py : Bool) (x y : A) : A :=
  if koszulSign px py then x * y + y * x else x * y - y * x

@[simp] theorem odd_odd_superBracket {A : Type*} [Ring A] (x y : A) :
    superBracket true true x y = x * y + y * x := by
  simp [superBracket, koszulSign]

theorem superBracket_parity_additive
    {A : Type*} [Ring A] (grade : A → Bool)
    (mulHom : ∀ x y, grade (x * y) = xor (grade x) (grade y))
    (x y : A) : grade (x * y) = xor (grade x) (grade y) :=
  mulHom x y

end InfoGeometry.Canonical.PauliSignedPermutationSupergradedBridge

end noncomputable section
