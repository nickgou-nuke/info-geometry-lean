import InfoGeometry.Modular.NoncommutativeModularBridge

/-!
# ModularSurprisalDerivationBridge

Compatibility surface for the noncommutative modular derivation API.
The authoritative definitions use units of an arbitrary ring and retain the
conjugation term in the logarithmic product rule.
-/

noncomputable section

namespace InfoGeometry.Modular

open Noncommutative

variable {A : Type*} [Ring A]

abbrev adK_surprisal (K : A) : A →ₗ[ℤ] A := adKLinear K

@[simp] theorem adK_surprisal_apply (K X : A) :
    adK_surprisal K X = K * X - X * K := rfl

theorem adK_surprisal_is_derivation (K X Y : A) :
    adK_surprisal K (X * Y) =
      adK_surprisal K X * Y + X * adK_surprisal K Y :=
  adK_mul K X Y

@[simp] theorem adK_surprisal_one (K : A) :
    adK_surprisal K 1 = 0 := adK_one K

abbrev IsLinearDerivationSurprisal (D : A →ₗ[ℤ] A) : Prop :=
  IsDerivation D

abbrev dlogRNSurprisal (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  dlog D u

theorem dlogRNSurprisal_mul (D : A →ₗ[ℤ] A)
    (hD : IsLinearDerivationSurprisal D) (u v : Aˣ) :
    dlogRNSurprisal D (u * v) =
      (↑(v⁻¹) : A) * dlogRNSurprisal D u * (v : A) +
        dlogRNSurprisal D v :=
  dlog_mul D hD u v

end InfoGeometry.Modular

end noncomputable section
