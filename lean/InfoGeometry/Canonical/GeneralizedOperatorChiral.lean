import Mathlib

/-!
# InfoGeometry.Canonical.GeneralizedOperatorChiral

Generalized directional operator with square parameter `sq_val` and its
hyperbolic (`sq_val = 1`) chiral polarization packet.

No wrappers. No `sorry`.
-/

namespace GeneralizedOperatorChiral

noncomputable section

/-! ## Core generalized operator -/

structure GeneralizedOperator (sq_val : ℝ) where
  scalar : ℝ
  directional : ℝ

namespace GeneralizedOperator

theorem ext {sq_val : ℝ} {A B : GeneralizedOperator sq_val}
    (hs : A.scalar = B.scalar) (hd : A.directional = B.directional) : A = B := by
  cases A
  cases B
  cases hs
  cases hd
  rfl

def mul {sq_val : ℝ} (A B : GeneralizedOperator sq_val) : GeneralizedOperator sq_val :=
  ⟨A.scalar * B.scalar + sq_val * A.directional * B.directional,
   A.scalar * B.directional + A.directional * B.scalar⟩

def add {sq_val : ℝ} (A B : GeneralizedOperator sq_val) : GeneralizedOperator sq_val :=
  ⟨A.scalar + B.scalar, A.directional + B.directional⟩

def one {sq_val : ℝ} : GeneralizedOperator sq_val := ⟨1, 0⟩
def zero {sq_val : ℝ} : GeneralizedOperator sq_val := ⟨0, 0⟩

/-! ## Hyperbolic chiral projectors (`sq_val = 1`) -/

def P_plus : GeneralizedOperator 1 := ⟨(1 / 2 : ℝ), (1 / 2 : ℝ)⟩
def P_minus : GeneralizedOperator 1 := ⟨(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩

theorem chiral_idempotent_plus :
    mul P_plus P_plus = P_plus := by
  apply ext <;> dsimp [mul, P_plus] <;> ring_nf

theorem chiral_idempotent_minus :
    mul P_minus P_minus = P_minus := by
  apply ext <;> dsimp [mul, P_minus] <;> ring_nf

theorem chiral_orthogonal_pm :
    mul P_plus P_minus = zero := by
  apply ext <;> dsimp [mul, P_plus, P_minus, zero] <;> ring_nf

theorem chiral_orthogonal_mp :
    mul P_minus P_plus = zero := by
  apply ext <;> dsimp [mul, P_plus, P_minus, zero] <;> ring_nf

theorem chiral_complete :
    add P_plus P_minus = one := by
  apply ext <;> dsimp [add, P_plus, P_minus, one] <;> ring_nf

/-- Normalized spectral decomposition on the `sq_val = 1` polarized channels. -/
theorem hyperbolic_spectral_decomposition'
    (V : GeneralizedOperator 1) :
    V =
      add
        (mul { scalar := V.scalar + V.directional, directional := 0 } P_plus)
        (mul { scalar := V.scalar - V.directional, directional := 0 } P_minus) := by
  apply ext <;> dsimp [add, mul, P_plus, P_minus] <;> ring_nf

/-! ## Closed-form polarized exponential (`sq_val = 1`) -/

noncomputable def chiralExp (V : GeneralizedOperator 1) : GeneralizedOperator 1 :=
  let lp := V.scalar + V.directional
  let lm := V.scalar - V.directional
  ⟨(Real.exp lp + Real.exp lm) / 2,
   (Real.exp lp - Real.exp lm) / 2⟩

theorem chiralExp_scalar_formula (V : GeneralizedOperator 1) :
    (chiralExp V).scalar =
      (Real.exp (V.scalar + V.directional) + Real.exp (V.scalar - V.directional)) / 2 := by
  simp [chiralExp]

theorem chiralExp_directional_formula (V : GeneralizedOperator 1) :
    (chiralExp V).directional =
      (Real.exp (V.scalar + V.directional) - Real.exp (V.scalar - V.directional)) / 2 := by
  simp [chiralExp]

/-- Polarized exponential decomposition on `sq_val = 1` channels. -/
theorem chiralExp_channel_decomposition (V : GeneralizedOperator 1) :
    chiralExp V =
      add
        (mul { scalar := Real.exp (V.scalar + V.directional), directional := 0 } P_plus)
        (mul { scalar := Real.exp (V.scalar - V.directional), directional := 0 } P_minus) := by
  apply ext <;> dsimp [chiralExp, add, mul, P_plus, P_minus] <;> ring_nf

/-- Hyperbolic Euler form on the `sq_val = 1` channel:
`exp(a+bΩ) = exp(a) * (cosh b + Ω sinh b)`. -/
theorem chiralExp_hyperbolic_euler (V : GeneralizedOperator 1) :
    chiralExp V =
      { scalar := Real.exp V.scalar * Real.cosh V.directional
      , directional := Real.exp V.scalar * Real.sinh V.directional } := by
  apply ext
  · calc
      (chiralExp V).scalar
          = (Real.exp (V.scalar + V.directional) + Real.exp (V.scalar - V.directional)) / 2 := by
              simp [chiralExp]
      _ = (Real.exp V.scalar * Real.exp V.directional +
            Real.exp V.scalar * Real.exp (-V.directional)) / 2 := by
              rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
      _ = Real.exp V.scalar * ((Real.exp V.directional + Real.exp (-V.directional)) / 2) := by
              ring
      _ = Real.exp V.scalar * Real.cosh V.directional := by
              rw [Real.cosh_eq]
  · calc
      (chiralExp V).directional
          = (Real.exp (V.scalar + V.directional) - Real.exp (V.scalar - V.directional)) / 2 := by
              simp [chiralExp]
      _ = (Real.exp V.scalar * Real.exp V.directional -
            Real.exp V.scalar * Real.exp (-V.directional)) / 2 := by
              have hsub : Real.exp (V.scalar - V.directional) =
                  Real.exp V.scalar * Real.exp (-V.directional) := by
                rw [sub_eq_add_neg, Real.exp_add]
              rw [Real.exp_add, hsub]
      _ = Real.exp V.scalar * ((Real.exp V.directional - Real.exp (-V.directional)) / 2) := by
              ring
      _ = Real.exp V.scalar * Real.sinh V.directional := by
              rw [Real.sinh_eq]

/-- `sq_val = 1` multiplication is commutative. -/
theorem mul_comm_hyperbolic (A B : GeneralizedOperator 1) :
    mul A B = mul B A := by
  apply ext <;> dsimp [mul] <;> ring

/--
Additive-to-multiplicative law for the hyperbolic closed-form exponential:
`chiralExp (A + B) = chiralExp A * chiralExp B`.
-/
theorem chiralExp_add (A B : GeneralizedOperator 1) :
    chiralExp (add A B) = mul (chiralExp A) (chiralExp B) := by
  apply ext
  · calc
      (chiralExp (add A B)).scalar
          = Real.exp (A.scalar + A.directional) * Real.exp (B.scalar + B.directional) / 2
            + Real.exp (A.scalar - A.directional) * Real.exp (B.scalar - B.directional) / 2 := by
              simp [chiralExp, add, Real.exp_add, sub_eq_add_neg]
              ring
      _ = (mul (chiralExp A) (chiralExp B)).scalar := by
            dsimp [mul, chiralExp]
            ring
  · calc
      (chiralExp (add A B)).directional
          = Real.exp (A.scalar + A.directional) * Real.exp (B.scalar + B.directional) / 2
            - Real.exp (A.scalar - A.directional) * Real.exp (B.scalar - B.directional) / 2 := by
              simp [chiralExp, add, Real.exp_add, sub_eq_add_neg]
              ring
      _ = (mul (chiralExp A) (chiralExp B)).directional := by
            dsimp [mul, chiralExp]
            ring

/-- Polarized logarithm coordinates on the hyperbolic channel (`sq_val = 1`). -/
noncomputable def chiralLog (W : GeneralizedOperator 1) : GeneralizedOperator 1 :=
  ⟨(Real.log (W.scalar + W.directional) + Real.log (W.scalar - W.directional)) / 2,
   (Real.log (W.scalar + W.directional) - Real.log (W.scalar - W.directional)) / 2⟩

/--
Left-inverse theorem on the hyperbolic polarized corridor:
`chiralLog (chiralExp V) = V`.
-/
theorem chiralLog_chiralExp (V : GeneralizedOperator 1) :
    chiralLog (chiralExp V) = V := by
  have hplus : Real.log (Real.exp (V.scalar + V.directional)) = V.scalar + V.directional :=
    Real.log_exp (V.scalar + V.directional)
  have hminus : Real.log (Real.exp (V.scalar - V.directional)) = V.scalar - V.directional :=
    Real.log_exp (V.scalar - V.directional)
  have hsumsimp :
      ((Real.exp (V.scalar + V.directional) + Real.exp (V.scalar - V.directional)) / 2 +
        (Real.exp (V.scalar + V.directional) - Real.exp (V.scalar - V.directional)) / 2)
        = Real.exp (V.scalar + V.directional) := by
    ring
  have hdiffsimp :
      ((Real.exp (V.scalar + V.directional) + Real.exp (V.scalar - V.directional)) / 2 -
        (Real.exp (V.scalar + V.directional) - Real.exp (V.scalar - V.directional)) / 2)
        = Real.exp (V.scalar - V.directional) := by
    ring
  apply ext
  · simp [chiralLog, chiralExp]
    rw [hsumsimp, hdiffsimp, hplus, hminus]
    ring
  · simp [chiralLog, chiralExp]
    rw [hsumsimp, hdiffsimp, hplus, hminus]
    ring

/--
Right-inverse theorem on the positive hyperbolic cone:
if both polarized channels are positive, then `chiralExp (chiralLog W) = W`.
-/
theorem chiralExp_chiralLog
    (W : GeneralizedOperator 1)
    (hplus : 0 < W.scalar + W.directional)
    (hminus : 0 < W.scalar - W.directional) :
    chiralExp (chiralLog W) = W := by
  apply ext
  · calc
      (chiralExp (chiralLog W)).scalar
          = (Real.exp (Real.log (W.scalar + W.directional)) +
              Real.exp (Real.log (W.scalar - W.directional))) / 2 := by
                simp [chiralExp, chiralLog]
                ring
      _ = ((W.scalar + W.directional) + (W.scalar - W.directional)) / 2 := by
            rw [Real.exp_log hplus, Real.exp_log hminus]
      _ = W.scalar := by ring
  · calc
      (chiralExp (chiralLog W)).directional
          = (Real.exp (Real.log (W.scalar + W.directional)) -
              Real.exp (Real.log (W.scalar - W.directional))) / 2 := by
                simp [chiralExp, chiralLog]
                ring
      _ = ((W.scalar + W.directional) - (W.scalar - W.directional)) / 2 := by
            rw [Real.exp_log hplus, Real.exp_log hminus]
      _ = W.directional := by ring

/--
Hyperbolic positivity witnesses produced by `chiralExp`:
the two polarized channels are strictly positive, so `chiralLog` is defined
without extra assumptions on the input `V`.
-/
theorem chiralExp_polarized_channels_pos (V : GeneralizedOperator 1) :
    0 < (chiralExp V).scalar + (chiralExp V).directional ∧
    0 < (chiralExp V).scalar - (chiralExp V).directional := by
  constructor
  · calc
      (chiralExp V).scalar + (chiralExp V).directional
          = Real.exp (V.scalar + V.directional) := by
              simp [chiralExp]
              ring
      _ = Real.exp (V.scalar + V.directional) := rfl
      _ > 0 := Real.exp_pos (V.scalar + V.directional)
  · calc
      (chiralExp V).scalar - (chiralExp V).directional
          = Real.exp (V.scalar - V.directional) := by
              simp [chiralExp]
              ring
      _ = Real.exp (V.scalar - V.directional) := rfl
      _ > 0 := Real.exp_pos (V.scalar - V.directional)

/--
Hyperbolic exp-log-exp closure without external assumptions:
`chiralExp (chiralLog (chiralExp V)) = chiralExp V`.
-/
theorem chiralExp_chiralLog_chiralExp (V : GeneralizedOperator 1) :
    chiralExp (chiralLog (chiralExp V)) = chiralExp V := by
  rcases chiralExp_polarized_channels_pos V with ⟨hplus, hminus⟩
  exact chiralExp_chiralLog (W := chiralExp V) hplus hminus

/-! ## Elliptic (`sq_val = -1`) and parabolic (`sq_val = 0`) closed forms -/

/-- Elliptic closed-form exponential coordinates (`Ω² = -1`). -/
noncomputable def ellipticExp (V : GeneralizedOperator (-1)) : GeneralizedOperator (-1) :=
  ⟨Real.exp V.scalar * Real.cos V.directional,
   Real.exp V.scalar * Real.sin V.directional⟩

theorem ellipticExp_scalar_formula (V : GeneralizedOperator (-1)) :
    (ellipticExp V).scalar = Real.exp V.scalar * Real.cos V.directional := by
  rfl

theorem ellipticExp_directional_formula (V : GeneralizedOperator (-1)) :
    (ellipticExp V).directional = Real.exp V.scalar * Real.sin V.directional := by
  rfl

/--
Elliptic norm identity (`Ω² = -1`):
the squared radius of `ellipticExp` is `exp(2a)`.
-/
theorem ellipticExp_norm_sq (V : GeneralizedOperator (-1)) :
    (ellipticExp V).scalar ^ 2 + (ellipticExp V).directional ^ 2 =
      Real.exp (2 * V.scalar) := by
  calc
    (ellipticExp V).scalar ^ 2 + (ellipticExp V).directional ^ 2
        = (Real.exp V.scalar * Real.cos V.directional) ^ 2
          + (Real.exp V.scalar * Real.sin V.directional) ^ 2 := by
            simp [ellipticExp]
    _ = (Real.exp V.scalar) ^ 2 * (Real.cos V.directional ^ 2 + Real.sin V.directional ^ 2) := by
          ring
    _ = (Real.exp V.scalar) ^ 2 := by
          rw [Real.cos_sq_add_sin_sq]
          ring
    _ = Real.exp (V.scalar + V.scalar) := by
          rw [pow_two, ← Real.exp_add]
    _ = Real.exp (2 * V.scalar) := by ring

/-- Parabolic closed-form exponential coordinates (`Ω² = 0`). -/
noncomputable def parabolicExp (V : GeneralizedOperator 0) : GeneralizedOperator 0 :=
  ⟨Real.exp V.scalar, Real.exp V.scalar * V.directional⟩

theorem parabolicExp_scalar_formula (V : GeneralizedOperator 0) :
    (parabolicExp V).scalar = Real.exp V.scalar := by
  rfl

theorem parabolicExp_directional_formula (V : GeneralizedOperator 0) :
    (parabolicExp V).directional = Real.exp V.scalar * V.directional := by
  rfl

/--
Parabolic additive law (`Ω² = 0`):
`exp(A + B) = exp(A) * exp(B)` in the dual-number channel.
-/
theorem parabolicExp_add (A B : GeneralizedOperator 0) :
    parabolicExp (add A B) = mul (parabolicExp A) (parabolicExp B) := by
  apply ext <;> dsimp [parabolicExp, add, mul] <;> simp [Real.exp_add] <;> ring

/-- Parabolic logarithm coordinates (`Ω² = 0`). -/
noncomputable def parabolicLog (W : GeneralizedOperator 0) : GeneralizedOperator 0 :=
  ⟨Real.log W.scalar, W.directional / W.scalar⟩

/-- Left inverse on the parabolic lane: `parabolicLog (parabolicExp V) = V`. -/
theorem parabolicLog_parabolicExp (V : GeneralizedOperator 0) :
    parabolicLog (parabolicExp V) = V := by
  apply ext
  · simp [parabolicLog, parabolicExp]
  · calc
      (parabolicLog (parabolicExp V)).directional
          = (Real.exp V.scalar * V.directional) / Real.exp V.scalar := by
              simp [parabolicLog, parabolicExp]
      _ = V.directional := by
            field_simp [Real.exp_ne_zero V.scalar]

/--
Right inverse on the positive parabolic cone:
if `W.scalar > 0`, then `parabolicExp (parabolicLog W) = W`.
-/
theorem parabolicExp_parabolicLog
    (W : GeneralizedOperator 0) (hW : 0 < W.scalar) :
    parabolicExp (parabolicLog W) = W := by
  apply ext
  · simp [parabolicExp, parabolicLog, Real.exp_log hW]
  · calc
      (parabolicExp (parabolicLog W)).directional
          = Real.exp (Real.log W.scalar) * (W.directional / W.scalar) := by
              simp [parabolicExp, parabolicLog]
      _ = W.scalar * (W.directional / W.scalar) := by rw [Real.exp_log hW]
      _ = W.directional := by
            field_simp [hW.ne']

/--
Parabolic logarithm turns multiplication into addition on the positive cone.

If `A.scalar > 0` and `B.scalar > 0`, then
`parabolicLog (A * B) = parabolicLog A + parabolicLog B`
in the `Ω² = 0` channel.
-/
theorem parabolicLog_mul_of_pos
    (A B : GeneralizedOperator 0)
    (hA : 0 < A.scalar) (hB : 0 < B.scalar) :
    parabolicLog (mul A B) = add (parabolicLog A) (parabolicLog B) := by
  apply ext
  · calc
      (parabolicLog (mul A B)).scalar
          = Real.log ((mul A B).scalar) := by rfl
      _ = Real.log (A.scalar * B.scalar) := by simp [mul]
      _ = Real.log A.scalar + Real.log B.scalar := by
            rw [Real.log_mul hA.ne' hB.ne']
      _ = (add (parabolicLog A) (parabolicLog B)).scalar := by rfl
  · have hABnz : A.scalar * B.scalar ≠ 0 := (mul_ne_zero hA.ne' hB.ne').symm.symm
    calc
      (parabolicLog (mul A B)).directional
          = (mul A B).directional / (mul A B).scalar := by rfl
      _ = (A.scalar * B.directional + A.directional * B.scalar) / (A.scalar * B.scalar) := by
            simp [mul]
      _ = A.directional / A.scalar + B.directional / B.scalar := by
            field_simp [hA.ne', hB.ne', hABnz]
            ring
      _ = (add (parabolicLog A) (parabolicLog B)).directional := by
            simp [add, parabolicLog]

/-- Parabolic analog of `P_+ = (1+Ω)/2` in the `Ω² = 0` lane. -/
def parabolicPPlus : GeneralizedOperator 0 := ⟨(1 / 2 : ℝ), (1 / 2 : ℝ)⟩

/-- Parabolic analog of `P_- = (1-Ω)/2` in the `Ω² = 0` lane. -/
def parabolicPMinus : GeneralizedOperator 0 := ⟨(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩

/--
In the parabolic lane (`Ω² = 0`), the naive chiral candidate `P_+`
is not idempotent.
-/
theorem parabolicPPlus_not_idempotent :
    mul parabolicPPlus parabolicPPlus ≠ parabolicPPlus := by
  intro h
  have hs : (mul parabolicPPlus parabolicPPlus).scalar = parabolicPPlus.scalar := by
    exact congrArg (fun X => X.scalar) h
  dsimp [mul, parabolicPPlus] at hs
  norm_num at hs

/--
In the parabolic lane (`Ω² = 0`), the naive chiral candidate `P_-`
is not idempotent.
-/
theorem parabolicPMinus_not_idempotent :
    mul parabolicPMinus parabolicPMinus ≠ parabolicPMinus := by
  intro h
  have hs : (mul parabolicPMinus parabolicPMinus).scalar = parabolicPMinus.scalar := by
    exact congrArg (fun X => X.scalar) h
  dsimp [mul, parabolicPMinus] at hs
  norm_num at hs

/--
Pure nilpotent exponential composition law:
`exp((χ₁+χ₂)Ω) = exp(χ₁Ω) * exp(χ₂Ω)` in the `Ω² = 0` lane.
-/
theorem parabolicExp_pure_nilpotent_add (χ₁ χ₂ : ℝ) :
    parabolicExp ({ scalar := (0 : ℝ), directional := χ₁ + χ₂ } : GeneralizedOperator 0)
      =
    mul (parabolicExp ({ scalar := (0 : ℝ), directional := χ₁ } : GeneralizedOperator 0))
        (parabolicExp ({ scalar := (0 : ℝ), directional := χ₂ } : GeneralizedOperator 0)) := by
  simpa [add] using
    (parabolicExp_add
      ({ scalar := (0 : ℝ), directional := χ₁ } : GeneralizedOperator 0)
      ({ scalar := (0 : ℝ), directional := χ₂ } : GeneralizedOperator 0))

/--
Pure parabolic directional elements are square-zero under `sq_val = 0`:
`(0 + χΩ)^2 = 0`.
-/
theorem parabolic_pure_square_zero (χ : ℝ) :
    mul ({ scalar := (0 : ℝ), directional := χ } : GeneralizedOperator 0)
        ({ scalar := (0 : ℝ), directional := χ } : GeneralizedOperator 0)
      = zero := by
  apply ext <;> dsimp [mul, zero] <;> ring_nf

/--
Nilpotent truncation seed (`Ω² = 0`):
for pure directional input, exponential truncates to `1 + χΩ`.
-/
theorem parabolic_nilpotent_truncation_seed (χ : ℝ) :
    parabolicExp ({ scalar := (0 : ℝ), directional := χ } : GeneralizedOperator 0)
      = { scalar := (1 : ℝ), directional := χ } := by
  apply ext <;> dsimp [parabolicExp] <;> simp

/--
Unified tri-square/chiral closure packet:

* elliptic lane (`Ω² = -1`) has the `exp(a)(cos b, sin b)` form,
* hyperbolic lane (`Ω² = 1`) has idempotent/orthogonal/completeness projectors
  and hyperbolic Euler form,
* parabolic lane (`Ω² = 0`) has square-zero pure direction and truncation
  `exp(χΩ) = 1 + χΩ`.
-/
theorem triSquare_chiral_closure_packet
    (Ve : GeneralizedOperator (-1))
    (Vh : GeneralizedOperator 1)
    (Vp : GeneralizedOperator 0)
    (χ : ℝ) :
    (ellipticExp Ve).scalar = Real.exp Ve.scalar * Real.cos Ve.directional ∧
    (ellipticExp Ve).directional = Real.exp Ve.scalar * Real.sin Ve.directional ∧
    mul P_plus P_plus = P_plus ∧
    mul P_minus P_minus = P_minus ∧
    mul P_plus P_minus = zero ∧
    mul P_minus P_plus = zero ∧
    add P_plus P_minus = one ∧
    chiralExp Vh =
      { scalar := Real.exp Vh.scalar * Real.cosh Vh.directional
      , directional := Real.exp Vh.scalar * Real.sinh Vh.directional } ∧
    mul ({ scalar := (0 : ℝ), directional := χ } : GeneralizedOperator 0)
        ({ scalar := (0 : ℝ), directional := χ } : GeneralizedOperator 0) = zero ∧
    parabolicExp ({ scalar := (0 : ℝ), directional := χ } : GeneralizedOperator 0)
      = { scalar := (1 : ℝ), directional := χ } ∧
    (parabolicExp Vp).scalar = Real.exp Vp.scalar ∧
    (parabolicExp Vp).directional = Real.exp Vp.scalar * Vp.directional := by
  refine ⟨ellipticExp_scalar_formula Ve, ellipticExp_directional_formula Ve, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chiral_idempotent_plus
  · exact chiral_idempotent_minus
  · exact chiral_orthogonal_pm
  · exact chiral_orthogonal_mp
  · exact chiral_complete
  · exact chiralExp_hyperbolic_euler Vh
  · exact parabolic_pure_square_zero χ
  · exact parabolic_nilpotent_truncation_seed χ
  · exact parabolicExp_scalar_formula Vp
  · exact parabolicExp_directional_formula Vp

/--
Hyperbolic polarized exp/log corridor packet (`sq_val = 1`):

* additive-to-multiplicative exponential law,
* logarithm is a left inverse of the polarized exponential,
* logarithm is also a right inverse on the positive polarized cone.
-/
theorem hyperbolic_chiral_exp_log_packet
    (A B : GeneralizedOperator 1)
    (W : GeneralizedOperator 1)
    (hplus : 0 < W.scalar + W.directional)
    (hminus : 0 < W.scalar - W.directional) :
    chiralExp (add A B) = mul (chiralExp A) (chiralExp B) ∧
    chiralLog (chiralExp A) = A ∧
    chiralExp (chiralLog W) = W := by
  refine ⟨?_, ?_, ?_⟩
  · exact chiralExp_add A B
  · exact chiralLog_chiralExp A
  · exact chiralExp_chiralLog W hplus hminus

end GeneralizedOperator
end

end GeneralizedOperatorChiral
