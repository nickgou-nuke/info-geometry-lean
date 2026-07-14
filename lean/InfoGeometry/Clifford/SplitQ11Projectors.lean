import InfoGeometry.Clifford.SplitQ11PhaseFlip
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Clifford.SplitQ11Projectors

Mathlib-canonical `ε`-spectral projectors in the split `Cl(1,1)` algebra.

This file stays on the abstract Clifford-algebra side:

- the null-pair products are packaged as the two `ε`-projectors,
- their half-idempotent formulas are proved directly in `CliffordAlgebra splitQ11`,
- complementarity and idempotence are established algebraically,
- the `K`-axis phase flip swaps the two projectors.
-/

namespace SplitQ11Projectors

open InfoGeometry.Clifford.SplitQ11PhaseFlip

/-- Left multiplication of `ε` by `J` yields `K`. -/
@[rep_depth krein, simp] theorem jGen_mul_epsGen :
    jGen * epsGen = kGen := by
  unfold epsGen
  calc
    jGen * (jGen * kGen) = (jGen * jGen) * kGen := by rw [← mul_assoc]
    _ = kGen := by simp [jGen_sq]

/-- Right multiplication of `ε` by `J` yields `-K`. -/
@[rep_depth krein, simp] theorem epsGen_mul_jGen :
    epsGen * jGen = -kGen := by
  unfold epsGen
  calc
    (jGen * kGen) * jGen = jGen * (kGen * jGen) := by rw [mul_assoc]
    _ = jGen * (-epsGen) := by rw [kGen_mul_jGen]
    _ = -(jGen * epsGen) := by simp
    _ = -kGen := by rw [jGen_mul_epsGen]

/-- Left multiplication of `ε` by `K` yields `J`. -/
@[rep_depth krein, simp] theorem kGen_mul_epsGen :
    kGen * epsGen = jGen := by
  unfold epsGen
  calc
    kGen * (jGen * kGen) = (kGen * jGen) * kGen := by rw [← mul_assoc]
    _ = (-(jGen * kGen)) * kGen := by simp [epsGen, kGen_mul_jGen]
    _ = -(jGen * (kGen * kGen)) := by simp [mul_assoc]
    _ = jGen := by simp [kGen_sq]

/-- Right multiplication of `ε` by `K` yields `-J`. -/
@[rep_depth krein, simp] theorem epsGen_mul_kGen :
    epsGen * kGen = -jGen := by
  unfold epsGen
  calc
    (jGen * kGen) * kGen = jGen * (kGen * kGen) := by rw [mul_assoc]
    _ = -jGen := by simp [kGen_sq]

/-- The `ε = JK` pseudoscalar squares to `1` in split `Cl(1,1)`. -/
@[rep_depth krein, simp] theorem epsGen_sq :
    epsGen * epsGen = 1 := by
  unfold epsGen
  calc
    (jGen * kGen) * (jGen * kGen)
        = jGen * (kGen * (jGen * kGen)) := by simp [mul_assoc]
    _ = jGen * (kGen * epsGen) := by rfl
    _ = jGen * jGen := by rw [kGen_mul_epsGen]
    _ = 1 := by simp [jGen_sq]

/-- The `ε = -1` spectral projector. -/
@[rep_depth krein]
noncomputable def epsMinusProjector : Alg :=
  nullMinus * nullPlus

/-- The `ε = +1` spectral projector. -/
@[rep_depth krein]
noncomputable def epsPlusProjector : Alg :=
  nullPlus * nullMinus

/-- The mixed `u_- u_+` product is the `ε`-negative half-projector. -/
@[rep_depth krein, simp] theorem epsMinusProjector_eq_half_one_sub_eps :
    epsMinusProjector = (1 / 2 : ℝ) • ((1 : Alg) - epsGen) := by
  unfold epsMinusProjector
  rw [nullMinus_eq_half_jGen_add_kGen, nullPlus_eq_half_jGen_sub_kGen]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add,
    kGen_mul_jGen, jGen_sq, kGen_sq, epsGen]
  module

/-- The mixed `u_+ u_-` product is the `ε`-positive half-projector. -/
@[rep_depth krein, simp] theorem epsPlusProjector_eq_half_one_add_eps :
    epsPlusProjector = (1 / 2 : ℝ) • ((1 : Alg) + epsGen) := by
  unfold epsPlusProjector
  rw [nullPlus_eq_half_jGen_sub_kGen, nullMinus_eq_half_jGen_add_kGen]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add,
    kGen_mul_jGen, jGen_sq, kGen_sq, epsGen]
  module

/-- The two `ε`-projectors add to the identity. -/
@[rep_depth krein, simp] theorem epsMinusProjector_add_epsPlusProjector :
    epsMinusProjector + epsPlusProjector = 1 := by
  unfold epsMinusProjector epsPlusProjector
  simpa [add_comm] using nullMinus_mul_nullPlus_add_swap

/-- The two `ε`-projectors annihilate in one order. -/
@[rep_depth krein, simp] theorem epsMinusProjector_mul_epsPlusProjector :
    epsMinusProjector * epsPlusProjector = 0 := by
  rw [epsMinusProjector_eq_half_one_sub_eps, epsPlusProjector_eq_half_one_add_eps]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add, epsGen_sq]
  module

/-- The two `ε`-projectors annihilate in the other order as well. -/
@[rep_depth krein, simp] theorem epsPlusProjector_mul_epsMinusProjector :
    epsPlusProjector * epsMinusProjector = 0 := by
  rw [epsPlusProjector_eq_half_one_add_eps, epsMinusProjector_eq_half_one_sub_eps]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add, epsGen_sq]
  module

/-- The `ε = -1` projector is idempotent. -/
@[rep_depth krein, simp] theorem epsMinusProjector_idempotent :
    epsMinusProjector * epsMinusProjector = epsMinusProjector := by
  have h :
      epsMinusProjector
        = epsMinusProjector * epsMinusProjector := by
    calc
      epsMinusProjector = epsMinusProjector * (epsMinusProjector + epsPlusProjector) := by
        rw [epsMinusProjector_add_epsPlusProjector, mul_one]
      _ = epsMinusProjector * epsMinusProjector + epsMinusProjector * epsPlusProjector := by
        rw [mul_add]
      _ = epsMinusProjector * epsMinusProjector := by
        rw [epsMinusProjector_mul_epsPlusProjector, add_zero]
  exact h.symm

/-- The `ε = +1` projector is idempotent. -/
@[rep_depth krein, simp] theorem epsPlusProjector_idempotent :
    epsPlusProjector * epsPlusProjector = epsPlusProjector := by
  have h :
      epsPlusProjector
        = epsPlusProjector * epsPlusProjector := by
    calc
      epsPlusProjector = epsPlusProjector * (epsMinusProjector + epsPlusProjector) := by
        rw [epsMinusProjector_add_epsPlusProjector, mul_one]
      _ = epsPlusProjector * epsMinusProjector + epsPlusProjector * epsPlusProjector := by
        rw [mul_add]
      _ = epsPlusProjector * epsPlusProjector := by
        rw [epsPlusProjector_mul_epsMinusProjector, zero_add]
  exact h.symm

/-- Left multiplication by `ε` acts by `-1` on the negative projector. -/
@[rep_depth krein, simp] theorem epsGen_mul_epsMinusProjector :
    epsGen * epsMinusProjector = -epsMinusProjector := by
  rw [epsMinusProjector_eq_half_one_sub_eps]
  rw [smul_sub]
  change epsGen * ((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen)
    = -((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen)
  calc
    epsGen * ((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen)
        = (1 / 2 : ℝ) • epsGen - (1 / 2 : ℝ) • (epsGen * epsGen) := by
            simp [mul_sub, mul_one]
    _ = (1 / 2 : ℝ) • epsGen - (1 / 2 : ℝ) • (1 : Alg) := by rw [epsGen_sq]
    _ = -((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen) := by
          module

/-- Right multiplication by `ε` acts by `-1` on the negative projector. -/
@[rep_depth krein, simp] theorem epsMinusProjector_mul_epsGen :
    epsMinusProjector * epsGen = -epsMinusProjector := by
  rw [epsMinusProjector_eq_half_one_sub_eps]
  rw [smul_sub]
  change (((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen) * epsGen)
    = -((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen)
  calc
    (((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen) * epsGen)
        = (1 / 2 : ℝ) • epsGen - (1 / 2 : ℝ) • (epsGen * epsGen) := by
            simp [sub_mul, one_mul]
    _ = (1 / 2 : ℝ) • epsGen - (1 / 2 : ℝ) • (1 : Alg) := by rw [epsGen_sq]
    _ = -((1 / 2 : ℝ) • (1 : Alg) - (1 / 2 : ℝ) • epsGen) := by
          module

/-- Left multiplication by `ε` acts by `+1` on the positive projector. -/
@[rep_depth krein, simp] theorem epsGen_mul_epsPlusProjector :
    epsGen * epsPlusProjector = epsPlusProjector := by
  rw [epsPlusProjector_eq_half_one_add_eps]
  rw [smul_add]
  change epsGen * ((1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen)
    = (1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen
  calc
    epsGen * ((1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen)
        = (1 / 2 : ℝ) • epsGen + (1 / 2 : ℝ) • (epsGen * epsGen) := by
            simp [mul_add, mul_one]
    _ = (1 / 2 : ℝ) • epsGen + (1 / 2 : ℝ) • (1 : Alg) := by rw [epsGen_sq]
    _ = (1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen := by
          module

/-- Right multiplication by `ε` acts by `+1` on the positive projector. -/
@[rep_depth krein, simp] theorem epsPlusProjector_mul_epsGen :
    epsPlusProjector * epsGen = epsPlusProjector := by
  rw [epsPlusProjector_eq_half_one_add_eps]
  rw [smul_add]
  change (((1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen) * epsGen)
    = (1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen
  calc
    (((1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen) * epsGen)
        = (1 / 2 : ℝ) • epsGen + (1 / 2 : ℝ) • (epsGen * epsGen) := by
            simp [add_mul, one_mul]
    _ = (1 / 2 : ℝ) • epsGen + (1 / 2 : ℝ) • (1 : Alg) := by rw [epsGen_sq]
    _ = (1 / 2 : ℝ) • (1 : Alg) + (1 / 2 : ℝ) • epsGen := by
          module

/-- The phase flip swaps the two `ε`-projectors. -/
@[rep_depth krein, simp] theorem phaseFlip_apply_epsMinusProjector :
    phaseFlipAlg epsMinusProjector = epsPlusProjector := by
  rw [epsMinusProjector_eq_half_one_sub_eps, epsPlusProjector_eq_half_one_add_eps]
  simp [phaseFlip_apply_epsGen, sub_eq_add_neg, smul_add]

/-- The phase flip swaps the two `ε`-projectors in the opposite direction. -/
@[rep_depth krein, simp] theorem phaseFlip_apply_epsPlusProjector :
    phaseFlipAlg epsPlusProjector = epsMinusProjector := by
  rw [epsPlusProjector_eq_half_one_add_eps, epsMinusProjector_eq_half_one_sub_eps]
  simp [phaseFlip_apply_epsGen, sub_eq_add_neg, smul_add]

end SplitQ11Projectors
