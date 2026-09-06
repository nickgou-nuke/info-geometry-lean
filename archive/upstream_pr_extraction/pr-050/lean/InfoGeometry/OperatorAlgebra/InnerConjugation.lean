import Mathlib
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR
import InfoGeometry.OperatorAlgebra.ThreeZ2OperatorGradings
import InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity

/-!
# Inner operator geometry

Conjugation by a unit is the native algebraic replacement for an analytic
flow parameter.  The construction is entirely internal to an associative
ring and therefore applies to noncommutative operator carriers.
-/

namespace InfoGeometry.OperatorAlgebra

section

variable {A : Type*} [Ring A]

def innerConjugation (u : Aˣ) (x : A) : A :=
  (u : A) * x * (↑(u⁻¹) : A)

def innerConjugationRingEquiv (u : Aˣ) : A ≃+* A :=
  { toFun := innerConjugation u
    invFun := innerConjugation (u⁻¹)
    left_inv := by
      intro x
      dsimp [innerConjugation]
      simp [mul_assoc]
    right_inv := by
      intro x
      dsimp [innerConjugation]
      simp [mul_assoc]
    map_add' := by
      intro x y
      dsimp [innerConjugation]
      simp only [add_mul, mul_add]
    map_mul' := by
      intro x y
      dsimp [innerConjugation]
      simp [mul_assoc] }

@[simp] theorem innerConjugationRingEquiv_apply
    (u : Aˣ) (x : A) :
    innerConjugationRingEquiv u x = innerConjugation u x := rfl

theorem innerConjugation_map_quadraticCommutator
    (u : Aˣ) (x y : A) :
    innerConjugationRingEquiv u (x * y - y * x) =
      innerConjugationRingEquiv u x *
          innerConjugationRingEquiv u y -
        innerConjugationRingEquiv u y *
          innerConjugationRingEquiv u x := by
  rw [map_sub, map_mul, map_mul]

theorem innerConjugation_map_grandCanonicalOperator
    (u : Aˣ) (β H μ N μχ Q : A) :
    innerConjugationRingEquiv u (grandCanonicalOperator β H μ N μχ Q) =
      grandCanonicalOperator
        (innerConjugationRingEquiv u β)
        (innerConjugationRingEquiv u H)
        (innerConjugationRingEquiv u μ)
        (innerConjugationRingEquiv u N)
        (innerConjugationRingEquiv u μχ)
        (innerConjugationRingEquiv u Q) := by
  exact InfoGeometry.OperatorAlgebra.RingHom.map_grandCanonicalOperator
    (innerConjugationRingEquiv u).toRingHom β H μ N μχ Q

theorem innerConjugation_map_thermalAnticommutator
    (u : Aˣ) (x y : A) :
    innerConjugationRingEquiv u (thermalAnticommutator x y) =
      thermalAnticommutator
        (innerConjugationRingEquiv u x)
        (innerConjugationRingEquiv u y) := by
  exact thermalAnticommutator_map (innerConjugationRingEquiv u).toRingHom x y

theorem innerConjugation_preserves_thermal_bogoliubov_car
    [Algebra ℂ A] (u : Aˣ) (a c b d : A) (p q : ℂ)
    (hpq : p ^ 2 + q ^ 2 = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    thermalAnticommutator
        (thermalAnnihilator
          (innerConjugation u a) (innerConjugation u d) p q)
        (thermalCreator
          (innerConjugation u c) (innerConjugation u b) p q) = 1 := by
  have h := thermal_bogoliubov_car_preserved
    (innerConjugationRingEquiv u a)
    (innerConjugationRingEquiv u c)
    (innerConjugationRingEquiv u b)
    (innerConjugationRingEquiv u d) p q hpq
    (by
      rw [← innerConjugation_map_thermalAnticommutator]
      simpa only [map_one, innerConjugationRingEquiv_apply] using
        congrArg (innerConjugationRingEquiv u) hac)
    (by
      rw [← innerConjugation_map_thermalAnticommutator]
      simpa only [map_one, innerConjugationRingEquiv_apply] using
        congrArg (innerConjugationRingEquiv u) hbd)
    (by
      rw [← innerConjugation_map_thermalAnticommutator]
      simpa only [map_zero, innerConjugationRingEquiv_apply] using
        congrArg (innerConjugationRingEquiv u) hab)
    (by
      rw [← innerConjugation_map_thermalAnticommutator]
      simpa only [map_zero, innerConjugationRingEquiv_apply] using
        congrArg (innerConjugationRingEquiv u) hcd)
  simpa [thermalAnnihilator, thermalCreator, innerConjugationRingEquiv,
    innerConjugation] using h

theorem innerConjugation_preserves_conjugation_of_commutes
    (u : Aˣ) (g x : A)
    (h : (u : A) * g = g * (u : A)) :
    innerConjugation u (g * x * g) =
      g * innerConjugation u x * g := by
  have h_inv : (↑(u⁻¹) : A) * g = g * (↑(u⁻¹) : A) := by
    calc
      (↑(u⁻¹) : A) * g =
          (↑(u⁻¹) : A) * (g * (u : A)) * (↑(u⁻¹) : A) := by
            simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = (↑(u⁻¹) : A) * ((u : A) * g) * (↑(u⁻¹) : A) := by rw [← h]
      _ = g * (↑(u⁻¹) : A) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
  dsimp [innerConjugation]
  calc
    (u : A) * (g * x * g) * (↑(u⁻¹) : A) =
        ((u : A) * g) * x * (g * (↑(u⁻¹) : A)) := by
          simp only [mul_assoc]
    _ = (g * (u : A)) * x * ((↑(u⁻¹) : A) * g) := by rw [h, h_inv]
    _ = g * ((u : A) * x * (↑(u⁻¹) : A)) * g := by
          simp only [mul_assoc]

theorem innerConjugation_preserves_hasZ2Parity
    (u : Aˣ) (g x : A) (ε : Fin 2)
    (hcomm : (u : A) * g = g * (u : A))
    (hx : hasZ2Parity g x ε) :
    hasZ2Parity g (innerConjugation u x) ε := by
  simp only [hasZ2Parity] at hx ⊢
  change g * innerConjugation u x * g = _
  rw [← innerConjugation_preserves_conjugation_of_commutes u g x hcomm]
  have hx' : g * x * g = if ε = 0 then x else -x := by
    simpa [gradingConjugation] using hx
  rw [hx']
  simp [innerConjugation]

theorem innerConjugation_preserves_triZ2Parity
    (u : Aˣ) (gW gχ gN x : A) (εW εχ εN : Fin 2)
    (hW : (u : A) * gW = gW * (u : A))
    (hχ : (u : A) * gχ = gχ * (u : A))
    (hN : (u : A) * gN = gN * (u : A))
    (hx : triZ2Parity gW gχ gN x εW εχ εN) :
    triZ2Parity gW gχ gN (innerConjugation u x) εW εχ εN := by
  rcases hx with ⟨hxW, hxχ, hxN⟩
  exact ⟨innerConjugation_preserves_hasZ2Parity u gW x εW hW hxW,
    innerConjugation_preserves_hasZ2Parity u gχ x εχ hχ hxχ,
    innerConjugation_preserves_hasZ2Parity u gN x εN hN hxN⟩

def innerConjugationNat (u : Aˣ) (n : ℕ) : A ≃+* A :=
  innerConjugationRingEquiv (u ^ n)

theorem unit_pow_commutes
    (u : Aˣ) (g : A)
    (h : (u : A) * g = g * (u : A)) (n : ℕ) :
    (↑(u ^ n) : A) * g = g * (↑(u ^ n) : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, Units.val_mul]
      have ih' : (u : A) ^ n * g = g * (u : A) ^ n := by
        simpa using ih
      calc
        (u : A) ^ n * (u : A) * g =
            (u : A) ^ n * (g * (u : A)) := by
              rw [mul_assoc, h, ← mul_assoc]
        _ = ((u : A) ^ n * g) * (u : A) := by simp [mul_assoc]
        _ = (g * (u : A) ^ n) * (u : A) := by rw [ih']
        _ = g * ((u : A) ^ n * (u : A)) := by simp [mul_assoc]

theorem innerConjugationNat_preserves_triZ2Parity
    (u : Aˣ) (gW gχ gN x : A) (n : ℕ) (εW εχ εN : Fin 2)
    (hW : (u : A) * gW = gW * (u : A))
    (hχ : (u : A) * gχ = gχ * (u : A))
    (hN : (u : A) * gN = gN * (u : A))
    (hx : triZ2Parity gW gχ gN x εW εχ εN) :
    triZ2Parity gW gχ gN (innerConjugationNat u n x) εW εχ εN := by
  exact innerConjugation_preserves_triZ2Parity (u ^ n) gW gχ gN x
    εW εχ εN (unit_pow_commutes u gW hW n)
    (unit_pow_commutes u gχ hχ n) (unit_pow_commutes u gN hN n) hx

theorem innerConjugationNat_zero (u : Aˣ) (x : A) :
    innerConjugationNat u 0 x = x := by
  simp [innerConjugationNat, innerConjugationRingEquiv, innerConjugation]

theorem innerConjugationNat_add (u : Aˣ) (m n : ℕ) (x : A) :
    innerConjugationNat u (m + n) x =
      innerConjugationNat u m (innerConjugationNat u n x) := by
  simp only [innerConjugationNat, pow_add]
  dsimp [innerConjugationRingEquiv, innerConjugation]
  simp [mul_assoc]

theorem innerConjugationNat_map_thermalAnticommutator
    (u : Aˣ) (n : ℕ) (x y : A) :
    innerConjugationNat u n (thermalAnticommutator x y) =
      thermalAnticommutator
        (innerConjugationNat u n x)
        (innerConjugationNat u n y) := by
  exact thermalAnticommutator_map (innerConjugationNat u n).toRingHom x y

theorem innerConjugationNat_map_quadraticCommutator
    (u : Aˣ) (n : ℕ) (x y : A) :
    innerConjugationNat u n (x * y - y * x) =
      innerConjugationNat u n x * innerConjugationNat u n y -
        innerConjugationNat u n y * innerConjugationNat u n x := by
  rw [map_sub, map_mul, map_mul]

end

end InfoGeometry.OperatorAlgebra
