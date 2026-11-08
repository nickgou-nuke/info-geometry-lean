/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentCartan

/-!
# Peirce realization of the Nambu--Gorkov algebra

An idempotent in an arbitrary associative ring determines the Cartan
reflection, its commutator direction, and its odd Peirce component. The
resulting polynomial identities are proved in the ring itself, with no matrix
coordinates or commutativity assumptions.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceNambuGorkov

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.IdempotentCartan

variable {A : Type*} [Ring A]

/-- The two algebraic generators associated with an idempotent and an
operator: the inner derivation direction and the odd Peirce component. -/
def diracPart (p a : A) : A := p * a - a * p

def massPart (p a : A) : A := oddPart p a

/-- The Clifford relations for two involutive reflections in an arbitrary
associative operator ring. The conclusions retain the ordered operator
product and require no matrix representation or commutative carrier. -/
theorem clifford_reflection_pair_relations {γ δ : A}
    (hγ : γ * γ = 1) (hδ : δ * δ = 1)
    (h_anticommute : γ * δ + δ * γ = 0) :
    γ * δ - δ * γ = 2 • (γ * δ) ∧
    (γ * δ) * (γ * δ) = -1 ∧
    δ * γ * δ = -γ := by
  have h_swap : δ * γ = -(γ * δ) :=
    eq_neg_of_add_eq_zero_right h_anticommute
  refine ⟨?_, ?_, ?_⟩
  · calc
      γ * δ - δ * γ = γ * δ - -(γ * δ) := by rw [h_swap]
      _ = γ * δ + γ * δ := sub_neg_eq_add _ _
      _ = 2 • (γ * δ) := by rw [two_nsmul]
  · calc
      (γ * δ) * (γ * δ) = γ * (δ * γ) * δ := by simp only [mul_assoc]
      _ = γ * (-(γ * δ)) * δ := by rw [h_swap]
      _ = -((γ * γ) * (δ * δ)) := by noncomm_ring
      _ = -(1 * 1) := by rw [hγ, hδ]
      _ = -1 := by simp
  · calc
      δ * γ * δ = (-(γ * δ)) * δ := by rw [h_swap]
      _ = -(γ * (δ * δ)) := by simp only [neg_mul, mul_assoc]
      _ = -γ := by rw [hδ, mul_one]

/-- Their sum is twice the forward Peirce corner. -/
theorem dirac_add_mass_eq_twice_forward_corner {p a : A} :
    diracPart p a + massPart p a = 2 • component10 p a := by
  simp only [diracPart, massPart, oddPart, component10, component01,
    complementIdempotent]
  noncomm_ring

/-- Opposite directed Peirce transitions have Lie and Jordan products related
by the Cartan reflection. The two amplitudes are independent, and all products
remain in the original associative operator algebra. -/
theorem directed_corner_lie_jordan_reflection {p a b : A}
    (hp : p * p = p) :
    (component10 p a * component01 p b - component01 p b * component10 p a) =
      reflection p * (component10 p a * component01 p b +
        component01 p b * component10 p a) ∧
    (component10 p a * component01 p b + component01 p b * component10 p a) =
      reflection p * (component10 p a * component01 p b -
        component01 p b * component10 p a) := by
  have hqp : (1 - p) * p = 0 := by noncomm_ring [hp]
  have hpq : p * (1 - p) = 0 := by noncomm_ring [hp]
  have huL : p * component10 p a = component10 p a := by
    simpa [component10, complementIdempotent, peirceCorner] using
      (peirceCorner_absorb_left (p := p) (q := 1 - p) (x := a) hp)
  have huR : component10 p a * p = 0 := by
    change (p * a * (1 - p)) * p = 0
    calc
      (p * a * (1 - p)) * p = p * a * ((1 - p) * p) := by noncomm_ring
      _ = 0 := by rw [hqp, mul_zero]
  have hvL : p * component01 p b = 0 := by
    change p * ((1 - p) * b * p) = 0
    calc
      p * ((1 - p) * b * p) = (p * (1 - p)) * b * p := by noncomm_ring
      _ = 0 := by rw [hpq, zero_mul, zero_mul]
  have hUVL : p * (component10 p a * component01 p b) =
      component10 p a * component01 p b := by
    rw [← mul_assoc, huL]
  have hVUL : p * (component01 p b * component10 p a) = 0 := by
    rw [← mul_assoc, hvL, zero_mul]
  have hFirst : reflection p * (component10 p a * component01 p b +
      component01 p b * component10 p a) =
        component10 p a * component01 p b - component01 p b * component10 p a := by
    unfold reflection
    rw [two_smul]
    noncomm_ring [hUVL, hVUL, hp]
  have hSecond : reflection p * (component10 p a * component01 p b -
      component01 p b * component10 p a) =
        component10 p a * component01 p b + component01 p b * component10 p a := by
    unfold reflection
    rw [two_smul]
    noncomm_ring [hUVL, hVUL, hp]
  exact ⟨hFirst.symm, hSecond.symm⟩

/-- A cyclic additive functional pairs the reflected Lie spin of two
independent directed Peirce amplitudes with twice their ordered forward/backward
product. This generalizes the finite matrix trace identity to arbitrary
associative operator rings equipped with a cyclic readout. -/
theorem cyclicFunctional_directed_corner_spin_pairing {S : Type*}
    [AddCommGroup S] (τ : A →+ S)
    (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    {p a b : A} (hp : p * p = p) :
    τ (reflection p *
        (component10 p a * component01 p b - component01 p b * component10 p a)) =
      2 • τ (component10 p a * component01 p b) := by
  have hSpin := (directed_corner_lie_jordan_reflection (p := p) (a := a) (b := b) hp).1
  calc
    τ (reflection p *
        (component10 p a * component01 p b - component01 p b * component10 p a)) =
        τ (reflection p * (reflection p *
          (component10 p a * component01 p b + component01 p b * component10 p a))) := by
            rw [hSpin]
    _ = τ ((reflection p * reflection p) *
        (component10 p a * component01 p b + component01 p b * component10 p a)) := by
          congr 1
          noncomm_ring
    _ = τ (component10 p a * component01 p b +
        component01 p b * component10 p a) := by
          rw [reflection_sq hp, one_mul]
    _ = τ (component10 p a * component01 p b) +
        τ (component01 p b * component10 p a) := by rw [map_add]
    _ = 2 • τ (component10 p a * component01 p b) := by
          rw [hτ (component01 p b) (component10 p a), two_nsmul]

/-- The Jordan mass and Lie spin of two opposite Peirce corners have the
expected diagonal compressions in any associative ring. -/
theorem directed_corner_mass_spin_compressions {p a b : A}
    (hp : p * p = p) :
    p * (component10 p a * component01 p b - component01 p b * component10 p a) * p =
        component10 p a * component01 p b ∧
    (1 - p) * (component10 p a * component01 p b - component01 p b * component10 p a) *
        (1 - p) = -(component01 p b * component10 p a) ∧
    p * (component10 p a * component01 p b + component01 p b * component10 p a) * p =
        component10 p a * component01 p b ∧
    (1 - p) * (component10 p a * component01 p b + component01 p b * component10 p a) *
        (1 - p) = component01 p b * component10 p a := by
  let q : A := 1 - p
  let u : A := p * a * q
  let v : A := q * b * p
  have hpq : p * q = 0 := by dsimp [q]; noncomm_ring [hp]
  have hqp : q * p = 0 := by dsimp [q]; noncomm_ring [hp]
  have hq : q * q = q := by dsimp [q]; noncomm_ring [hp]
  have hpu : p * u = u := by
    dsimp [u]
    calc
      p * (p * a * q) = (p * p) * a * q := by noncomm_ring
      _ = p * a * q := by rw [hp]
  have hup : u * p = 0 := by
    dsimp [u]
    calc
      (p * a * q) * p = p * a * (q * p) := by noncomm_ring
      _ = 0 := by rw [hqp]; simp
  have hpv : p * v = 0 := by
    dsimp [v]
    calc
      p * (q * b * p) = (p * q) * b * p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hvp : v * p = v := by
    dsimp [v]
    calc
      (q * b * p) * p = q * b * (p * p) := by noncomm_ring
      _ = q * b * p := by rw [hp]
  have hqu : q * u = 0 := by
    dsimp [u]
    calc
      q * (p * a * q) = (q * p) * a * q := by noncomm_ring
      _ = 0 := by rw [hqp]; simp
  have huq : u * q = u := by
    dsimp [u]
    calc
      (p * a * q) * q = p * a * (q * q) := by noncomm_ring
      _ = p * a * q := by rw [hq]
  have hqv : q * v = v := by
    dsimp [v]
    calc
      q * (q * b * p) = (q * q) * b * p := by noncomm_ring
      _ = q * b * p := by rw [hq]
  have hvq : v * q = 0 := by
    dsimp [v]
    calc
      (q * b * p) * q = q * b * (p * q) := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hpUVp : p * (u * v) * p = u * v := by
    calc
      p * (u * v) * p = (p * u) * (v * p) := by noncomm_ring
      _ = u * v := by rw [hpu, hvp]
  have hpVUp : p * (v * u) * p = 0 := by
    calc
      p * (v * u) * p = (p * v) * (u * p) := by noncomm_ring
      _ = 0 := by rw [hpv, hup]; simp
  have hqUVq : q * (u * v) * q = 0 := by
    calc
      q * (u * v) * q = (q * u) * (v * q) := by noncomm_ring
      _ = 0 := by rw [hqu, hvq]; simp
  have hqVUq : q * (v * u) * q = v * u := by
    calc
      q * (v * u) * q = (q * v) * (u * q) := by noncomm_ring
      _ = v * u := by rw [hqv, huq]
  change p * (u * v - v * u) * p = u * v ∧
    q * (u * v - v * u) * q = -(v * u) ∧
    p * (u * v + v * u) * p = u * v ∧
    q * (u * v + v * u) * q = v * u
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      p * (u * v - v * u) * p = p * (u * v) * p - p * (v * u) * p := by noncomm_ring
      _ = u * v := by rw [hpUVp, hpVUp]; simp
  · calc
      q * (u * v - v * u) * q = q * (u * v) * q - q * (v * u) * q := by noncomm_ring
      _ = -(v * u) := by rw [hqUVq, hqVUq]; simp
  · calc
      p * (u * v + v * u) * p = p * (u * v) * p + p * (v * u) * p := by noncomm_ring
      _ = u * v := by rw [hpUVp, hpVUp]; simp
  · calc
      q * (u * v + v * u) * q = q * (u * v) * q + q * (v * u) * q := by noncomm_ring
      _ = v * u := by rw [hqUVq, hqVUq]; simp

/-- Any cyclic additive readout sees opposite spin source and sink values,
equal mass on the two Peirce sheets, and twice the forward ordered product as
the total mass readout. -/
theorem cyclicFunctional_peirce_corner_source_sink {S : Type*}
    [AddCommGroup S] (τ : A →+ S)
    (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    {p a b : A} (hp : p * p = p) :
    τ (p * (component10 p a * component01 p b - component01 p b * component10 p a) * p) +
      τ ((1 - p) * (component10 p a * component01 p b - component01 p b * component10 p a) *
        (1 - p)) = 0 ∧
    τ (p * (component10 p a * component01 p b + component01 p b * component10 p a) * p) =
      τ ((1 - p) * (component10 p a * component01 p b + component01 p b * component10 p a) *
        (1 - p)) ∧
    τ (component10 p a * component01 p b + component01 p b * component10 p a) =
      2 • τ (component10 p a * component01 p b) := by
  rcases directed_corner_mass_spin_compressions hp with
    ⟨hSpinP, hSpinQ, hMassP, hMassQ⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hSpinP, hSpinQ, map_neg, hτ (component10 p a) (component01 p b)]
    simp
  · rw [hMassP, hMassQ, hτ (component10 p a) (component01 p b)]
  · rw [map_add, hτ (component01 p b) (component10 p a), two_nsmul]

/-- For a square-zero operator pair, the Lie and Jordan combinations have the
same square, and the Lie combination anticommutes with their sum. This is the
generic operator algebra behind the transcript's spin/mass identities. -/
theorem squareZeroPair_lie_jordan_relations {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (u * v - v * u) * (u * v - v * u) =
      (u * v + v * u) * (u * v + v * u) ∧
    (u * v - v * u) * (u + v) + (u + v) * (u * v - v * u) = 0 := by
  have huu : u * (u * v) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvv : v * (v * u) = 0 := by rw [← mul_assoc, hv, zero_mul]
  have huv : u * (v * v) = 0 := by rw [hv, mul_zero]
  have hvu : v * (u * u) = 0 := by rw [hu, mul_zero]
  constructor
  · noncomm_ring [huu, hvv]
  · noncomm_ring [huu, hvv, huv, hvu]

/-- The mass and spin tetraktys of any square-zero operator pair. The
precession formulas hold in the associative operator ring without a
reflexivity or finite-dimensionality assumption. -/
theorem squareZeroPair_spin_mass_precession {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (u * v + v * u) * (u + v) = (u + v) * (u * v + v * u) ∧
    (u * v + v * u) * (u - v) = (u - v) * (u * v + v * u) ∧
    (u * v - v * u) * (u + v) - (u + v) * (u * v - v * u) =
      2 • ((u * v + v * u) * (u - v)) ∧
    (u * v - v * u) * (u - v) - (u - v) * (u * v - v * u) =
      2 • ((u * v + v * u) * (u + v)) := by
  have huu : u * (u * v) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvv : v * (v * u) = 0 := by rw [← mul_assoc, hv, zero_mul]
  have huv : u * (v * v) = 0 := by rw [hv, mul_zero]
  have hvu : v * (u * u) = 0 := by rw [hu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · noncomm_ring [huu, hvv, huv, hvu]
  · noncomm_ring [huu, hvv, huv, hvu]
  · rw [two_nsmul]
    noncomm_ring [huu, hvv, huv, hvu]
  · rw [two_nsmul]
    noncomm_ring [huu, hvv, huv, hvu]

/-- Independent forward and backward Peirce amplitudes have square-zero
directed sectors, while their mixed square is an even operator. The amplitudes
need not arise from the same element of the noncommutative algebra. -/
theorem independent_directed_corner_mass_sector {p a b : A}
    (hp : p * p = p) :
    component10 p a * component10 p a = 0 ∧
    component01 p b * component01 p b = 0 ∧
    (component10 p a + component01 p b) *
        (component10 p a + component01 p b) =
      component10 p a * component01 p b + component01 p b * component10 p a ∧
    p * (component10 p a * component01 p b + component01 p b * component10 p a) =
      (component10 p a * component01 p b + component01 p b * component10 p a) * p := by
  have ha := corners_square_zero hp a
  have hb := corners_square_zero hp b
  refine ⟨ha.1, hb.2, ?_, ?_⟩
  · noncomm_ring [ha.1, hb.2]
  · have huL : p * component10 p a = component10 p a := by
      simp only [component10, complementIdempotent]
      noncomm_ring [hp, idempotent_mul_nested p hp]
    have huR : component10 p a * p = 0 := by
      simp only [component10, complementIdempotent]
      noncomm_ring [hp, idempotent_mul_nested p hp]
    have hvL : p * component01 p b = 0 := by
      simp only [component01, complementIdempotent]
      noncomm_ring [hp, idempotent_mul_nested p hp]
    have hvR : component01 p b * p = component01 p b := by
      simp only [component01, complementIdempotent]
      noncomm_ring [hp, idempotent_mul_nested p hp]
    have hleft : p * (component10 p a * component01 p b +
        component01 p b * component10 p a) =
        component10 p a * component01 p b := by
      calc
        _ = (p * component10 p a) * component01 p b +
            (p * component01 p b) * component10 p a := by noncomm_ring
        _ = _ := by rw [huL, hvL]; noncomm_ring
    have hright : (component10 p a * component01 p b +
        component01 p b * component10 p a) * p =
        component10 p a * component01 p b := by
      calc
        _ = component10 p a * (component01 p b * p) +
            component01 p b * (component10 p a * p) := by noncomm_ring
        _ = _ := by rw [hvR, huR]; noncomm_ring
    exact hleft.trans hright.symm

/-- The sum of independent directed Peirce amplitudes is odd under the
idempotent's Cartan reflection. -/
theorem independent_directed_corner_sum_is_odd {p a b : A}
    (hp : p * p = p) :
    reflection p * (component10 p a + component01 p b) +
        (component10 p a + component01 p b) * reflection p = 0 := by
  simp only [reflection, two_nsmul, add_mul, mul_add,
    component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- A reflexive square-zero pair produces an idempotent Jordan mass operator
and a tripotent Lie spin operator. Reflexivity is an explicit hypothesis; the
conclusion is not asserted for arbitrary square-zero pairs. -/
theorem reflexiveSquareZeroPair_tripotency {u v : A}
    (hu : u * u = 0) (hv : v * v = 0)
    (huvu : u * v * u = u) (hvuv : v * u * v = v) :
    (u * v - v * u) * (u * v - v * u) = u * v + v * u ∧
    (u * v + v * u) * (u * v + v * u) = u * v + v * u ∧
    (u * v - v * u) * ((u * v - v * u) * (u * v - v * u)) =
      u * v - v * u := by
  have huvuv : (u * v) * (u * v) = u * v := by
    calc
      (u * v) * (u * v) = (u * v * u) * v := by noncomm_ring
      _ = u * v := by rw [huvu]
  have hvuvu : (v * u) * (v * u) = v * u := by
    calc
      (v * u) * (v * u) = (v * u * v) * u := by noncomm_ring
      _ = v * u := by rw [hvuv]
  have huvvu : (u * v) * (v * u) = 0 := by
    calc
      (u * v) * (v * u) = u * (v * v) * u := by noncomm_ring
      _ = 0 := by rw [hv, mul_zero, zero_mul]
  have hvuuv : (v * u) * (u * v) = 0 := by
    calc
      (v * u) * (u * v) = v * (u * u) * v := by noncomm_ring
      _ = 0 := by rw [hu, mul_zero, zero_mul]
  have hSpinSq :
      (u * v - v * u) * (u * v - v * u) = u * v + v * u := by
    noncomm_ring [huvuv, hvuvu, huvvu, hvuuv]
  have hMassSq :
      (u * v + v * u) * (u * v + v * u) = u * v + v * u := by
    noncomm_ring [huvuv, hvuvu, huvvu, hvuuv]
  have hSpinMass :
      (u * v - v * u) * (u * v + v * u) = u * v - v * u := by
    noncomm_ring [huvuv, hvuvu, huvvu, hvuuv]
  refine ⟨hSpinSq, hMassSq, ?_⟩
  rw [hSpinSq]
  exact hSpinMass

/-- The reflexive square-zero pair has an operator-valued vacuum complement.
Adding that complement to either the electron sum or the spin difference gives
an involution. The final identity is the exact propagator factorization for
any central operator parameter `z`. -/
theorem reflexivePair_vacuum_completion {u v z : A}
    (hu : u * u = 0) (hv : v * v = 0)
    (huvu : u * v * u = u) (hvuv : v * u * v = v)
    (hz : ∀ x : A, z * x = x * z) :
    let mass := u * v + v * u
    let electron := u + v
    let spin := u * v - v * u
    (1 - mass) * (1 - mass) = 1 - mass ∧
    ((1 - mass) + electron) * ((1 - mass) + electron) = 1 ∧
    ((1 - mass) + spin) * ((1 - mass) + spin) = 1 ∧
    (z - electron) * (z + electron) =
      z * z * (1 - mass) + (z * z - 1) * mass := by
  dsimp only
  have huvuv : (u * v) * (u * v) = u * v := by
    calc
      (u * v) * (u * v) = (u * v * u) * v := by noncomm_ring
      _ = u * v := by rw [huvu]
  have hvuvu : (v * u) * (v * u) = v * u := by
    calc
      (v * u) * (v * u) = (v * u * v) * u := by noncomm_ring
      _ = v * u := by rw [hvuv]
  have huvvu : (u * v) * (v * u) = 0 := by
    calc
      (u * v) * (v * u) = u * (v * v) * u := by noncomm_ring
      _ = 0 := by rw [hv, mul_zero, zero_mul]
  have hvuuv : (v * u) * (u * v) = 0 := by
    calc
      (v * u) * (u * v) = v * (u * u) * v := by noncomm_ring
      _ = 0 := by rw [hu, mul_zero, zero_mul]
  have hee : (u + v) * (u + v) = u * v + v * u := by
    noncomm_ring [hu, hv]
  have hmm : (u * v + v * u) * (u * v + v * u) = u * v + v * u := by
    noncomm_ring [huvuv, hvuvu, huvvu, hvuuv]
  have huuv : u * (u * v) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have huvv : u * (v * v) = 0 := by rw [hv, mul_zero]
  have hvuu : v * (u * u) = 0 := by rw [hu, mul_zero]
  have hvvu : v * (v * u) = 0 := by rw [← mul_assoc, hv, zero_mul]
  have huvu' : u * (v * u) = u := by rw [← mul_assoc, huvu]
  have hvuv' : v * (u * v) = v := by rw [← mul_assoc, hvuv]
  have hem : (u + v) * (u * v + v * u) = u + v := by
    noncomm_ring [huuv, huvv, hvuu, hvvu, huvu', hvuv']
  have hme : (u * v + v * u) * (u + v) = u + v := by
    noncomm_ring [huuv, huvv, hvuu, hvvu, huvu', hvuv']
  have hsm : (u * v - v * u) * (u * v + v * u) = u * v - v * u := by
    noncomm_ring [huvuv, hvuvu, huvvu, hvuuv]
  have hms : (u * v + v * u) * (u * v - v * u) = u * v - v * u := by
    noncomm_ring [huvuv, hvuvu, huvvu, hvuuv]
  have hq : (1 - (u * v + v * u)) * (1 - (u * v + v * u)) =
      1 - (u * v + v * u) := by
    calc
      _ = 1 - (u * v + v * u) - (u * v + v * u) +
          (u * v + v * u) * (u * v + v * u) := by noncomm_ring
      _ = 1 - (u * v + v * u) := by rw [hmm]; abel
  have hqe : (1 - (u * v + v * u)) * (u + v) = 0 := by
    calc
      _ = (u + v) - (u * v + v * u) * (u + v) := by noncomm_ring
      _ = 0 := by rw [hme]; exact sub_self _
  have heq : (u + v) * (1 - (u * v + v * u)) = 0 := by
    calc
      _ = (u + v) - (u + v) * (u * v + v * u) := by noncomm_ring
      _ = 0 := by rw [hem]; exact sub_self _
  have hqs : (1 - (u * v + v * u)) * (u * v - v * u) = 0 := by
    calc
      _ = (u * v - v * u) - (u * v + v * u) * (u * v - v * u) := by noncomm_ring
      _ = 0 := by rw [hms]; exact sub_self _
  have hsq : (u * v - v * u) * (1 - (u * v + v * u)) = 0 := by
    calc
      _ = (u * v - v * u) - (u * v - v * u) * (u * v + v * u) := by noncomm_ring
      _ = 0 := by rw [hsm]; exact sub_self _
  have hDirac :
      ((1 - (u * v + v * u)) + (u + v)) *
        ((1 - (u * v + v * u)) + (u + v)) = 1 := by
    calc
      _ = (1 - (u * v + v * u)) * (1 - (u * v + v * u)) +
          (1 - (u * v + v * u)) * (u + v) +
          (u + v) * (1 - (u * v + v * u)) + (u + v) * (u + v) := by
        noncomm_ring
      _ = (1 - (u * v + v * u)) + (u * v + v * u) := by
        rw [hq, hqe, heq, hee]
        simp
      _ = 1 := by noncomm_ring
  have hSpin :
      ((1 - (u * v + v * u)) + (u * v - v * u)) *
        ((1 - (u * v + v * u)) + (u * v - v * u)) = 1 := by
    calc
      _ = (1 - (u * v + v * u)) * (1 - (u * v + v * u)) +
          (1 - (u * v + v * u)) * (u * v - v * u) +
          (u * v - v * u) * (1 - (u * v + v * u)) +
          (u * v - v * u) * (u * v - v * u) := by noncomm_ring
      _ = (1 - (u * v + v * u)) + (u * v + v * u) := by
        rw [hq, hqs, hsq,
          (reflexiveSquareZeroPair_tripotency hu hv huvu hvuv).1]
        simp
      _ = 1 := by noncomm_ring
  have hProp :
      (z - (u + v)) * (z + (u + v)) =
        z * z * (1 - (u * v + v * u)) +
          (z * z - 1) * (u * v + v * u) := by
    have hze := hz (u + v)
    calc
      (z - (u + v)) * (z + (u + v)) =
          z * z - (u + v) * (u + v) := by
        calc
          _ = z * z + z * (u + v) - (u + v) * z - (u + v) * (u + v) := by
            noncomm_ring
          _ = z * z - (u + v) * (u + v) := by rw [hze]; abel
      _ = z * z - (u * v + v * u) := by rw [hee]
      _ = z * z * (1 - (u * v + v * u)) +
          (z * z - 1) * (u * v + v * u) := by
        symm
        calc
          _ = z * z - z * z * (u * v + v * u) +
              (z * z * (u * v + v * u) - (u * v + v * u)) := by noncomm_ring
          _ = z * z - (u * v + v * u) := by abel
  exact ⟨hq, hDirac, hSpin, hProp⟩

/-- Peirce decomposition gives the complete characteristic-free Nambu--Gorkov
relations: unit Cartan grading, oddness of both generators, mutual
anticommutation, opposite squares, and a square-zero forward supercharge. -/
theorem idempotent_peirce_nambu_gorkov_relations {p a : A}
    (hp : p * p = p) :
    reflection p * reflection p = 1 ∧
    reflection p * diracPart p a + diracPart p a * reflection p = 0 ∧
    reflection p * massPart p a + massPart p a * reflection p = 0 ∧
    diracPart p a * massPart p a + massPart p a * diracPart p a = 0 ∧
    diracPart p a * diracPart p a + massPart p a * massPart p a = 0 ∧
    (diracPart p a + massPart p a) * (diracPart p a + massPart p a) = 0 ∧
    diracPart p a + massPart p a = 2 • component10 p a := by
  have hDodd := (commutator_is_odd hp a).2
  have hModd := (reflection_parities hp a).2
  have hD : diracPart p a = component10 p a - component01 p a := by
    simp only [diracPart, component10, component01, complementIdempotent]
    noncomm_ring [hp, idempotent_mul_nested p hp]
  have hM : massPart p a = component10 p a + component01 p a := rfl
  have h10 := corners_square_zero hp a |>.1
  have h01 := corners_square_zero hp a |>.2
  have hDM : diracPart p a * massPart p a + massPart p a * diracPart p a = 0 := by
    rw [hD, hM]
    noncomm_ring [h10, h01]
  have hDsq : diracPart p a * diracPart p a + massPart p a * massPart p a = 0 := by
    rw [hD, hM]
    noncomm_ring [h10, h01]
  have hQ : diracPart p a + massPart p a = 2 • component10 p a :=
    dirac_add_mass_eq_twice_forward_corner
  refine ⟨reflection_sq hp, hDodd, hModd, hDM, hDsq, ?_, hQ⟩
  rw [hQ, two_nsmul]
  noncomm_ring [h10]

end InfoGeometry.OperatorAlgebra.PeirceNambuGorkov
