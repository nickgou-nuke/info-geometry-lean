/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.PerjesConventions
import InfoGeometry.Topology.KleinGlideCovering

/-!
# Klein glide, Mobius sign line and pinorial transport

The base is the existing torus/Klein quotient. Fibers are the existing
complex four-dimensional twistor carrier. A universal-cover glide squares
to longitudinal translation. The two fiber-square signs are independent
choices. The minus choice requires an antiperiodic translation condition;
it is not an involution on an ordinary periodic product torus.

This is an explicit auxiliary Clifford-plane transport model, not a
classification of Pin bundles or an identification with all Lorentz twistor
transformations or physical spin holonomies.
-/

noncomputable section
namespace InfoGeometry.Twistor.KleinTwistorPinTransport

open PenroseIncidence PerjesConventions
open KleinBrillouinBase KleinBottleOrbitQuotient

def blockSwap : Twistor4 ≃ₗ[ℂ] Twistor4 := LinearEquiv.prodComm ℂ Spinor2 Spinor2

def pinPlus : Module.End ℂ Twistor4 := blockSwap.toLinearMap

def grading : Module.End ℂ Twistor4 := -incidenceSign.toLinearMap

def pinMinus : Module.End ℂ Twistor4 := Complex.I • pinPlus

@[simp] theorem blockSwap_apply (Z : Twistor4) : blockSwap Z = (Z.2, Z.1) := rfl
@[simp] theorem pinPlus_apply (Z : Twistor4) : pinPlus Z = (Z.2, Z.1) := rfl
@[simp] theorem grading_apply (Z : Twistor4) : grading Z = (Z.1, -Z.2) := by
  simp [grading, incidenceSign]

@[simp] theorem pinPlus_sq : pinPlus * pinPlus = 1 := by
  apply LinearMap.ext
  intro Z
  rfl

@[simp] theorem grading_sq : grading * grading = 1 := by
  apply LinearMap.ext
  intro Z
  simp [Module.End.mul_apply]

theorem grading_pinPlus_anticommute : grading * pinPlus = -(pinPlus * grading) := by
  apply LinearMap.ext
  intro Z
  simp [Module.End.mul_apply]

@[simp] theorem pinMinus_sq : pinMinus * pinMinus = -1 := by
  simp [pinMinus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    Complex.I_mul_I]

/-- Clifford action of the auxiliary Euclidean tangent plane. -/
def tangentClifford (v : Cover) : Module.End ℂ Twistor4 :=
  (v.1 : ℂ) • grading + (v.2 : ℂ) • pinPlus

theorem tangentClifford_sq (v : Cover) :
    tangentClifford v * tangentClifford v =
      ((v.1 ^ 2 + v.2 ^ 2 : ℝ) : ℂ) • (1 : Module.End ℂ Twistor4) := by
  apply LinearMap.ext
  intro Z
  apply Prod.ext <;> funext i <;>
    simp [tangentClifford, Module.End.mul_apply, smul_eq_mul] <;> ring

/-- The twisted Clifford adjoint covers the derivative of the base glide. -/
theorem pinPlus_covers_reflection (v : Cover) :
    -(pinPlus * tangentClifford v * pinPlus) = tangentClifford (v.1, -v.2) := by
  apply LinearMap.ext
  intro Z
  apply Prod.ext <;> funext i <;>
    simp [tangentClifford, Module.End.mul_apply, smul_eq_mul] <;> ring

/-- A square-minus lift uses inverse `-pinMinus`, not `pinMinus`. -/
theorem pinMinus_covers_reflection (v : Cover) :
    -(pinMinus * tangentClifford v * (-pinMinus)) = tangentClifford (v.1, -v.2) := by
  apply LinearMap.ext
  intro Z
  apply Prod.ext <;> funext i <;>
    simp [pinMinus, tangentClifford, Module.End.mul_apply, smul_eq_mul] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def liftedGlide (c : ℂ) (p : Cover × Twistor4) : Cover × Twistor4 :=
  (glide p.1, c • blockSwap p.2)

theorem liftedGlide_sq (c : ℂ) (p : Cover × Twistor4) :
    liftedGlide c (liftedGlide c p) = (tx p.1, (c * c) • p.2) := by
  simp [liftedGlide, glide_sq, smul_smul]
  rfl

/-- Equivariance relates different base points, not eigenvectors at one point. -/
def IsEquivariant (c : ℂ) (ψ : Cover → Twistor4) : Prop :=
  ∀ k, ψ (glide k) = c • blockSwap (ψ k)

theorem equivariant_translation (c : ℂ) (ψ : Cover → Twistor4)
    (hψ : IsEquivariant c ψ) (k : Cover) :
    ψ (tx k) = (c * c) • ψ k := by
  rw [← glide_sq, hψ, hψ]
  simp [smul_smul]
  rfl

theorem minus_lift_antiperiodic (ψ : Cover → Twistor4)
    (hψ : IsEquivariant Complex.I ψ) (k : Cover) : ψ (tx k) = -ψ k := by
  simpa using equivariant_translation Complex.I ψ hψ k

/-- A periodic product torus cannot silently absorb the minus fiber square. -/
theorem periodic_torus_minus_forces_zero (ψ : BrillouinTorus → Twistor4)
    (hψ : ∀ k, ψ (torusGlide k) = Complex.I • blockSwap (ψ k)) : ψ = 0 := by
  funext k
  have hh := hψ (torusGlide k)
  rw [torusGlide_involutive, hψ] at hh
  have hs (Z : Twistor4) : Complex.I • blockSwap (Complex.I • blockSwap Z) = -Z := by
    apply Prod.ext <;> funext i <;> simp [smul_smul]
  rw [hs] at hh
  have he : ψ k = -ψ k := hh
  have hz : (2 : ℂ) • ψ k = 0 := by
    calc (2 : ℂ) • ψ k = ψ k + ψ k := by module
         _ = -ψ k + ψ k := congrArg (fun x => x + ψ k) he
         _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

def commonSpinor : Twistor4 := (![1, 0], ![1, 0])

@[simp] theorem blockSwap_commonSpinor : blockSwap commonSpinor = commonSpinor := rfl

def quarterPhase : ℂ := Complex.exp (((Real.pi : ℂ) / 2) * Complex.I)

theorem quarterPhase_sq : quarterPhase * quarterPhase = -1 := by
  rw [quarterPhase, ← Complex.exp_add]
  have h : ((Real.pi : ℂ) / 2) * Complex.I + ((Real.pi : ℂ) / 2) * Complex.I =
      (Real.pi : ℂ) * Complex.I := by ring
  rw [h, Complex.exp_pi_mul_I]

/-- A nonzero antiperiodic section on the universal cover. -/
def minusSection (k : Cover) : Twistor4 :=
  Complex.exp (((k.1 : ℂ) / 2) * Complex.I) • commonSpinor

theorem minusSection_equivariant : IsEquivariant quarterPhase minusSection := by
  intro k
  have he : (((k.1 + Real.pi : ℝ) : ℂ) / 2) * Complex.I =
      (((Real.pi : ℂ) / 2) * Complex.I) + (((k.1 : ℂ) / 2) * Complex.I) := by
    push_cast
    ring
  simp only [minusSection, glide, he, Complex.exp_add, quarterPhase,
    map_smul, blockSwap_commonSpinor, smul_smul]

theorem minusSection_translation (k : Cover) : minusSection (tx k) = -minusSection k := by
  simpa [quarterPhase_sq] using equivariant_translation quarterPhase minusSection
    minusSection_equivariant k

theorem minusSection_transverse_periodic (k : Cover) : minusSection (ty k) = minusSection k := rfl

theorem minusSection_nonzero : minusSection ≠ 0 := by
  intro h
  have h0 := congrArg (fun ψ : Cover → Twistor4 => (ψ (0, 0)).1 0) h
  norm_num [minusSection, commonSpinor] at h0

def torusLift (p : BrillouinTorus × Twistor4) : BrillouinTorus × Twistor4 :=
  (torusGlide p.1, blockSwap p.2)

theorem torusLift_involutive : Function.Involutive torusLift := by
  rintro ⟨k, Z⟩
  change (torusGlide (torusGlide k), Z) = (k, Z)
  rw [torusGlide_involutive k]

def twistedSetoid : Setoid (BrillouinTorus × Twistor4) where
  r p q := q = p ∨ q = torusLift p
  iseqv := by
    constructor
    · intro p; exact Or.inl rfl
    · intro p q h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right; rw [h, torusLift_involutive]
    · intro p q r hpq hqr
      rcases hpq with rfl | hpq
      · exact hqr
      · rcases hqr with rfl | hqr
        · exact Or.inr hpq
        · left; rw [hqr, hpq, torusLift_involutive]

abbrev TwistedTotalSpace := Quotient twistedSetoid

/-- Projection to the existing Klein quotient, not a renamed scalar base. -/
def twistedProjection : TwistedTotalSpace → KleinBrillouinQuotient :=
  Quotient.lift (fun p => quotientMap p.1) (by
    intro p q h
    rcases h with rfl | h
    · rfl
    · rw [h]
      exact (quotientMap_glide p.1).symm)

def signLine (v : Spinor2) : Twistor4 := (v, -v)

/-- The minus eigenline has the Mobius transition sign on a single glide. -/
theorem signLine_glide (k : BrillouinTorus) (v : Spinor2) :
    Quotient.mk twistedSetoid (torusGlide k, signLine (-v)) =
      Quotient.mk twistedSetoid (k, signLine v) := by
  apply Quotient.sound
  right
  change (k, signLine v) = (torusGlide (torusGlide k), blockSwap (signLine (-v)))
  rw [torusGlide_involutive k]
  simp [signLine]

/-- Spin rotations of the auxiliary plane remain distinct from reflection. -/
def spinRotor (θ : ℝ) : Module.End ℂ Twistor4 :=
  (Real.cos (θ / 2) : ℂ) • 1 + (Real.sin (θ / 2) : ℂ) • (grading * pinPlus)

theorem spinRotor_two_pi : spinRotor (2 * Real.pi) = -1 := by
  simp [spinRotor, neg_smul, Algebra.smul_def]

theorem spinRotor_four_pi : spinRotor (4 * Real.pi) = 1 := by
  have h : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  simp [spinRotor, h]

end InfoGeometry.Twistor.KleinTwistorPinTransport
