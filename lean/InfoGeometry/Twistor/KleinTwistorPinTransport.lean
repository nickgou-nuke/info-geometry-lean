import InfoGeometry.Twistor.PerjesConventions
import InfoGeometry.Topology.KleinGlideCovering

/-!
# Klein glide, Mobius sign line and pinorial transport

The base is the existing torus/Klein quotient, not a replacement scalar
model. The fibers are the existing complex four-dimensional twistor carrier.
On the universal cover the glide squares to translation, not to identity.
The two fiber signs are separate explicit choices. The minus choice cannot
act involutively on an ordinary periodic product torus: its translation
boundary condition is antiperiodic. This is a flat equivariant transport
model, not a classification of Pin bundles or an explanation of all spin.
-/

noncomputable section
namespace InfoGeometry.Twistor.KleinTwistorPinTransport

open PenroseIncidence PerjesConventions
open KleinBrillouinBase KleinBottleOrbitQuotient

/-- Exchange of the two native spinor blocks. -/
def blockSwap : Twistor4 ≃ₗ[ℂ] Twistor4 := LinearEquiv.prodComm ℂ Spinor2 Spinor2

/-- The square-plus fiber lift. -/
def pinPlus : Module.End ℂ Twistor4 := blockSwap.toLinearMap

/-- The independent block grading, not the scalar imaginary unit. -/
def grading : Module.End ℂ Twistor4 := -incidenceSignChange.toLinearMap

/-- A square-minus lift on the same complex carrier. -/
def pinMinus : Module.End ℂ Twistor4 := Complex.I • pinPlus

@[simp] theorem blockSwap_apply (Z : Twistor4) : blockSwap Z = (Z.2, Z.1) := rfl
@[simp] theorem pinPlus_apply (Z : Twistor4) : pinPlus Z = (Z.2, Z.1) := rfl
@[simp] theorem grading_apply (Z : Twistor4) : grading Z = (Z.1, -Z.2) := by
  simp [grading, incidenceSignChange]

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

/-- Clifford action for the Euclidean tangent plane. -/
def tangentClifford (v : Cover) : Module.End ℂ Twistor4 :=
  (v.1 : ℂ) • grading + (v.2 : ℂ) • pinPlus

theorem tangentClifford_sq (v : Cover) :
    tangentClifford v * tangentClifford v =
      ((v.1 ^ 2 + v.2 ^ 2 : ℝ) : ℂ) • (1 : Module.End ℂ Twistor4) := by
  apply LinearMap.ext
  intro Z
  apply Prod.ext <;> funext i <;>
    simp [tangentClifford, Module.End.mul_apply, smul_eq_mul] <;> ring

/-- Twisted Clifford adjoint covers the derivative of the actual base glide. -/
theorem pinPlus_covers_reflection (v : Cover) :
    -(pinPlus * tangentClifford v * pinPlus) = tangentClifford (v.1, -v.2) := by
  apply LinearMap.ext
  intro Z
  apply Prod.ext <;> funext i <;>
    simp [tangentClifford, Module.End.mul_apply, smul_eq_mul] <;> ring

/-- Same base reflection with inverse `-pinMinus`, not `pinMinus`. -/
theorem pinMinus_covers_reflection (v : Cover) :
    -(pinMinus * tangentClifford v * (-pinMinus)) = tangentClifford (v.1, -v.2) := by
  rw [pinMinus, pinMinus]
  simpa [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    Complex.I_mul_I] using pinPlus_covers_reflection v

/-- The literal lifted glide on the universal cover and native twistor fiber. -/
def liftedGlide (c : ℂ) (p : Cover × Twistor4) : Cover × Twistor4 :=
  (glide p.1, c • blockSwap p.2)

theorem liftedGlide_sq (c : ℂ) (p : Cover × Twistor4) :
    liftedGlide c (liftedGlide c p) = (tx p.1, (c * c) • p.2) := by
  simp [liftedGlide, glide_sq, smul_smul]

/-- Boundary equivariance is between different base points, not an eigenvector equation. -/
def IsEquivariant (c : ℂ) (ψ : Cover → Twistor4) : Prop :=
  ∀ k, ψ (glide k) = c • blockSwap (ψ k)

theorem equivariant_translation (c : ℂ) (ψ : Cover → Twistor4)
    (hψ : IsEquivariant c ψ) (k : Cover) :
    ψ (tx k) = (c * c) • ψ k := by
  rw [← glide_sq, hψ, hψ]
  simp [smul_smul]

theorem minus_lift_antiperiodic (ψ : Cover → Twistor4)
    (hψ : IsEquivariant Complex.I ψ) (k : Cover) : ψ (tx k) = -ψ k := by
  simpa using equivariant_translation Complex.I ψ hψ k

/-- A minus lift cannot be imposed on a periodic product torus without killing the field. -/
theorem periodic_torus_minus_forces_zero (ψ : BrillouinTorus → Twistor4)
    (hψ : ∀ k, ψ (torusGlide k) = Complex.I • blockSwap (ψ k)) : ψ = 0 := by
  funext k
  have hh := hψ (torusGlide k)
  rw [torusGlide_involutive, hψ] at hh
  have he : ψ k = -ψ k := by simpa [smul_smul] using hh
  have hz : (2 : ℂ) • ψ k = 0 := by
    calc (2 : ℂ) • ψ k = ψ k + ψ k := by module
         _ = 0 := by rw [he]; simp
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- A nonzero common-block vector supplies an equivariant test section. -/
def commonSpinor : Twistor4 := (![1, 0], ![1, 0])

@[simp] theorem blockSwap_commonSpinor : blockSwap commonSpinor = commonSpinor := rfl

def quarterPhase : ℂ := Complex.exp (((Real.pi : ℂ) / 2) * Complex.I)

theorem quarterPhase_sq : quarterPhase * quarterPhase = -1 := by
  rw [quarterPhase, ← Complex.exp_add]
  convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring

/-- A genuine nonzero antiperiodic section on the universal cover. -/
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

theorem minusSection_nonzero : minusSection ≠ 0 := by
  intro h
  have h0 := congrArg (fun ψ : Cover → Twistor4 => (ψ (0, 0)).1 0) h
  norm_num [minusSection, commonSpinor] at h0

/-- An involutive lift to the actual two-sheeted torus covering. -/
def torusLift (p : BrillouinTorus × Twistor4) : BrillouinTorus × Twistor4 :=
  (torusGlide p.1, blockSwap p.2)

theorem torusLift_involutive : Function.Involutive torusLift := by
  intro p
  simp [torusLift, torusGlide_involutive]

/-- Orbit relation for the associated square-plus transport carrier. -/
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

/-- Projection lands in the existing Klein quotient, not a renamed base set. -/
def twistedProjection : TwistedTotalSpace → KleinBrillouinQuotient :=
  Quotient.lift (fun p => quotientMap p.1) (by
    intro p q h
    rcases h with rfl | h
    · rfl
    · rw [h]
      exact (quotientMap_glide p.1).symm)

/-- The minus eigenline carries the Mobius sign under one torus glide. -/
def signLine (v : Spinor2) : Twistor4 := (v, -v)

theorem signLine_glide (k : BrillouinTorus) (v : Spinor2) :
    Quotient.mk twistedSetoid (torusGlide k, signLine (-v)) =
      Quotient.mk twistedSetoid (k, signLine v) := by
  apply Quotient.sound
  right
  simp [torusLift, signLine, torusGlide_involutive]

/-- Spin rotations and orientation-reversing transport are different operations. -/
def spinRotor (θ : ℝ) : Module.End ℂ Twistor4 :=
  (Real.cos (θ / 2) : ℂ) • 1 + (Real.sin (θ / 2) : ℂ) • (grading * pinPlus)

theorem spinRotor_two_pi : spinRotor (2 * Real.pi) = -1 := by
  simp [spinRotor]

theorem spinRotor_four_pi : spinRotor (4 * Real.pi) = 1 := by
  have h : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  simp [spinRotor, h]

end InfoGeometry.Twistor.KleinTwistorPinTransport
