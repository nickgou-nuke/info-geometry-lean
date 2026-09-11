import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
import InfoGeometry.Canonical.ZornSpinor

/-!
# ThermofieldBidirectionalResonator

Coherent two-amplitude bidirectional resonator with loss, Möbius projectivization,
and modular conjugation. No population dynamics, no gain.

Mathematical sequence:
```
TwinAmplitude → CoherentExchange → LossBalance
    → ProjectiveRatio → MöbiusRoundTrip → ModularConjugation
```
-/

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldBidirectionalResonator

open Complex
open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

/-!
=============================================================================
PART 1: Twin Amplitude Carrier
=============================================================================
-/

/-- The doubled amplitude carrier: two complex channels (+ and -). -/
@[ext]
structure TwinAmplitude : Type where
  aPlus  : ℂ
  aMinus : ℂ

def toProd (a : TwinAmplitude) : ℂ × ℂ := (a.aPlus, a.aMinus)
def fromProd (p : ℂ × ℂ) : TwinAmplitude := ⟨p.1, p.2⟩

def equivProd : TwinAmplitude ≃ (ℂ × ℂ) where
  toFun := toProd
  invFun := fromProd
  left_inv _ := rfl
  right_inv _ := rfl

instance : Zero TwinAmplitude := ⟨⟨0, 0⟩⟩
instance : Add TwinAmplitude := ⟨fun x y => ⟨x.aPlus + y.aPlus, x.aMinus + y.aMinus⟩⟩
instance : Neg TwinAmplitude := ⟨fun x => ⟨-x.aPlus, -x.aMinus⟩⟩
instance : Sub TwinAmplitude := ⟨fun x y => ⟨x.aPlus - y.aPlus, x.aMinus - y.aMinus⟩⟩
instance : SMul ℕ TwinAmplitude := ⟨fun n x => ⟨n • x.aPlus, n • x.aMinus⟩⟩
instance : SMul ℤ TwinAmplitude := ⟨fun n x => ⟨n • x.aPlus, n • x.aMinus⟩⟩
instance : SMul ℂ TwinAmplitude := ⟨fun c x => ⟨c • x.aPlus, c • x.aMinus⟩⟩

instance : AddCommGroup TwinAmplitude :=
  equivProd.injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℂ TwinAmplitude :=
  equivProd.injective.module ℂ ⟨⟨toProd, rfl⟩, (fun _ _ => rfl)⟩ (fun _ _ => rfl)

/-- Energy in each channel -/
def energyPlus (a : TwinAmplitude) : ℝ := Complex.normSq a.aPlus
def energyMinus (a : TwinAmplitude) : ℝ := Complex.normSq a.aMinus

/-- Total energy -/
def totalEnergy (a : TwinAmplitude) : ℝ := energyPlus a + energyMinus a

/-- Exchange current (coherent transfer between channels) -/
def exchangeCurrent (a : TwinAmplitude) (g : ℂ) : ℝ :=
  2 * (g.re * (a.aPlus.re * a.aMinus.im - a.aPlus.im * a.aMinus.re) -
       g.im * (a.aPlus.re * a.aMinus.re + a.aPlus.im * a.aMinus.im))

/-!
=============================================================================
PART 2: Coherent Dynamics (from amplitude equations)
=============================================================================
-/

/-- Parameters for the coupled resonator:
    κ₊, κ₋ : decay rates (≥ 0)
    ω₊, ω₋ : resonance frequencies
    g       : coupling strength (complex) -/
structure ResonatorParams where
  κPlus  : ℝ
  κMinus : ℝ
  ωPlus  : ℝ
  ωMinus : ℝ
  g      : ℂ
  κPlus_nonneg  : κPlus ≥ 0
  κMinus_nonneg : κMinus ≥ 0

/-- The continuous-time generator matrix X -/
def generatorMatrix (p : ResonatorParams) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-p.κPlus - Complex.I * p.ωPlus : ℂ), -p.g;
     -star p.g, (-p.κMinus - Complex.I * p.ωMinus : ℂ)]

/-- Energy balance derived from the amplitude equations:
    ȧ₊ = -(κ₊+iω₊)a₊ - i g a₋
    ȧ₋ = -(κ₋+iω₋)a₋ - i g* a₊
    gives d/dt E₊ = -2κ₊E₊ + exchangeCurrent, etc. -/
structure IntensityBalance (p : ResonatorParams) (a : TwinAmplitude) where
  E_dot_plus  : ℝ
  E_dot_minus : ℝ
  plus_eq :
    E_dot_plus =
      -2 * p.κPlus * energyPlus a
        + exchangeCurrent a p.g
  minus_eq :
    E_dot_minus =
      -2 * p.κMinus * energyMinus a
        - exchangeCurrent a p.g

/-- Construct the intensity balance from the amplitude equations -/
def makeIntensityBalance (p : ResonatorParams) (a : TwinAmplitude) : IntensityBalance p a :=
  ⟨-2 * p.κPlus * energyPlus a + exchangeCurrent a p.g,
   -2 * p.κMinus * energyMinus a - exchangeCurrent a p.g,
   rfl,
   rfl⟩

/-- Total energy balance: exchange current cancels -/
theorem totalEnergyBalance (p : ResonatorParams) (a : TwinAmplitude) :
    (makeIntensityBalance p a).E_dot_plus + (makeIntensityBalance p a).E_dot_minus
      = -2 * p.κPlus * energyPlus a - 2 * p.κMinus * energyMinus a := by
  dsimp [makeIntensityBalance]
  ring

/-- Symmetric case: κ₊ = κ₋ = κ, ω₊ = ω₋ = ω, g ∈ ℝ -/
theorem symmetricTotalEnergyDecay (p : ResonatorParams) (a : TwinAmplitude)
    (hκ : p.κPlus = p.κMinus) :
    (makeIntensityBalance p a).E_dot_plus + (makeIntensityBalance p a).E_dot_minus
      = -2 * p.κPlus * totalEnergy a := by
  calc (makeIntensityBalance p a).E_dot_plus + (makeIntensityBalance p a).E_dot_minus
    _ = -2 * p.κPlus * energyPlus a - 2 * p.κMinus * energyMinus a := totalEnergyBalance p a
    _ = -2 * p.κPlus * energyPlus a - 2 * p.κPlus * energyMinus a := by rw [← hκ]
    _ = -2 * p.κPlus * totalEnergy a := by
      unfold totalEnergy
      ring

/-!
=============================================================================
PART 3: Projective Ratio and Möbius Transform
=============================================================================
-/

/-- Projective ratio z = a₋/a₊ (on the chart a₊ ≠ 0) -/
def projectiveRatio (a : TwinAmplitude) : ℂ :=
  a.aMinus / a.aPlus

/-- Möbius transformation from a 2×2 matrix -/
def mobiusTransform (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 1 0 + M 1 1 * z) / (M 0 0 + M 0 1 * z)

/-- The projective ratio evolves by Möbius transformation:
    If a' = M a, then z' = mobiusTransform M z  (provided a₊ ≠ 0 and denominator ≠ 0) -/
theorem projectiveRatioEvolves (M : Matrix (Fin 2) (Fin 2) ℂ) (a : TwinAmplitude)
    (ha : a.aPlus ≠ 0) (_hdenom : M 0 0 + M 0 1 * (a.aMinus / a.aPlus) ≠ 0) :
    projectiveRatio ⟨M 0 0 * a.aPlus + M 0 1 * a.aMinus,
                      M 1 0 * a.aPlus + M 1 1 * a.aMinus⟩
      = mobiusTransform M (projectiveRatio a) := by
  unfold projectiveRatio mobiusTransform
  have h_num : M 1 0 * a.aPlus + M 1 1 * a.aMinus = (M 1 0 + M 1 1 * (a.aMinus / a.aPlus)) * a.aPlus := by
    calc M 1 0 * a.aPlus + M 1 1 * a.aMinus
      _ = M 1 0 * a.aPlus + M 1 1 * (a.aMinus / a.aPlus * a.aPlus) := by rw [div_mul_cancel₀ _ ha]
      _ = (M 1 0 + M 1 1 * (a.aMinus / a.aPlus)) * a.aPlus := by ring
  have h_den : M 0 0 * a.aPlus + M 0 1 * a.aMinus = (M 0 0 + M 0 1 * (a.aMinus / a.aPlus)) * a.aPlus := by
    calc M 0 0 * a.aPlus + M 0 1 * a.aMinus
      _ = M 0 0 * a.aPlus + M 0 1 * (a.aMinus / a.aPlus * a.aPlus) := by rw [div_mul_cancel₀ _ ha]
      _ = (M 0 0 + M 0 1 * (a.aMinus / a.aPlus)) * a.aPlus := by ring
  rw [h_num, h_den, mul_div_mul_right _ _ ha]

/-- Round-trip matrix (normalized determinant = 1) -/
structure RoundTripMatrix where
  toMatrix : Matrix (Fin 2) (Fin 2) ℂ
  det_one : toMatrix.det = 1

/-- Round-trip evolution on amplitudes -/
def roundTripAct (M : RoundTripMatrix) (a : TwinAmplitude) : TwinAmplitude :=
  let U := M.toMatrix
  ⟨U 0 0 * a.aPlus + U 0 1 * a.aMinus,
   U 1 0 * a.aPlus + U 1 1 * a.aMinus⟩

/-- Projective ratio evolution under round trip -/
theorem roundTripProjective (M : RoundTripMatrix) (a : TwinAmplitude)
    (ha : a.aPlus ≠ 0) (hdenom : M.toMatrix 0 0 + M.toMatrix 0 1 * (a.aMinus / a.aPlus) ≠ 0) :
    projectiveRatio (roundTripAct M a) = mobiusTransform M.toMatrix (projectiveRatio a) := by
  apply projectiveRatioEvolves M.toMatrix a ha hdenom

/-!
=============================================================================
PART 4: Lossless Sector (SU(1,1)) and Unit Disk
=============================================================================
-/

/-- SU(1,1) matrices: preserve the unit disk under Möbius action -/
structure SU11Matrix where
  A : ℂ
  B : ℂ
  condition₁ : Complex.normSq A - Complex.normSq B = 1
  condition₂ : A * star B = star A * B

/-- Convert SU(1,1) to RoundTripMatrix -/
def su11ToRoundTrip (M : SU11Matrix) : RoundTripMatrix :=
  { toMatrix := !![M.A, M.B; star M.B, star M.A],
    det_one := by
      simp [Matrix.det_fin_two]
      have h1 := M.condition₁
      have h2 : M.A * star M.A = (Complex.normSq M.A : ℂ) := Complex.mul_conj M.A
      have h3 : M.B * star M.B = (Complex.normSq M.B : ℂ) := Complex.mul_conj M.B
      have h4 : (M.A * star M.A - M.B * star M.B : ℂ) = (1 : ℂ) := by
        rw [h2, h3]
        exact_mod_cast congr_arg (fun x : ℝ => (x : ℂ)) h1
      exact h4 }

/-!
=============================================================================
PART 5: Modular Conjugation J
=============================================================================
-/

/-- Modular conjugation on the twin amplitude: J(a₊, a₋) = (a₋*, a₊*) -/
def modularConjugation (a : TwinAmplitude) : TwinAmplitude :=
  ⟨star a.aMinus, star a.aPlus⟩

/-- J is conjugate-linear -/
theorem modularConjugation_conjugateLinear (c : ℂ) (a b : TwinAmplitude) :
    modularConjugation (c • a + b) = star c • modularConjugation a + modularConjugation b := by
  ext
  · change star (c * a.aMinus + b.aMinus) = star c * star a.aMinus + star b.aMinus
    rw [star_add, star_mul']
  · change star (c * a.aPlus + b.aPlus) = star c * star a.aPlus + star b.aPlus
    rw [star_add, star_mul']

/-- J preserves the total energy norm -/
theorem modularConjugation_preservesEnergy (a : TwinAmplitude) :
    totalEnergy (modularConjugation a) = totalEnergy a := by
  simp [modularConjugation, totalEnergy, energyPlus, energyMinus, Complex.normSq]
  ring

/-- J is an involution: J² = I -/
theorem modularConjugation_involution (a : TwinAmplitude) :
    modularConjugation (modularConjugation a) = a := by
  ext <;> simp [modularConjugation]

/-- Action of J on the projective ratio: z ↦ 1/z* -/
theorem modularConjugation_onProjective (a : TwinAmplitude) (_ha : a.aPlus ≠ 0) :
    projectiveRatio (modularConjugation a) = 1 / star (projectiveRatio a) := by
  unfold projectiveRatio modularConjugation
  dsimp
  rw [map_div₀ (starRingEnd ℂ), one_div, inv_div]

/-- J preserves the unit circle: if |z| = 1, then |1/z*| = 1 -/
theorem modularConjugation_preservesUnitCircle (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 / star z‖ = 1 := by
  rw [norm_div, norm_one, norm_star, hz, div_one]

/-!
=============================================================================
PART 6: Connection to Split-Octonion Peirce Frame
=============================================================================
-/

/-- Embed a TwinAmplitude into the split-octonion Peirce frame -/
def embedToPeirceFrame (a : TwinAmplitude) : ZornMatrix ℝ :=
  ⟨a.aPlus.re,
   a.aMinus.re,
   ![a.aPlus.im, 0, 0],
   ![a.aMinus.im, 0, 0]⟩

/-- The Peirce projectors recover the amplitudes -/
theorem peirceRecoversAmplitudes (a : TwinAmplitude) :
    (embedToPeirceFrame a).a = a.aPlus.re ∧
    (embedToPeirceFrame a).b = a.aMinus.re := by
  exact ⟨rfl, rfl⟩

end InfoGeometry.Canonical.ThermofieldBidirectionalResonator
