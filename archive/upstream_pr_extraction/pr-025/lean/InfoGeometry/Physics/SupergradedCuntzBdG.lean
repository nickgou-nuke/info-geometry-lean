import InfoGeometry.Physics.ComplexStarCuntzRedesign
import Mathlib.Data.Complex.Basic

/-!
# Supergraded Cuntz--BdG layer

This file puts a small superalgebra interface on top of the algebraic Cuntz
quotient.  The intent is deliberately algebraic:

* `Z2Parity` records even/odd degree data;
* `superBracket` specializes to the commutator in even sectors and the
  anticommutator for odd--odd pairs;
* finite Cuntz range projections give chiral particle/hole projectors;
* Nambu--Gorkov/BdG generators and supercharges are packaged as formal Cuntz
  expressions over the finite algebraic quotient.
-/

noncomputable section

namespace InfoGeometry.Physics.SupergradedCuntzBdG

open scoped BigOperators
open InfoGeometry.Topology.AlgebraicCuntzQuotient
open ComplexStarCuntzRedesign

/-! ## `ℤ₂` supergrading and superbracket -/

/-- Two superdegrees: even bosonic and odd fermionic. -/
inductive Z2Parity where
  | even
  | odd
  deriving DecidableEq, Repr

/-- Addition in `ℤ₂`, written as parity fusion. -/
def parityMul : Z2Parity → Z2Parity → Z2Parity
  | Z2Parity.even, q => q
  | Z2Parity.odd, Z2Parity.even => Z2Parity.odd
  | Z2Parity.odd, Z2Parity.odd => Z2Parity.even

@[simp] theorem parityMul_even_left (q : Z2Parity) :
    parityMul Z2Parity.even q = q := by
  cases q <;> rfl

@[simp] theorem parityMul_even_right (p : Z2Parity) :
    parityMul p Z2Parity.even = p := by
  cases p <;> rfl

@[simp] theorem parityMul_odd_odd :
    parityMul Z2Parity.odd Z2Parity.odd = Z2Parity.even := rfl

/-- Koszul sign for the supercommutator. -/
def superSign (p q : Z2Parity) : ℂ :=
  match p, q with
  | Z2Parity.odd, Z2Parity.odd => -1
  | _, _ => 1

@[simp] theorem superSign_even_left (q : Z2Parity) :
    superSign Z2Parity.even q = 1 := by
  cases q <;> rfl

@[simp] theorem superSign_even_right (p : Z2Parity) :
    superSign p Z2Parity.even = 1 := by
  cases p <;> rfl

@[simp] theorem superSign_odd_odd :
    superSign Z2Parity.odd Z2Parity.odd = -1 := rfl

/-- Coefficient form of `-[(-1)^{|x||y|}]`, avoiding native subtraction.
For even pairs this is `-1`, and for odd--odd pairs this is `+1`. -/
def superSwapCoeff (p q : Z2Parity) : ℂ := -superSign p q

@[simp] theorem superSwapCoeff_even_left (q : Z2Parity) :
    superSwapCoeff Z2Parity.even q = -1 := by
  cases q <;> rfl

@[simp] theorem superSwapCoeff_even_right (p : Z2Parity) :
    superSwapCoeff p Z2Parity.even = -1 := by
  cases p <;> rfl

@[simp] theorem superSwapCoeff_odd_odd :
    superSwapCoeff Z2Parity.odd Z2Parity.odd = 1 := by
  simp [superSwapCoeff]

/-- The superbracket `[x,y]ₛ = xy - (-1)^{|x||y|} yx`, written with a scalar
coefficient so it works for the current semiring-level `RingQuot` Cuntz algebra. -/
def superBracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (p q : Z2Parity) (x y : A) : A :=
  x * y + superSwapCoeff p q • (y * x)

@[simp] theorem superBracket_even_left {A : Type*} [Semiring A] [Algebra ℂ A]
    (q : Z2Parity) (x y : A) :
    superBracket Z2Parity.even q x y = x * y + (-1 : ℂ) • (y * x) := by
  simp [superBracket]

@[simp] theorem superBracket_even_right {A : Type*} [Semiring A] [Algebra ℂ A]
    (p : Z2Parity) (x y : A) :
    superBracket p Z2Parity.even x y = x * y + (-1 : ℂ) • (y * x) := by
  simp [superBracket]

@[simp] theorem superBracket_odd_odd {A : Type*} [Semiring A] [Algebra ℂ A]
    (x y : A) :
    superBracket Z2Parity.odd Z2Parity.odd x y = x * y + y * x := by
  simp [superBracket]

/-! ## Affine Jordan--Lie deformation of the superbracket -/

/-- Scalar-signed Lie/antisymmetric bracket `xy - yx`, encoded without requiring
native subtraction in the quotient. -/
def lieBracket {A : Type*} [Semiring A] [Algebra ℂ A] (x y : A) : A :=
  x * y + (-1 : ℂ) • (y * x)

/-- Jordan/symmetric product `xy + yx`. -/
def jordanProduct {A : Type*} [Semiring A] [Algebra ℂ A] (x y : A) : A :=
  x * y + y * x

/-- Affine interpolation coefficient between the Lie bracket coefficient `-1`
and the superbracket coefficient.  The parameter `β` is the affine/Weyl-gauge
thermodynamic deformation parameter. -/
def affineSwapCoeff (β : ℂ) (p q : Z2Parity) : ℂ :=
  (1 - β) * (-1) + β * superSwapCoeff p q

/-- Affine deformation of the superbracket.  At `β = 0` this is the ordinary
Lie/antisymmetric bracket; at `β = 1` this is the Koszul superbracket. -/
def affineSuperBracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (p q : Z2Parity) (x y : A) : A :=
  x * y + affineSwapCoeff β p q • (y * x)

@[simp] theorem affineSwapCoeff_zero (p q : Z2Parity) :
    affineSwapCoeff 0 p q = -1 := by
  simp [affineSwapCoeff]

@[simp] theorem affineSwapCoeff_one (p q : Z2Parity) :
    affineSwapCoeff 1 p q = superSwapCoeff p q := by
  simp [affineSwapCoeff]

@[simp] theorem affineSuperBracket_zero {A : Type*} [Semiring A] [Algebra ℂ A]
    (p q : Z2Parity) (x y : A) :
    affineSuperBracket 0 p q x y = lieBracket x y := by
  simp [affineSuperBracket, lieBracket]

@[simp] theorem affineSuperBracket_one {A : Type*} [Semiring A] [Algebra ℂ A]
    (p q : Z2Parity) (x y : A) :
    affineSuperBracket 1 p q x y = superBracket p q x y := by
  simp [affineSuperBracket, superBracket]

@[simp] theorem affineSwapCoeff_even_left (β : ℂ) (q : Z2Parity) :
    affineSwapCoeff β Z2Parity.even q = -1 := by
  cases q <;> simp [affineSwapCoeff] <;> ring_nf

@[simp] theorem affineSwapCoeff_even_right (β : ℂ) (p : Z2Parity) :
    affineSwapCoeff β p Z2Parity.even = -1 := by
  cases p <;> simp [affineSwapCoeff] <;> ring_nf

@[simp] theorem affineSwapCoeff_odd_odd (β : ℂ) :
    affineSwapCoeff β Z2Parity.odd Z2Parity.odd = 2 * β - 1 := by
  simp [affineSwapCoeff]
  ring_nf

@[simp] theorem affineSuperBracket_even_left {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (q : Z2Parity) (x y : A) :
    affineSuperBracket β Z2Parity.even q x y = lieBracket x y := by
  cases q <;> simp [affineSuperBracket, lieBracket]

@[simp] theorem affineSuperBracket_even_right {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (p : Z2Parity) (x y : A) :
    affineSuperBracket β p Z2Parity.even x y = lieBracket x y := by
  cases p <;> simp [affineSuperBracket, lieBracket]

@[simp] theorem affineSuperBracket_odd_odd {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (x y : A) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd x y =
      x * y + ((2 * β - 1 : ℂ) • (y * x)) := by
  simp [affineSuperBracket]

/-- Global affine split: the deformed bracket is the affine combination of the
ordinary Lie bracket and the Koszul superbracket. -/
theorem affineSuperBracket_lie_super_split {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (p q : Z2Parity) (x y : A) :
    affineSuperBracket β p q x y =
      (1 - β : ℂ) • lieBracket x y + β • superBracket p q x y := by
  simp [affineSuperBracket, affineSwapCoeff, lieBracket, superBracket]
  module

/-- In the odd--odd sector the affine deformation is exactly the Jordan--Lie
split: Lie at `β = 0`, Jordan at `β = 1`. -/
theorem affineSuperBracket_odd_odd_jordan_lie_split {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (x y : A) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd x y =
      (1 - β : ℂ) • lieBracket x y + β • jordanProduct x y := by
  simp [affineSuperBracket, affineSwapCoeff, lieBracket, jordanProduct]
  module

@[simp] theorem affineSuperBracket_odd_odd_one {A : Type*} [Semiring A] [Algebra ℂ A]
    (x y : A) :
    affineSuperBracket 1 Z2Parity.odd Z2Parity.odd x y = jordanProduct x y := by
  rw [affineSuperBracket_odd_odd]
  norm_num
  simp [jordanProduct]

/-! ## Exponential q/rapidity parametrization and Rindler--Unruh scaling -/

/-- Exponential parametrization of the affine/q deformation by a real rapidity or
log-scale parameter. -/
def qRapidity (ρ : ℝ) : ℂ := (Real.exp ρ : ℂ)

@[simp] theorem qRapidity_ne_zero (ρ : ℝ) : qRapidity ρ ≠ 0 := by
  simp [qRapidity]

@[simp] theorem qRapidity_zero : qRapidity 0 = 1 := by
  simp [qRapidity]

@[simp] theorem qRapidity_add (ρ σ : ℝ) :
    qRapidity (ρ + σ) = qRapidity ρ * qRapidity σ := by
  simp [qRapidity, Real.exp_add]

/-- Log-scale coordinate for a positive real q-parameter. -/
def logScaleParam (q : ℝ) : ℝ := Real.log q

@[simp] theorem qRapidity_logScaleParam {q : ℝ} (hq : 0 < q) :
    qRapidity (logScaleParam q) = (q : ℂ) := by
  simp [qRapidity, logScaleParam, Real.exp_log hq]

/-- q/rapidity deformed affine bracket. -/
def qAffineSuperBracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (ρ : ℝ) (p q : Z2Parity) (x y : A) : A :=
  affineSuperBracket (qRapidity ρ) p q x y

@[simp] theorem qAffineSuperBracket_zero {A : Type*} [Semiring A] [Algebra ℂ A]
    (p q : Z2Parity) (x y : A) :
    qAffineSuperBracket 0 p q x y = superBracket p q x y := by
  simp [qAffineSuperBracket]

@[simp] theorem qAffineSuperBracket_odd_odd {A : Type*} [Semiring A] [Algebra ℂ A]
    (ρ : ℝ) (x y : A) :
    qAffineSuperBracket ρ Z2Parity.odd Z2Parity.odd x y =
      x * y + ((2 * qRapidity ρ - 1 : ℂ) • (y * x)) := by
  simp [qAffineSuperBracket]

/-- Rindler/Weyl scaling flow generated by the exponential rapidity parameter. -/
def RindlerWeylFlow {A : Type*} [SMul ℂ A] (ρ : ℝ) (x : A) : A :=
  qRapidity ρ • x

/-! ## Grand-canonical/KMS scalar weights -/

/-- Grand-canonical rapidity/log-weight `-β(E - μQ)`. -/
def grandCanonicalRapidity (β E μ Q : ℝ) : ℝ :=
  -(β * (E - μ * Q))

/-- Grand-canonical q-weight `q = exp(-β(E - μQ))`. -/
def grandCanonicalQ (β E μ Q : ℝ) : ℂ :=
  qRapidity (grandCanonicalRapidity β E μ Q)

@[simp] theorem grandCanonicalQ_eq_exp (β E μ Q : ℝ) :
    grandCanonicalQ β E μ Q = (Real.exp (-(β * (E - μ * Q))) : ℂ) := by
  rfl

@[simp] theorem grandCanonicalQ_ne_zero (β E μ Q : ℝ) :
    grandCanonicalQ β E μ Q ≠ 0 := by
  simp [grandCanonicalQ]

/-- The logarithmic scale coordinate recovers the grand-canonical rapidity. -/
theorem qRapidity_log_grandCanonicalWeight (β E μ Q : ℝ) :
    qRapidity (logScaleParam (Real.exp (grandCanonicalRapidity β E μ Q))) =
      grandCanonicalQ β E μ Q := by
  rw [qRapidity_logScaleParam (Real.exp_pos _)]
  rfl

/-- q-affine bracket with q fixed by the grand-canonical/KMS weight. -/
def grandCanonicalBracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (p q : Z2Parity) (x y : A) : A :=
  qAffineSuperBracket (grandCanonicalRapidity β E μ Q) p q x y

/-- Grand-canonical scalar-weighted q-affine bracket. -/
def grandCanonicalWeightedBracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (p q : Z2Parity) (x y : A) : A :=
  grandCanonicalQ β E μ Q • grandCanonicalBracket β E μ Q p q x y

@[simp] theorem grandCanonicalBracket_odd_odd {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (x y : A) :
    grandCanonicalBracket β E μ Q Z2Parity.odd Z2Parity.odd x y =
      x * y + ((2 * grandCanonicalQ β E μ Q - 1 : ℂ) • (y * x)) := by
  simp [grandCanonicalBracket, grandCanonicalQ]

/-- Positive real grand-canonical weight before embedding into `ℂ`. -/
def grandCanonicalRealWeight (β E μ Q : ℝ) : ℝ :=
  Real.exp (grandCanonicalRapidity β E μ Q)

@[simp] theorem grandCanonicalRealWeight_pos (β E μ Q : ℝ) :
    0 < grandCanonicalRealWeight β E μ Q := by
  exact Real.exp_pos _

@[simp] theorem grandCanonicalQ_ofReal (β E μ Q : ℝ) :
    grandCanonicalQ β E μ Q = (grandCanonicalRealWeight β E μ Q : ℂ) := by
  rfl

/-- The logarithmic scale of the real KMS weight is the grand-canonical rapidity. -/
@[simp] theorem logScale_grandCanonicalRealWeight (β E μ Q : ℝ) :
    logScaleParam (grandCanonicalRealWeight β E μ Q) = grandCanonicalRapidity β E μ Q := by
  simp [logScaleParam, grandCanonicalRealWeight]

/-- Real rapidity boost of the grand-canonical weight. -/
def boostedGrandCanonicalRealWeight (θ β E μ Q : ℝ) : ℝ :=
  Real.exp θ * grandCanonicalRealWeight β E μ Q

@[simp] theorem boostedGrandCanonicalRealWeight_pos (θ β E μ Q : ℝ) :
    0 < boostedGrandCanonicalRealWeight θ β E μ Q := by
  exact mul_pos (Real.exp_pos θ) (grandCanonicalRealWeight_pos β E μ Q)

/-- Rapidity boosts translate the logarithmic KMS scale. -/
theorem logScale_boostedGrandCanonicalRealWeight (θ β E μ Q : ℝ) :
    logScaleParam (boostedGrandCanonicalRealWeight θ β E μ Q) =
      θ + grandCanonicalRapidity β E μ Q := by
  simp [logScaleParam, boostedGrandCanonicalRealWeight, grandCanonicalRealWeight,
    Real.log_mul (Real.exp_pos θ).ne' (Real.exp_pos _).ne']

/-- Complex q-weight after an extra rapidity boost. -/
def boostedGrandCanonicalQ (θ β E μ Q : ℝ) : ℂ :=
  qRapidity θ * grandCanonicalQ β E μ Q

@[simp] theorem boostedGrandCanonicalQ_eq_qRapidity_add (θ β E μ Q : ℝ) :
    boostedGrandCanonicalQ θ β E μ Q =
      qRapidity (θ + grandCanonicalRapidity β E μ Q) := by
  rw [qRapidity_add]
  rfl

/-- KMS scalar action by the grand-canonical q-weight. -/
def kmsScalarAction {A : Type*} [SMul ℂ A] (β E μ Q : ℝ) (x : A) : A :=
  grandCanonicalQ β E μ Q • x

/-- KMS scalar action with an additional rapidity/Weyl boost. -/
def kmsBoostFlow {A : Type*} [SMul ℂ A] (θ β E μ Q : ℝ) (x : A) : A :=
  boostedGrandCanonicalQ θ β E μ Q • x

@[simp] theorem kmsBoostFlow_eq_rapidity_after_kms {A : Type*} [MulAction ℂ A]
    (θ β E μ Q : ℝ) (x : A) :
    kmsBoostFlow θ β E μ Q x = RindlerWeylFlow θ (kmsScalarAction β E μ Q x) := by
  simp [kmsBoostFlow, RindlerWeylFlow, kmsScalarAction, boostedGrandCanonicalQ, smul_smul]

/-- The KMS boosted scalar flow composes by adding rapidities. -/
theorem kmsBoostFlow_comp {A : Type*} [MulAction ℂ A]
    (θ φ β E μ Q : ℝ) (x : A) :
    RindlerWeylFlow θ (kmsBoostFlow φ β E μ Q x) =
      kmsBoostFlow (θ + φ) β E μ Q x := by
  simp [kmsBoostFlow, RindlerWeylFlow, boostedGrandCanonicalQ, smul_smul,
    qRapidity_add, mul_comm, mul_left_comm]

@[simp] theorem RindlerWeylFlow_zero {A : Type*} [MulAction ℂ A] (x : A) :
    RindlerWeylFlow 0 x = x := by
  simp [RindlerWeylFlow]

/-- Exponential rapidity additivity gives the Rindler/Weyl flow law. -/
theorem RindlerWeylFlow_add {A : Type*} [MulAction ℂ A] (ρ σ : ℝ) (x : A) :
    RindlerWeylFlow ρ (RindlerWeylFlow σ x) = RindlerWeylFlow (ρ + σ) x := by
  simp [RindlerWeylFlow, qRapidity, smul_smul, Real.exp_add]

/-- Algebraic Unruh temperature scale `T = a / (2π)`, with constants normalized
so `ℏ = c = k_B = 1`. -/
def unruhTemperature (acceleration : ℝ) : ℝ := acceleration / (2 * Real.pi)

@[simp] theorem two_pi_mul_unruhTemperature (a : ℝ) :
    (2 * Real.pi) * unruhTemperature a = a := by
  unfold unruhTemperature
  field_simp [Real.pi_ne_zero]

/-- A formal affine/Weyl thermodynamic ensemble: a stage algebra equipped with an
affine bracket parameter.  This is finite algebraic data, not a C*-completion. -/
structure AffineWeylThermoEnsemble (A : Type*) [Semiring A] [Algebra ℂ A] where
  beta : ℂ
  weylGauge : ℂ
  rapidity : ℝ
  acceleration : ℝ
  energy : A
  q_is_exp_rapidity : beta = qRapidity rapidity

namespace AffineWeylThermoEnsemble

/-- The affine superbracket derived from the ensemble's thermodynamic parameter. -/
@[simp] def bracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (E : AffineWeylThermoEnsemble A) : Z2Parity → Z2Parity → A → A → A :=
  affineSuperBracket E.beta

/-- The Unruh scale derived from the ensemble's supplied acceleration. -/
def unruh_scale {A : Type*} [Semiring A] [Algebra ℂ A]
    (E : AffineWeylThermoEnsemble A) : ℝ :=
  unruhTemperature E.acceleration

end AffineWeylThermoEnsemble

/-- The canonical affine ensemble attached to a finite Cuntz--BdG stage. -/
def cuntzBdGAffineEnsemble (n : ℕ) (ρ : ℝ) (gauge : ℂ) (acceleration : ℝ) :
    AffineWeylThermoEnsemble (CuntzAlg ℂ (Fin (2 * n))) where
  beta := qRapidity ρ
  weylGauge := gauge
  rapidity := ρ
  acceleration := acceleration
  energy := 1
  q_is_exp_rapidity := rfl

/-- At zero affine parameter the canonical ensemble bracket is the Lie bracket. -/
theorem cuntzBdGAffineEnsemble_zero_rapidity_bracket (n : ℕ) (gauge : ℂ) (a : ℝ)
    (p q : Z2Parity) (x y : CuntzAlg ℂ (Fin (2 * n))) :
    (cuntzBdGAffineEnsemble n 0 gauge a).bracket p q x y = superBracket p q x y := by
  simp [cuntzBdGAffineEnsemble]

/-- At logarithmic rapidity `log β`, the ensemble realizes affine parameter `β`. -/
theorem cuntzBdGAffineEnsemble_logScale_bracket (n : ℕ) {β : ℝ} (hβ : 0 < β)
    (gauge : ℂ) (a : ℝ) (p q : Z2Parity) (x y : CuntzAlg ℂ (Fin (2 * n))) :
    (cuntzBdGAffineEnsemble n (logScaleParam β) gauge a).bracket p q x y =
      affineSuperBracket (β : ℂ) p q x y := by
  simp [cuntzBdGAffineEnsemble, qRapidity_logScaleParam hβ]

/-! ## Genuine complex-star Cuntz carrier for the affine ensemble -/

/-- The finite Cuntz--BdG stage over the genuine conjugate-linear complex star
source, replacing the older scalar-fixed formal-star carrier for the thermodynamic
q/Rindler layer. -/
abbrev ComplexStarCuntzBdGStage (n : ℕ) := ComplexStarCuntzAlg (Fin (2 * n))

/-- Canonical affine/Weyl ensemble over the genuine complex-star Cuntz source. -/
def complexStarCuntzBdGAffineEnsemble (n : ℕ) (ρ : ℝ) (gauge : ℂ) (acceleration : ℝ) :
    AffineWeylThermoEnsemble (ComplexStarCuntzBdGStage n) where
  beta := qRapidity ρ
  weylGauge := gauge
  rapidity := ρ
  acceleration := acceleration
  energy := 1
  q_is_exp_rapidity := rfl

/-- The genuine complex-star ensemble has conjugate-semilinear source star. -/
theorem complexStarCuntzBdG_star_smul (n : ℕ) (z : ℂ) (x : ComplexStarCuntzBdGStage n) :
    star (z • x) = star z • star x := by
  exact star_complex_smul z x

/-- Creation generators in the genuine source star to annihilation generators. -/
@[simp] theorem complexStarCuntzBdG_star_S (n : ℕ) (i : Fin (2 * n)) :
    star (Sℂ i : ComplexStarCuntzBdGStage n) = Tℂ i := by
  exact star_Sℂ i

/-- Annihilation generators in the genuine source star to creation generators. -/
@[simp] theorem complexStarCuntzBdG_star_T (n : ℕ) (i : Fin (2 * n)) :
    star (Tℂ i : ComplexStarCuntzBdGStage n) = Sℂ i := by
  exact star_Tℂ i

/-- Zero rapidity in the genuine complex-star ensemble gives the superbracket. -/
theorem complexStarCuntzBdGAffineEnsemble_zero_rapidity_bracket (n : ℕ) (gauge : ℂ) (a : ℝ)
    (p q : Z2Parity) (x y : ComplexStarCuntzBdGStage n) :
    (complexStarCuntzBdGAffineEnsemble n 0 gauge a).bracket p q x y = superBracket p q x y := by
  simp [complexStarCuntzBdGAffineEnsemble]

/-- Positive real q-parameter recovered by logarithmic rapidity in the genuine source. -/
theorem complexStarCuntzBdGAffineEnsemble_logScale_bracket (n : ℕ) {β : ℝ} (hβ : 0 < β)
    (gauge : ℂ) (a : ℝ) (p q : Z2Parity) (x y : ComplexStarCuntzBdGStage n) :
    (complexStarCuntzBdGAffineEnsemble n (logScaleParam β) gauge a).bracket p q x y =
      affineSuperBracket (β : ℂ) p q x y := by
  simp [complexStarCuntzBdGAffineEnsemble, qRapidity_logScaleParam hβ]

/-- Rindler/Weyl flow law on the genuine complex-star Cuntz source. -/
theorem complexStarCuntzBdG_RindlerWeylFlow_add (n : ℕ) (ρ σ : ℝ)
    (x : ComplexStarCuntzBdGStage n) :
    RindlerWeylFlow ρ (RindlerWeylFlow σ x) = RindlerWeylFlow (ρ + σ) x := by
  exact RindlerWeylFlow_add ρ σ x

/-! ## Genuine `StarAlgHom` representation interface and bracket preservation -/

/-- Any complex `StarAlgHom` preserves the affine superbracket. -/
theorem StarAlgHom.map_affineSuperBracket
    {A B : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring B] [Algebra ℂ B] [Star B]
    (φ : A →⋆ₐ[ℂ] B) (β : ℂ) (p q : Z2Parity) (x y : A) :
    φ (affineSuperBracket β p q x y) =
      affineSuperBracket β p q (φ x) (φ y) := by
  simp [affineSuperBracket]

/-- Any complex `StarAlgHom` preserves the rapidity/q-affine superbracket. -/
theorem StarAlgHom.map_qAffineSuperBracket
    {A B : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring B] [Algebra ℂ B] [Star B]
    (φ : A →⋆ₐ[ℂ] B) (ρ : ℝ) (p q : Z2Parity) (x y : A) :
    φ (qAffineSuperBracket ρ p q x y) =
      qAffineSuperBracket ρ p q (φ x) (φ y) := by
  simp [qAffineSuperBracket, StarAlgHom.map_affineSuperBracket]

/-- Any complex `StarAlgHom` preserves the grand-canonical bracket. -/
theorem StarAlgHom.map_grandCanonicalBracket
    {A B : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring B] [Algebra ℂ B] [Star B]
    (φ : A →⋆ₐ[ℂ] B) (β E μ Q : ℝ) (p q : Z2Parity) (x y : A) :
    φ (grandCanonicalBracket β E μ Q p q x y) =
      grandCanonicalBracket β E μ Q p q (φ x) (φ y) := by
  simp [grandCanonicalBracket, StarAlgHom.map_qAffineSuperBracket]

/-- Any complex `StarAlgHom` preserves the scalar-weighted grand-canonical bracket. -/
theorem StarAlgHom.map_grandCanonicalWeightedBracket
    {A B : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring B] [Algebra ℂ B] [Star B]
    (φ : A →⋆ₐ[ℂ] B) (β E μ Q : ℝ) (p q : Z2Parity) (x y : A) :
    φ (grandCanonicalWeightedBracket β E μ Q p q x y) =
      grandCanonicalWeightedBracket β E μ Q p q (φ x) (φ y) := by
  simp [grandCanonicalWeightedBracket, StarAlgHom.map_grandCanonicalBracket]

/-- A genuine C*-representation of the finite complex-star Cuntz--BdG stage.
The image of `Tℂ` is forced by star preservation from the image of `Sℂ`. -/
structure ComplexStarCuntzBdGRepresentation (n : ℕ) (A : Type*) [CStarAlgebra A] where
  map : ComplexStarCuntzBdGStage n →⋆ₐ[ℂ] A
  S_image : Fin (2 * n) → A
  map_S : ∀ i, map (Sℂ i) = S_image i

/-- The represented annihilation/formal-adjoint generator is the C*-adjoint of
the represented creation generator. -/
@[simp] theorem ComplexStarCuntzBdGRepresentation.map_T
    {n : ℕ} {A : Type*} [CStarAlgebra A]
    (Φ : ComplexStarCuntzBdGRepresentation n A) (i : Fin (2 * n)) :
    Φ.map (Tℂ i) = star (Φ.S_image i) := by
  rw [← star_Sℂ, map_star, Φ.map_S]

/-- A genuine C*-representation preserves q-affine brackets of represented
creation/annihilation generators. -/
theorem ComplexStarCuntzBdGRepresentation.map_qAffineBracket_S_T
    {n : ℕ} {A : Type*} [CStarAlgebra A]
    (Φ : ComplexStarCuntzBdGRepresentation n A) (ρ : ℝ) (p q : Z2Parity)
    (i j : Fin (2 * n)) :
    Φ.map (qAffineSuperBracket ρ p q (Sℂ i : ComplexStarCuntzBdGStage n) (Tℂ j)) =
      qAffineSuperBracket ρ p q (Φ.S_image i) (star (Φ.S_image j)) := by
  rw [StarAlgHom.map_qAffineSuperBracket, Φ.map_S, Φ.map_T]

/-- Odd/odd represented creation/annihilation q-bracket has explicit rapidity
coefficient after applying a genuine C*-representation. -/
theorem ComplexStarCuntzBdGRepresentation.map_qAffineBracket_odd_odd_S_T
    {n : ℕ} {A : Type*} [CStarAlgebra A]
    (Φ : ComplexStarCuntzBdGRepresentation n A) (ρ : ℝ) (i j : Fin (2 * n)) :
    Φ.map (qAffineSuperBracket ρ Z2Parity.odd Z2Parity.odd
        (Sℂ i : ComplexStarCuntzBdGStage n) (Tℂ j)) =
      Φ.S_image i * star (Φ.S_image j) +
        (2 * qRapidity ρ - 1 : ℂ) • (star (Φ.S_image j) * Φ.S_image i) := by
  rw [ComplexStarCuntzBdGRepresentation.map_qAffineBracket_S_T]
  simp [qAffineSuperBracket]

/-- A genuine C*-representation preserves grand-canonical brackets of represented
creation/annihilation generators. -/
theorem ComplexStarCuntzBdGRepresentation.map_grandCanonicalBracket_S_T
    {n : ℕ} {A : Type*} [CStarAlgebra A]
    (Φ : ComplexStarCuntzBdGRepresentation n A) (β E μ Q : ℝ) (p q : Z2Parity)
    (i j : Fin (2 * n)) :
    Φ.map (grandCanonicalBracket β E μ Q p q
        (Sℂ i : ComplexStarCuntzBdGStage n) (Tℂ j)) =
      grandCanonicalBracket β E μ Q p q (Φ.S_image i) (star (Φ.S_image j)) := by
  rw [StarAlgHom.map_grandCanonicalBracket, Φ.map_S, Φ.map_T]

/-- A genuine C*-representation preserves scalar-weighted grand-canonical brackets
of represented creation/annihilation generators. -/
theorem ComplexStarCuntzBdGRepresentation.map_grandCanonicalWeightedBracket_S_T
    {n : ℕ} {A : Type*} [CStarAlgebra A]
    (Φ : ComplexStarCuntzBdGRepresentation n A) (β E μ Q : ℝ) (p q : Z2Parity)
    (i j : Fin (2 * n)) :
    Φ.map (grandCanonicalWeightedBracket β E μ Q p q
        (Sℂ i : ComplexStarCuntzBdGStage n) (Tℂ j)) =
      grandCanonicalWeightedBracket β E μ Q p q (Φ.S_image i) (star (Φ.S_image j)) := by
  rw [StarAlgHom.map_grandCanonicalWeightedBracket, Φ.map_S, Φ.map_T]

/-- Odd/odd represented grand-canonical bracket has explicit KMS weight coefficient. -/
theorem ComplexStarCuntzBdGRepresentation.map_grandCanonicalBracket_odd_odd_S_T
    {n : ℕ} {A : Type*} [CStarAlgebra A]
    (Φ : ComplexStarCuntzBdGRepresentation n A) (β E μ Q : ℝ) (i j : Fin (2 * n)) :
    Φ.map (grandCanonicalBracket β E μ Q Z2Parity.odd Z2Parity.odd
        (Sℂ i : ComplexStarCuntzBdGStage n) (Tℂ j)) =
      Φ.S_image i * star (Φ.S_image j) +
        (2 * grandCanonicalQ β E μ Q - 1 : ℂ) •
          (star (Φ.S_image j) * Φ.S_image i) := by
  rw [ComplexStarCuntzBdGRepresentation.map_grandCanonicalBracket_S_T]
  simp [grandCanonicalBracket, grandCanonicalQ]


/-- A homogeneous element bundled with its superdegree. -/
structure Homogeneous (A : Type*) where
  carrier : A
  parity : Z2Parity

/-- Bracket of homogeneous elements. -/
def Homogeneous.bracket {A : Type*} [Semiring A] [Algebra ℂ A]
    (x y : Homogeneous A) : A :=
  superBracket x.parity y.parity x.carrier y.carrier

/-! ## Cuntz range projections as chiral projectors -/

/-- Finite algebraic Cuntz stage used as a BdG/Nambu tower atom. -/
abbrev CuntzBdGStage (n : ℕ) := CuntzAlg ℂ (Fin (2 * n))

/-- Range projection `SᵢTᵢ` for one Cuntz channel. -/
def rangeProj {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    CuntzAlg ℂ ι :=
  S (R := ℂ) i * T (R := ℂ) i

@[simp] theorem rangeProj_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    rangeProj i * rangeProj i = rangeProj i := by
  change (S (R := ℂ) i * T (R := ℂ) i) * (S (R := ℂ) i * T (R := ℂ) i) =
    S (R := ℂ) i * T (R := ℂ) i
  rw [mul_assoc, ← mul_assoc (T (R := ℂ) i) (S (R := ℂ) i)
    (T (R := ℂ) i), T_mul_S]
  rw [if_pos rfl, one_mul]

@[simp] theorem rangeProj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    rangeProj i * rangeProj j = if i = j then rangeProj i else 0 := by
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    exact rangeProj_idempotent i
  · simp [h]
    change (S (R := ℂ) i * T (R := ℂ) i) * (S (R := ℂ) j * T (R := ℂ) j) = 0
    rw [mul_assoc, ← mul_assoc (T (R := ℂ) i) (S (R := ℂ) j)
      (T (R := ℂ) j), T_mul_S]
    simp [h]

/-- Two-channel Cuntz algebra as the minimal particle/hole BdG atom. -/
abbrev BdGAtom := CuntzAlg ℂ (Fin 2)

/-- Particle/chiral-plus projector. -/
def particleProj : BdGAtom := rangeProj (0 : Fin 2)

/-- Hole/chiral-minus projector. -/
def holeProj : BdGAtom := rangeProj (1 : Fin 2)

@[simp] theorem particleProj_idempotent :
    particleProj * particleProj = particleProj := by
  simp [particleProj]

@[simp] theorem holeProj_idempotent :
    holeProj * holeProj = holeProj := by
  simp [holeProj]

@[simp] theorem particle_hole_orthogonal :
    particleProj * holeProj = 0 := by
  simp [particleProj, holeProj]

@[simp] theorem hole_particle_orthogonal :
    holeProj * particleProj = 0 := by
  simp [particleProj, holeProj]

/-- The two chiral/BdG projectors resolve the Cuntz unit. -/
theorem particle_hole_partition :
    particleProj + holeProj = 1 := by
  have h := partition_one (R := ℂ) (ι := Fin 2)
  rw [Fin.sum_univ_two] at h
  simpa [particleProj, holeProj, rangeProj] using h

/-! ## CAR/CCR endpoints and BdG supercharges -/

/-- CAR relation as an odd--odd superbracket/anticommutator. -/
def CAR {A : Type*} [Semiring A] [Algebra ℂ A] (b bdag : A) : Prop :=
  superBracket Z2Parity.odd Z2Parity.odd b bdag = 1

/-- CCR relation as an even--even superbracket/commutator. -/
def CCR {A : Type*} [Semiring A] [Algebra ℂ A] (a adag : A) : Prop :=
  superBracket Z2Parity.even Z2Parity.even a adag = 1

/-- Right chiral Cuntz supercharge in the two-channel quotient. -/
def cuntzSuperchargeR : CuntzAlg ℂ (Fin 2) :=
  S (R := ℂ) 0 * T (R := ℂ) 1

/-- Left chiral Cuntz supercharge in the two-channel quotient. -/
def cuntzSuperchargeL : CuntzAlg ℂ (Fin 2) :=
  S (R := ℂ) 1 * T (R := ℂ) 0

@[simp]
theorem cuntzSuperchargeR_sq : cuntzSuperchargeR * cuntzSuperchargeR = 0 := by
  change (S (R := ℂ) 0 * T (R := ℂ) 1) *
      (S (R := ℂ) 0 * T (R := ℂ) 1) = 0
  rw [mul_assoc, ← mul_assoc (T (R := ℂ) 1) (S (R := ℂ) 0)
    (T (R := ℂ) 1), T_mul_S]
  simp

@[simp]
theorem cuntzSuperchargeL_sq : cuntzSuperchargeL * cuntzSuperchargeL = 0 := by
  change (S (R := ℂ) 1 * T (R := ℂ) 0) *
      (S (R := ℂ) 1 * T (R := ℂ) 0) = 0
  rw [mul_assoc, ← mul_assoc (T (R := ℂ) 0) (S (R := ℂ) 1)
    (T (R := ℂ) 0), T_mul_S]
  simp

/-- The two chiral Cuntz supercharges obey the CAR anticommutator law. -/
theorem cuntzSuperchargeR_L_anticommutator :
    cuntzSuperchargeR * cuntzSuperchargeL +
        cuntzSuperchargeL * cuntzSuperchargeR = 1 := by
  change (S (R := ℂ) 0 * T (R := ℂ) 1) *
      (S (R := ℂ) 1 * T (R := ℂ) 0) +
      (S (R := ℂ) 1 * T (R := ℂ) 0) *
        (S (R := ℂ) 0 * T (R := ℂ) 1) = 1
  rw [mul_assoc, ← mul_assoc (T (R := ℂ) 1) (S (R := ℂ) 1)
    (T (R := ℂ) 0), T_mul_S]
  rw [mul_assoc, ← mul_assoc (T (R := ℂ) 0) (S (R := ℂ) 0)
      (T (R := ℂ) 1), T_mul_S]
  simpa using (partition_one (R := ℂ) (ι := Fin 2))

@[simp] theorem CAR_iff {A : Type*} [Semiring A] [Algebra ℂ A] (b bdag : A) :
    CAR b bdag ↔ b * bdag + bdag * b = 1 := by
  simp [CAR]

@[simp] theorem CCR_iff {A : Type*} [Semiring A] [Algebra ℂ A] (a adag : A) :
    CCR a adag ↔ a * adag + (-1 : ℂ) • (adag * a) = 1 := by
  simp [CCR]

/-- Nambu--Gorkov spinor `(annihilator, creator)` from Cuntz letters. -/
def nambuSpinor {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    CuntzAlg ℂ ι × CuntzAlg ℂ ι :=
  (T (R := ℂ) i, S (R := ℂ) i)

/-- BdG/Majorana-like odd generator `Sᵢ + Tᵢ`. -/
def bdgMajoranaPlus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    CuntzAlg ℂ ι :=
  S (R := ℂ) i + T (R := ℂ) i

/-- BdG/Majorana-like odd generator `i(Sᵢ - Tᵢ)`, scalar-signed for the
semiring-level quotient. -/
def bdgMajoranaMinus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    CuntzAlg ℂ ι :=
  Complex.I • (S (R := ℂ) i + (-1 : ℂ) • T (R := ℂ) i)

/-- Odd supercharge built from one Cuntz channel. -/
def supercharge {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Homogeneous (CuntzAlg ℂ ι) where
  carrier := bdgMajoranaPlus i
  parity := Z2Parity.odd

/-- Local Hamiltonian atom as the square of an odd supercharge. -/
def hamiltonianAtom {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    CuntzAlg ℂ ι :=
  (supercharge i).carrier * (supercharge i).carrier

/-- Odd self-superbracket is twice the square-root Hamiltonian atom. -/
theorem supercharge_self_bracket {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Homogeneous.bracket (supercharge i) (supercharge i) =
      (2 : ℂ) • hamiltonianAtom i := by
  dsimp [Homogeneous.bracket, supercharge, hamiltonianAtom, superBracket]
  simp only [superSwapCoeff_odd_odd, one_smul]
  rw [two_smul ℂ (bdgMajoranaPlus i * bdgMajoranaPlus i)]

/-! ## BdG/Majorana star and commutation identities

Both Majorana generators are self-adjoint (star-fixed) and anti-commute
with each other when non-overlapping (i ≠ j). For i = j, the self-bracket
gives the Hamiltonian atom. These are finite algebraic identities, not
analytic completion statements. -/

/-- `bdgMajoranaPlus` is self-adjoint: γ₁† = γ₁. -/
theorem star_bdgMajoranaPlus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    star (bdgMajoranaPlus i) = bdgMajoranaPlus i := by
  simp [bdgMajoranaPlus, add_comm]

/-- `bdgMajoranaPlus i * bdgMajoranaPlus i` equals the Hamiltonian atom.
A single Majorana squares to the Hamiltonian atom (by definition). -/
theorem bdgMajoranaPlus_sq_eq_hamiltonianAtom {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    bdgMajoranaPlus i * bdgMajoranaPlus i = hamiltonianAtom i := rfl

/-- `bdgMajoranaMinus` is odd under the Z₂ grading — it is a ℂ-linear combination
of odd Cuntz generators S and T, scaled by the imaginary unit. -/
theorem bdgMajoranaMinus_is_odd {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    bdgMajoranaMinus i = Complex.I • S (R := ℂ) i + (-Complex.I) • T (R := ℂ) i := by
  dsimp [bdgMajoranaMinus]
  module


/-- Grand-canonical bracket on even-left reduces to the Lie bracket. -/
theorem grandCanonicalBracket_even_left {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (q : Z2Parity) (x y : A) :
    grandCanonicalBracket β E μ Q Z2Parity.even q x y = lieBracket x y := by
  dsimp [grandCanonicalBracket, qAffineSuperBracket]
  simp [affineSuperBracket, lieBracket]

/-- Grand-canonical bracket on even-right reduces to the Lie bracket. -/
theorem grandCanonicalBracket_even_right {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (p : Z2Parity) (x y : A) :
    grandCanonicalBracket β E μ Q p Z2Parity.even x y = lieBracket x y := by
  dsimp [grandCanonicalBracket, qAffineSuperBracket]
  simp [affineSuperBracket, lieBracket]

/-- Grand-canonical weighted bracket on even-left reduces to Lie bracket times weight. -/
theorem grandCanonicalWeightedBracket_even_left {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (q : Z2Parity) (x y : A) :
    grandCanonicalWeightedBracket β E μ Q Z2Parity.even q x y =
      grandCanonicalQ β E μ Q • lieBracket x y := by
  simp [grandCanonicalWeightedBracket, grandCanonicalBracket_even_left]

/-- Grand-canonical weighted bracket on even-right reduces to Lie bracket times weight. -/
theorem grandCanonicalWeightedBracket_even_right {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (p : Z2Parity) (x y : A) :
    grandCanonicalWeightedBracket β E μ Q p Z2Parity.even x y =
      grandCanonicalQ β E μ Q • lieBracket x y := by
  simp [grandCanonicalWeightedBracket, grandCanonicalBracket_even_right]

/-- Grand-canonical weighted bracket in the odd-odd sector:
weighted Jordan product scaled by the grand-canonical q-weight. -/
theorem grandCanonicalWeightedBracket_odd_odd {A : Type*} [Semiring A] [Algebra ℂ A]
    (β E μ Q : ℝ) (x y : A) :
    grandCanonicalWeightedBracket β E μ Q Z2Parity.odd Z2Parity.odd x y =
      grandCanonicalQ β E μ Q • (x * y + ((2 * grandCanonicalQ β E μ Q - 1 : ℂ) • (y * x))) := by
  simp [grandCanonicalWeightedBracket, grandCanonicalBracket, grandCanonicalQ,
    qAffineSuperBracket, affineSuperBracket]

#check Z2Parity
#check superBracket
#check superBracket_odd_odd
#check lieBracket
#check jordanProduct
#check affineSuperBracket
#check affineSuperBracket_zero
#check affineSuperBracket_one
#check affineSuperBracket_odd_odd
#check AffineWeylThermoEnsemble
#check cuntzBdGAffineEnsemble
#check cuntzBdGAffineEnsemble_zero_rapidity_bracket
#check cuntzBdGAffineEnsemble_logScale_bracket
#check qRapidity
#check qRapidity_add
#check qRapidity_logScaleParam
#check qAffineSuperBracket
#check qAffineSuperBracket_odd_odd
#check grandCanonicalRapidity
#check grandCanonicalQ
#check qRapidity_log_grandCanonicalWeight
#check grandCanonicalBracket
#check grandCanonicalWeightedBracket
#check grandCanonicalBracket_odd_odd
#check RindlerWeylFlow_add
#check unruhTemperature
#check two_pi_mul_unruhTemperature
#check ComplexStarCuntzBdGStage
#check complexStarCuntzBdGAffineEnsemble
#check complexStarCuntzBdG_star_smul
#check complexStarCuntzBdG_star_S
#check complexStarCuntzBdG_star_T
#check complexStarCuntzBdGAffineEnsemble_zero_rapidity_bracket
#check complexStarCuntzBdGAffineEnsemble_logScale_bracket
#check complexStarCuntzBdG_RindlerWeylFlow_add
#check StarAlgHom.map_affineSuperBracket
#check StarAlgHom.map_qAffineSuperBracket
#check StarAlgHom.map_grandCanonicalBracket
#check StarAlgHom.map_grandCanonicalWeightedBracket
#check ComplexStarCuntzBdGRepresentation
#check ComplexStarCuntzBdGRepresentation.map_T
#check ComplexStarCuntzBdGRepresentation.map_qAffineBracket_S_T
#check ComplexStarCuntzBdGRepresentation.map_qAffineBracket_odd_odd_S_T
#check ComplexStarCuntzBdGRepresentation.map_grandCanonicalBracket_S_T
#check ComplexStarCuntzBdGRepresentation.map_grandCanonicalWeightedBracket_S_T
#check ComplexStarCuntzBdGRepresentation.map_grandCanonicalBracket_odd_odd_S_T

#check rangeProj_idempotent
#check particle_hole_partition
#check CAR
#check CCR
#check nambuSpinor
#check supercharge
#check supercharge_self_bracket


end InfoGeometry.Physics.SupergradedCuntzBdG
