import Mathlib
import InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearPhononRPAAlgebra

/-!
# A common algebraic carrier for one quasiparticle mode and one phonon mode

This module closes the previously abstract CAR--RPA socket on an explicit
associative endomorphism algebra.  The coefficient module is the native real
Zorn split-octonion module, but none of the operator products below uses the
nonassociative Zorn multiplication: all ladder products are compositions in a
linear endomorphism ring.

The carrier

`ℕ → (NativeZorn × NativeZorn)`

combines a two-sheet one-mode CAR module with a countable algebraic boson
occupation module.  It supports exact CAR, exact CCR, all quasiparticle--phonon
cross commutators, and the coefficientwise action of the Zorn derivation Lie
algebra.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearCARPhononCommonCarrier

open InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearPhononRPA

abbrev Coefficient := NativeZorn
abbrev Sheet := FermionSheetModule
abbrev SheetEnd := FermionSheetEnd
abbrev Carrier := ℕ → Sheet
abbrev Operator := Module.End ℝ Carrier

/-- Pointwise lift of a two-sheet endomorphism to the occupation carrier. -/
def pointwiseSheetLift (T : SheetEnd) : Operator where
  toFun ψ n := T (ψ n)
  map_add' ψ φ := by
    funext n
    exact T.map_add (ψ n) (φ n)
  map_smul' c ψ := by
    funext n
    exact T.map_smul c (ψ n)

@[simp] theorem pointwiseSheetLift_apply
    (T : SheetEnd) (ψ : Carrier) (n : ℕ) :
    pointwiseSheetLift T ψ n = T (ψ n) := rfl

/-- The lift preserves composition. -/
theorem pointwiseSheetLift_mul (S T : SheetEnd) :
    pointwiseSheetLift (S * T) =
      pointwiseSheetLift S * pointwiseSheetLift T := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- Pointwise quasiparticle annihilation. -/
def qpAnnihilation : Operator :=
  pointwiseSheetLift fermionAnnihilation

/-- Pointwise quasiparticle creation. -/
def qpCreation : Operator :=
  pointwiseSheetLift fermionCreation

@[simp] theorem qpAnnihilation_apply
    (ψ : Carrier) (n : ℕ) :
    qpAnnihilation ψ n = fermionAnnihilation (ψ n) := rfl

@[simp] theorem qpCreation_apply
    (ψ : Carrier) (n : ℕ) :
    qpCreation ψ n = fermionCreation (ψ n) := rfl

/-- Fermionic nilpotency survives pointwise extension. -/
@[simp] theorem qpAnnihilation_sq :
    qpAnnihilation * qpAnnihilation = 0 := by
  apply LinearMap.ext
  intro ψ
  funext n
  rcases ψ n with ⟨x₀, x₁⟩
  rfl

/-- Fermionic nilpotency survives pointwise extension. -/
@[simp] theorem qpCreation_sq :
    qpCreation * qpCreation = 0 := by
  apply LinearMap.ext
  intro ψ
  funext n
  rcases ψ n with ⟨x₀, x₁⟩
  rfl

/-- Exact one-mode CAR on the common carrier. -/
theorem qp_CAR :
    qpAnnihilation * qpCreation + qpCreation * qpAnnihilation = 1 := by
  apply LinearMap.ext
  intro ψ
  funext n
  rcases ψ n with ⟨x₀, x₁⟩
  rfl

/-- Bosonic creation shift on the occupation coordinate. -/
def phononCreation : Operator where
  toFun ψ n :=
    match n with
    | 0 => 0
    | k + 1 => ψ k
  map_add' ψ φ := by
    funext n
    cases n <;> rfl
  map_smul' c ψ := by
    funext n
    cases n <;> rfl

/-- Bosonic annihilation shift, in the unnormalised polynomial basis. -/
def phononAnnihilation : Operator where
  toFun ψ n := ((n + 1 : ℕ) : ℝ) • ψ (n + 1)
  map_add' ψ φ := by
    funext n
    simp [smul_add]
  map_smul' c ψ := by
    funext n
    simp only [Pi.smul_apply, smul_smul]
    rw [mul_comm]

@[simp] theorem phononCreation_zero (ψ : Carrier) :
    phononCreation ψ 0 = 0 := rfl

@[simp] theorem phononCreation_succ (ψ : Carrier) (n : ℕ) :
    phononCreation ψ (n + 1) = ψ n := rfl

@[simp] theorem phononAnnihilation_apply
    (ψ : Carrier) (n : ℕ) :
    phononAnnihilation ψ n = ((n + 1 : ℕ) : ℝ) • ψ (n + 1) := rfl

/-- Exact Heisenberg CCR on the countable algebraic occupation carrier. -/
theorem phonon_CCR :
    phononAnnihilation * phononCreation -
      phononCreation * phononAnnihilation = 1 := by
  apply LinearMap.ext
  intro ψ
  funext n
  change phononAnnihilation (phononCreation ψ) n -
      phononCreation (phononAnnihilation ψ) n = ψ n
  cases n with
  | zero =>
      change (1 : ℝ) • ψ 0 - 0 = ψ 0
      simp
  | succ n =>
      change (((n + 2 : ℕ) : ℝ) • ψ (n + 1)) -
          (((n + 1 : ℕ) : ℝ) • ψ (n + 1)) = ψ (n + 1)
      rw [← sub_smul]
      have hscalar :
          (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = 1 := by
        norm_num
      rw [hscalar, one_smul]

/-- Quasiparticle annihilation commutes with phonon creation. -/
theorem qpAnnihilation_commutes_phononCreation :
    qpAnnihilation * phononCreation =
      phononCreation * qpAnnihilation := by
  apply LinearMap.ext
  intro ψ
  funext n
  cases n <;> rfl

/-- Quasiparticle creation commutes with phonon creation. -/
theorem qpCreation_commutes_phononCreation :
    qpCreation * phononCreation =
      phononCreation * qpCreation := by
  apply LinearMap.ext
  intro ψ
  funext n
  cases n <;> rfl

/-- Quasiparticle annihilation commutes with phonon annihilation. -/
theorem qpAnnihilation_commutes_phononAnnihilation :
    qpAnnihilation * phononAnnihilation =
      phononAnnihilation * qpAnnihilation := by
  apply LinearMap.ext
  intro ψ
  funext n
  change fermionAnnihilation (((n + 1 : ℕ) : ℝ) • ψ (n + 1)) =
    ((n + 1 : ℕ) : ℝ) • fermionAnnihilation (ψ (n + 1))
  exact fermionAnnihilation.map_smul _ _

/-- Quasiparticle creation commutes with phonon annihilation. -/
theorem qpCreation_commutes_phononAnnihilation :
    qpCreation * phononAnnihilation =
      phononAnnihilation * qpCreation := by
  apply LinearMap.ext
  intro ψ
  funext n
  change fermionCreation (((n + 1 : ℕ) : ℝ) • ψ (n + 1)) =
    ((n + 1 : ℕ) : ℝ) • fermionCreation (ψ (n + 1))
  exact fermionCreation.map_smul _ _

/-- Concrete one-mode nuclear quasiparticle CAR structure. -/
def commonCAR : QuasiparticleCAR (Fin 1) Operator where
  a := fun _ => qpAnnihilation
  adag := fun _ => qpCreation
  anticomm_a_a := by
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    rw [qpAnnihilation_sq]
    simp
  anticomm_adag_adag := by
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    rw [qpCreation_sq]
    simp
  anticomm_a_adag := by
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    simpa using qp_CAR

/-- Concrete one-mode exact phonon CCR structure. -/
def commonRPA : PhononRPA (Fin 1) Operator where
  Q := fun _ => phononAnnihilation
  Qdag := fun _ => phononCreation
  comm_Q_Q := by
    intro i j
    simp [comm]
  comm_Qdag_Qdag := by
    intro i j
    simp [comm]
  comm_Q_Qdag := by
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    simpa [comm] using phonon_CCR

/-- The abstract coupled quasiparticle--phonon socket now has a concrete
instance on one associative operator algebra. -/
def commonCoupledSystem :
    CoupledQuasiparticlePhononSystem (Fin 1) (Fin 1) Operator where
  car := commonCAR
  rpa := commonRPA
  cross_comm_a_Q := by
    intro i j
    rw [comm, qpAnnihilation_commutes_phononAnnihilation, sub_self]
  cross_comm_adag_Q := by
    intro i j
    rw [comm, qpCreation_commutes_phononAnnihilation, sub_self]
  cross_comm_a_Qdag := by
    intro i j
    rw [comm, qpAnnihilation_commutes_phononCreation, sub_self]
  cross_comm_adag_Qdag := by
    intro i j
    rw [comm, qpCreation_commutes_phononCreation, sub_self]

/-! ## Coefficient derivations as even internal symmetries -/

/-- Coefficientwise lift of a native Zorn endomorphism. -/
def coefficientLift (D : NativeZornEnd) : Operator :=
  pointwiseSheetLift (diagonalSheetLift D)

@[simp] theorem coefficientLift_apply
    (D : NativeZornEnd) (ψ : Carrier) (n : ℕ) :
    coefficientLift D ψ n =
      (D (ψ n).1, D (ψ n).2) := rfl

/-- The coefficient lift preserves composition. -/
theorem coefficientLift_mul (D E : NativeZornEnd) :
    coefficientLift (D * E) = coefficientLift D * coefficientLift E := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- Consequently it preserves the endomorphism commutator. -/
theorem coefficientLift_commutator (D E : NativeZornEnd) :
    coefficientLift (D * E - E * D) =
      coefficientLift D * coefficientLift E -
        coefficientLift E * coefficientLift D := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- Coefficient endomorphisms commute with both fermionic ladder maps. -/
theorem coefficientLift_even_CAR (D : NativeZornEnd) :
    coefficientLift D * qpAnnihilation =
        qpAnnihilation * coefficientLift D ∧
      coefficientLift D * qpCreation =
        qpCreation * coefficientLift D := by
  constructor
  · apply LinearMap.ext
    intro ψ
    funext n
    have h := LinearMap.congr_fun
      (diagonalSheetLift_commutes_annihilation D) (ψ n)
    simpa [coefficientLift, qpAnnihilation, pointwiseSheetLift,
      Module.End.mul_apply] using h
  · apply LinearMap.ext
    intro ψ
    funext n
    have h := LinearMap.congr_fun
      (diagonalSheetLift_commutes_creation D) (ψ n)
    simpa [coefficientLift, qpCreation, pointwiseSheetLift,
      Module.End.mul_apply] using h

/-- Coefficient endomorphisms commute with both bosonic occupation shifts. -/
theorem coefficientLift_even_CCR (D : NativeZornEnd) :
    coefficientLift D * phononAnnihilation =
        phononAnnihilation * coefficientLift D ∧
      coefficientLift D * phononCreation =
        phononCreation * coefficientLift D := by
  constructor
  · apply LinearMap.ext
    intro ψ
    funext n
    change (D (((n + 1 : ℕ) : ℝ) • (ψ (n + 1)).1),
        D (((n + 1 : ℕ) : ℝ) • (ψ (n + 1)).2)) =
      (((n + 1 : ℕ) : ℝ) • D (ψ (n + 1)).1,
        ((n + 1 : ℕ) : ℝ) • D (ψ (n + 1)).2)
    constructor <;> exact D.map_smul _ _
  · apply LinearMap.ext
    intro ψ
    funext n
    cases n <;> rfl

/-- Compact concrete closure packet. -/
theorem common_car_phonon_packet
    (D E : NativeZornDerLie) :
    qpAnnihilation * qpCreation + qpCreation * qpAnnihilation = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      qpCreation * phononCreation = phononCreation * qpCreation ∧
      coefficientLift ((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D : NativeZornEnd) *
            coefficientLift (E : NativeZornEnd) -
          coefficientLift (E : NativeZornEnd) *
            coefficientLift (D : NativeZornEnd) ∧
      coefficientLift (D : NativeZornEnd) * qpCreation =
        qpCreation * coefficientLift (D : NativeZornEnd) := by
  refine ⟨qp_CAR, phonon_CCR, qpCreation_commutes_phononCreation, ?_,
    (coefficientLift_even_CAR (D : NativeZornEnd)).2⟩
  rw [derivationLie_bracket_apply]
  exact coefficientLift_commutator (D : NativeZornEnd) (E : NativeZornEnd)

end InfoGeometry.Physics.NuclearCARPhononCommonCarrier
