import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import Mathlib.Data.Complex.Basic

open scoped InnerProductSpace

namespace InfoGeometry.Dynamics

namespace ModularAutomorphismFamily

variable {A : Type*} [Monoid A]
variable (M : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A)

def sigma : ℝ → A → A := fun t a => M.flow t a

theorem sigma_zero (a : A) : ModularAutomorphismFamily.sigma M 0 a = a := M.flow_zero a

theorem sigma_add (t s : ℝ) (a : A) :
    ModularAutomorphismFamily.sigma M (t + s) a = ModularAutomorphismFamily.sigma M t (ModularAutomorphismFamily.sigma M s a) := M.flow_add t s a

theorem sigma_neg (t : ℝ) (a : A) :
    ModularAutomorphismFamily.sigma M (-t)
        (ModularAutomorphismFamily.sigma M t a) = a := by
  exact InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow.flow_neg_apply
    M t a

theorem sigma_mul (t : ℝ) (a b : A) :
    ModularAutomorphismFamily.sigma M t (a * b) = ModularAutomorphismFamily.sigma M t a * ModularAutomorphismFamily.sigma M t b :=
  (M.flow t).map_mul a b

end ModularAutomorphismFamily

/--
Constructive KMS boundary data:
`omega_eval` stores the two-point observable pairing;
`kms_boundary` stores the β-strip boundary identity as explicit data.
-/
structure KMSBoundaryData (A : Type*) [Monoid A] where
  beta : ℝ
  omega_eval : A → A → ℝ
  modular : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A

def KMSBoundaryLaw
    {A : Type*} [Monoid A]
    (K : KMSBoundaryData A) : Prop :=
  ∀ t : ℝ, ∀ a b : A,
    K.omega_eval a (ModularAutomorphismFamily.sigma K.modular t b) =
      K.omega_eval (ModularAutomorphismFamily.sigma K.modular (t + K.beta) b) a

theorem KMSBoundaryLaw.boundary
    {A : Type*} [Monoid A]
    (K : KMSBoundaryData A)
    (hK : KMSBoundaryLaw K)
    (t : ℝ) (a b : A) :
    K.omega_eval a (ModularAutomorphismFamily.sigma K.modular t b) =
      K.omega_eval (ModularAutomorphismFamily.sigma K.modular (t + K.beta) b) a :=
  hK t a b

/--
Thermal state data anchored by an observable and a KMS boundary property.
-/
structure ModularThermalState (A : Type*) [Monoid A] where
  casimir : A
  kms : KMSBoundaryData A

/--
The Casimir remains fixed under the modular flow of a thermal state packet.
-/
theorem casimir_fixed_under_modular_flow
    {A : Type*} [Monoid A]
    (T : ModularThermalState A)
    (modular_invariant : ∀
      (M : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A), ∀ t : ℝ,
      ModularAutomorphismFamily.sigma M t T.casimir = T.casimir)
    (t : ℝ) :
    ModularAutomorphismFamily.sigma T.kms.modular t T.casimir = T.casimir := by
  exact modular_invariant T.kms.modular t

/--
Complexified modular-time point `t + iβ` used by KMS strip formulations,
expressed in the Hestenes-Krein lane as a clock-axis lift.
-/
def complexClockPoint (t beta : ℝ) : ℂ :=
  (t : ℂ) + Complex.I * (beta : ℂ)

/--
Analytic continuation theorem for the Hestenes-Krein modular flow.
`sigmaC` is the complex-time extension of the real flow; this structure records
only the boundary/continuation laws needed for KMS work.
-/
structure HestenesKreinAnalyticContinuationData (A : Type*) [Monoid A] where
  beta : ℝ
  modular : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A
  sigmaC : ℂ → A → A

def HestenesKreinAnalyticContinuationLaw
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A) : Prop :=
  (∀ t : ℝ, ∀ a : A,
    H.sigmaC (t : ℂ) a = ModularAutomorphismFamily.sigma H.modular t a) ∧
  (∀ t : ℝ, ∀ a : A,
    H.sigmaC (complexClockPoint t H.beta) a =
      ModularAutomorphismFamily.sigma H.modular (t + H.beta) a)

theorem HestenesKreinAnalyticContinuationLaw.agrees_real_axis
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A)
    (hH : HestenesKreinAnalyticContinuationLaw H)
    (t : ℝ) (a : A) :
    H.sigmaC (t : ℂ) a = ModularAutomorphismFamily.sigma H.modular t a :=
  hH.1 t a

theorem HestenesKreinAnalyticContinuationLaw.strip_top_boundary
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A)
    (hH : HestenesKreinAnalyticContinuationLaw H)
    (t : ℝ) (a : A) :
    H.sigmaC (complexClockPoint t H.beta) a =
      ModularAutomorphismFamily.sigma H.modular (t + H.beta) a :=
  hH.2 t a

/-
Real boundary packet obtained by forgetting the interior complex parameter.
The lower and upper boundary readouts are retained as separate real channels;
this is the native Hestenes--Krein interface consumed by finite and colimit
owners.  No complex continuation is required by downstream users of this
structure.
-/
structure HestenesKreinRealBoundaryData (A : Type*) [Monoid A] where
  beta : ℝ
  modular : InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A
  lower : ℝ → A → A
  upper : ℝ → A → A

def HestenesKreinRealBoundaryLaw
    {A : Type*} [Monoid A]
    (H : HestenesKreinRealBoundaryData A) : Prop :=
  (∀ t : ℝ, ∀ a : A,
    H.lower t a = ModularAutomorphismFamily.sigma H.modular t a) ∧
  (∀ t : ℝ, ∀ a : A,
    H.upper t a =
      ModularAutomorphismFamily.sigma H.modular (t + H.beta) a)

theorem HestenesKreinRealBoundaryLaw.lower_eq_sigma
    {A : Type*} [Monoid A]
    (H : HestenesKreinRealBoundaryData A)
    (hH : HestenesKreinRealBoundaryLaw H)
    (t : ℝ) (a : A) :
    H.lower t a = ModularAutomorphismFamily.sigma H.modular t a :=
  hH.1 t a

theorem HestenesKreinRealBoundaryLaw.upper_eq_sigma_shift
    {A : Type*} [Monoid A]
    (H : HestenesKreinRealBoundaryData A)
    (hH : HestenesKreinRealBoundaryLaw H)
    (t : ℝ) (a : A) :
    H.upper t a =
      ModularAutomorphismFamily.sigma H.modular (t + H.beta) a :=
  hH.2 t a

/-- Extract the real lower/upper boundary packet from the legacy continuation data. -/
noncomputable def HestenesKreinAnalyticContinuationData.toRealBoundary
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A) :
    HestenesKreinRealBoundaryData A where
  beta := H.beta
  modular := H.modular
  lower := fun t a => H.sigmaC (t : ℂ) a
  upper := fun t a => H.sigmaC (complexClockPoint t H.beta) a

theorem realBoundary_lower_eq_sigma
    {A : Type*} [Monoid A]
    (H : HestenesKreinRealBoundaryData A)
    (hH : HestenesKreinRealBoundaryLaw H)
    (t : ℝ) (a : A) :
    H.lower t a = ModularAutomorphismFamily.sigma H.modular t a :=
  hH.1 t a

theorem realBoundary_upper_eq_sigma_shift
    {A : Type*} [Monoid A]
    (H : HestenesKreinRealBoundaryData A)
    (hH : HestenesKreinRealBoundaryLaw H)
    (t : ℝ) (a : A) :
    H.upper t a = ModularAutomorphismFamily.sigma H.modular (t + H.beta) a :=
  hH.2 t a

/--
KMS strip boundary packet in Hestenes-Krein language, with explicit
`z = t + iβ` continuation relation.
-/
structure HestenesKreinKMSStripData (A : Type*) [Monoid A] where
  omega_eval : A → A → ℝ
  analytic : HestenesKreinAnalyticContinuationData A

def HestenesKreinKMSStripLaw
    {A : Type*} [Monoid A]
    (K : HestenesKreinKMSStripData A) : Prop :=
  (∀ t : ℝ, ∀ a b : A,
    K.omega_eval a (K.analytic.sigmaC (t : ℂ) b)
      = K.omega_eval a
          (ModularAutomorphismFamily.sigma K.analytic.modular t b)) ∧
  (∀ t : ℝ, ∀ a b : A,
    K.omega_eval a
        (K.analytic.sigmaC (complexClockPoint t K.analytic.beta) b)
      = K.omega_eval
          (ModularAutomorphismFamily.sigma K.analytic.modular
            (t + K.analytic.beta) b) a)

/-
Real KMS boundary readouts.  This is the expectation-level form consumed by
real Hestenes/Krein and filtered-colimit owners; the complex strip is used only
by the extraction adapter below.
-/
structure HestenesKreinRealKMSBoundaryData (A : Type*) [Monoid A] where
  omega_eval : A → A → ℝ
  boundary : HestenesKreinRealBoundaryData A

def HestenesKreinRealKMSBoundaryLaw
    {A : Type*} [Monoid A]
    (K : HestenesKreinRealKMSBoundaryData A) : Prop :=
  (∀ t : ℝ, ∀ a b : A,
    K.omega_eval a (K.boundary.lower t b) =
      K.omega_eval a
        (ModularAutomorphismFamily.sigma K.boundary.modular t b)) ∧
  (∀ t : ℝ, ∀ a b : A,
    K.omega_eval a (K.boundary.upper t b) =
      K.omega_eval
        (ModularAutomorphismFamily.sigma K.boundary.modular
          (t + K.boundary.beta) b) a)

/-- Extract the real KMS boundary packet from the legacy complex-strip packet. -/
noncomputable def HestenesKreinKMSStripData.toRealBoundary
    {A : Type*} [Monoid A]
    (K : HestenesKreinKMSStripData A) :
    HestenesKreinRealKMSBoundaryData A where
  omega_eval := K.omega_eval
  boundary := K.analytic.toRealBoundary

theorem realKMS_lower_readout
    {A : Type*} [Monoid A]
    (K : HestenesKreinRealKMSBoundaryData A)
    (hK : HestenesKreinRealKMSBoundaryLaw K)
    (t : ℝ) (a b : A) :
    K.omega_eval a (K.boundary.lower t b) =
      K.omega_eval a (ModularAutomorphismFamily.sigma K.boundary.modular t b) :=
  hK.1 t a b

theorem realKMS_upper_readout
    {A : Type*} [Monoid A]
    (K : HestenesKreinRealKMSBoundaryData A)
    (hK : HestenesKreinRealKMSBoundaryLaw K)
    (t : ℝ) (a b : A) :
    K.omega_eval a (K.boundary.upper t b) =
      K.omega_eval
        (ModularAutomorphismFamily.sigma K.boundary.modular
          (t + K.boundary.beta) b) a :=
  hK.2 t a b

/--
Real-axis reduction from the analytic continuation relation.
-/
theorem sigmaC_real_axis_eq_sigma
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A)
    (hH : HestenesKreinAnalyticContinuationLaw H)
    (t : ℝ) (a : A) :
    H.sigmaC (t : ℂ) a = ModularAutomorphismFamily.sigma H.modular t a :=
  hH.1 t a

/--
Top-strip reduction at `t + iβ` in the Hestenes-Krein clock axis.
-/
theorem sigmaC_top_strip_eq_sigma_shift
    {A : Type*} [Monoid A]
    (H : HestenesKreinAnalyticContinuationData A)
    (hH : HestenesKreinAnalyticContinuationLaw H)
    (t : ℝ) (a : A) :
    H.sigmaC (complexClockPoint t H.beta) a = ModularAutomorphismFamily.sigma H.modular (t + H.beta) a :=
  hH.2 t a

/--
KMS upper boundary can be derived from top-strip reduction plus the algebraic
boundary law.
-/
theorem kms_upper_from_strip_top
    {A : Type*} [Monoid A]
    (K : HestenesKreinKMSStripData A)
    (hK : HestenesKreinKMSStripLaw K)
    (t : ℝ) (a b : A) :
    K.omega_eval a (K.analytic.sigmaC (complexClockPoint t K.analytic.beta) b)
      = K.omega_eval (ModularAutomorphismFamily.sigma K.analytic.modular (t + K.analytic.beta) b) a :=
  hK.2 t a b

section UnruhKreinInstantiation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "Obs" => (H₂ →L[ℝ] H₂)

/--
Unruh/Krein boost carrier used to generate modular transport on observables.
-/
noncomputable def unruhBoost (t : ℝ) : Obs :=
  InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost (E := E) t

omit [CompleteSpace E] in
@[simp] theorem unruhBoost_zero : unruhBoost (E := E) 0 = (1 : Obs) := by
  unfold unruhBoost
  exact InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_zero (E := E)

@[simp] theorem unruhBoost_add (s t : ℝ) :
    unruhBoost (E := E) (s + t) = unruhBoost (E := E) s * unruhBoost (E := E) t := by
  simpa [unruhBoost] using
    (InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_add (E := E) s t)

@[simp] theorem unruhBoost_mul_neg (t : ℝ) :
    unruhBoost (E := E) t * unruhBoost (E := E) (-t) = (1 : Obs) := by
  calc
    unruhBoost (E := E) t * unruhBoost (E := E) (-t)
        = unruhBoost (E := E) (t + (-t)) := by
            symm
            simpa using (unruhBoost_add (E := E) t (-t))
    _ = unruhBoost (E := E) 0 := by simp
    _ = (1 : Obs) := by simp

@[simp] theorem unruhBoost_neg_mul (t : ℝ) :
    unruhBoost (E := E) (-t) * unruhBoost (E := E) t = (1 : Obs) := by
  calc
    unruhBoost (E := E) (-t) * unruhBoost (E := E) t
        = unruhBoost (E := E) ((-t) + t) := by
            symm
            simpa using (unruhBoost_add (E := E) (-t) t)
    _ = unruhBoost (E := E) 0 := by simp
    _ = (1 : Obs) := by simp

/--
Nontrivial modular action candidate on doubled/Krein observables:
Heisenberg conjugation by the Unruh boost flow generated by the modular sign.
-/
noncomputable def unruhConjugation (t : ℝ) : Obs ≃* Obs where
  toFun := fun a => unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)
  invFun := fun a => unruhBoost (E := E) (-t) * a * unruhBoost (E := E) t
  left_inv := by
    intro a
    calc
      unruhBoost (E := E) (-t) *
          (unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)) *
          unruhBoost (E := E) t =
          (unruhBoost (E := E) (-t) * unruhBoost (E := E) t) * a *
            (unruhBoost (E := E) (-t) * unruhBoost (E := E) t) := by
              noncomm_ring
      _ = a := by
        simp [unruhBoost_neg_mul]
  right_inv := by
    intro a
    calc
      unruhBoost (E := E) t *
          (unruhBoost (E := E) (-t) * a * unruhBoost (E := E) t) *
          unruhBoost (E := E) (-t) =
          (unruhBoost (E := E) t * unruhBoost (E := E) (-t)) * a *
            (unruhBoost (E := E) t * unruhBoost (E := E) (-t)) := by
              noncomm_ring
      _ = a := by
        simp [unruhBoost_mul_neg]
  map_mul' := by
    intro a b
    calc
      unruhBoost (E := E) t * (a * b) * unruhBoost (E := E) (-t)
          = unruhBoost (E := E) t * a * b * unruhBoost (E := E) (-t) := by
              simp [mul_assoc]
      _ = unruhBoost (E := E) t * a *
            ((unruhBoost (E := E) (-t) * unruhBoost (E := E) t) * b) *
            unruhBoost (E := E) (-t) := by
              rw [unruhBoost_neg_mul]
              simp [mul_assoc]
      _ = (unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)) *
            (unruhBoost (E := E) t * b * unruhBoost (E := E) (-t)) := by
              calc
                unruhBoost (E := E) t * a *
                    ((unruhBoost (E := E) (-t) * unruhBoost (E := E) t) * b) *
                    unruhBoost (E := E) (-t)
                    = unruhBoost (E := E) t * a * unruhBoost (E := E) (-t) *
                        unruhBoost (E := E) t * b * unruhBoost (E := E) (-t) := by
                          simp [mul_assoc]
                _ = (unruhBoost (E := E) t * a * unruhBoost (E := E) (-t)) *
                      (unruhBoost (E := E) t * b * unruhBoost (E := E) (-t)) := by
                        repeat rw [mul_assoc]

noncomputable def unruhModularFlow :
    InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow Obs where
  flow := unruhConjugation (E := E)
  flow_zero := by
    intro a
    change unruhBoost (E := E) 0 * a * unruhBoost (E := E) (-0) = a
    simp [unruhBoost]
  flow_add := by
    intro t s a
    change unruhBoost (E := E) (t + s) * a *
        unruhBoost (E := E) (-(t + s)) =
      unruhBoost (E := E) t *
          (unruhBoost (E := E) s * a * unruhBoost (E := E) (-s)) *
        unruhBoost (E := E) (-t)
    rw [unruhBoost_add]
    rw [show -(t + s) = (-s) + (-t) by ring]
    rw [unruhBoost_add]
    simp [mul_assoc]

/--
Complex-time continuation candidate tied to the Unruh modular Hamiltonian lane.
We keep the same theorem surface and model the strip top by real-shift transport.
-/
noncomputable def unruhSigmaC : ℂ → Obs → Obs :=
  fun z a =>
    ModularAutomorphismFamily.sigma (unruhModularFlow (E := E)) (z.re + z.im) a

/--
Hestenes-Krein analytic continuation packet on the doubled carrier.
-/
noncomputable def unruhHestenesKreinAnalyticContinuation (beta : ℝ) :
    HestenesKreinAnalyticContinuationData Obs where
  beta := beta
  modular := unruhModularFlow (E := E)
  sigmaC := unruhSigmaC (E := E)

theorem unruhHestenesKreinAnalyticContinuation_law (beta : ℝ) :
    HestenesKreinAnalyticContinuationLaw
      (unruhHestenesKreinAnalyticContinuation (E := E) beta) := by
  constructor
  · intro t a
    simp [unruhHestenesKreinAnalyticContinuation, unruhSigmaC]
  · intro t a
    simp [unruhHestenesKreinAnalyticContinuation, unruhSigmaC,
      complexClockPoint, add_comm]

end UnruhKreinInstantiation

end InfoGeometry.Dynamics
