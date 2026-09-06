import Mathlib.Tactic

noncomputable section

namespace LECM2022ElectroweakRadiiISB

abbrev Q := ℚ

def presentationYear : ℕ := 2022
def lowEnergyCommunityMeeting : String := "LECM 2022"
def speaker : String := "Chien-Yeah Seng"
def topic : String := "Electroweak nuclear radii constrain isospin-breaking correction to Vud"

def Vud2 (Vud : Q) : Q := Vud * Vud
def Vus2 (Vus : Q) : Q := Vus * Vus
def Vub2 (Vub : Q) : Q := Vub * Vub
def ckmFirstRowSum (Vud Vus Vub : Q) : Q := Vud2 Vud + Vus2 Vus + Vub2 Vub
def ckmUnitarityDefect (Vud Vus Vub : Q) : Q := ckmFirstRowSum Vud Vus Vub - 1

class HasSpin (α : Type) where
  J : Q

class HasIsospin (α : Type) where
  T : Q

/-- A representation of a superallowed beta decay transition state.
    In physics, these are transitions between 0+ states of an isospin T=1 multiplet. -/
structure SuperallowedBetaDecayState where
  state_id : ℕ

instance : HasSpin SuperallowedBetaDecayState where
  J := 0

instance : HasIsospin SuperallowedBetaDecayState where
  T := 1

def T_superallowed : Q := HasIsospin.T SuperallowedBetaDecayState
def J_superallowed : Q := HasSpin.J SuperallowedBetaDecayState
def bareFermiMatrixSquared : Q := 2
def deltaCMin_permyriad : Q := 10
def deltaCMax_permyriad : Q := 100

def correctedFermiSquared (deltaC : Q) : Q := bareFermiMatrixSquared * (1 - deltaC)
def FtCorrected (ft deltaR deltaC : Q) : Q := ft * (1 + deltaR) * (1 - deltaC)

def betaMonopoleMatrix (offDiagonalRadius : Q) : Q := offDiagonalRadius
def radiusMonopoleMatrix (chargeRadius weakRadius : Q) : Q := chargeRadius - weakRadius
def combinedISBObservable (beta radius : Q) : Q := beta + radius
def exactIsospinRadiusConstraint (x : Q) : Q × Q := (x, -x)
def isbDeviationFromExact (beta radius : Q) : Q := combinedISBObservable beta radius

def uniformSphereCoulombScale (Z R : Q) : Q := Z / R
def isovectorMonopoleScale (NminusZ A : Q) : Q := NminusZ / A

def permyriadToPercent (x : Q) : Q := x / 100
def percentToFraction (x : Q) : Q := x / 100

theorem ckm_unitarity_zero_defect {Vud Vus Vub : Q}
    (h : ckmFirstRowSum Vud Vus Vub = 1) :
    ckmUnitarityDefect Vud Vus Vub = 0 := by
  simp [ckmUnitarityDefect, h]

theorem ckm_sum_345_exact :
    ckmFirstRowSum (3/5) (4/5) 0 = 1 := by
  norm_num [ckmFirstRowSum, Vud2, Vus2, Vub2]

theorem ckm_345_defect_zero :
    ckmUnitarityDefect (3/5) (4/5) 0 = 0 := by
  norm_num [ckmUnitarityDefect, ckmFirstRowSum, Vud2, Vus2, Vub2]

theorem T_superallowed_eq_one :
    T_superallowed = 1 := by
  unfold T_superallowed
  rfl

theorem J_superallowed_eq_zero :
    J_superallowed = 0 := by
  unfold J_superallowed
  rfl

theorem deltaCMin_permyriad_percent :
    permyriadToPercent deltaCMin_permyriad = 1/10 := by
  norm_num [permyriadToPercent, deltaCMin_permyriad]

theorem deltaCMax_permyriad_percent :
    permyriadToPercent deltaCMax_permyriad = 1 := by
  norm_num [permyriadToPercent, deltaCMax_permyriad]

theorem corrected_fermi_zero_delta :
    correctedFermiSquared 0 = bareFermiMatrixSquared := by
  norm_num [correctedFermiSquared, bareFermiMatrixSquared]

theorem corrected_fermi_delta_one_percent :
    correctedFermiSquared (1/100) = 99/50 := by
  norm_num [correctedFermiSquared, bareFermiMatrixSquared]

theorem Ft_zero_corrections : ∀ ft : Q, FtCorrected ft 0 0 = ft := by
  intro ft
  simp [FtCorrected]

theorem exact_isospin_combined_zero (x : Q) :
    combinedISBObservable (exactIsospinRadiusConstraint x).1 (exactIsospinRadiusConstraint x).2 = 0 := by
  simp [combinedISBObservable, exactIsospinRadiusConstraint]

theorem exact_isospin_deviation_zero (x : Q) :
    isbDeviationFromExact (exactIsospinRadiusConstraint x).1 (exactIsospinRadiusConstraint x).2 = 0 := by
  simp [isbDeviationFromExact, combinedISBObservable, exactIsospinRadiusConstraint]

theorem combinedISBObservable_nonzero_eval :
    combinedISBObservable (3/10) (-1/5) = 1/10 := by
  norm_num [combinedISBObservable]

theorem isbDeviation_nonzero_eval :
    isbDeviationFromExact (3/10) (-1/5) = 1/10 := by
  norm_num [isbDeviationFromExact, combinedISBObservable]

theorem monopole_radius_difference_zero_iff {Rp Rw : Q} :
    radiusMonopoleMatrix Rp Rw = 0 ↔ Rp = Rw := by
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · simp [radiusMonopoleMatrix, h]

theorem symmetry_energy_scale_eval :
    isovectorMonopoleScale 2 40 = 1/20 := by
  norm_num [isovectorMonopoleScale]

theorem coulomb_uniform_sphere_eval :
    uniformSphereCoulombScale 20 4 = 5 := by
  norm_num [uniformSphereCoulombScale]

inductive Concept where
  | CKM_First_Row_Unitarity
  | Superallowed_Beta_Decay
  | ISB_Correction_deltaC
  | Electroweak_Nuclear_Radii
  | Isovector_Monopole_Operator
  | Combined_ISB_Observable
  deriving DecidableEq, Repr

inductive Edge where
  | constrains
  | measures
  | corrects
  | probes
  | cancels_under_exact_isospin
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Superallowed_Beta_Decay, Edge.constrains, Concept.CKM_First_Row_Unitarity => true
  | Concept.ISB_Correction_deltaC, Edge.corrects, Concept.Superallowed_Beta_Decay => true
  | Concept.Electroweak_Nuclear_Radii, Edge.probes, Concept.ISB_Correction_deltaC => true
  | Concept.Isovector_Monopole_Operator, Edge.measures, Concept.Electroweak_Nuclear_Radii => true
  | Concept.Combined_ISB_Observable, Edge.cancels_under_exact_isospin, Concept.Isovector_Monopole_Operator => true
  | _, _, _ => false

theorem superallowed_beta_decay_constrains_ckm_first_row_unitarity :
    edgeHolds Concept.Superallowed_Beta_Decay Edge.constrains Concept.CKM_First_Row_Unitarity = true := by
  rfl

theorem deltaC_corrects_superallowed_beta_decay :
    edgeHolds Concept.ISB_Correction_deltaC Edge.corrects Concept.Superallowed_Beta_Decay = true := by
  rfl

theorem electroweak_nuclear_radii_probe_deltaC :
    edgeHolds Concept.Electroweak_Nuclear_Radii Edge.probes Concept.ISB_Correction_deltaC = true := by
  rfl

theorem isovector_monopole_measures_electroweak_nuclear_radii :
    edgeHolds Concept.Isovector_Monopole_Operator Edge.measures Concept.Electroweak_Nuclear_Radii = true := by
  rfl

theorem combined_observable_cancels_under_exact_isospin :
    edgeHolds Concept.Combined_ISB_Observable Edge.cancels_under_exact_isospin Concept.Isovector_Monopole_Operator =
      true := by
  rfl

end LECM2022ElectroweakRadiiISB

end noncomputable section
