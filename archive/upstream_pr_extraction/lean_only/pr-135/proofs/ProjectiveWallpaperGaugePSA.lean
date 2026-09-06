import Mathlib

/-!
# Projective wallpaper symmetry algebras with gauge structures

Digest/formalization of Chen--Zhang--Yang--Zhao,
"Classification of time-reversal-invariant crystals with gauge structures",
Nature Communications 14, 743 (2023), DOI 10.1038/s41467-023-36447-7.

Core facts formalized:

* for 17 wallpaper groups, time-reversal-invariant projective algebras are
  classified by `H²(G,Z₂) ≃ Z₂^n`;
* Table 1 totals `458` projective symmetry algebras (PSAs), of which `189` are
  algebraically non-equivalent;
* the five invariant classes are `σ, α, β, η, τ`;
* `σ=-1` is the algebraic π-flux/magnetic-translation commutator;
* `α=-1` is a projective square-root of `-I`, matching the half-integer
  logarithm/spinorial branch used in the ribbon formalization;
* the three physical signatures are shifted high-symmetry momenta, enforced
  nontrivial Zak phase, and a spinless eightfold nodal point.
-/

noncomputable section

namespace ProjectiveWallpaperGaugePSA

/-! ## 1. Table 1 counts -/

/-- The 17 wallpaper groups in IUCr notation. -/
inductive WallpaperGroup where
  | p1 | p2 | pm | pg | cm | pmm | pmg | pgg | cmm | p4 | p4m | p4g | p3 | p3m1 | p31m | p6 | p6m
  deriving DecidableEq, Repr

/-- Explicit list of all 17 groups. -/
def allWallpaperGroups : List WallpaperGroup :=
  [.p1, .p2, .pm, .pg, .cm, .pmm, .pmg, .pgg, .cmm,
   .p4, .p4m, .p4g, .p3, .p3m1, .p31m, .p6, .p6m]

/-- Exponent `n` for `H²(G,Z₂) ≃ Z₂^n`, from Table 1. -/
def H2Exponent : WallpaperGroup → ℕ
  | .p1 => 1
  | .p2 => 4
  | .pm => 4
  | .pg => 1
  | .cm => 2
  | .pmm => 8
  | .pmg => 4
  | .pgg => 2
  | .cmm => 5
  | .p4 => 3
  | .p4m => 6
  | .p4g => 3
  | .p3 => 1
  | .p3m1 => 2
  | .p31m => 2
  | .p6 => 2
  | .p6m => 4

/-- Number `N_G` of algebraically non-equivalent PSAs, from Table 1. -/
def nonEquivalentPSACount : WallpaperGroup → ℕ
  | .p1 => 2
  | .p2 => 5
  | .pm => 10
  | .pg => 2
  | .cm => 4
  | .pmm => 51
  | .pmg => 12
  | .pgg => 3
  | .cmm => 18
  | .p4 => 6
  | .p4m => 40
  | .p4g => 6
  | .p3 => 2
  | .p3m1 => 4
  | .p31m => 4
  | .p6 => 4
  | .p6m => 16

/-- There are 17 wallpaper groups. -/
theorem allWallpaperGroups_length : allWallpaperGroups.length = 17 := by
  norm_num [allWallpaperGroups]

/-- Number of PSAs for a group: `|Z₂^n|=2^n`. -/
def PSACount (G : WallpaperGroup) : ℕ := 2 ^ H2Exponent G

/-- Total number of PSAs in Table 1. -/
def totalPSACount : ℕ := (allWallpaperGroups.map PSACount).sum

/-- Total number of algebraically non-equivalent PSAs in Table 1. -/
def totalNonEquivalentPSACount : ℕ := (allWallpaperGroups.map nonEquivalentPSACount).sum

/-- Chen et al. Table 1: 458 PSAs. -/
theorem totalPSACount_eq_458 : totalPSACount = 458 := by
  norm_num [totalPSACount, allWallpaperGroups, PSACount, H2Exponent]

/-- Chen et al. Table 1: 189 algebraically non-equivalent PSAs. -/
theorem totalNonEquivalentPSACount_eq_189 : totalNonEquivalentPSACount = 189 := by
  norm_num [totalNonEquivalentPSACount, allWallpaperGroups, nonEquivalentPSACount]

/-! ## 2. Five invariant classes and projective relations -/

/-- The five classes of Z₂-valued cohomology invariants used in the paper. -/
inductive InvariantClass where
  | sigma   -- translation commutator / gauge flux
  | alpha   -- projective rotational invariant
  | beta    -- mirror-square invariant
  | eta     -- mirror/glide-translation commutation invariant
  | tau     -- glide-square/fractional translation invariant
  deriving DecidableEq, Repr

/-- Explicit list of the five invariant classes. -/
def invariantClasses : List InvariantClass := [.sigma, .alpha, .beta, .eta, .tau]

theorem invariantClasses_length : invariantClasses.length = 5 := by
  norm_num [invariantClasses]

/-- A Z₂-valued phase/factor system sign. -/
inductive Z2Phase where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Interpret `Z₂` phase as a complex number. -/
def Z2Phase.toComplex : Z2Phase → ℂ
  | .plus => 1
  | .minus => -1

/-- The nontrivial phase squares to `+1`. -/
theorem minusPhase_sq : Z2Phase.toComplex .minus * Z2Phase.toComplex .minus = 1 := by
  norm_num [Z2Phase.toComplex]

/-- A projective symmetry algebra carrying cohomology invariant labels. -/
structure ProjectiveSymmetryAlgebra where
  group : WallpaperGroup
  invariant : InvariantClass → Z2Phase

/-- Ordinary representations have all invariants `+1`. -/
def ordinaryPSA (G : WallpaperGroup) : ProjectiveSymmetryAlgebra where
  group := G
  invariant := fun _ => .plus

/-- A π-flux PSA has nontrivial `σ`. -/
def piFluxTranslationPSA (G : WallpaperGroup) : ProjectiveSymmetryAlgebra where
  group := G
  invariant := fun
    | .sigma => .minus
    | _ => .plus

/-- If `σ=-1`, the translation commutator is the π-flux sign. -/
theorem piFlux_sigma_minus (G : WallpaperGroup) :
    (piFluxTranslationPSA G).invariant .sigma = .minus := rfl

/-! ## 3. Matrices for `σ=-1` and `α=-1` -/

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Magnetic translation representative `L_a`. -/
def La : M2C := !![1, 0; 0, -1]

/-- Magnetic translation representative `L_b`. -/
def Lb : M2C := !![0, 1; 1, 0]

/-- The first magnetic translation representative is involutive. -/
theorem La_sq : La * La = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [La]

/-- The second magnetic translation representative is involutive. -/
theorem Lb_sq : Lb * Lb = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lb]

/-- `L_a L_b L_a⁻¹ L_b⁻¹ = -I`, the `σ=-1` π-flux invariant. -/
theorem magnetic_translation_commutator_neg :
    La * Lb * La * Lb = -(1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [La, Lb, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- The π-flux magnetic translations genuinely fail to commute. -/
theorem magnetic_translations_noncommute : La * Lb ≠ Lb * La := by
  intro h
  have hentry := congr_fun (congr_fun h 0) 1
  norm_num [La, Lb, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- Projective rotation/square-root representative with square `-I`. -/
def projectiveHalfRotation : M2C := !![I, 0; 0, -I]

/-- `α=-1` is represented by a symmetry whose square is `-I`. -/
theorem projectiveHalfRotation_sq_neg :
    projectiveHalfRotation * projectiveHalfRotation = -(1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveHalfRotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply,
      Complex.I_mul_I]

/-! ## 4. Physical signatures -/

/-- The three physical signatures identified in the paper. -/
inductive PSASignature where
  | shiftedHighSymmetryMomenta
  | enforcedNontrivialZakPhase
  | spinlessEightfoldNodalPoint
  deriving DecidableEq, Repr

/-- Explicit signature list. -/
def psaSignatures : List PSASignature :=
  [.shiftedHighSymmetryMomenta, .enforcedNontrivialZakPhase, .spinlessEightfoldNodalPoint]

theorem psaSignatures_length : psaSignatures.length = 3 := by
  norm_num [psaSignatures]

/-- A π Zak phase has Wilson loop `-1`; encoded as the nontrivial Z₂ phase. -/
def piZakWilsonPhase : Z2Phase := .minus

/-- Nontrivial Zak phase gives Wilson sign `-1`. -/
theorem piZakWilsonPhase_complex : piZakWilsonPhase.toComplex = (-1 : ℂ) := rfl

end ProjectiveWallpaperGaugePSA
