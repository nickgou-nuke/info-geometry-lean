import Mathlib
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
import InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement

namespace InfoGeometry.Arithmetic.SarnakLocalCertification

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
open InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement

inductive Archetype
  | arithmetic
  | continuation
  | reflection
  | localCounting
  | localCertification
  | globalCoverage
  deriving DecidableEq, Fintype

abbrev DependencyContext := Finset Archetype

def reflectionContext : DependencyContext :=
  {.continuation, .reflection}

def countingContext : DependencyContext :=
  {.continuation, .localCounting}

def certificationContext : DependencyContext :=
  reflectionContext ∪ countingContext ∪ {.localCertification}

def globalContext : DependencyContext :=
  certificationContext ∪ {.arithmetic, .globalCoverage}

theorem reflection_precedes_certification :
    reflectionContext ≤ certificationContext := by
  decide

theorem counting_precedes_certification :
    countingContext ≤ certificationContext := by
  decide

theorem certification_precedes_global :
    certificationContext ≤ globalContext := by
  decide

theorem reflection_and_counting_are_incomparable :
    ¬ reflectionContext ≤ countingContext ∧
      ¬ countingContext ≤ reflectionContext := by
  decide

def critical_reflection (point : ℂ) : ℂ :=
  1 - star point

theorem critical_reflection_involutive :
    Function.Involutive critical_reflection := by
  intro point
  simp [critical_reflection]

theorem critical_reflection_fixed_iff (point : ℂ) :
    critical_reflection point = point ↔ point.re = 1 / 2 := by
  constructor
  · intro fixed
    have realFixed : 1 - point.re = point.re := by
      simpa [critical_reflection] using congrArg Complex.re fixed
    linarith
  · intro onLine
    apply Complex.ext
    · simp only [critical_reflection, Complex.sub_re, Complex.one_re,
        Complex.star_def, Complex.conj_re]
      linarith
    · simp [critical_reflection]

class RiemannSymmetric (function : ℂ → ℂ) : Prop where
  zero_reflection : ∀ point,
    function point = 0 ↔ function (critical_reflection point) = 0

instance entireRiemannXi_riemannSymmetric : RiemannSymmetric entireRiemannXi where
  zero_reflection point := by
    constructor
    · exact entireRiemannXi_reflected_zero
    · intro reflectedZero
      have twice := entireRiemannXi_reflected_zero reflectedZero
      change entireRiemannXi (critical_reflection (critical_reflection point)) = 0 at twice
      rwa [critical_reflection_involutive point] at twice

structure CertifiedRegion (function : ℂ → ℂ) where
  carrier : Set ℂ
  reflectionInvariant :
    Set.MapsTo critical_reflection carrier carrier
  uniqueZero :
    (carrier ∩ {point | function point = 0}).Subsingleton

variable {function : ℂ → ℂ} [RiemannSymmetric function]

namespace CertifiedRegion

theorem zero_on_critical_line
    (region : CertifiedRegion function) {point : ℂ}
    (member : point ∈ region.carrier)
    (zeroAt : function point = 0) :
    point.re = 1 / 2 := by
  apply (critical_reflection_fixed_iff point).mp
  exact region.uniqueZero
    ⟨region.reflectionInvariant member,
      (RiemannSymmetric.zero_reflection point).mp zeroAt⟩
    ⟨member, zeroAt⟩

theorem nonzero_off_critical_line
    (region : CertifiedRegion function) {point : ℂ}
    (member : point ∈ region.carrier)
    (offLine : point.re ≠ 1 / 2) :
    function point ≠ 0 := by
  intro zeroAt
  exact offLine (region.zero_on_critical_line member zeroAt)

end CertifiedRegion

theorem covered_zeros_on_critical_line
    {Index : Type*}
    (regions : Index → CertifiedRegion function)
    (domain : Set ℂ)
    (coverage :
      ∀ point ∈ domain, function point = 0 →
        ∃ index, point ∈ (regions index).carrier) :
    ∀ point ∈ domain, function point = 0 →
      point.re = 1 / 2 := by
  intro point member zeroAt
  obtain ⟨index, inRegion⟩ := coverage point member zeroAt
  exact (regions index).zero_on_critical_line inRegion zeroAt

theorem finite_height_certificate
    {count : ℕ}
    (regions : Fin count → CertifiedRegion function)
    (height : ℝ)
    (coverage :
      ∀ point : ℂ, |point.im| ≤ height →
        function point = 0 →
        ∃ index, point ∈ (regions index).carrier) :
    ∀ point : ℂ, |point.im| ≤ height →
      function point = 0 → point.re = 1 / 2 := by
  exact covered_zeros_on_critical_line regions
    {point : ℂ | |point.im| ≤ height} coverage

theorem global_confinement_of_certificates_at_every_height
    (certificates :
      ∀ height : ℝ, ∃ count : ℕ,
        ∃ regions : Fin count → CertifiedRegion function,
          ∀ point : ℂ, |point.im| ≤ height →
            function point = 0 →
            ∃ index, point ∈ (regions index).carrier) :
    ∀ point : ℂ, function point = 0 →
      point.re = 1 / 2 := by
  intro point zeroAt
  obtain ⟨count, regions, coverage⟩ := certificates |point.im|
  exact finite_height_certificate regions |point.im| coverage
    point le_rfl zeroAt

theorem symmetric_functions_need_not_have_critical_zeros :
    ¬ (∀ function : ℂ → ℂ, EvenCentered function →
      ∀ point : ℂ, ZeroAt function point → point.re = 0) := by
  intro claimedConfinement
  obtain ⟨function, point, symmetry, zeroAt, _, offAxis⟩ :=
    even_symmetry_allows_off_axis_zero_pair
  exact offAxis (claimedConfinement function symmetry point zeroAt)

def counterexample_f (point : ℂ) : ℂ :=
  point * (point - 1)

theorem counterexample_is_symmetric : RiemannSymmetric counterexample_f := by
  constructor
  intro point
  have reflected : counterexample_f (critical_reflection point) =
      star (counterexample_f point) := by
    simp only [counterexample_f, critical_reflection, map_mul, map_sub, star_one]
    ring
  rw [reflected]
  constructor
  · intro zeroAt
    rw [zeroAt, star_zero]
  · intro reflectedZero
    have originalZero := congrArg star reflectedZero
    simpa only [star_star, star_zero] using originalZero

theorem zero_reflection_does_not_imply_confinement :
    ¬ (∀ candidate : ℂ → ℂ, RiemannSymmetric candidate →
      ∀ point : ℂ, candidate point = 0 → point.re = 1 / 2) := by
  intro claimedConfinement
  have forced := claimedConfinement counterexample_f counterexample_is_symmetric
    0 (by simp [counterexample_f])
  norm_num at forced

end InfoGeometry.Arithmetic.SarnakLocalCertification
