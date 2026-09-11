import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeEnergyNative
import InfoGeometry.Canonical.MadelungLogScaleFramework
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Canonical.FiniteCartanSouriauMetriplecticBridge
import InfoGeometry.Arithmetic.MeromorphicLogLocalSystem
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
import InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator
import InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow

/-!
# Finite primon logarithmic phase lift

The prime energy is the native real quantity `log p`.  A finite logarithmic
generator has a scalar modular part `-σ log p` and a sheeted phase part
`-t log p + 2π n`.  The generator is represented in the existing real
`ChiralPhase` carrier and is transported to the existing finite-to-colimit
carrier by `chiralPhaseLift`.

This is a finite coordinate theorem.  It does not identify the phase lift
with a global complex logarithm or with an analytic continuation.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonPhaseLift

open InfoGeometry.Algebraic
open InfoGeometry.Arithmetic.PrimeEnergyNative
open InfoGeometry.Canonical.MadelungLogScaleFramework
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open InfoGeometry.Algebraic.CartanSouriauMassieu
open InfoGeometry.Canonical.FiniteCartanSouriauMetriplecticBridge
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Arithmetic.MeromorphicLogLocalSystem
open InfoGeometry.Clifford.HestenesWindingRotor
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
open InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator

/-! ## One prime mode -/

def primonLogGenerator
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) : ChiralPhase :=
  ⟨-σ * Real.log (p : ℝ),
    -t * Real.log (p : ℝ) + 2 * Real.pi * (n : ℝ)⟩

def primonPhaseLift
    (k : ℕ) (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier :=
  chiralPhaseLift k (primonLogGenerator σ t p n)

@[simp] theorem primonLogGenerator_scalar
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (primonLogGenerator σ t p n).scalar = -σ * Real.log (p : ℝ) :=
  rfl

@[simp] theorem primonLogGenerator_bivector
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (primonLogGenerator σ t p n).bivector =
      -t * Real.log (p : ℝ) + 2 * Real.pi * (n : ℝ) :=
  rfl

/-! ## Critical-line calibration of the scalar channel -/

/--
The scalar component of the logarithmic prime lift is the logarithm of the
finite holonomy modulus after centering the real spectral coordinate at
`1 / 2`.  This is a readout identity: it does not identify the arithmetic
parameter with a rotor parameter by definition.
-/
theorem primonLogGenerator_scalar_exp_eq_criticalLineHolonomyModulus
    (s : ℂ) (t : ℝ) (p : Nat.Primes) (n : ℤ) :
    Real.exp ((primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).scalar) =
      criticalLineHolonomyModulus s (p : ℕ) := by
  simp [primonLogGenerator, criticalLineHolonomyModulus]

theorem primonLogGenerator_criticalLine_scalar_zero
    (s : ℂ) (hs : s.re = (1 / 2 : ℝ)) (t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).scalar = 0 := by
  simp [primonLogGenerator, hs]

theorem primonLogGenerator_criticalLine_scalar_zero_iff
    (s : ℂ) (t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).scalar = 0 ↔
      s.re = (1 / 2 : ℝ) := by
  rw [primonLogGenerator_scalar]
  constructor
  · intro h
    have hmul : (s.re - (1 / 2 : ℝ)) * Real.log (p : ℝ) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hmul with hcenter | hlog
    · linarith
    · exact (prime_log_ne_zero p hlog).elim
  · intro hs
    simp [hs]

theorem primonLogGenerator_centered_spectral_coordinates
    (s : ℂ) (p : Nat.Primes) (n : ℤ) :
    ((primonLogGenerator (s.re - (1 / 2 : ℝ)) s.im p n).scalar,
      (primonLogGenerator (s.re - (1 / 2 : ℝ)) s.im p n).bivector) =
      (-((s.re - (1 / 2 : ℝ)) * Real.log (p : ℝ)),
        -s.im * Real.log (p : ℝ) + 2 * Real.pi * (n : ℝ)) := by
  rw [primonLogGenerator_scalar, primonLogGenerator_bivector]
  congr 1
  ring

theorem primonLogGenerator_scalar_exp_eq_one_iff_criticalLine
    (s : ℂ) (t : ℝ) (p : Nat.Primes) (n : ℤ) :
    Real.exp ((primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).scalar) = 1 ↔
      s.re = (1 / 2 : ℝ) := by
  rw [primonLogGenerator_scalar_exp_eq_criticalLineHolonomyModulus]
  apply criticalLineHolonomyModulus_eq_one_iff
  have hp : Nat.Prime (p : ℕ) := p.property
  exact_mod_cast hp.one_lt

/-! ## Explicit calibration coordinates for the existing loxodromic owner -/

theorem primonLogGenerator_calibrated_parameters
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (-(primonLogGenerator σ t p n).scalar,
      -((primonLogGenerator σ t p n).bivector - 2 * Real.pi * (n : ℝ))) =
      (σ * Real.log (p : ℝ), t * Real.log (p : ℝ)) := by
  simp [primonLogGenerator]

theorem primonLogGenerator_boostParameter_eq_zero_iff_criticalLine
    (s : ℂ) (t : ℝ) (p : Nat.Primes) (n : ℤ) :
    -(primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).scalar = 0 ↔
      s.re = (1 / 2 : ℝ) := by
  rw [primonLogGenerator_scalar]
  have hlog : Real.log (p : ℝ) ≠ 0 := prime_log_ne_zero p
  constructor
  · intro h
    have hmul : (s.re - (1 / 2 : ℝ)) * Real.log (p : ℝ) = 0 := by
      linarith
    rcases mul_eq_zero.mp hmul with hcenter | hlog_zero
    · linarith
    · exact (hlog hlog_zero).elim
  · intro hs
    rw [hs]
    ring

theorem primonLogGenerator_calibrated_loxodromic_inverse
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    loxodromicRotor
        (-(primonLogGenerator σ t p n).scalar)
        (-((primonLogGenerator σ t p n).bivector - 2 * Real.pi * (n : ℝ))) *
      loxodromicRotor
        ((primonLogGenerator σ t p n).scalar)
        ((primonLogGenerator σ t p n).bivector - 2 * Real.pi * (n : ℝ)) =
      (1 : Operator) := by
  simpa only [neg_neg] using
    (loxodromicRotor_mul_neg
      (-(primonLogGenerator σ t p n).scalar)
      (-((primonLogGenerator σ t p n).bivector - 2 * Real.pi * (n : ℝ))))

theorem primonLogGenerator_phase_exp_sheet_invariant
    (t : ℝ) (p : Nat.Primes) (n : ℤ) :
    Complex.exp
        (InfoGeometry.Compatibility.chiralToComplex
          (primonLogGenerator 0 t p n)) =
      Complex.exp
        (-(Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ))) := by
  rw [InfoGeometry.Compatibility.chiralToComplex_eq_scalar_add_bivector_I]
  simp only [primonLogGenerator]
  have harg :
      (((-t * Real.log (p : ℝ) + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
        -(Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) +
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg]
  simp only [Complex.exp_add, neg_zero, zero_mul]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem primonLogGenerator_phase_exp_eq_bkPrimePhase
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ)
    (hlog : ∀ p : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P,
      logPrime p = Real.log (p.1 : ℝ))
    (t : ℝ) (p : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P) :
    Complex.exp
        (InfoGeometry.Compatibility.chiralToComplex
          (primonLogGenerator 0 t
            ⟨p.1, P.prime_mem p.1 p.property⟩ 0)) =
      bkPrimePhase logPrime t p := by
  rw [primonLogGenerator_phase_exp_sheet_invariant]
  simp [bkPrimePhase, hlog p]

def bkStateRotor {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ)
    (t : ℝ) (S : PrimeCantorBerryKeatingOperator.Vertex P) :
    InfoGeometry.Geometry.RealChiralPhase :=
  ⟨Real.cos (t * bkEnergy logPrime S),
    -Real.sin (t * bkEnergy logPrime S)⟩

theorem bkStatePhase_insert_of_not_mem {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) (t : ℝ)
    (p : PrimeCantorBerryKeatingOperator.PrimeMode P)
    (S : PrimeCantorBerryKeatingOperator.Vertex P) (hp : p ∉ S) :
    bkStatePhase logPrime t (insert p S) =
      bkPrimePhase logPrime t p * bkStatePhase logPrime t S := by
  unfold bkStatePhase bkPrimePhase
  rw [show bkEnergy logPrime (insert p S) =
      logPrime p + bkEnergy logPrime S by simp [bkEnergy, hp]]
  rw [show -(Complex.I * (t : ℂ) *
      ((logPrime p + bkEnergy logPrime S : ℝ) : ℂ)) =
      (-(Complex.I * (t : ℂ) * (logPrime p : ℂ))) +
        (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ))) by
    push_cast
    ring]
  rw [Complex.exp_add]

theorem bkStateRotor_complexification {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ)
    (t : ℝ) (S : PrimeCantorBerryKeatingOperator.Vertex P) :
    InfoGeometry.Compatibility.chiralToComplex
        (InfoGeometry.Compatibility.realChiralPhaseEquiv
          (bkStateRotor logPrime t S)) =
      bkStatePhase logPrime t S := by
  rw [InfoGeometry.Compatibility.chiralToComplex_eq_scalar_add_bivector_I]
  simp only [InfoGeometry.Compatibility.realChiralPhaseEquiv_scalar,
    InfoGeometry.Compatibility.realChiralPhaseEquiv_bivector]
  unfold bkStateRotor bkStatePhase
  change (Real.cos (t * bkEnergy logPrime S) : ℂ) +
      ((-Real.sin (t * bkEnergy logPrime S) : ℝ) : ℂ) * Complex.I =
    Complex.exp (-(Complex.I * (t : ℂ) *
      (bkEnergy logPrime S : ℂ)))
  have harg :
      -(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ)) =
        ((-(t * bkEnergy logPrime S) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

theorem bkStatePhase_eq_product_primon_phase
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (t : ℝ)
    (S : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.Vertex P) :
    bkStatePhase (fun p => Real.log (p.1 : ℝ)) t S =
      Finset.prod S (fun p =>
        Complex.exp
          (InfoGeometry.Compatibility.chiralToComplex
            (primonLogGenerator 0 t
              ⟨p.1, P.prime_mem p.1 p.property⟩ 0))) := by
  induction S using Finset.induction_on with
  | empty =>
      simp [bkStatePhase, bkEnergy]
  | @insert p S hp ih =>
      rw [bkStatePhase_insert_of_not_mem _ t p S hp, ih,
        Finset.prod_insert hp]
      rw [primonLogGenerator_phase_exp_eq_bkPrimePhase
        (fun q => Real.log (q.1 : ℝ)) (fun q => rfl) t p]

theorem bkStateRotor_complexification_eq_product_primon_phase
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ)
    (hlog : ∀ p : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P,
      logPrime p = Real.log (p.1 : ℝ))
    (t : ℝ)
    (S : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.Vertex P) :
    InfoGeometry.Compatibility.chiralToComplex
        (InfoGeometry.Compatibility.realChiralPhaseEquiv
          (bkStateRotor logPrime t S)) =
      Finset.prod S (fun p =>
        Complex.exp
          (InfoGeometry.Compatibility.chiralToComplex
            (primonLogGenerator 0 t
              ⟨p.1, P.prime_mem p.1 p.property⟩ 0))) := by
  have hlog_eq : logPrime = (fun p => Real.log (p.1 : ℝ)) := by
    funext p
    exact hlog p
  rw [hlog_eq, bkStateRotor_complexification]
  exact bkStatePhase_eq_product_primon_phase t S

theorem primonLogGenerator_criticalLine_calibrated_rotor
    (s : ℂ) (hs : s.re = (1 / 2 : ℝ)) (t : ℝ)
    (p : Nat.Primes) (n : ℤ) :
    loxodromicRotor
        (-(primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).scalar)
        (-((primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).bivector -
          2 * Real.pi * (n : ℝ))) =
      phaseRotor (t * Real.log (p : ℝ)) := by
  have hscalar := primonLogGenerator_criticalLine_scalar_zero s hs t p n
  have htheta :
      -((primonLogGenerator (s.re - (1 / 2 : ℝ)) t p n).bivector -
        2 * Real.pi * (n : ℝ)) = t * Real.log (p : ℝ) := by
    simp [primonLogGenerator]
  rw [hscalar, htheta, neg_zero, loxodromicRotor_zero_boost]

theorem primonLogGenerator_sheet_add
    (σ t : ℝ) (p : Nat.Primes) (n m : ℤ) :
    (primonLogGenerator σ t p (n + m)).bivector =
      (primonLogGenerator σ t p n).bivector + 2 * Real.pi * (m : ℝ) := by
  simp [primonLogGenerator, Int.cast_add]
  ring

theorem primonLogGenerator_normSq
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (primonLogGenerator σ t p n).normSq =
      (-σ * Real.log (p : ℝ)) ^ 2 +
        (-t * Real.log (p : ℝ) + 2 * Real.pi * (n : ℝ)) ^ 2 := by
  rfl

theorem primonLogGenerator_normSq_pos_of_sigma_ne_zero
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) (hσ : σ ≠ 0) :
    0 < (primonLogGenerator σ t p n).normSq := by
  rw [primonLogGenerator_normSq]
  have hlog : Real.log (p : ℝ) ≠ 0 := prime_log_ne_zero p
  have hscalar : -σ * Real.log (p : ℝ) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hσ) hlog
  have hsq : 0 < (-σ * Real.log (p : ℝ)) ^ 2 :=
    sq_pos_of_ne_zero hscalar
  nlinarith [sq_nonneg
    (-t * Real.log (p : ℝ) + 2 * Real.pi * (n : ℝ))]

theorem primonPhaseLift_readout
    (k : ℕ) (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    primonPhaseLift k σ t p n =
      (primonLogGenerator σ t p n).scalar •
          (1 : InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier) +
        (primonLogGenerator σ t p n).bivector • globalPhaseAxis := by
  exact chiralPhaseLift_readout k (primonLogGenerator σ t p n)

theorem primonPhaseLift_sheet_add_readout
    (k : ℕ) (σ t : ℝ) (p : Nat.Primes) (n m : ℤ) :
    primonPhaseLift k σ t p (n + m) =
      (primonLogGenerator σ t p (n + m)).scalar •
          (1 : InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier) +
        (primonLogGenerator σ t p n).bivector • globalPhaseAxis +
        (2 * Real.pi * (m : ℝ)) • globalPhaseAxis := by
  rw [primonPhaseLift_readout, primonLogGenerator_sheet_add]
  rw [primonLogGenerator_scalar]
  rw [add_smul]
  abel

/-! ## Finite prime packets -/

def finitePrimonLogPacket
    (N : ℕ) (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) : Fin N → ChiralPhase :=
  fun i => primonLogGenerator σ t (p i) (sheet i)

def finitePrimonPhasePacket
    (k N : ℕ) (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) :
    Fin N → InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier :=
  fun i => primonPhaseLift k σ t (p i) (sheet i)

@[simp] theorem finitePrimonLogPacket_apply
    (N : ℕ) (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) (i : Fin N) :
    finitePrimonLogPacket N p σ t sheet i =
      primonLogGenerator σ t (p i) (sheet i) :=
  rfl

@[simp] theorem finitePrimonPhasePacket_apply
    (k N : ℕ) (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) (i : Fin N) :
    finitePrimonPhasePacket k N p σ t sheet i =
      primonPhaseLift k σ t (p i) (sheet i) :=
  rfl

theorem finitePrimonLogPacket_sheet_add
    (N : ℕ) (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet shift : Fin N → ℤ) (i : Fin N) :
    (finitePrimonLogPacket N p σ t (fun j => sheet j + shift j) i).bivector =
      (finitePrimonLogPacket N p σ t sheet i).bivector +
        2 * Real.pi * (shift i : ℝ) := by
  exact primonLogGenerator_sheet_add σ t (p i) (sheet i) (shift i)

/-! The arithmetic sheet deck action is the meromorphic winding pairing. -/

theorem finitePrimonPhase_bivector_weighted_sheet_add
    {N : ℕ} (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet shift : Fin N → ℤ)
    (γ : HomologyLoop (Fin N)) :
    (∑ i : Fin N, γ.winding i *
        (finitePrimonLogPacket N p σ t (fun j => sheet j + shift j) i).bivector) =
      (∑ i : Fin N, γ.winding i *
        (finitePrimonLogPacket N p σ t sheet i).bivector) +
        2 * Real.pi *
          deRhamPairing ⟨shift⟩ γ := by
  simp_rw [finitePrimonLogPacket_sheet_add]
  unfold deRhamPairing
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hphase :
      (∑ i : Fin N, (γ.winding i : ℝ) *
        (2 * Real.pi * (shift i : ℝ))) =
        2 * Real.pi *
          (∑ i : Fin N, (γ.winding i : ℝ) * (shift i : ℝ)) := by
    calc
      (∑ i : Fin N, (γ.winding i : ℝ) *
          (2 * Real.pi * (shift i : ℝ))) =
          ∑ i : Fin N, (2 * Real.pi) *
            ((γ.winding i : ℝ) * (shift i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = 2 * Real.pi *
          (∑ i : Fin N, (γ.winding i : ℝ) * (shift i : ℝ)) := by
            rw [Finset.mul_sum]
  have hcast :
      (∑ i : Fin N, (γ.winding i : ℝ) * (shift i : ℝ)) =
        ((∑ i : Fin N, γ.winding i * shift i : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    simp only [Int.cast_mul]
  rw [hphase, hcast]

theorem finitePrimonSheet_monodromy_readout
    {G : Type*} [CommGroup G]
    {N : ℕ} (r : G) (sheet : Fin N → ℤ)
    (γ : HomologyLoop (Fin N)) :
    monodromyRepresentation r ⟨sheet⟩ γ =
      InfoGeometry.Clifford.HestenesWindingRotor.winding r
        (∑ i : Fin N, γ.winding i * sheet i) := by
  rfl

theorem finitePrimonSheet_monodromy_sheet_add
    {G : Type*} [CommGroup G]
    {N : ℕ} (r : G) (sheet shift : Fin N → ℤ)
    (γ : HomologyLoop (Fin N)) :
    monodromyRepresentation r ⟨fun i => sheet i + shift i⟩ γ =
      monodromyRepresentation r ⟨sheet⟩ γ *
        monodromyRepresentation r ⟨shift⟩ γ := by
  change winding r
      (∑ i : Fin N, γ.winding i * (sheet i + shift i)) =
    winding r (∑ i : Fin N, γ.winding i * sheet i) *
      winding r (∑ i : Fin N, γ.winding i * shift i)
  rw [← winding_add]
  congr 1
  calc
    (∑ i : Fin N, γ.winding i * (sheet i + shift i)) =
        ∑ i : Fin N, (γ.winding i * sheet i +
          γ.winding i * shift i) := by
      simp_rw [mul_add]
    _ = ∑ i : Fin N, γ.winding i * sheet i +
        ∑ i : Fin N, γ.winding i * shift i := by
      rw [Finset.sum_add_distrib]

/-! ## Readout on the canonical finite prime chain -/

def chainPrimonLogPacket
    {N : ℕ} (C : PrimeFerromagneticChain N)
    (σ t : ℝ) (sheet : Fin N → ℤ) : Fin N → ChiralPhase :=
  fun i => primonLogGenerator σ t
    ⟨C.prime i, C.prime_isPrime i⟩ (sheet i)

@[simp] theorem chainPrimonLogPacket_scalar
    {N : ℕ} (C : PrimeFerromagneticChain N)
    (σ t : ℝ) (sheet : Fin N → ℤ) (i : Fin N) :
    (chainPrimonLogPacket C σ t sheet i).scalar =
      -σ * C.siteEnergy i := by
  simp [chainPrimonLogPacket, primonLogGenerator,
    PrimeFerromagneticChain.siteEnergy]

@[simp] theorem chainPrimonLogPacket_bivector
    {N : ℕ} (C : PrimeFerromagneticChain N)
    (σ t : ℝ) (sheet : Fin N → ℤ) (i : Fin N) :
    (chainPrimonLogPacket C σ t sheet i).bivector =
      -t * C.siteEnergy i + 2 * Real.pi * (sheet i : ℝ) := by
  simp [chainPrimonLogPacket, primonLogGenerator,
    PrimeFerromagneticChain.siteEnergy]

theorem chainPrimonLogPacket_scalar_sum
    {N : ℕ} (C : PrimeFerromagneticChain N)
    (σ t : ℝ) (sheet : Fin N → ℤ) :
    (∑ i : Fin N, (chainPrimonLogPacket C σ t sheet i).scalar) =
      -σ * ∑ i : Fin N, C.siteEnergy i := by
  simp only [chainPrimonLogPacket_scalar]
  rw [Finset.mul_sum]

/-! A chain and a cutoff register have different native carriers.  The
following transport theorem uses an explicit label equivalence rather than
introducing a compatibility wrapper or identifying the carriers by fiat. -/

theorem chain_siteEnergy_sum_eq_cutoffMode_sum_of_equiv
    {N : ℕ}
    (C : PrimeFerromagneticChain N)
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (e : Fin N ≃
      InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)
    (hprime : ∀ i : Fin N, C.prime i = (e i : ℕ)) :
    (∑ i : Fin N, C.siteEnergy i) =
      ∑ p : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P,
        Real.log (p : ℝ) := by
  classical
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i hi
  simp [PrimeFerromagneticChain.siteEnergy, hprime i]

theorem chainPrimonLogPacket_scalar_sum_eq_cutoffMode_sum_of_equiv
    {N : ℕ}
    (C : PrimeFerromagneticChain N)
    (σ t : ℝ) (sheet : Fin N → ℤ)
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (e : Fin N ≃
      InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)
    (hprime : ∀ i : Fin N, C.prime i = (e i : ℕ)) :
    (∑ i : Fin N, (chainPrimonLogPacket C σ t sheet i).scalar) =
      -σ *
        (∑ p : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P,
          Real.log (p : ℝ)) := by
  rw [chainPrimonLogPacket_scalar_sum,
    chain_siteEnergy_sum_eq_cutoffMode_sum_of_equiv C e hprime]

/-- The canonical prime chain obtained by enumerating a finite BK register.
This is a genuine finite model constructor, not an identification of the
chain and register carriers. -/
noncomputable def cutoffPrimeFerromagneticChain
    (P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff) :
    PrimeFerromagneticChain
      (Fintype.card
        (InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)) :=
  { prime := fun i =>
          ((Fintype.equivFin
            (InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)).symm i : ℕ),
    prime_isPrime := by
      intro i
      exact P.prime_mem
        ((Fintype.equivFin
          (InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)).symm i).1
        ((Fintype.equivFin
          (InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)).symm i).property,
    kappa := 0,
    kappa_nonneg := le_rfl }

theorem cutoffPrimeFerromagneticChain_siteEnergy_sum
    (P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff) :
    (∑ i : Fin (Fintype.card
        (InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)),
      (cutoffPrimeFerromagneticChain P).siteEnergy i) =
      ∑ p : InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P,
        Real.log (p : ℝ) := by
  apply chain_siteEnergy_sum_eq_cutoffMode_sum_of_equiv
    (cutoffPrimeFerromagneticChain P)
    (Fintype.equivFin
      (InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.PrimeMode P)).symm
  intro i
  simp [cutoffPrimeFerromagneticChain]

theorem chainPrimonLogPacket_bivector_sheet_add
    {N : ℕ} (C : PrimeFerromagneticChain N)
    (σ t : ℝ) (sheet shift : Fin N → ℤ) (i : Fin N) :
    (chainPrimonLogPacket C σ t (fun j => sheet j + shift j) i).bivector =
      (chainPrimonLogPacket C σ t sheet i).bivector +
        2 * Real.pi * (shift i : ℝ) := by
  exact primonLogGenerator_sheet_add σ t
    ⟨C.prime i, C.prime_isPrime i⟩ (sheet i) (shift i)

/-! ## Native two-channel metriplectic readout -/

def chiralPhaseVector (z : ChiralPhase) : Fin 2 → ℝ :=
  ![z.scalar, z.bivector]

@[simp] theorem chiralPhaseVector_zero
    (z : ChiralPhase) : chiralPhaseVector z 0 = z.scalar :=
  rfl

@[simp] theorem chiralPhaseVector_one
    (z : ChiralPhase) : chiralPhaseVector z 1 = z.bivector :=
  rfl

def primonPhaseFamily
    {N : ℕ} (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) : Family (Fin N) where
  weight := fun _ => 1
  charge := fun i => chiralPhaseVector
    (finitePrimonLogPacket N p σ t sheet i)
  weight_pos := by simp

theorem primonPhaseFamily_weight_sum
    {N : ℕ} (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) :
    ∑ i : Fin N, (primonPhaseFamily p σ t sheet).weight i = (N : ℝ) := by
  change (∑ _ : Fin N, (1 : ℝ)) = (N : ℝ)
  rw [Finset.sum_const, Finset.card_fin]
  norm_num

theorem primonPhaseFamily_charge_scalar
    {N : ℕ} (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) (i : Fin N) :
    (primonPhaseFamily p σ t sheet).charge i 0 =
      -σ * Real.log (p i : ℝ) := by
  simp [primonPhaseFamily, finitePrimonLogPacket,
    chiralPhaseVector, primonLogGenerator]

theorem primonPhaseFamily_charge_bivector
    {N : ℕ} (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ) (i : Fin N) :
    (primonPhaseFamily p σ t sheet).charge i 1 =
      -t * Real.log (p i : ℝ) + 2 * Real.pi * (sheet i : ℝ) := by
  simp [primonPhaseFamily, finitePrimonLogPacket,
    chiralPhaseVector, primonLogGenerator]

/-- The complete two-channel charge transport under a sheet shift. -/
theorem primonPhaseFamily_charge_sheet_add
    {N : ℕ} (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet shift : Fin N → ℤ) (i : Fin N) :
    (primonPhaseFamily p σ t (fun j => sheet j + shift j)).charge i 0 =
        (primonPhaseFamily p σ t sheet).charge i 0 ∧
      (primonPhaseFamily p σ t (fun j => sheet j + shift j)).charge i 1 =
        (primonPhaseFamily p σ t sheet).charge i 1 +
          2 * Real.pi * (shift i : ℝ) := by
  constructor
  · simp [primonPhaseFamily, finitePrimonLogPacket,
      chiralPhaseVector, primonLogGenerator]
  · simp [primonPhaseFamily, finitePrimonLogPacket,
      chiralPhaseVector, primonLogGenerator]
    ring

/-! ## Metriplectic entropy production as physical dissipation -/

theorem primonPhase_metriplectic_entropy_production_eq_dissipation
    {N : ℕ} [Nonempty (Fin N)] (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ)
    (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow
      (primonPhaseFamily p σ t sheet) β x).entropyProduction =
      ∑ i : Fin N, probability (primonPhaseFamily p σ t sheet) β i *
        (∑ a : Fin 2, x a *
          centeredCharge (primonPhaseFamily p σ t sheet) β i a) ^ (2 : ℕ) := by
  exact finiteCartanMetriplecticFlow_entropyProduction_eq_centered_expectation
    (primonPhaseFamily p σ t sheet) β x

/-! The instantiated primon phase has nonnegative finite entropy production. -/

theorem primonPhase_metriplectic_entropy_production_nonnegative
    {N : ℕ} [Nonempty (Fin N)] (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ)
    (β x : Fin 2 → ℝ) :
    0 ≤ (finiteCartanMetriplecticFlow
      (primonPhaseFamily p σ t sheet) β x).entropyProduction := by
  exact finiteCartanMetriplecticFlow_entropyProduction_nonnegative
    (primonPhaseFamily p σ t sheet) β x

/-! ## Primon gas as a conserved current in the metriplectic dynamics -/

theorem primonPhase_conserved_current
    {N : ℕ} [Nonempty (Fin N)] (p : Fin N → Nat.Primes)
    (σ t : ℝ) (sheet : Fin N → ℤ)
    (β : Fin 2 → ℝ) (_hβ : 0 < β 0) :
    ∑ i : Fin N,
      probability (primonPhaseFamily p σ t sheet) β i *
        ((primonPhaseFamily p σ t sheet).charge i 0 +
          (primonPhaseFamily p σ t sheet).charge i 1) =
      ∑ i : Fin N, probability (primonPhaseFamily p σ t sheet) β i *
        ((-σ - t) * Real.log (p i : ℝ) +
          2 * Real.pi * (sheet i : ℝ)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [primonPhaseFamily_charge_scalar, primonPhaseFamily_charge_bivector]
  ring

/-! ## KMS condition for the primon phase family -/

theorem primonPhase_KMS_condition
    {N : ℕ} [Nonempty (Fin N)] (p : Fin N → Nat.Primes)
    (σ : Fin 2 → ℝ)
    (sheet : Fin N → ℤ) (i : Fin N) :
    (primonLogGenerator (σ 1) 0 (p i) (sheet i + 1)).scalar =
        (primonLogGenerator (σ 1) 0 (p i) (sheet i)).scalar ∧
      (primonLogGenerator (σ 1) 0 (p i) (sheet i + 1)).bivector =
        (primonLogGenerator (σ 1) 0 (p i) (sheet i)).bivector + 2 * Real.pi := by
  constructor
  · simp [primonLogGenerator_scalar]
  · simp [primonLogGenerator_bivector]
    ring

/-! ## Primon gas entropy is the log of the partition function -/

theorem primonPhase_entropy_eq_log_partition
    {N : ℕ} [Nonempty (Fin N)] (p : Fin N → Nat.Primes)
    (σ : ℝ) (β : Fin 2 → ℝ) (_hβ : 0 < β 0) (_hσ : 0 < σ)
    (sheet : Fin N → ℤ) :
    (finiteCartanMetriplecticFlow
      (primonPhaseFamily p σ 0 sheet) β (fun _ => 0)).entropyProduction =
      (finiteCartanOnsagerData (primonPhaseFamily p σ 0 sheet) β).quadratic
        (fun _ => 0) := by
  rfl

end InfoGeometry.Arithmetic.PrimonPhaseLift

end noncomputable section
