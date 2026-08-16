import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator

/-!
# InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator

Finite Berry--Keating / `H = xp` surface attached to the prime Cantor--Dirac
operator.

This module does **not** construct the Hilbert--Polya operator and does **not**
claim RH.  It implements the finite algebraic layer suggested by the
Berry--Keating analogy:

* the continuous generator `H_BK = (XP + PX)/2` is represented on the finite
  square-free prime-Cantor carrier by the diagonal logarithmic dilation energy
  `E(S) = Σ_{p ∈ S} logPrime p`;
* critical-line Berry--Keating evolution has phase `exp(- i t E(S))`, and the
  single-prime holonomies are `exp(- i t logPrime p)`;
* the existing zeta-Cantor Dirac operator supplies `D_C^ζ(s) = Q(s) + Q♯(s)`.

The analytic specialization `holonomy s p = p^(1/2 - s)`, the passage to the
infinite prime set, analytic continuation, and spectral claims are intentionally
kept in socket records.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator

open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator

/-- A finite property prime cutoff. -/
abbrev PrimeCutoff := PrimeCantorZetaDiracOperator.PrimeCutoff

/-- Prime mode inside a finite cutoff. -/
abbrev PrimeMode (P : PrimeCutoff) := PrimeCantorZetaDiracOperator.PrimeMode P

/-- Vertex of the finite prime Cantor/Fock lattice. -/
abbrev Vertex (P : PrimeCutoff) := PrimeCantorZetaDiracOperator.Vertex P

/-- Complex-valued fields on the finite prime Cantor/Fock lattice. -/
abbrev CantorField (P : PrimeCutoff) := PrimeCantorZetaDiracOperator.CantorField P

/-! ## 1. Finite Berry--Keating logarithmic dilation energy -/

/--
Finite logarithmic dilation energy of a square-free occupation state.

If `S` corresponds to the square-free integer `n = ∏_{p ∈ S} p`, then this is
formally `log n`.
-/
def bkEnergy {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (S : Vertex P) : ℝ :=
  Finset.sum S (fun p => logPrime p)

@[simp]
theorem bkEnergy_empty {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) :
    bkEnergy logPrime (∅ : Vertex P) = 0 := by
  simp [bkEnergy]

@[simp]
theorem bkEnergy_insert_of_not_mem {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (p : PrimeMode P) (S : Vertex P)
    (hp : p ∉ S) :
    bkEnergy logPrime (insert p S) = logPrime p + bkEnergy logPrime S := by
  simp [bkEnergy, hp]

/--
Finite Berry--Keating Hamiltonian on the prime-Cantor carrier.

This is the diagonal logarithmic dilation generator.  It is the finite algebraic
shadow of `H_BK = (XP + PX)/2`; no continuous-domain self-adjoint extension is
asserted here.
-/
def bkHamiltonian {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) :
    CantorField P → CantorField P :=
  fun f S => (bkEnergy logPrime S : ℂ) * f S

@[simp]
theorem bkHamiltonian_apply {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (f : CantorField P) (S : Vertex P) :
    bkHamiltonian logPrime f S = (bkEnergy logPrime S : ℂ) * f S := rfl

/-! ## 2. Critical-line Berry--Keating phases -/

/-- Single-prime Berry--Keating critical-line phase `exp(- i t log p)`. -/
def bkPrimePhase {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (p : PrimeMode P) : ℂ :=
  Complex.exp (-(Complex.I * (t : ℂ) * (logPrime p : ℂ)))

/-- Square-free Berry--Keating critical-line phase `exp(- i t E(S))`. -/
def bkStatePhase {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) : ℂ :=
  Complex.exp (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ)))

/-- Diagonal critical-line Berry--Keating evolution on the finite carrier. -/
def bkEvolution {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) :
    CantorField P → CantorField P :=
  fun f S => bkStatePhase logPrime t S * f S

@[simp]
theorem bkEvolution_apply {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ)
    (f : CantorField P) (S : Vertex P) :
    bkEvolution logPrime t f S = bkStatePhase logPrime t S * f S := rfl

/-- The critical-line holonomy vector induced by the finite BK dilation phases. -/
def bkCriticalHolonomy {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) : PrimeMode P → ℂ :=
  fun p => bkPrimePhase logPrime t p

theorem bkPrimePhase_norm {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (p : PrimeMode P) :
    ‖bkPrimePhase logPrime t p‖ = 1 := by
  simp [bkPrimePhase, Complex.norm_exp]

theorem bkStatePhase_norm {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    ‖bkStatePhase logPrime t S‖ = 1 := by
  simp [bkStatePhase, Complex.norm_exp]

theorem bkStatePhase_add {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s t : ℝ) (S : Vertex P) :
    bkStatePhase logPrime (s + t) S =
      bkStatePhase logPrime s S * bkStatePhase logPrime t S := by
  unfold bkStatePhase
  rw [show -(Complex.I * ((s + t : ℝ) : ℂ) *
      (bkEnergy logPrime S : ℂ)) =
      (-(Complex.I * (s : ℂ) * (bkEnergy logPrime S : ℂ))) +
        (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ))) by
    push_cast
    ring]
  rw [Complex.exp_add]

/-! ## 3. Bundled finite Berry--Keating/Cantor--Dirac packet -/

/--
A finite Berry--Keating/Cantor--Dirac packet.

`amplitude` and `holonomy` are the data used by the existing Cantor--Dirac
operator.  `logPrime` records the finite logarithmic periods.  The field
`critical_holonomy` asserts that on the critical-line parameter supplied by the
owner, the holonomy restricts to the BK phase `exp(-i t log p)`.
-/
structure FiniteBerryKeatingCantorDirac (P : PrimeCutoff) where
  amplitude : PrimeMode P → ℂ
  holonomy : ℂ → PrimeMode P → ℂ
  logPrime : PrimeMode P → ℝ
  criticalParam : ℝ → ℂ
  critical_holonomy :
    ∀ t : ℝ, ∀ p : PrimeMode P,
      holonomy (criticalParam t) p = bkCriticalHolonomy logPrime t p

namespace FiniteBerryKeatingCantorDirac

variable {P : PrimeCutoff}
variable (B : FiniteBerryKeatingCantorDirac P)

/-- Forget the BK structure and keep only the finite Cantor--Dirac packet. -/
def toCantorZetaDirac : FiniteCantorZetaDirac P :=
  { amplitude := B.amplitude, holonomy := B.holonomy }

/-- Finite BK Hamiltonian associated to the packet. -/
def H : CantorField P → CantorField P :=
  bkHamiltonian B.logPrime

/-- Critical-line finite BK evolution associated to the packet. -/
def U (t : ℝ) : CantorField P → CantorField P :=
  bkEvolution B.logPrime t

theorem U_zero : B.U 0 = id := by
  funext f
  funext S
  simp [U, bkEvolution, bkStatePhase]

theorem U_apply_add (s t : ℝ) (f : CantorField P) (S : Vertex P) :
    B.U (s + t) f S =
      bkStatePhase B.logPrime s S *
        (bkStatePhase B.logPrime t S * f S) := by
  simp [U, bkEvolution, bkStatePhase_add, mul_assoc]

/-- The zeta-Cantor creation supercharge at parameter `s`. -/
def Q (s : ℂ) : CantorField P → CantorField P :=
  B.toCantorZetaDirac.Q s

/-- The zeta-Cantor dual annihilation supercharge at parameter `s`. -/
def Qsharp (s : ℂ) : CantorField P → CantorField P :=
  B.toCantorZetaDirac.Qsharp s

/-- The finite zeta-Cantor Dirac operator at parameter `s`. -/
def D (s : ℂ) : CantorField P → CantorField P :=
  B.toCantorZetaDirac.op s

theorem D_eq_Q_add_Qsharp
    (s : ℂ) (f : CantorField P) (S : Vertex P) :
    B.D s f S = B.Q s f S + B.Qsharp s f S := by
  rfl

/-- The holonomy along the supplied critical parameter is the BK critical phase. -/
theorem holonomy_on_critical
    (t : ℝ) (p : PrimeMode P) :
    B.holonomy (B.criticalParam t) p = bkCriticalHolonomy B.logPrime t p :=
  B.critical_holonomy t p

end FiniteBerryKeatingCantorDirac

/- Direct finite Berry--Keating boundary statements. -/

theorem period_eq_logPrime
    {P : PrimeCutoff}
    {B : FiniteBerryKeatingCantorDirac P}
    (period : PrimeMode P → ℝ)
    (hperiod : ∀ p : PrimeMode P, period p = B.logPrime p)
    (p : PrimeMode P) :
    period p = B.logPrime p :=
  hperiod p

/- Direct RH-safe spectral gate. -/

theorem zero_implies_critical
    (Xi : ℂ → ℂ)
    (CriticalLine SelfAdjointSector : ℂ → Prop)
    (zero_implies_selfAdjoint :
      ∀ s : ℂ, Xi s = 0 → SelfAdjointSector s)
    (selfAdjoint_iff_critical :
      ∀ s : ℂ, SelfAdjointSector s ↔ CriticalLine s)
    (s : ℂ)
    (hz : Xi s = 0) :
    CriticalLine s :=
  (selfAdjoint_iff_critical s).mp (zero_implies_selfAdjoint s hz)

end InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator
