import InfoGeometry.Canonical.CelikErlangenBraidBridge
import InfoGeometry.Canonical.CreationAnnihilationTomitaBridge
import InfoGeometry.Canonical.SouriauDiracHodgeCoupling
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Cantor Phenomenology Readout

This module records a conservative dictionary from phenomenological labels to
already-owned algebraic Lean readouts.

It does **not** prove experimental realization, cold-atom implementation,
hardware verification, a Josephson law, vortex dynamics, Kibble--Zurek scaling,
or any Riemann-zeta consequence.  The theorem payload is restricted to:

* the tripotent null projector is idempotent and annihilated by the tripotent;
* Tomita-swapped creation/annihilation pairs split into even and odd channels;
* the finite chiral anomaly pairing vanishes under the owner hypotheses;
* the finite Çelik/Fibonacci braid matrix corridor supplies a phase readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorPhenomenologyReadout

open Matrix
open InfoGeometry.Canonical.CelikErlangenBraidBridge
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Canonical.CreationAnnihilationTomitaBridge
open InfoGeometry.Canonical.TrifactorDecomposition

/-- Phenomenological labels used only as dictionary keys. -/
inductive PhysicalPhenomenon where
  | superlocalization
  | goldstinoMode
  | boseFermiPairing
  | vortexPinning
  | fractionalJosephson
deriving DecidableEq, Repr

/-- Algebraic owner surfaces that can be read back from the current repository. -/
inductive AlgebraicReadout where
  | nullProjector
  | tomitaOddDensity
  | tomitaEvenMajorana
  | twistedIndexCancellation
  | finiteBraidPhase
deriving DecidableEq, Repr

/-- Conservative dictionary from physical labels to theorem-owned algebraic readouts. -/
def readoutOf : PhysicalPhenomenon → AlgebraicReadout
  | .superlocalization => .nullProjector
  | .goldstinoMode => .tomitaOddDensity
  | .boseFermiPairing => .tomitaEvenMajorana
  | .vortexPinning => .twistedIndexCancellation
  | .fractionalJosephson => .finiteBraidPhase

@[simp] theorem readoutOf_superlocalization :
    readoutOf .superlocalization = .nullProjector := rfl

@[simp] theorem readoutOf_goldstinoMode :
    readoutOf .goldstinoMode = .tomitaOddDensity := rfl

@[simp] theorem readoutOf_boseFermiPairing :
    readoutOf .boseFermiPairing = .tomitaEvenMajorana := rfl

@[simp] theorem readoutOf_vortexPinning :
    readoutOf .vortexPinning = .twistedIndexCancellation := rfl

@[simp] theorem readoutOf_fractionalJosephson :
    readoutOf .fractionalJosephson = .finiteBraidPhase := rfl

/--
Experimental status of a phenomenological label.

`externalEvidenceRequired` is intentionally the value for every physical
phenomenon here: Lean proves only the algebraic readout, not a laboratory
implementation.
-/
inductive ExperimentalStatus where
  | kernelAlgebraicReadout
  | externalEvidenceRequired
deriving DecidableEq, Repr

/-- Physical realization is not claimed by this algebraic bridge. -/
def experimentalStatus : PhysicalPhenomenon → ExperimentalStatus
  | _ => .externalEvidenceRequired

/-- Every physical label in this file still requires external experimental evidence. -/
theorem experimentalStatus_external (p : PhysicalPhenomenon) :
    experimentalStatus p = .externalEvidenceRequired := by
  cases p <;> rfl

/-! ## Owner-backed theorem readouts -/

/--
Tripotent null-sector readout: `P₀` is idempotent and the tripotent annihilates
that sector.
-/
theorem nullProjector_owner_readout
    {R : Type*} [CommRing R] [Invertible (2 : R)]
    (T : R) (hT : T ^ 3 = T) :
    P_zero T * P_zero T = P_zero T ∧ T * P_zero T = 0 :=
  ⟨P_zero_idempotent T hT, T_on_P_zero T hT⟩

/-- The null projector is explicitly idempotent. -/
theorem nullProjector_idempotent_readout
    {R : Type*} [CommRing R] [Invertible (2 : R)]
    (T : R) (hT : T ^ 3 = T) :
    P_zero T * P_zero T = P_zero T :=
  (nullProjector_owner_readout T hT).1

/-- The tripotent annihilates the null projector explicitly. -/
theorem tripotent_null_readout
    {R : Type*} [CommRing R] [Invertible (2 : R)]
    (T : R) (hT : T ^ 3 = T) :
    T * P_zero T = 0 :=
  (nullProjector_owner_readout T hT).2

/--
Tomita ladder readout: the `c+a` channel is even and the `c-a` channel is odd
whenever the supplied Tomita mirror swaps creation and annihilation.
-/
theorem tomita_even_odd_owner_readout
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : TomitaLadderPair V) :
    P.IsEvenSector P.evenMajorana ∧ P.IsOddSector P.oddDensity :=
  ⟨P.evenMajorana_mem_evenSector, P.oddDensity_mem_oddSector⟩

/-- The Tomita-even sector readout is explicit. -/
theorem tomita_even_owner_readout
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : TomitaLadderPair V) :
    P.IsEvenSector P.evenMajorana :=
  (tomita_even_odd_owner_readout P).1

/-- The Tomita-odd sector readout is explicit. -/
theorem tomita_odd_owner_readout
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : TomitaLadderPair V) :
    P.IsOddSector P.oddDensity :=
  (tomita_even_odd_owner_readout P).2

/--
Finite anomaly-cancellation readout from the Souriau/Dirac/Hodge owner.

The statement keeps every nontrivial geometric assumption explicit.
-/
theorem finite_anomaly_cancellation_owner_readout
    (tilt D proj : Matrix (Fin 2) (Fin 2) ℂ)
    (h_proj_idem : proj * proj = proj)
    (h_anticomm : D * tilt + tilt * D = 0)
    (h_comm : D * proj = proj * D)
    (h_Dinv : ∃ D_inv, D * D_inv = 1 ∧ D_inv * D = 1) :
    index_pairing tilt (⟨proj, h_proj_idem⟩ : KTheoryProjection 2) = 0 :=
  InfoGeometry.Canonical.SouriauDiracHodgeCoupling.anomaly_vanishes
    tilt D proj h_proj_idem h_anticomm h_comm h_Dinv

/-- The finite anomaly cancellation readout is explicit. -/
theorem finite_anomaly_cancellation_readout
    (tilt D proj : Matrix (Fin 2) (Fin 2) ℂ)
    (h_proj_idem : proj * proj = proj)
    (h_anticomm : D * tilt + tilt * D = 0)
    (h_comm : D * proj = proj * D)
    (h_Dinv : ∃ D_inv, D * D_inv = 1 ∧ D_inv * D = 1) :
    index_pairing tilt (⟨proj, h_proj_idem⟩ : KTheoryProjection 2) = 0 :=
  finite_anomaly_cancellation_owner_readout tilt D proj h_proj_idem h_anticomm h_comm h_Dinv

/-- Finite Çelik/Fibonacci phase readout: conjugating `V` by `R` gives a scalar phase. -/
theorem finite_braid_phase_owner_readout (q : Units ℂ) :
    fibonacciRMatrix q * InfoGeometry.Canonical.CelikCantorClifford.V * fibonacciRMatrix q =
      (((q ^ (-4 : ℤ) : Units ℂ) : ℂ) * ((q ^ (3 : ℤ) : Units ℂ) : ℂ)) •
        InfoGeometry.Canonical.CelikCantorClifford.V :=
  fibonacci_R_anticomm_with_V q

/-- The finite braid phase readout is explicit. -/
theorem finite_braid_phase_readout (q : Units ℂ) :
    fibonacciRMatrix q * InfoGeometry.Canonical.CelikCantorClifford.V * fibonacciRMatrix q =
      (((q ^ (-4 : ℤ) : Units ℂ) : ℂ) * ((q ^ (3 : ℤ) : Units ℂ) : ℂ)) •
        InfoGeometry.Canonical.CelikCantorClifford.V :=
  finite_braid_phase_owner_readout q

/-- Closed finite `Z₃` braid-owner readout from the Çelik--Erlangen bridge. -/
theorem finite_z3_braid_owner_readout :
    ((InfoGeometry.Canonical.CelikCantorClifford.U = fibonacciFusionMatrix (1 : ℂ) (0 : ℂ) ∧
      InfoGeometry.Canonical.CelikCantorClifford.V = fibonacciFusionMatrix (0 : ℂ) (1 : ℂ)) ∧
     (∀ τ s : ℂ, fibonacciFusionMatrix τ s =
        τ • InfoGeometry.Canonical.CelikCantorClifford.U +
          s • InfoGeometry.Canonical.CelikCantorClifford.V) ∧
     (∀ q : Units ℂ, fibonacciRMatrix q * InfoGeometry.Canonical.CelikCantorClifford.U =
        InfoGeometry.Canonical.CelikCantorClifford.U * fibonacciRMatrix q)) ∧
    ((InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix :
        Matrix (Fin 2) (Fin 2) ℝ) *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix *
          InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix) :=
  celik_erlangen_z3_concrete_braid_bridge

/-- The `U`-channel of the finite `Z₃` braid owner readout is explicit. -/
theorem finite_z3_braid_U_readout :
    InfoGeometry.Canonical.CelikCantorClifford.U = fibonacciFusionMatrix (1 : ℂ) (0 : ℂ) :=
  (finite_z3_braid_owner_readout).1.1.1

/-- The `V`-channel of the finite `Z₃` braid owner readout is explicit. -/
theorem finite_z3_braid_V_readout :
    InfoGeometry.Canonical.CelikCantorClifford.V = fibonacciFusionMatrix (0 : ℂ) (1 : ℂ) :=
  (finite_z3_braid_owner_readout).1.1.2

/-- The spanning-law channel of the finite `Z₃` braid owner readout is explicit. -/
theorem finite_z3_braid_span_readout :
    ∀ τ s : ℂ, fibonacciFusionMatrix τ s =
      τ • InfoGeometry.Canonical.CelikCantorClifford.U +
        s • InfoGeometry.Canonical.CelikCantorClifford.V :=
  (finite_z3_braid_owner_readout).1.2.1

/-- The braid-compatibility channel of the finite `Z₃` braid owner readout is explicit. -/
theorem finite_z3_braid_commute_readout :
    ∀ q : Units ℂ, fibonacciRMatrix q * InfoGeometry.Canonical.CelikCantorClifford.U =
      InfoGeometry.Canonical.CelikCantorClifford.U * fibonacciRMatrix q :=
  (finite_z3_braid_owner_readout).1.2.2

/-- The finite `Z₃` braid relation itself is explicit. -/
theorem finite_z3_braid_relation_readout :
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix :
        Matrix (Fin 2) (Fin 2) ℝ) *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix *
          InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix :=
  (finite_z3_braid_owner_readout).2

/-- The finite `Z₃` braid-owner readout is explicit. -/
theorem finite_z3_braid_readout :
    ((InfoGeometry.Canonical.CelikCantorClifford.U = fibonacciFusionMatrix (1 : ℂ) (0 : ℂ) ∧
      InfoGeometry.Canonical.CelikCantorClifford.V = fibonacciFusionMatrix (0 : ℂ) (1 : ℂ)) ∧
     (∀ τ s : ℂ, fibonacciFusionMatrix τ s =
        τ • InfoGeometry.Canonical.CelikCantorClifford.U +
          s • InfoGeometry.Canonical.CelikCantorClifford.V) ∧
     (∀ q : Units ℂ, fibonacciRMatrix q * InfoGeometry.Canonical.CelikCantorClifford.U =
        InfoGeometry.Canonical.CelikCantorClifford.U * fibonacciRMatrix q)) ∧
    ((InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix :
        Matrix (Fin 2) (Fin 2) ℝ) *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix *
          InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix) :=
  finite_z3_braid_owner_readout

end InfoGeometry.Canonical.CantorPhenomenologyReadout

end noncomputable section
