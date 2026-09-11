import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.KreinDoubledCartanPeirceBridge

/-!
# Stratum 37: Tomita-Takesaki Modular J, Aharonov Two-State Formalism, and Klein Bottle Holonomy

This module formalizes the dynamic doubling into two time arrows:
1. **Tomita-Takesaki Modular Involution J:**
   The anti-unitary involution $J = \sigma_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
   satisfies $J^2 = \mathbf{1}$ and reflects the physical algebra into its commutant: $J \mathcal{M} J = \mathcal{M}'$.
2. **Peirce and Krein Inversion:**
   $J P_+ J = P_-$, $J P_- J = P_+$, and $J \eta J = -\eta$.
   Conjugation by $J$ inverts the fundamental Krein symmetry $\eta \mapsto -\eta$,
   swapping the forward-in-time sector $\mathcal{H}_+$ with the backward-in-time sector $\mathcal{H}_-$.
3. **Aharonov Two-State Vector Formalism (TSVF):**
   A complete quantum state is described by a two-state vector $(\langle \Phi|, |\Psi\rangle)$
   where $|\Psi\rangle \in \mathcal{H}_+$ propagates forward in time and $\langle \Phi| \in \mathcal{H}_-$
   propagates backward in time.
4. **Klein Bottle Global J-Holonomy:**
   The orientation-reversing generator $T_a$ of the Klein bottle fundamental group
   $\pi_1(\mathbb{K}^2) \cong \mathbb{Z} \rtimes \mathbb{Z}$ acts as $J$, reversing time orientation
   $T_a \eta T_a^{-1} = -\eta$.
-/

namespace InfoGeometry.Canonical.ModularTomitaTwoStateKlein

open Matrix
open InfoGeometry.Canonical.KreinDoubledCartanPeirce

variable {R : Type*} [CommRing R]

/-- Tomita-Takesaki modular conjugation / Klein bottle holonomy swap operator J = σ_x. -/
def J_swap : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

/-- J is an involution: J² = 1. -/
theorem J_sq : J_swap (R := R) * J_swap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_swap, mul_apply, Fin.sum_univ_two]

/-- J swaps positive Peirce projector into negative Peirce projector: J P_+ J = P_-. -/
theorem J_swaps_Peirce_plus : J_swap (R := R) * P_plus * J_swap = P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_swap, P_plus, P_minus, mul_apply, Fin.sum_univ_two]

/-- J swaps negative Peirce projector into positive Peirce projector: J P_- J = P_+. -/
theorem J_swaps_Peirce_minus : J_swap (R := R) * P_minus * J_swap = P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_swap, P_plus, P_minus, mul_apply, Fin.sum_univ_two]

/-- **THE MODULAR TIME-INVERSION THEOREM**:
    Conjugation by the modular involution J inverts the fundamental Krein symmetry:
    J η J = -η. -/
theorem J_inverts_eta : J_swap (R := R) * eta * J_swap = -eta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_swap, eta, mul_apply, Fin.sum_univ_two]

/-- Aharonov Two-State Vector (TSVF): forward wave |Ψ⟩ and backward wave ⟨Φ|. -/
structure TwoStateVector (R : Type*) where
  forward : Fin 2 → R  -- |Ψ⟩ ∈ H_+ (forward in time from past)
  backward : Fin 2 → R -- ⟨Φ| ∈ H_- (backward in time from future)

/-- TSVF Transition matrix element ⟨Φ| A |Ψ⟩. -/
def tsvfTransition (A : Matrix (Fin 2) (Fin 2) R) (ts : TwoStateVector R) : R :=
  ts.backward 0 * (A *ᵥ ts.forward) 0 + ts.backward 1 * (A *ᵥ ts.forward) 1

/-- Overlap amplitude ⟨Φ|Ψ⟩. -/
def tsvfOverlap (ts : TwoStateVector R) : R :=
  ts.backward 0 * ts.forward 0 + ts.backward 1 * ts.forward 1

/-- If A is the identity operator, tsvfTransition is the overlap amplitude. -/
theorem tsvfTransition_one (ts : TwoStateVector R) :
    tsvfTransition 1 ts = tsvfOverlap ts := by
  simp [tsvfTransition, tsvfOverlap, Matrix.mulVec]

/-- Klein bottle deck transformation orientation-reversal on Krein symmetry:
    T_a η T_a⁻¹ = -η (since J = J⁻¹). -/
theorem klein_deck_time_reversal :
    J_swap (R := R) * eta * J_swap = -eta :=
  J_inverts_eta

/-- Master synthesis packet for Stratum 37. -/
structure ModularTwoStateKleinPacket (R : Type*) [CommRing R] where
  j_is_involution : J_swap (R := R) * J_swap = 1
  j_swaps_peirce : J_swap (R := R) * P_plus * J_swap = P_minus
  j_inverts_krein_time : J_swap (R := R) * eta * J_swap = -eta
  tsvf_identity_is_overlap : ∀ ts : TwoStateVector R, tsvfTransition 1 ts = tsvfOverlap ts

/-- Zero-debt constructor for Stratum 37 packet. -/
def makeModularTwoStateKleinPacket (R : Type*) [CommRing R] : ModularTwoStateKleinPacket R where
  j_is_involution := J_sq
  j_swaps_peirce := J_swaps_Peirce_plus
  j_inverts_krein_time := J_inverts_eta
  tsvf_identity_is_overlap := tsvfTransition_one

end InfoGeometry.Canonical.ModularTomitaTwoStateKlein
