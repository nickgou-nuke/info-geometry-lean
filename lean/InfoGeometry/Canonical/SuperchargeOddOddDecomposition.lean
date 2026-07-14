import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SuperchargeHoppingBridge
import Mathlib

/-!
# InfoGeometry.Canonical.SuperchargeOddOddDecomposition

Proof-carrying decomposition of odd-odd supercharge closure into transport,
central, and defect lanes.

This is the honest discrete/quasilattice shadow:

* odd-odd closure is primitive,
* translation/hopping is a distinguished component of that closure,
* central and defect lanes are separated explicitly,
* entropy-production vanishes on the central/BPS kernel lane.

No continuum super-Poincare theorem is claimed here.
-/

set_option linter.unusedSectionVars false

namespace SuperchargeOddOddDecomposition

open InfoGeometry.Canonical.SuperchargeHoppingBridge

section Core

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Norm-based entropy-production shadow of an operator on a state. -/
@[rep_depth operator]
def entropyProductionShadow (A : EndH) (ψ : E) : ℝ :=
  ‖A ψ‖

/--
Proof-carrying odd-odd decomposition data.

`translationCandidate` is the discrete hopping/transport lane,
`centralCandidate` is the protected topological lane,
`defectCandidate` collects the residual nontransport piece.
-/
@[rep_depth operator]
structure OddOddDecompositionData where
  Qi : EndH
  Qj : EndH
  translationCandidate : EndH
  centralCandidate : EndH
  defectCandidate : EndH
  oddOdd_decomposition :
    oddOddBracket Qi Qj =
      translationCandidate + centralCandidate + defectCandidate

namespace OddOddDecompositionData

variable (D : OddOddDecompositionData (E := E))

/-- The central/BPS lane is the kernel of the central candidate. -/
@[rep_depth operator]
noncomputable def centralBPSCore : Submodule ℝ E :=
  D.centralCandidate.ker

/-- The odd-odd bracket decomposes into translation, central, and defect lanes. -/
@[capstone, rep_depth operator]
theorem oddOddBracket_decomposes :
    oddOddBracket D.Qi D.Qj =
      D.translationCandidate + D.centralCandidate + D.defectCandidate :=
  D.oddOdd_decomposition

/--
Transport of the odd-odd decomposition through a ring homomorphism.

If

`{Qᵢ,Qⱼ} = T + Z + R`,

then after algebra transport `φ`,

`{φQᵢ,φQⱼ} = φT + φZ + φR`.
-/
@[rep_depth operator]
theorem oddOdd_decomposition_transport_ringHom
    (φ : EndH →+* EndH) :
    oddOddBracket (φ D.Qi) (φ D.Qj) =
      φ D.translationCandidate +
        φ D.centralCandidate +
          φ D.defectCandidate := by
  calc
    oddOddBracket (φ D.Qi) (φ D.Qj)
        = φ (oddOddBracket D.Qi D.Qj) := by
            exact (oddOddBracket_map (E := E) φ D.Qi D.Qj).symm
    _ = φ (D.translationCandidate + D.centralCandidate + D.defectCandidate) := by
            rw [D.oddOdd_decomposition]
    _ = φ D.translationCandidate +
          φ D.centralCandidate +
            φ D.defectCandidate := by
            simp

/--
Transport of the odd-odd decomposition through an invertible duality map.
-/
@[rep_depth operator]
theorem oddOdd_decomposition_transport_ringEquiv
    (Φ : EndH ≃+* EndH) :
    oddOddBracket (Φ D.Qi) (Φ D.Qj) =
      Φ D.translationCandidate +
        Φ D.centralCandidate +
          Φ D.defectCandidate := by
  calc
    oddOddBracket (Φ D.Qi) (Φ D.Qj)
        = Φ (oddOddBracket D.Qi D.Qj) := by
            exact (oddOddBracket_ringEquiv (E := E) Φ D.Qi D.Qj).symm
    _ = Φ (D.translationCandidate + D.centralCandidate + D.defectCandidate) := by
            rw [D.oddOdd_decomposition]
    _ = Φ D.translationCandidate +
          Φ D.centralCandidate +
            Φ D.defectCandidate := by
            simp

/-- Entropy production vanishes on the central/BPS kernel lane. -/
@[capstone, rep_depth operator]
theorem entropyProduction_vanishes_on_centralCore
    (ψ : E) (h_core : ψ ∈ D.centralBPSCore) :
    entropyProductionShadow D.centralCandidate ψ = 0 := by
  unfold entropyProductionShadow centralBPSCore at *
  rw [show D.centralCandidate ψ = 0 from h_core]
  simp

/-- Combined packet for the odd-odd decomposition lane. -/
@[rep_depth operator]
theorem oddOdd_decomposition_packet :
    (oddOddBracket D.Qi D.Qj =
      D.translationCandidate + D.centralCandidate + D.defectCandidate)
      ∧
    (∀ ψ : E, ψ ∈ D.centralBPSCore →
      entropyProductionShadow D.centralCandidate ψ = 0) := by
  refine ⟨D.oddOddBracket_decomposes, ?_⟩
  intro ψ hψ
  exact D.entropyProduction_vanishes_on_centralCore ψ hψ

end OddOddDecompositionData

/--
Finite N=2 central-charge transport.

If a supercharge closes as

`{Q,Q} = H + Z`,

then after a ring-hom transport `φ`,

`{φQ,φQ} = φH + φZ`.
-/
@[rep_depth operator]
theorem n2_centralCharge_transport_ringHom
    (φ : EndH →+* EndH)
    (Q H Z : EndH)
    (hclosure : oddOddBracket Q Q = H + Z) :
    oddOddBracket (φ Q) (φ Q) = φ H + φ Z := by
  calc
    oddOddBracket (φ Q) (φ Q)
        = φ (oddOddBracket Q Q) := by
            exact (oddOddBracket_map (E := E) φ Q Q).symm
    _ = φ (H + Z) := by
            rw [hclosure]
    _ = φ H + φ Z := by
            simp

/--
Finite N=2 central-charge transport with central term fixed.

If `φ Z = Z`, then

`{φQ,φQ} = φH + Z`.
-/
@[rep_depth operator]
theorem n2_centralCharge_transport_preserves_central_ringHom
    (φ : EndH →+* EndH)
    (Q H Z : EndH)
    (hclosure : oddOddBracket Q Q = H + Z)
    (hZ : φ Z = Z) :
    oddOddBracket (φ Q) (φ Q) = φ H + Z := by
  rw [n2_centralCharge_transport_ringHom (E := E) φ Q H Z hclosure, hZ]

/--
Finite N=2 central-charge roundtrip under an invertible duality.

If

`{Q,Q} = H + Z`,

then pulling back the transported closure by `Φ⁻¹` recovers the original
closure.
-/
@[rep_depth operator]
theorem n2_centralCharge_duality_roundtrip
    (Φ : EndH ≃+* EndH)
    (Q H Z : EndH)
    (hclosure : oddOddBracket Q Q = H + Z) :
    Φ.symm (oddOddBracket (Φ Q) (Φ Q)) = H + Z := by
  rw [← oddOddBracket_ringEquiv (E := E) Φ Q Q, hclosure]
  simp

/--
Finite inductive-chain central-charge invariance.

Suppose each bonding map transports

`Qₙ ↦ Qₙ₊₁`, `Hₙ ↦ Hₙ₊₁`

and fixes the central term `Z`.

If the N=2 closure holds at stage `0`, then it holds at every finite stage.
-/
@[rep_depth operator]
theorem n2_centralCharge_transport_chain
    (φ : ℕ → EndH →+* EndH)
    (Q H : ℕ → EndH)
    (Z : EndH)
    (hQ : ∀ n, Q (n + 1) = φ n (Q n))
    (hH : ∀ n, H (n + 1) = φ n (H n))
    (hZ : ∀ n, φ n Z = Z)
    (h0 : oddOddBracket (Q 0) (Q 0) = H 0 + Z) :
    ∀ n, oddOddBracket (Q n) (Q n) = H n + Z := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        oddOddBracket (Q (n + 1)) (Q (n + 1))
            = oddOddBracket (φ n (Q n)) (φ n (Q n)) := by
                rw [hQ n]
        _ = φ n (oddOddBracket (Q n) (Q n)) := by
                exact (oddOddBracket_map (E := E) (φ n) (Q n) (Q n)).symm
        _ = φ n (H n + Z) := by
                rw [ih]
        _ = φ n (H n) + φ n Z := by
                simp
        _ = H (n + 1) + Z := by
                rw [hH n, hZ n]

/--
Finite inductive-chain preservation of the full odd-odd decomposition.

If every bonding map transports all five lanes,

`Qᵢ, Qⱼ, T, Z, R`,

then the closure

`{Qᵢ,Qⱼ} = T + Z + R`

is stable at every finite stage.
-/
@[rep_depth operator]
theorem oddOdd_decomposition_transport_chain
    (φ : ℕ → EndH →+* EndH)
    (Qi Qj T Z R : ℕ → EndH)
    (hQi : ∀ n, Qi (n + 1) = φ n (Qi n))
    (hQj : ∀ n, Qj (n + 1) = φ n (Qj n))
    (hT : ∀ n, T (n + 1) = φ n (T n))
    (hZ : ∀ n, Z (n + 1) = φ n (Z n))
    (hR : ∀ n, R (n + 1) = φ n (R n))
    (h0 : oddOddBracket (Qi 0) (Qj 0) = T 0 + Z 0 + R 0) :
    ∀ n, oddOddBracket (Qi n) (Qj n) = T n + Z n + R n := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        oddOddBracket (Qi (n + 1)) (Qj (n + 1))
            = oddOddBracket (φ n (Qi n)) (φ n (Qj n)) := by
                rw [hQi n, hQj n]
        _ = φ n (oddOddBracket (Qi n) (Qj n)) := by
                exact (oddOddBracket_map (E := E) (φ n) (Qi n) (Qj n)).symm
        _ = φ n (T n + Z n + R n) := by
                rw [ih]
        _ = φ n (T n) + φ n (Z n) + φ n (R n) := by
                simp
        _ = T (n + 1) + Z (n + 1) + R (n + 1) := by
                rw [hT n, hZ n, hR n]

end Core

end SuperchargeOddOddDecomposition
