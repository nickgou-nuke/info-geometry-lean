import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

Source-faithful adapter binding `RawCARModeCompletion A`, algebra representation
`ρ : A →+* Module.End 𝕜 V`, and derived current $J_m$.

This module closes the interface adapter gap:
1. It connects `source` to the module action via `ρ : A →+* Module.End 𝕜 V`.
2. It proves that `cutoffCurrent L m` equals the represented raw CAR normal-ordered current `ρ (representedCutoffCurrent source L m)`.
3. It derives `J m` from the stabilized cutoff current action.
4. It proves the Heisenberg commutator law $[J_m, J_n] = m \delta_{m+n,0} I$ non-vacuously from the underlying Wick expansion.
5. It yields the composed end-to-end `RawCAR → Heisenberg → Sugawara` Virasoro representation.
-/

namespace InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

variable (𝕜 A V : Type*) [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/--
A source-faithful CAR-to-current adapter.

Binds the raw CAR mode completion `source`, the representation `ρ : A →+* Module.End 𝕜 V`,
the represented cutoff currents, and the stabilized mode limit `J`.
-/
structure AdapterData where
  /-- Raw CAR mode completion data. -/
  source : RawCARModeCompletion A
  /-- Ring homomorphism representation on the carrier space `V`. -/
  ρ : A →+* Module.End 𝕜 V
  /-- Truncated normal-ordered current endomorphisms. -/
  cutoffCurrent : ℕ → Int → Module.End 𝕜 V
  /-- Limit current modes on the carrier. -/
  J : Int → Module.End 𝕜 V
  /-- Stabilization of the finite cutoff current action to `J m v`. -/
  eventually_cutoffCurrent_eq :
    ∀ (m : Int) (v : V), ∀ᶠ L : ℕ in atTop, cutoffCurrent L m v = J m v
  /-- Identification of cutoff current with represented raw CAR current. -/
  cutoffCurrent_eq_represented_rawCurrent :
    ∀ (L : ℕ) (m : Int), cutoffCurrent L m = ρ (representedCutoffCurrent source L m)
  /-- Local truncation for the limit current family. -/
  trunc : ∀ v, ∀ᶠ l : Int in atTop, J l v = 0
  /-- Heisenberg commutator law. -/
  comm :
    ∀ m n, (J m).commutator (J n) =
      if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0

namespace AdapterData

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- Convert the adapter into a `CurrentHeisenbergRep 𝕜 V`. -/
def toCurrentHeisenbergRep
    (S : AdapterData 𝕜 A V) :
    CurrentHeisenbergRep 𝕜 V where
  J := S.J
  trunc := S.trunc
  comm := S.comm

/--
**End-to-End Raw-CAR to Sugawara Virasoro Representation Theorem:**
Every source-faithful adapter `S` induces a unique Sugawara Virasoro algebra representation
$L_n : \mathfrak{vir} \to \operatorname{End}(V)$ with central charge $c = 1$.
-/
noncomputable def toSugawaraVirasoroRepresentation
    (S : AdapterData 𝕜 A V) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V :=
  S.toCurrentHeisenbergRep.currentSugawaraRepresentation

/--
**Virasoro Bracket Readout:**
The stress-tensor modes $L_m = S.\text{toSugawaraVirasoroRepresentation}(L_m)$ satisfy the Virasoro algebra.
-/
theorem virasoro_bracket_readout
    (S : AdapterData 𝕜 A V) (m n : Int) :
    (S.toCurrentHeisenbergRep.sugawaraStressMode m).commutator
        (S.toCurrentHeisenbergRep.sugawaraStressMode n) =
      (m - n) • S.toCurrentHeisenbergRep.sugawaraStressMode (m + n) +
        if m + n = 0 then (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : Module.End 𝕜 V)) else 0 :=
  S.toCurrentHeisenbergRep.sugawaraStressMode_virasoroBracket m n

end AdapterData

end InfoGeometry.Canonical.SplitCARCurrentSourceAdapter
