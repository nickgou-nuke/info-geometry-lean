import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

Source-side bridge from split-Clifford current data into the existing
`CurrentHeisenbergRep` interface.

This file does not prove a new Sugawara theorem.  It packages exactly the
data required by `CurrentHeisenbergRep`:

* current modes `J : Int → V →ₗ[𝕜] V`;
* local truncation;
* the Heisenberg commutator law.

Once that witness is supplied, the downstream Sugawara/Virasoro construction
is delegated to `CurrentSugawaraBridge`.

No new Virasoro construction.
No vague `IsHeisenbergPair`.
No theorem pretending that the split direct limit automatically supplies the
current algebra.

Repository policy boundary:
this file is conditional. The missing theorem remains source-side construction
of `J`, `trunc`, and `comm` from split-current data.
No theorem here claims that split completion automatically yields an affine
current algebra witness.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

open Filter
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

/--
Source-side split-Clifford current witness.

This is intentionally the same shape as `CurrentHeisenbergRep`, but it is
named from the source side.  It is the bridge target for split-Clifford
completion data, transported CAR currents, or any concrete split current
construction.
-/
structure SplitCliffordHeisenbergWitness
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- Current modes. -/
  J : Int → V →ₗ[𝕜] V

  /-- Local truncation of current modes. -/
  trunc : ∀ v, atTop.Eventually (fun l => J l v = 0)

  /-- Heisenberg current commutator. -/
  comm :
    ∀ m n,
      (J m).commutator (J n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

namespace SplitCliffordHeisenbergWitness

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/--
Convert the source-side split-Clifford current witness into the exact
current interface consumed by the Sugawara bridge.
-/
def toCurrentHeisenbergRep
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V where
  J := W.J
  trunc := W.trunc
  comm := W.comm

@[simp]
theorem toCurrentHeisenbergRep_J
    (W : SplitCliffordHeisenbergWitness 𝕜 V)
    (n : Int) :
    (W.toCurrentHeisenbergRep).J n = W.J n :=
  rfl

@[simp]
theorem toCurrentHeisenbergRep_trunc
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    (W.toCurrentHeisenbergRep).trunc = W.trunc :=
  rfl

/--
Existence form of the bridge into the existing current interface.
-/
theorem nonempty_currentHeisenbergRep
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentHeisenbergRep 𝕜 V) :=
  ⟨W.toCurrentHeisenbergRep⟩

/--
Pack the witness into the downstream Sugawara morphism interface.

This stays on the safe side of the bridge: it does not construct the source
Heisenberg witness, it only packages a witness that is already present.
-/
noncomputable def toCurrentSugawaraMorphism
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V :=
  CurrentSugawaraMorphism.ofHeisenberg W.toCurrentHeisenbergRep

@[simp]
theorem toCurrentSugawaraMorphism_heisenberg
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.toCurrentSugawaraMorphism.heisenberg = W.toCurrentHeisenbergRep :=
  rfl

@[simp]
theorem toCurrentSugawaraMorphism_virasoro
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.toCurrentSugawaraMorphism.virasoro =
      (W.toCurrentHeisenbergRep).currentSugawaraRepresentation :=
  rfl

/-- Every split-Clifford current witness yields a Sugawara morphism package. -/
theorem nonempty_currentSugawaraMorphism
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentSugawaraMorphism 𝕜 V) :=
  ⟨W.toCurrentSugawaraMorphism⟩

/--
Sugawara representation obtained from the existing owner surface.

This is a definition, not a new theorem: the construction is delegated to
`CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation`.
-/
noncomputable def currentSugawaraRepresentation
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  (W.toCurrentHeisenbergRep).currentSugawaraRepresentation

/--
The central Virasoro generator acts as the identity in the representation
obtained from the split-Clifford current witness.
-/
theorem currentSugawaraRepresentation_central
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.currentSugawaraRepresentation (VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) :=
  CurrentHeisenbergRep.currentSugawaraRepresentation_central
    W.toCurrentHeisenbergRep

/--
The Virasoro `lgen` action is the Sugawara stress mode attached to the
underlying current witness.
-/
theorem currentSugawaraRepresentation_lgen_apply
    (W : SplitCliffordHeisenbergWitness 𝕜 V) (n : Int) :
    W.currentSugawaraRepresentation (VirasoroAlgebra.lgen 𝕜 n) =
      (W.toCurrentHeisenbergRep).sugawaraStressMode n :=
  CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply
    W.toCurrentHeisenbergRep n

/--
The Sugawara stress modes satisfy the Virasoro bracket with central charge one,
as inherited from the existing owner theorem.
-/
theorem sugawaraStressMode_virasoroBracket
    (W : SplitCliffordHeisenbergWitness 𝕜 V) (m n : Int) :
    ((W.toCurrentHeisenbergRep).sugawaraStressMode m).commutator
        ((W.toCurrentHeisenbergRep).sugawaraStressMode n) =
      (m - n) • (W.toCurrentHeisenbergRep).sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0 :=
  CurrentHeisenbergRep.sugawaraStressMode_virasoroBracket
    W.toCurrentHeisenbergRep m n

/--
Bundled source-side theorem surface: a split-Clifford current witness gives
both the exact Heisenberg current representation and the downstream Sugawara
representation.
-/
theorem current_and_sugawara_nonempty
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentHeisenbergRep 𝕜 V) ∧
      Nonempty (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) :=
  ⟨⟨W.toCurrentHeisenbergRep⟩,
    ⟨W.currentSugawaraRepresentation⟩⟩

/-- Bundled source-side theorem surface through the Sugawara morphism. -/
theorem currentSugawaraMorphism_and_current_nonempty
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentSugawaraMorphism 𝕜 V) ∧
      Nonempty (CurrentHeisenbergRep 𝕜 V) :=
  ⟨⟨W.toCurrentSugawaraMorphism⟩, ⟨W.toCurrentHeisenbergRep⟩⟩

end SplitCliffordHeisenbergWitness


/-! ## Top-level theorem names -/

/--
Source-side bridge into the existing `CurrentHeisenbergRep`.

This is the theorem requested by the implementation plan.
-/
theorem splitClifford_to_currentHeisenbergRep
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentHeisenbergRep 𝕜 V) :=
  W.nonempty_currentHeisenbergRep

/--
Source-side bridge into the existing Sugawara/Virasoro owner surface.

No new Sugawara theorem is proved here; the result is obtained by applying the
existing construction to the current witness.
-/
theorem splitClifford_to_sugawaraRepresentation
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) :=
  ⟨W.currentSugawaraRepresentation⟩

/-- Source-side bridge into the packaged Sugawara morphism surface. -/
theorem splitClifford_to_currentSugawaraMorphism
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentSugawaraMorphism 𝕜 V) :=
  W.nonempty_currentSugawaraMorphism

/--
The strongest theorem surface for this bridge: once a split-Clifford source
witness supplies the Heisenberg current laws, both the current representation
and Sugawara representation are available.
-/
theorem splitClifford_current_and_sugawara
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentHeisenbergRep 𝕜 V) ∧
      Nonempty (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) :=
  W.current_and_sugawara_nonempty

/-- The bridge also exposes the packaged Sugawara morphism and current datum. -/
theorem splitClifford_currentSugawara_and_current
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    Nonempty (CurrentSugawaraMorphism 𝕜 V) ∧
      Nonempty (CurrentHeisenbergRep 𝕜 V) :=
  W.currentSugawaraMorphism_and_current_nonempty

end InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
