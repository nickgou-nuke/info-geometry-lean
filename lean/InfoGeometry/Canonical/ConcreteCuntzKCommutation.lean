import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Krein.DoubledSpace

open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Topology

/-!
# Concrete Cuntz/K-linear commutation

The Cuntz left shift S_left and the phase axis K = J·ε commute on the
concrete product carrier H = (BinaryCantorBoundary → ℝ) × DoubledSpace E,
because S_left acts on the base (Cantor boundary) and K acts on the fiber
(DoubledSpace).

The operator-level theorem below isolates the remaining concrete construction:
once the actual Cuntz left branch is supplied as a continuous doubled operator
with identical action on both real sheets, `concrete_S_left_KLinear` proves the
`KLinear` hypothesis needed by `e2_isSelfAdjoint_of_left_KLinear`.
-/

section ConcreteCuntzKCommutation

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Real-valued functions on the binary Cuntz/Cantor boundary. -/
abbrev BinaryCantorBoundaryFunctionSpace :=
  BinaryCantorBoundary → ℝ

/--
The concrete product carrier: product of the Cantor boundary function space
with the doubled fiber.

This replaces the abstract ℓ²(CantorBoundary) ⊗ ℂ² tensor product by the
simpler product representation for the commutation readback.
-/
structure ConcreteHilbert where
  base : BinaryCantorBoundaryFunctionSpace
  fiber : H₂

/--
The concrete Cuntz left shift S_left on the product carrier.

S_left acts on the base by shifting the Cantor boundary word (prefix 0),
and leaves the fiber unchanged.
-/
noncomputable def concrete_S_left
    (ψ : ConcreteHilbert (E := E)) : ConcreteHilbert (E := E) :=
  { base := ψ.base ∘ prefixBoundary BinarySector.plus,
    fiber := ψ.fiber
  }

/--
The concrete phase axis K = J·ε on the product carrier.

K acts on the fiber as phaseAxisK, and leaves the base unchanged.
-/
noncomputable def concrete_K
    (ψ : ConcreteHilbert (E := E)) : ConcreteHilbert (E := E) :=
  { base := ψ.base,
    fiber := phaseAxisK (E := E) ψ.fiber
  }

/--
**THEOREM**: S_left and K commute on the concrete product carrier.

  S_left ∘ K = K ∘ S_left

Proof: For any state ψ = (base, fiber),

  (S_left ∘ K)(ψ) = S_left(K(ψ))
                   = S_left(base, K(fiber))
                   = (base ∘ prefixBoundary 0, K(fiber))

  (K ∘ S_left)(ψ) = K(S_left(ψ))
                   = K(base ∘ prefixBoundary 0, fiber)
                   = (base ∘ prefixBoundary 0, K(fiber))

Both give the same result because K acts only on the fiber component and
S_left acts only on the base component.
-/
theorem concrete_S_left_K_commute (ψ : ConcreteHilbert (E := E)) :
    concrete_S_left (E := E) (concrete_K (E := E) ψ) =
      concrete_K (E := E) (concrete_S_left (E := E) ψ) :=
  rfl

/--
Any doubled operator that applies the same real operator to both doubled
coordinates commutes with the phase axis `K = Jε`.

This is the tensor-factor separation core: a base/fiber-separated Cuntz shift
has no access to the internal phase coordinate, so it is `KLinear`.
-/
theorem KLinear_of_same_doubled_action
    (A : EndH) (T : E →L[ℝ] E)
    (hA : ∀ x ξ : E, A (to_doubled x ξ : H₂) = to_doubled (T x) (T ξ)) :
    KLinear (E := E) A := by
  unfold KLinear InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  have hKu :
      (InfoGeometry.Krein.clockAxis (E := E)) u =
        (to_doubled (-(WithLp.snd u)) (WithLp.fst u) : H₂) := by
    rw [← hu]
    simp
  calc
    (A.comp (InfoGeometry.Krein.clockAxis (E := E))) u
        = A ((InfoGeometry.Krein.clockAxis (E := E)) u) := rfl
    _ = A (to_doubled (-(WithLp.snd u)) (WithLp.fst u) : H₂) := by
          rw [hKu]
    _ = to_doubled (T (-(WithLp.snd u))) (T (WithLp.fst u)) := by
          rw [hA]
    _ = to_doubled (-(T (WithLp.snd u))) (T (WithLp.fst u)) := by
          simp
    _ =
        (InfoGeometry.Krein.clockAxis (E := E))
          (to_doubled (T (WithLp.fst u)) (T (WithLp.snd u)) : H₂) := by
          rw [InfoGeometry.Krein.clockAxis_to_doubled]
    _ =
        (InfoGeometry.Krein.clockAxis (E := E))
          (A (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂)) := by
          rw [hA]
    _ = (InfoGeometry.Krein.clockAxis (E := E)) (A u) := by
          rw [hu]
    _ = ((InfoGeometry.Krein.clockAxis (E := E)).comp A) u := rfl

/--
Concrete left-branch K-linearity reduced to the only remaining construction:
prove that the concrete left Cuntz operator acts diagonally with the same base
operator on both doubled real sheets.
-/
theorem concrete_S_left_KLinear
    (S_left : EndH) (baseShift : E →L[ℝ] E)
    (hS_left :
      ∀ x ξ : E,
        S_left (to_doubled x ξ : H₂) = to_doubled (baseShift x) (baseShift ξ)) :
    KLinear (E := E) S_left :=
  KLinear_of_same_doubled_action (E := E) S_left baseShift hS_left

end ConcreteCuntzKCommutation
