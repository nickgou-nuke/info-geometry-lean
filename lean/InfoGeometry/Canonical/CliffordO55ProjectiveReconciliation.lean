import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Algebraic.NarainOrthogonalCore
import InfoGeometry.Clifford.SpinorRep

/-!
# Clifford / `O(5,5)` / Projective Reconciliation

This file formalizes the layer separation:

* `Cl(1,1)` is the recursive split Clifford atom;
* `Cl(5,5)` is the stage-5 finite window in the split tower;
* the split direct limit absorbs finite tails after the stage-5 window;
* `O(5,5)` is the metric-preserving Narain/split-charge symmetry layer;
* the rational projective language is an ambient `PGL_10(Q)` shadow, not a
  replacement for `O(5,5)`.

The notation `PGL(5,5,Q)` is therefore deliberately not introduced.  The
formal projective object here is the scalar-line relation on `Fin 10 → ℚ`,
which is the coordinate carrier for an ambient `PGL_10(ℚ)` action.
-/

set_option autoImplicit false

noncomputable section

namespace CliffordO55ProjectiveReconciliation

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Algebraic.Split

/-! ## Clifford tower layers -/

/-- The split `Cl(1,1)` atom used by the recursive tower. -/
abbrev Cl11Atom :=
  SplitCl11Alg

/-- The split `Cl(4,4)` triality window. -/
abbrev Cl44TrialityWindow :=
  SplitCl44Alg

/-- The finite split `Cl(5,5)` window. -/
abbrev Cl55Window :=
  SplitCl55Alg

/-- The split Clifford direct limit `Cl(∞,∞)` in the current tower API. -/
abbrev ClInfinity :=
  SplitCliffordInfinity

/-- The stage-5 window is definitionally the recursive split `Cl(n,n)` stage at `n = 5`. -/
theorem cl55_window_is_stage_five :
    Cl55Window = SplitClNNAlg 5 :=
  rfl

/--
Owner-backed Bott step:
`Cl(5,5) ≃ Cl(1,1) ⊗ Cl(4,4)`.
-/
def cl55_as_cl11_tensor_cl44 :
    Cl55Window ≃ₐ[ℝ] SplitClNNTensorStep 4 :=
  splitCl55_headCl11TensorCl44Equiv

/--
Owner-backed user-order Bott step:
`Cl(4,4) ⊗ Cl(1,1) ≃ Cl(5,5)`.
-/
def cl44_tensor_cl11_as_cl55 :
    SplitCl55TailHeadTensorStep ≃ₐ[ℝ] Cl55Window :=
  splitCl55_cl44TensorCl11Equiv

/-- The named `Cl(5,5)` tensor step is exactly the recursive owner step at `n = 4`. -/
theorem cl55_tensor_step_eq_owner :
    cl55_as_cl11_tensor_cl44 = splitCliffordTensorStepEquiv 4 :=
  rfl

/--
Compatibility between the split `Cl(4,4)` stage and the recursive stage-4
spinor matrix basis.

This is the source-backed generator-level readout: the recursive spinor
representation is exactly the stage-4 carrier image of the split tower.
-/
theorem cl44_spinorMatrix4_basis_compatibility
    (x : InfoGeometry.Clifford.SpinorRep.SplitSpace 4) :
    InfoGeometry.Clifford.SpinorRep.spinorRepresentation 4
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.SpinorRep.SplitQuad 4) x) =
      InfoGeometry.Clifford.SpinorRep.recursiveGamma 4 x := by
  simpa using InfoGeometry.Clifford.SpinorRep.spinorRepresentation_ι 4 x

/--
Combined owner packet for the stage-4 recursive spinor basis and the stage-5
`Cl(1,1)` tensor polarization.

The first conjunct is the explicit spinor-basis compatibility theorem above;
the second conjunct is the repo-owned `Cl(5,5)` tensor-step equality.
-/
theorem cl44_spinorMatrix4_and_cl55_tensor_polarization :
    (∀ x : InfoGeometry.Clifford.SpinorRep.SplitSpace 4,
      InfoGeometry.Clifford.SpinorRep.spinorRepresentation 4
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.SpinorRep.SplitQuad 4) x) =
        InfoGeometry.Clifford.SpinorRep.recursiveGamma 4 x) ∧
    (splitCl55_headCl11TensorCl44Equiv = splitCliffordTensorStepEquiv 4) := by
  constructor
  · intro x
    simpa using InfoGeometry.Clifford.SpinorRep.spinorRepresentation_ι 4 x
  · exact splitCl55_headCl11TensorCl44Equiv_eq_owner

/--
Finite `Cl(5,5)` window absorption in the direct limit:
adding a finite split-Clifford tail to a stage-5 representative does not change
its direct-limit element.
-/
theorem cl55_window_absorbs_finite_tail
    (x : Cl55Window) (k : ℕ) :
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
      =
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 5 x :=
  splitCliffordInfinity_cl55_window_absorbs_finite_tail x k

/--
Every direct-limit element has a representative at or beyond the `Cl(5,5)`
window.
-/
theorem every_limit_element_has_representative_beyond_cl55
    (z : ClInfinity) :
    ∃ n ≥ 5, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z :=
  splitCliffordInfinity_has_representative_beyond_cl55_window z

/--
Predicate transport from the stage-5 window to any absorbed finite tail.
-/
theorem cl55_predicate_lifts_to_finite_tail
    {P : ClInfinity → Prop}
    (h5 : ∀ x : Cl55Window,
      P (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 5 x))
    (x : Cl55Window) (k : ℕ) :
    P (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)) :=
  splitCliffordInfinity_cl55_predicate_lifts_to_finite_tail h5 x k

/-! ## Narain / `O(5,5)` metric layer -/

/-- Rational/integral split-charge symmetry at the five-mode Narain window. -/
abbrev RationalO55Window :=
  NarainChargeSymmetry 5

/-- Momentum/winding swap as an `O(5,5)`-style split-charge symmetry. -/
def rationalO55Swap : RationalO55Window :=
  (canonicalNarainOrthogonalCore 5).swap

/-- Global parity twist as an `O(5,5)`-style split-charge symmetry. -/
def rationalO55ParityTwist : RationalO55Window :=
  (canonicalNarainOrthogonalCore 5).parityTwist

/-- The momentum/winding swap preserves the five-mode hyperbolic pairing. -/
theorem rationalO55Swap_preserves_pairing
    (q r : SplitCharge 5) :
    SplitCharge.hyperbolicPair (rationalO55Swap.apply q) (rationalO55Swap.apply r) =
      SplitCharge.hyperbolicPair q r :=
  rationalO55Swap.preserves_hyperbolicPair q r

/-- The global parity twist preserves the five-mode hyperbolic pairing. -/
theorem rationalO55ParityTwist_preserves_pairing
    (q r : SplitCharge 5) :
    SplitCharge.hyperbolicPair
        (rationalO55ParityTwist.apply q) (rationalO55ParityTwist.apply r) =
      SplitCharge.hyperbolicPair q r :=
  rationalO55ParityTwist.preserves_hyperbolicPair q r

/-! ## Ambient `PGL_10(ℚ)` projective shadow -/

/-- Ambient rational ten-vector carrier for projective chart shadows. -/
abbrev RationalTenCarrier :=
  Fin 10 → ℚ

/--
Scalar-line equivalence on the rational ten-vector carrier.

This is the concrete relation quotiented by the ambient projective group
`PGL_10(ℚ)`.
-/
def SameProjectiveLine (v w : RationalTenCarrier) : Prop :=
  ∃ a : ℚ, a ≠ 0 ∧ w = a • v

/-- Reflexivity of the projective-line relation. -/
theorem sameProjectiveLine_refl (v : RationalTenCarrier) :
    SameProjectiveLine v v := by
  exact ⟨1, by norm_num, by simp⟩

/-- Scalar sign is invisible in projective space. -/
theorem sameProjectiveLine_neg (v : RationalTenCarrier) :
    SameProjectiveLine v (-v) := by
  exact ⟨-1, by norm_num, by simp⟩

/-- Linear equivalences preserve projective-line equivalence. -/
theorem linearEquiv_preserves_sameProjectiveLine
    (L : RationalTenCarrier ≃ₗ[ℚ] RationalTenCarrier)
    {v w : RationalTenCarrier}
    (h : SameProjectiveLine v w) :
    SameProjectiveLine (L v) (L w) := by
  rcases h with ⟨a, ha, hw⟩
  refine ⟨a, ha, ?_⟩
  rw [hw]
  exact L.map_smul a v

/--
The projective shadow forgets the global sign of any rational linear
representative.
-/
theorem linearEquiv_projective_forgets_global_sign
    (L : RationalTenCarrier ≃ₗ[ℚ] RationalTenCarrier)
    (v : RationalTenCarrier) :
    SameProjectiveLine (L v) (-(L v)) :=
  sameProjectiveLine_neg (L v)

/--
Layer reconciliation capstone:
the finite `Cl(5,5)` window is a stage-5 Clifford carrier, it absorbs finite
tails in the direct limit, `O(5,5)` is represented by hyperbolic-pair-preserving
Narain symmetries, and the projective layer is the scalar-line quotient on the
ambient rational ten-carrier.
-/
theorem reconciliation_capstone :
    Cl55Window = SplitClNNAlg 5 ∧
    (∀ x : Cl55Window, ∀ k : ℕ,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) (5 + k)
          (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
        =
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 5 x) ∧
    (∀ q r : SplitCharge 5,
      SplitCharge.hyperbolicPair (rationalO55Swap.apply q) (rationalO55Swap.apply r) =
        SplitCharge.hyperbolicPair q r) ∧
    (∀ v : RationalTenCarrier, SameProjectiveLine v (-v)) := by
  exact ⟨cl55_window_is_stage_five, cl55_window_absorbs_finite_tail,
    rationalO55Swap_preserves_pairing, sameProjectiveLine_neg⟩

end CliffordO55ProjectiveReconciliation
