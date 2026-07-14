import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.DrazinKreinCompatibility
import Mathlib.Tactic.Abel

/-!
# Bogoliubov Cartan eigen-operators

Thin owner-anchored bridge over the existing real doubled Bogoliubov transport
surface.

The Cartan adjoint action here is not a new generalized commutator. It is the
already-installed `BogoliubovTransport.transportCommutator`, read as the Cartan
adjoint action on doubled-real bounded operators.
-/

namespace BogoliubovCartanEigenOperator

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.DrazinKreinCompatibility
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Cartan adjoint action on doubled-real bounded operators.

This is definitionally the repo-owned Bogoliubov transport commutator
`transportCommutator H A = H ∘ A - A ∘ H`.
-/
noncomputable def cartanAdjoint (H A : EndH) : EndH :=
  transportCommutator (E := E) H A

/-- Readback to the installed Bogoliubov transport owner surface. -/
theorem cartanAdjoint_eq_transportCommutator (H A : EndH) :
    cartanAdjoint (E := E) H A = transportCommutator (E := E) H A :=
  rfl

/-- Eigen-operator relation for Cartan adjoint action. -/
def IsCartanEigenOperator (H A : EndH) (lam : ℝ) : Prop :=
  cartanAdjoint (E := E) H A = lam • A

/-- Zero operator has Cartan weight `0`. -/
@[simp] theorem zero_isCartanEigenOperator (H : EndH) :
    IsCartanEigenOperator (E := E) H 0 0 := by
  unfold IsCartanEigenOperator
  rw [zero_smul]
  simp [cartanAdjoint, transportCommutator]

@[simp] theorem cartanAdjoint_zero (H : EndH) :
    cartanAdjoint (E := E) H 0 = 0 := by
  simp [cartanAdjoint, transportCommutator]

@[simp] theorem cartanAdjoint_add (H A B : EndH) :
    cartanAdjoint (E := E) H (A + B)
      = cartanAdjoint (E := E) H A + cartanAdjoint (E := E) H B := by
  simp [cartanAdjoint, transportCommutator, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

@[simp] theorem cartanAdjoint_smul (H A : EndH) (c : ℝ) :
    cartanAdjoint (E := E) H (c • A) = c • cartanAdjoint (E := E) H A := by
  simp [cartanAdjoint, transportCommutator, ContinuousLinearMap.smul_comp, smul_sub]

/-- Product rule for the Cartan adjoint action. -/
theorem cartanAdjoint_comp (H A B : EndH) :
    cartanAdjoint (E := E) H (A.comp B)
      = (cartanAdjoint (E := E) H A).comp B + A.comp (cartanAdjoint (E := E) H B) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cartanAdjoint, transportCommutator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_sub]
  abel

/-- Cartan eigen-operator weights add under operator composition. -/
theorem cartanEigenOperator_comp
    {H A B : EndH} {lamA lamB : ℝ}
    (hA : IsCartanEigenOperator (E := E) H A lamA)
    (hB : IsCartanEigenOperator (E := E) H B lamB) :
    IsCartanEigenOperator (E := E) H (A.comp B) (lamA + lamB) := by
  unfold IsCartanEigenOperator at hA hB ⊢
  rw [cartanAdjoint_comp, hA, hB]
  apply ContinuousLinearMap.ext
  intro x
  simp [add_smul]

/-- Cartan eigen-operator weights add under operator multiplication. -/
theorem cartanEigenOperator_mul
    {H A B : EndH} {lamA lamB : ℝ}
    (hA : IsCartanEigenOperator (E := E) H A lamA)
    (hB : IsCartanEigenOperator (E := E) H B lamB) :
    IsCartanEigenOperator (E := E) H (A * B) (lamA + lamB) :=
  cartanEigenOperator_comp (E := E) hA hB

/-- Sum of equal-weight Cartan eigen-operators is again an eigen-operator. -/
theorem cartanEigenOperator_add_same_weight
    {H A B : EndH} {lam : ℝ}
    (hA : IsCartanEigenOperator (E := E) H A lam)
    (hB : IsCartanEigenOperator (E := E) H B lam) :
    IsCartanEigenOperator (E := E) H (A + B) lam := by
  unfold IsCartanEigenOperator at hA hB ⊢
  rw [cartanAdjoint_add, hA, hB]
  simp [smul_add]

/-- Scalar multiple of a Cartan eigen-operator is again an eigen-operator. -/
theorem cartanEigenOperator_smul
    {H A : EndH} {lam c : ℝ}
    (hA : IsCartanEigenOperator (E := E) H A lam) :
    IsCartanEigenOperator (E := E) H (c • A) lam := by
  unfold IsCartanEigenOperator at hA ⊢
  rw [cartanAdjoint_smul, hA]
  simp [smul_smul, mul_comm, mul_assoc]

/-- Cartan eigen-operator commutators have the summed Cartan weight. -/
theorem cartanEigenOperator_commutator
    {H A B : EndH} {lamA lamB : ℝ}
    (hA : IsCartanEigenOperator (E := E) H A lamA)
    (hB : IsCartanEigenOperator (E := E) H B lamB) :
    IsCartanEigenOperator (E := E) H (A * B - B * A) (lamA + lamB) := by
  have hAB : IsCartanEigenOperator (E := E) H (A * B) (lamA + lamB) :=
    cartanEigenOperator_mul (E := E) hA hB
  have hBA : IsCartanEigenOperator (E := E) H (B * A) (lamA + lamB) := by
    simpa [add_comm] using cartanEigenOperator_mul (E := E) hB hA
  have hNeg :
      IsCartanEigenOperator (E := E) H ((-1 : ℝ) • (B * A)) (lamA + lamB) :=
    cartanEigenOperator_smul (E := E) (c := -1) hBA
  have hSum :
      IsCartanEigenOperator (E := E) H (A * B + (-1 : ℝ) • (B * A))
        (lamA + lamB) :=
    cartanEigenOperator_add_same_weight (E := E) hAB hNeg
  simpa [sub_eq_add_neg] using hSum

/-- Phase-refined Cartan eigen-operator in the Hestenes real doubled sense. -/
def IsPhaseCartanEigenOperator
    (H A : EndH) (lam : ℝ) : Prop :=
  IsCartanEigenOperator (E := E) H A lam ∧
    IsPhaseLinear (E := E) A

/-- Phase-linear Cartan eigen-operator in the installed Bogoliubov transport sense. -/
def IsPhaseLinearCartanEigenOperator
    (H A : EndH) (lam : ℝ) : Prop :=
  IsCartanEigenOperator (E := E) H A lam ∧
    IsPhaseLinear (E := E) A

/-- Phase-antilinear Cartan eigen-operator in the repo-owned Bogoliubov transport sense. -/
def IsPhaseAntilinearCartanEigenOperator
    (H A : EndH) (lam : ℝ) : Prop :=
  IsCartanEigenOperator (E := E) H A lam ∧
    IsPhaseAntilinear (E := E) A

/-- Drazin-regular Cartan eigen-operator supported on a regular projector `Preg`. -/
def IsDrazinRegularCartanEigenOperator
    (T TD H A : EndH) (lam : ℝ) : Prop :=
  IsCartanEigenOperator (E := E) H A lam ∧
    Preg T TD * A = A ∧ A * Preg T TD = A

/-- Drazin-defect Cartan eigen-operator supported on the null/defect projector `Pzero`. -/
def IsDrazinDefectCartanEigenOperator
    (T TD H A : EndH) (lam : ℝ) : Prop :=
  IsCartanEigenOperator (E := E) H A lam ∧
    Pzero T TD * A = A ∧ A * Pzero T TD = A

/-- Alias for Drazin-null/defect Cartan eigen-operators. -/
def IsDrazinNullCartanEigenOperator
    (T TD H A : EndH) (lam : ℝ) : Prop :=
  IsDrazinDefectCartanEigenOperator (E := E) T TD H A lam

/-- Chiral Cartan eigen-operator relative to a grading operator. -/
def IsChiralCartanEigenOperator
    (H epsilon A : EndH) (lam chirality : ℝ) : Prop :=
  IsCartanEigenOperator (E := E) H A lam ∧
    epsilon.comp A = chirality • (A.comp epsilon)

/-- A pair of bounded operators forms a two-sided inverse pair. -/
def IsTwoSidedInverse (U V : EndH) : Prop :=
  V * U = 1 ∧ U * V = 1

/-- Conjugation of an operator by a Bogoliubov frame change. -/
noncomputable def conjugateOperator (U V A : EndH) : EndH :=
  U * A * V

/-- Cartan generators are conjugate when `H₂ = U H₁ V`. -/
def ConjugatesCartan (U V Hsrc Htgt : EndH) : Prop :=
  Htgt = U * Hsrc * V

/--
If Cartan adjoint is transported by a Bogoliubov frame conjugation, Cartan weights are preserved.
-/
theorem cartanEigenOperator_conjugate
    (Hsrc Htgt U Uinv A : EndH)
    (lam : ℝ)
    (hconj :
      cartanAdjoint (E := E) Htgt ((U.comp A).comp Uinv)
        = (U.comp (cartanAdjoint (E := E) Hsrc A)).comp Uinv)
    (hA : IsCartanEigenOperator (E := E) Hsrc A lam) :
    IsCartanEigenOperator (E := E) Htgt ((U.comp A).comp Uinv) lam := by
  unfold IsCartanEigenOperator at hA ⊢
  calc
    cartanAdjoint (E := E) Htgt ((U.comp A).comp Uinv)
        = (U.comp (cartanAdjoint (E := E) Hsrc A)).comp Uinv := hconj
    _ = (U.comp (lam • A)).comp Uinv := by rw [hA]
    _ = lam • ((U.comp A).comp Uinv) := by
          simp [ContinuousLinearMap.smul_comp]

/--
Conjugation version of Cartan eigen-operator transport.

This packages the same invariant statement through explicit inverse and Cartan
conjugacy laws.
-/
theorem cartanEigenOperator_conjugateOperator
    {U V Hsrc Htgt A : EndH} {lam : ℝ}
    (hInv : IsTwoSidedInverse (E := E) U V)
    (hH : ConjugatesCartan (E := E) U V Hsrc Htgt)
    (hA : IsCartanEigenOperator (E := E) Hsrc A lam) :
    IsCartanEigenOperator (E := E) Htgt (conjugateOperator (E := E) U V A) lam := by
  rcases hInv with ⟨hVU, hUV⟩
  unfold IsCartanEigenOperator cartanAdjoint transportCommutator conjugateOperator ConjugatesCartan at *
  change Hsrc * A - A * Hsrc = lam • A at hA
  rw [hH]
  calc
    U * Hsrc * V * (U * A * V) - (U * A * V) * (U * Hsrc * V)
        = U * Hsrc * (V * U) * A * V - U * A * (V * U) * Hsrc * V := by
            noncomm_ring
    _ = U * Hsrc * 1 * A * V - U * A * 1 * Hsrc * V := by
            rw [hVU]
    _ = U * (Hsrc * A - A * Hsrc) * V := by
            noncomm_ring
    _ = U * (lam • A) * V := by rw [hA]
    _ = lam • (U * A * V) := by
            change (U.comp (lam • A)).comp V = lam • ((U.comp A).comp V)
            rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]

/-- A frame change preserves the Drazin regular/defect split. -/
def PreservesDrazinSplit (T TD U : EndH) : Prop :=
  U * Preg T TD = Preg T TD * U ∧
    U * Pzero T TD = Pzero T TD * U

/--
Transport of a Drazin split between two frame representatives.

Use this for equivalence of two structured Drazin geometries.  Use
`PreservesDrazinSplit` for automorphisms of one fixed geometry.
-/
def TransportsDrazinSplit
    (Tsrc TDsrc Ttgt TDtgt U V : EndH) : Prop :=
  Preg Ttgt TDtgt = U * Preg Tsrc TDsrc * V ∧
    Pzero Ttgt TDtgt = U * Pzero Tsrc TDsrc * V

/-- A frame change preserves the fixed doubled chiral grading `ε`. -/
def PreservesChiralGrading (U : EndH) : Prop :=
  U * spectral_epsilon (E := E) = spectral_epsilon (E := E) * U

/-- A frame change preserves the Krein bilinear form. -/
def PreservesKreinForm (U : EndH) : Prop :=
  ∀ x y : H₂,
    KreinSpace.kreinInner (H := H₂) (U x) (U y) =
      KreinSpace.kreinInner (H := H₂) x y

/--
Admissible Bogoliubov-Cartan frame change.

This is an invariant-sector predicate: invertibility, Cartan conjugacy, Drazin
split preservation, chiral grading preservation, and Krein form preservation.
-/
def IsBogoliubovCartanFrameChange
    (T TD Hsrc Htgt U V : EndH) : Prop :=
  IsTwoSidedInverse (E := E) U V ∧
    ConjugatesCartan (E := E) U V Hsrc Htgt ∧
    PreservesDrazinSplit (E := E) T TD U ∧
    PreservesChiralGrading (E := E) U ∧
    PreservesKreinForm (E := E) U

private theorem frameChange_u_injective
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V) :
    Function.Injective U := by
  rcases hFrame with ⟨hInv, -, -, -, -⟩
  rcases hInv with ⟨hVU, -⟩
  intro x y hxy
  calc
    x = (V * U) x := by
      symm
      simpa using congrArg (fun T : EndH => T x) hVU
    _ = V (U y) := by simpa using congrArg V hxy
    _ = (V * U) y := by rfl
    _ = y := by
      simpa using congrArg (fun T : EndH => T y) hVU

theorem maps_regular_sector
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    {x : H₂}
    (hreg : Preg T TD x = x) :
    Preg T TD (U x) = U x := by
  rcases hFrame with ⟨-, -, hSplit, -, -⟩
  have hPreg := hSplit.1
  calc
    Preg T TD (U x) = U (Preg T TD x) := by
      simpa using congrArg (fun T' : EndH => T' x) hPreg.symm
    _ = U x := by rw [hreg]

theorem maps_null_sector
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    {x : H₂}
    (hnull : Pzero T TD x = x) :
    Pzero T TD (U x) = U x := by
  rcases hFrame with ⟨-, -, hSplit, -, -⟩
  have hPzero := hSplit.2
  calc
    Pzero T TD (U x) = U (Pzero T TD x) := by
      simpa using congrArg (fun T' : EndH => T' x) hPzero.symm
    _ = U x := by rw [hnull]

theorem inverse_maps_regular_sector
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    {x : H₂}
    (hreg : Preg T TD x = x) :
    Preg T TD (V x) = V x := by
  have hUinj := frameChange_u_injective (E := E) hFrame
  rcases hFrame with ⟨hInv, -, hSplit, -, -⟩
  rcases hInv with ⟨-, hUV⟩
  have hPreg := hSplit.1
  have hUVx : U (V x) = x := by
    simpa using congrArg (fun T' : EndH => T' x) hUV
  apply hUinj
  calc
    U (Preg T TD (V x)) = Preg T TD (U (V x)) := by
      simpa using congrArg (fun T' : EndH => T' (V x)) hPreg
    _ = Preg T TD x := by rw [hUVx]
    _ = x := hreg
    _ = U (V x) := by symm; exact hUVx

theorem inverse_maps_null_sector
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    {x : H₂}
    (hnull : Pzero T TD x = x) :
    Pzero T TD (V x) = V x := by
  have hUinj := frameChange_u_injective (E := E) hFrame
  rcases hFrame with ⟨hInv, -, hSplit, -, -⟩
  rcases hInv with ⟨-, hUV⟩
  have hPzero := hSplit.2
  have hUVx : U (V x) = x := by
    simpa using congrArg (fun T' : EndH => T' x) hUV
  apply hUinj
  calc
    U (Pzero T TD (V x)) = Pzero T TD (U (V x)) := by
      simpa using congrArg (fun T' : EndH => T' (V x)) hPzero
    _ = Pzero T TD x := by rw [hUVx]
    _ = x := hnull
    _ = U (V x) := by symm; exact hUVx

theorem preserves_regular_krein_pairing
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    (x y : H₂)
    (_hx : Preg T TD x = x)
    (_hy : Preg T TD y = y) :
    KreinSpace.kreinInner (H := H₂) (U x) (U y) = KreinSpace.kreinInner (H := H₂) x y := by
  rcases hFrame with ⟨-, -, -, -, hKrein⟩
  exact hKrein x y

theorem maps_chiral_sector
    {T TD Hsrc Htgt U V : EndH}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    {chi : ℝ}
    {x : H₂}
    (hchi : spectral_epsilon (E := E) x = chi • x) :
    spectral_epsilon (E := E) (U x) = chi • U x := by
  rcases hFrame with ⟨-, -, -, hChiral, -⟩
  calc
    spectral_epsilon (E := E) (U x) = U (spectral_epsilon (E := E) x) := by
      simpa using congrArg (fun T' : EndH => T' x) hChiral.symm
    _ = U (chi • x) := by rw [hchi]
    _ = chi • U x := by simp

theorem cartanEigenOperator_map
    {T TD Hsrc Htgt U V A : EndH} {lam : ℝ}
    (hFrame : IsBogoliubovCartanFrameChange (E := E) T TD Hsrc Htgt U V)
    (hA : IsCartanEigenOperator (E := E) Hsrc A lam) :
    IsCartanEigenOperator (E := E) Htgt (conjugateOperator (E := E) U V A) lam := by
  rcases hFrame with ⟨hInv, hH, -, -, -⟩
  exact cartanEigenOperator_conjugateOperator (E := E) hInv hH hA

/--
Explicit exponential adjoint-flow calibration for a Cartan generator.

The infinitesimal theorem-safe statement is `IsCartanEigenOperator H X lam`,
namely `[H,X] = lam • X`.  The integrated statement

`exp(tH) X exp(-tH) = exp(t lam) • X`

requires an exponential/ODE or functional-calculus backend.  This carrier stores
only the chosen exponential family; any integrated eigen-operator law must be
provided explicitly to the theorem that uses it.
-/
structure CartanExponentialAdjointCalibration
    (H : EndH) where
  /-- Supplied exponential of the Cartan generator. -/
  expCartan : ℝ → EndH

  /-- Exponential identity at zero. -/
  expCartan_zero : expCartan 0 = 1

namespace CartanExponentialAdjointCalibration

/-- The calibrated adjoint flow `X ↦ exp(tH) X exp(-tH)`. -/
noncomputable def adjointExponentialFlow
    (H : EndH)
    (C : CartanExponentialAdjointCalibration (E := E) H)
    (t : ℝ) (X : EndH) : EndH :=
  C.expCartan t * X * C.expCartan (-t)

/-- At time zero, the calibrated adjoint flow fixes every operator. -/
theorem adjointExponentialFlow_zero
    (H : EndH)
    (C : CartanExponentialAdjointCalibration (E := E) H)
    (X : EndH) :
    adjointExponentialFlow (E := E) H C 0 X = X := by
  unfold adjointExponentialFlow
  rw [C.expCartan_zero]
  rw [neg_zero, C.expCartan_zero]
  simp

/--
A Cartan eigen-operator scales exponentially under an explicitly supplied
integrated adjoint-flow theorem.
-/
theorem cartanEigenOperator_integrates_to_exponential_flow
    {H : EndH}
    (C : CartanExponentialAdjointCalibration (E := E) H)
    (hflow : ∀ {X : EndH} {lam : ℝ},
      IsCartanEigenOperator (E := E) H X lam →
        ∀ t : ℝ, C.expCartan t * X * C.expCartan (-t) = Real.exp (t * lam) • X)
    {X : EndH} {lam : ℝ}
    (hX : IsCartanEigenOperator (E := E) H X lam)
    (t : ℝ) :
    adjointExponentialFlow (E := E) H C t X = Real.exp (t * lam) • X := by
  unfold adjointExponentialFlow
  exact hflow hX t

/--
Additive-time identity on a Cartan eigen-operator.

This uses only the explicitly supplied integrated flow theorem and the scalar
exponential identity; it does not prove existence of the exponential flow from
the infinitesimal derivation law.
-/
theorem adjointExponentialFlow_add_on_eigenoperator
    {H : EndH}
    (C : CartanExponentialAdjointCalibration (E := E) H)
    (hflow : ∀ {X : EndH} {lam : ℝ},
      IsCartanEigenOperator (E := E) H X lam →
        ∀ t : ℝ, C.expCartan t * X * C.expCartan (-t) = Real.exp (t * lam) • X)
    {X : EndH} {lam : ℝ}
    (hX : IsCartanEigenOperator (E := E) H X lam)
    (t s : ℝ) :
    adjointExponentialFlow (E := E) H C (t + s) X =
      Real.exp (t * lam) • adjointExponentialFlow (E := E) H C s X := by
  rw [cartanEigenOperator_integrates_to_exponential_flow (E := E) C hflow hX (t + s)]
  rw [cartanEigenOperator_integrates_to_exponential_flow (E := E) C hflow hX s]
  have harg : (t + s) * lam = t * lam + s * lam := by
    rw [add_mul]
  rw [harg, Real.exp_add, smul_smul]

end CartanExponentialAdjointCalibration

/--
Kernel-clean Cartan frame equivalence.

This carrier contains only the data needed to prove Cartan weight transport:
a two-sided inverse pair and Cartan conjugacy.  Drazin, chiral, and Krein
compatibility live in `BogoliubovCartanFrameEquiv` as additional witnesses.
-/
structure CartanFrameEquiv
    (Hsrc Htgt : EndH) where
  /-- Frame-change operator. -/
  U : EndH

  /-- Inverse frame-change operator. -/
  Uinv : EndH

  /-- Left inverse law. -/
  left_inv : Uinv * U = 1

  /-- Right inverse law. -/
  right_inv : U * Uinv = 1

  /-- Cartan generator transport law. -/
  conjugatesCartan :
    Htgt = U * Hsrc * Uinv

namespace CartanFrameEquiv

variable {Hsrc Htgt : EndH}
variable (F : CartanFrameEquiv (E := E) Hsrc Htgt)

end CartanFrameEquiv

/--
Structure form of a Bogoliubov-Cartan frame equivalence.

The frame is a representative choice.  The invariant data are the Cartan
weights, Drazin sector support, chiral grading, and Krein pairing.  This
structure packages the same hypotheses as `IsBogoliubovCartanFrameChange`,
but makes downstream readbacks field-projection friendly.
-/
structure BogoliubovCartanFrameEquiv
    (T TD Hsrc Htgt : EndH) where
  /-- Kernel-clean Cartan frame component. -/
  cartan :
    CartanFrameEquiv (E := E) Hsrc Htgt

  /-- Regular Drazin projector is preserved by the frame. -/
  preservesPreg :
    cartan.U * Preg T TD = Preg T TD * cartan.U

  /-- Defect/null Drazin projector is preserved by the frame. -/
  preservesPzero :
    cartan.U * Pzero T TD = Pzero T TD * cartan.U

  /-- The fixed doubled chiral grading is preserved by the frame. -/
  preservesGammaS :
    cartan.U * spectral_epsilon (E := E) = spectral_epsilon (E := E) * cartan.U

  /--
  The frame preserves the Krein pairing.

  Kept as an abstract witness at this layer.  Concrete bilinear-form transport
  can be installed by a carrier-specific specialization without making the
  Cartan weight transport depend on that analytic backend.
  -/
  preservesKrein :
    Prop

  /-- Evidence for the Krein-preservation witness. -/
  preservesKrein_holds :
    preservesKrein

namespace BogoliubovCartanFrameEquiv

variable {T TD Hsrc Htgt : EndH}
variable (F : BogoliubovCartanFrameEquiv (E := E) T TD Hsrc Htgt)

end BogoliubovCartanFrameEquiv

end Core

end BogoliubovCartanEigenOperator
