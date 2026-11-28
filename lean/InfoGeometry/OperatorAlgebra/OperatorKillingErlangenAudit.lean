/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorKillingErlangenBridge
import InfoGeometry.OperatorAlgebra.RealMatrixKillingErlangen
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-!
# Operator Killing/Erlangen declaration audit and independent consumers

The consumers check the inverse-pullback convention on linear functionals,
both slots of bilinear forms, and their product action. Group-law consumers
also check coherence of the scoped scalar-action and group-action instances.
The real matrix consumers exhibit noncommutativity and independent
functional and Frobenius-invariance obstructions; the bounded-flow consumer differentiates
the constructed exponential automorphism rather than assuming a flow.

The audit uses native module ownership to enumerate all declarations of the
five operator owners and their shared action-level closure owner, including
private and generated declarations. It rejects owned axioms, unsafe and
partial declarations, and transitive axioms outside the three stated
foundations. The final success record is suppressed if a consumer or any
other earlier command logged an error. This does not certify positivity,
star preservation, complete positivity, or a modular interpretation.
-/

noncomputable section

namespace OperatorKillingErlangenAudit

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure
open InfoGeometry.OperatorAlgebra.OperatorKillingExponential
open InfoGeometry.OperatorAlgebra.OperatorKillingErlangenBridge
open InfoGeometry.OperatorAlgebra.RealMatrixKillingErlangen
open InfoGeometry.Geometry.AssociativeGaugeConnection
open InfoGeometry.Canonical.FlowErlangenClosure

section ExplicitActions

variable {A : Type*} [Ring A] [Algebra ℝ A]

-- The named action remains usable before opening its notation scope.
example (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) (x : A) :
    (algebraAutFunctionalAction A).smul α ω x = ω (α.symm x) := rfl

example (α : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) (x y : A) :
    (algebraAutBilinFormAction A).smul α B x y =
      B (α.symm x) (α.symm y) := rfl

end ExplicitActions

section ScopedPullback

open scoped OperatorInvariantPullback

variable {A : Type*} [Ring A] [Algebra ℝ A]

-- The functional uses the inverse automorphism on its argument.
example (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) (x : A) :
    (α • ω) x = ω (α.symm x) := rfl

-- The form uses that inverse in both arguments, not only in the outer map.
example (α : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) (x y : A) :
    (α • B) x y = B (α.symm x) (α.symm y) := rfl

example (α : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) (x y : A) :
    (α • B) (α x) y = B x (α.symm y) := by
  simp only [algebraAut_bilinForm_smul_apply, AlgEquiv.symm_apply_apply]

example (α : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) (x y : A) :
    (α • B) x (α y) = B (α.symm x) y := by
  simp only [algebraAut_bilinForm_smul_apply, AlgEquiv.symm_apply_apply]

-- The high-priority SMul projections agree with the selected MulAction laws.
example (α β : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) :
    (α * β) • ω = α • (β • ω) := mul_smul α β ω

example (α β : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) :
    (α * β) • B = α • (β • B) := mul_smul α β B

-- Both factors of the native product inherit their intended pullback action.
example (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ A) (x : A) :
    (α • (ω, B)).1 x = ω (α.symm x) := rfl

example (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ A) (x y : A) :
    (α • (ω, B)).2 x y = B (α.symm x) (α.symm y) := rfl

example (α β : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ A) :
    (α * β) • (ω, B) = α • (β • (ω, B)) := mul_smul α β (ω, B)

-- The public stabilizer statement exposes forward preservation for both data.
example (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A) :
    α ∈ functionalFormAutomorphismSubgroup ω B ↔
      (∀ x, ω (α x) = ω x) ∧ (∀ x y, B (α x) (α y) = B x y) :=
  mem_functionalFormAutomorphismSubgroup_iff α ω B

-- Closure is relative to the displayed product carrier, with a bound rather
-- than an unjustified equality to every symmetry preserving a chosen pair.
example (H : Subgroup (A ≃ₐ[ℝ] A)) (ω : A →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ A) :
    symmetryClosure (A ≃ₐ[ℝ] A)
        ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A) H ≤
        functionalFormAutomorphismSubgroup ω B ↔
      H ≤ functionalFormAutomorphismSubgroup ω B :=
  symmetryClosure_le_functionalForm_iff H ω B

end ScopedPullback

section NoncommutativeMatrices

-- The specialization is the full noncommutative real matrix algebra.
example : raising * lowering ≠ lowering * raising := raising_lowering_noncommute

example : entryZero (innerDerivative (R := ℝ) raising lowering) = 1 :=
  innerDerivative_raising_lowering_entry

-- The same actual derivation preserves trace but fails a separate functional.
example :
    IsOperatorialKillingField (Matrix.traceLinearMap (Fin 2) ℝ ℝ) matrixTraceForm
        (innerDerivative (R := ℝ) raising) ∧
      ¬ (∀ X : RealMatrixTwo, entryZero (innerDerivative (R := ℝ) raising X) = 0) :=
  ⟨innerDerivative_isOperatorialKilling raising,
    leibniz_not_imply_functional_invariance.2⟩

-- The form used by this specialization is nondegenerate but indefinite.
example : (matrixTraceForm (n := Fin 2)).Nondegenerate := matrixTraceForm_nondegenerate

example : matrixTraceForm (raising - lowering) (raising - lowering) = -2 :=
  matrixTraceForm_negative_direction

-- Leibniz plus trace annihilation still does not imply Frobenius skewness.
example :
    Matrix.trace ((innerDerivative (R := ℝ) diagonalGenerator raising).transpose * raising) +
      Matrix.trace (raising.transpose *
        innerDerivative (R := ℝ) diagonalGenerator raising) = 2 :=
  frobenius_killing_defect

example : ¬ (∀ X Y : RealMatrixTwo,
    Matrix.trace ((innerDerivative (R := ℝ) diagonalGenerator X).transpose * Y) +
      Matrix.trace (X.transpose * innerDerivative (R := ℝ) diagonalGenerator Y) = 0) :=
  leibniz_trace_not_imply_frobenius_killing.2.2

end NoncommutativeMatrices

section BoundedGenerator

open scoped OperatorInvariantPullback

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

-- Only infinitesimal hypotheses are supplied: the owner constructs the
-- automorphism group and proves that its derivative is the specified D.
example (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap)
    (x : A) :
    HasDerivAt
      (fun t : ℝ => boundedKillingFlowHom ω B D hD (Multiplicative.ofAdd t) x)
      (D x) 0 :=
  hasDerivAt_boundedKillingFlow_zero ω B D hD x

-- Inverse time is the inverse of that same native algebra automorphism.
example (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap)
    (t : ℝ) :
    boundedKillingFlowHom ω B D hD (Multiplicative.ofAdd (-t)) =
      (boundedKillingFlowHom ω B D hD (Multiplicative.ofAdd t)).symm :=
  map_inv (boundedKillingFlowHom ω B D hD) (Multiplicative.ofAdd t)

-- Finite-time invariance inhabits the very same scoped product stabilizer.
example (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hD : IsOperatorialKillingField ω.toLinearMap (continuousBilinForm B) D.toLinearMap)
    (t : Multiplicative ℝ) :
    boundedKillingFlowHom ω B D hD t • (ω.toLinearMap, continuousBilinForm B) =
      (ω.toLinearMap, continuousBilinForm B) := by
  have h := boundedKillingFlow_mem_stabilizer ω B D hD t
  rw [functionalFormAutomorphismSubgroup_eq_stabilizer_pair] at h
  exact h

end BoundedGenerator

section ReverseWithoutCompleteness

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

example (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (D : A →L[ℝ] A)
    (hΦ : ∀ x : A,
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0)
    (x y : A) :
    D (x * y) = D x * y + x * D y :=
  isDerivation_of_hasDerivAt_automorphismFlow Φ D hΦ x y

end ReverseWithoutCompleteness

section BackwardExistenceEquivalence

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

example (ω : A →L[ℝ] ℝ) (B : A →L[ℝ] A →L[ℝ] ℝ)
    (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (D : A →L[ℝ] A)
    (hΦ : ∀ x : A,
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0)
    (hω : ∀ (t : Multiplicative ℝ) (x : A), ω (Φ t x) = ω x)
    (hB : ∀ (t : Multiplicative ℝ) (x y : A), B (Φ t x) (Φ t y) = B x y) :
    D.toLinearMap ∈
      operatorialKillingLieSubalgebra ω.toLinearMap (continuousBilinForm B) := by
  apply (mem_operatorialKillingLieSubalgebra
    ω.toLinearMap (continuousBilinForm B) D.toLinearMap).mpr
  exact (isOperatorialKilling_iff_exists_invariant_flow ω B D).mpr
    ⟨Φ, hΦ, hω, hB⟩

end BackwardExistenceEquivalence

open Lean Elab Command

private def owners : Array Name := #[
  `InfoGeometry.Canonical.FlowErlangenClosure,
  `InfoGeometry.OperatorAlgebra.OperatorialKillingLieClosure,
  `InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure,
  `InfoGeometry.OperatorAlgebra.OperatorKillingExponential,
  `InfoGeometry.OperatorAlgebra.RealMatrixKillingErlangen,
  `InfoGeometry.OperatorAlgebra.OperatorKillingErlangenBridge
]

private def ownerOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if owners.contains (ownerOf env name) then
      names := names.push name
  names := names.qsort Name.lt
  for owner in owners do
    if !(names.any fun name => ownerOf env name == owner) then
      throwError "No declarations found in requested owner module {owner}"
  for name in names do
    let some info := env.checked.get.find? name |
      throwError "Missing checked declaration {name}"
    let axioms ← collectAxioms name
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Rejected axiom {ax} in declaration {name}"
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    let ownedDeps := dependencies.filter fun dependency => owners.contains (ownerOf env dependency)
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "declaration"),
      ("name", toJson name.toString),
      ("module", toJson (ownerOf env name).toString),
      ("kind", toJson (kindOf info)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson (dependencies.map Name.toString)),
      ("owned_dependencies", toJson (ownedDeps.map Name.toString))
    ]).compress
  if (← MonadLog.hasErrors) then
    throwError "Consumer or declaration audit logged an error; refusing a success summary"
  let moduleCounts := owners.map fun owner => Json.mkObj [
    ("module", toJson owner.toString),
    ("declarations", toJson (names.filter fun name => ownerOf env name == owner).size)
  ]
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("declarations", toJson names.size),
    ("module_counts", Json.arr moduleCounts),
    ("modules", toJson (owners.map Name.toString)),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("status", toJson "PASS")
  ]).compress

end OperatorKillingErlangenAudit
