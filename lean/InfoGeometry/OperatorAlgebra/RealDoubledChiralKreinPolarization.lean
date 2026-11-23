/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinHadamard
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinCarrier
import InfoGeometry.Algebra.GradedNullconeAlgebra

/-!
# Polarization, Positive Compatibility, and Separations for Doubled Krein Spaces

This module separates the purely algebraic null-polarization structure `(V, b, Γ, J)` from
positive Hilbert compatibility `g_J(u, v) = b(u, J v)`, connects the diagonal Krein form to the
chiral cross-sheet form via an explicit Hadamard coordinate-change equivalence, formulates an
explicit `ChiralObservablesDynamics` structure for energy/mass positivity without assuming
calibrated readouts, and records explicit R5 separation theorems (`dim E > 1` null vectors outside
the chiral subspaces, and `J ↦ -J` sign reversal of `g_J`).
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization

open InfoGeometry.Krein
open InfoGeometry.Carrier
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinHadamard
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinCarrier
open InfoGeometry.Algebra.GradedNullconeAlgebra

universe u v

/-! ## 1. Abstract Null Polarization Data -/

/-- Purely algebraic null-polarization datum `(V, b, Γ, J)` without assuming positivity of
`b(u, J u)`.  Here `b` is a symmetric nondegenerate bilinear form, `Γ` is a chiral grading
involution that anti-preserves `b` (making `N₊` and `N₋` isotropic), and `J` is an anticommuting
mirror involution preserving `b`. -/
structure NullPolarizationData (V : Type u) [AddCommGroup V] [Module ℝ V] : Type u where
  /-- Indefinite symmetric Krein pairing `b`. -/
  b : LinearMap.BilinForm ℝ V
  /-- Chiral `ℤ/2`-grading involution `Γ`. -/
  Γ : Module.End ℝ V
  /-- Mirror / fundamental involution `J`. -/
  J : Module.End ℝ V
  /-- `b` is symmetric. -/
  b_symm : ∀ u v : V, b u v = b v u
  /-- `b` is nondegenerate. -/
  b_nondegenerate : IsNondegeneratePairing b
  /-- `Γ² = I`. -/
  Γ_sq : Γ.comp Γ = LinearMap.id
  /-- `J² = I`. -/
  J_sq : J.comp J = LinearMap.id
  /-- `{Γ, J} = 0`. -/
  Γ_J_anticomm : Γ.comp J = -(J.comp Γ)
  /-- `Γ` reverses the sign of `b`. -/
  b_Γ_anti : ∀ u v : V, b (Γ u) (Γ v) = -b u v
  /-- `J` preserves `b`. -/
  b_J_invariant : ∀ u v : V, b (J u) (J v) = b u v

namespace NullPolarizationData

section AlgebraicLaws

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (P : NullPolarizationData V)

/-- Induced symmetric bilinear form `g_J(u, v) = b(u, J v)`. -/
def gJ : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ
    (fun u v => P.b u (P.J v))
    (fun u₁ u₂ v => by simp [map_add])
    (fun c u v => by simp [map_smul])
    (fun u v₁ v₂ => by simp [map_add])
    (fun c u v => by simp [map_smul])

/-- Antisymmetric symplectic form `ω(u, v) = b(Γ u, v)`. -/
def symplecticForm : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ
    (fun u v => P.b (P.Γ u) v)
    (fun u₁ u₂ v => by simp [map_add])
    (fun c u v => by simp [map_smul])
    (fun u v₁ v₂ => (P.b (P.Γ u)).map_add v₁ v₂)
    (fun c u v => (P.b (P.Γ u)).map_smul c v)

/-- Induced real complex structure `K = J ∘ Γ`. -/
def complexStructure : Module.End ℝ V :=
  P.J.comp P.Γ

/-- Positive chiral / nullcone projector `(I + Γ) / 2`. -/
def projPlus : Module.End ℝ V :=
  (1 / 2 : ℝ) • (LinearMap.id + P.Γ)

/-- Negative chiral / nullcone projector `(I - Γ) / 2`. -/
def projMinus : Module.End ℝ V :=
  (1 / 2 : ℝ) • (LinearMap.id - P.Γ)

/-- Positive isotropic nullcone `N₊ = im((I + Γ) / 2)`. -/
def nullPlusSubmodule : Submodule ℝ V :=
  LinearMap.range P.projPlus

/-- Negative isotropic nullcone `N₋ = im((I - Γ) / 2)`. -/
def nullMinusSubmodule : Submodule ℝ V :=
  LinearMap.range P.projMinus

@[simp] theorem gJ_apply (u v : V) : P.gJ u v = P.b u (P.J v) := rfl

@[simp] theorem symplecticForm_apply (u v : V) : P.symplecticForm u v = P.b (P.Γ u) v := rfl

@[simp] theorem Γ_apply_Γ (u : V) : P.Γ (P.Γ u) = u := by
  simpa [LinearMap.comp_apply] using congrArg (fun T : Module.End ℝ V => T u) P.Γ_sq

@[simp] theorem J_apply_J (u : V) : P.J (P.J u) = u := by
  simpa [LinearMap.comp_apply] using congrArg (fun T : Module.End ℝ V => T u) P.J_sq

theorem Γ_J_apply (u : V) : P.Γ (P.J u) = -P.J (P.Γ u) := by
  simpa [LinearMap.comp_apply] using congrArg (fun T : Module.End ℝ V => T u) P.Γ_J_anticomm

theorem J_Γ_apply (u : V) : P.J (P.Γ u) = -P.Γ (P.J u) := by
  have h := congrArg Neg.neg (P.Γ_J_apply u)
  simpa using h.symm

theorem b_eq_zero_of_forall_right {u : V} (hu : ∀ v : V, P.b u v = 0) : u = 0 := by
  apply P.b_nondegenerate
  ext v
  change P.b u v = P.b 0 v
  simp [hu v]

theorem projPlus_apply (u : V) : P.projPlus u = (1 / 2 : ℝ) • (u + P.Γ u) := by
  simp [projPlus]

theorem projMinus_apply (u : V) : P.projMinus u = (1 / 2 : ℝ) • (u - P.Γ u) := by
  simp [projMinus]

theorem projPlus_add_projMinus : P.projPlus + P.projMinus = LinearMap.id := by
  ext u
  simp only [LinearMap.add_apply, LinearMap.id_apply, projPlus_apply, projMinus_apply]
  rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ u, smul_smul]
  norm_num

theorem projPlus_add_projMinus_apply (u : V) : P.projPlus u + P.projMinus u = u := by
  simpa [LinearMap.add_apply] using
    congrArg (fun T : Module.End ℝ V => T u) P.projPlus_add_projMinus

theorem projPlus_idempotent : P.projPlus.comp P.projPlus = P.projPlus := by
  ext u
  simp only [LinearMap.comp_apply, projPlus_apply, map_smul, map_add, Γ_apply_Γ]
  module

theorem projMinus_idempotent : P.projMinus.comp P.projMinus = P.projMinus := by
  ext u
  simp only [LinearMap.comp_apply, projMinus_apply, map_smul, map_sub, Γ_apply_Γ]
  module

theorem projPlus_comp_projMinus : P.projPlus.comp P.projMinus = 0 := by
  ext u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, projPlus_apply, projMinus_apply,
    map_smul, map_sub, Γ_apply_Γ]
  module

theorem projMinus_comp_projPlus : P.projMinus.comp P.projPlus = 0 := by
  ext u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, projPlus_apply, projMinus_apply,
    map_smul, map_add, Γ_apply_Γ]
  module

theorem mem_nullPlusSubmodule_iff (u : V) : u ∈ P.nullPlusSubmodule ↔ P.Γ u = u := by
  constructor
  · rintro ⟨x, rfl⟩
    simp only [projPlus_apply, map_smul, map_add, Γ_apply_Γ]
    rw [add_comm]
  · intro h
    refine ⟨u, ?_⟩
    simp only [projPlus_apply, h, ← two_smul ℝ u, smul_smul]
    norm_num

theorem mem_nullMinusSubmodule_iff (u : V) : u ∈ P.nullMinusSubmodule ↔ P.Γ u = -u := by
  constructor
  · rintro ⟨x, rfl⟩
    simp only [projMinus_apply, map_smul, map_sub, Γ_apply_Γ, ← smul_neg]
    congr 1
    abel
  · intro h
    refine ⟨u, ?_⟩
    simp only [projMinus_apply, h, sub_neg_eq_add, ← two_smul ℝ u, smul_smul]
    norm_num

theorem isCompl_nullSubmodules : IsCompl P.nullPlusSubmodule P.nullMinusSubmodule := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff_inf_le]
    intro u hu
    rcases hu with ⟨huPlus, huMinus⟩
    change u ∈ P.nullPlusSubmodule at huPlus
    change u ∈ P.nullMinusSubmodule at huMinus
    rw [P.mem_nullPlusSubmodule_iff] at huPlus
    rw [P.mem_nullMinusSubmodule_iff] at huMinus
    have hneg : u = -u := huPlus.symm.trans huMinus
    have h2 : (2 : ℝ) • u = 0 := by
      rw [two_smul]
      conv_lhs => rhs; rw [hneg]
      exact add_neg_cancel u
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  · rw [codisjoint_iff, eq_top_iff]
    intro u _
    rw [Submodule.mem_sup]
    refine ⟨P.projPlus u, ⟨u, rfl⟩, P.projMinus u, ⟨u, rfl⟩, P.projPlus_add_projMinus_apply u⟩

theorem J_comp_projPlus : P.J.comp P.projPlus = P.projMinus.comp P.J := by
  ext u
  simp only [LinearMap.comp_apply, projPlus_apply, projMinus_apply, map_smul, map_add,
    P.J_Γ_apply, sub_eq_add_neg]

theorem J_comp_projMinus : P.J.comp P.projMinus = P.projPlus.comp P.J := by
  ext u
  simp only [LinearMap.comp_apply, projPlus_apply, projMinus_apply, map_smul, map_sub,
    P.J_Γ_apply, sub_neg_eq_add]

theorem J_mem_nullMinus_of_mem_nullPlus {u : V} (hu : u ∈ P.nullPlusSubmodule) :
    P.J u ∈ P.nullMinusSubmodule := by
  rw [P.mem_nullPlusSubmodule_iff] at hu
  rw [P.mem_nullMinusSubmodule_iff, P.Γ_J_apply, hu]

theorem J_mem_nullPlus_of_mem_nullMinus {u : V} (hu : u ∈ P.nullMinusSubmodule) :
    P.J u ∈ P.nullPlusSubmodule := by
  rw [P.mem_nullMinusSubmodule_iff] at hu
  rw [P.mem_nullPlusSubmodule_iff, P.Γ_J_apply, hu, map_neg, neg_neg]

theorem nullPlus_isotropic {u v : V} (hu : u ∈ P.nullPlusSubmodule)
    (hv : v ∈ P.nullPlusSubmodule) : P.b u v = 0 := by
  rw [P.mem_nullPlusSubmodule_iff] at hu hv
  have hanti := P.b_Γ_anti u v
  rw [hu, hv] at hanti
  have hsum : P.b u v + P.b u v = 0 := by
    conv_lhs => rhs; rw [hanti]
    exact add_neg_cancel (P.b u v)
  exact add_self_eq_zero.mp hsum

theorem nullMinus_isotropic {u v : V} (hu : u ∈ P.nullMinusSubmodule)
    (hv : v ∈ P.nullMinusSubmodule) : P.b u v = 0 := by
  rw [P.mem_nullMinusSubmodule_iff] at hu hv
  have hanti := P.b_Γ_anti u v
  rw [hu, hv, map_neg, map_neg] at hanti
  have hneg : P.b u v = -P.b u v := by simpa using hanti
  have hsum : P.b u v + P.b u v = 0 := by
    conv_lhs => rhs; rw [hneg]
    exact add_neg_cancel (P.b u v)
  exact add_self_eq_zero.mp hsum

theorem b_self_Γ_eq_zero (u : V) : P.b u (P.Γ u) = 0 := by
  have h1 : P.b (P.Γ u) (P.Γ (P.Γ u)) = -P.b u (P.Γ u) := P.b_Γ_anti u (P.Γ u)
  rw [P.Γ_apply_Γ, P.b_symm (P.Γ u) u] at h1
  have hsum : P.b u (P.Γ u) + P.b u (P.Γ u) = 0 := by
    conv_lhs => rhs; rw [h1]
    exact add_neg_cancel (P.b u (P.Γ u))
  exact add_self_eq_zero.mp hsum

theorem gJ_symm (u v : V) : P.gJ u v = P.gJ v u := by
  simp only [gJ_apply]
  calc
    P.b u (P.J v) = P.b (P.J u) (P.J (P.J v)) := (P.b_J_invariant u (P.J v)).symm
    _ = P.b (P.J u) v := by rw [P.J_apply_J]
    _ = P.b v (P.J u) := P.b_symm (P.J u) v

theorem gJ_nondegenerate : IsNondegeneratePairing P.gJ := by
  intro u v huv
  apply P.b_nondegenerate
  ext w
  have hw := congrArg (fun f : Module.Dual ℝ V => f (P.J w)) huv
  change P.gJ u (P.J w) = P.gJ v (P.J w) at hw
  change P.b u w = P.b v w
  simpa [gJ_apply, P.J_apply_J] using hw

theorem gJ_J_invariant (u v : V) : P.gJ (P.J u) (P.J v) = P.gJ u v := by
  simp only [gJ_apply, P.J_apply_J]
  have h := P.b_J_invariant u (P.J v)
  simpa [P.J_apply_J] using h

theorem gJ_Γ_invariant (u v : V) : P.gJ (P.Γ u) (P.Γ v) = P.gJ u v := by
  simp only [gJ_apply, P.J_Γ_apply, map_neg]
  rw [P.b_Γ_anti u (P.J v), neg_neg]

theorem gJ_nullPlus_orthogonal_nullMinus {u v : V} (hu : u ∈ P.nullPlusSubmodule)
    (hv : v ∈ P.nullMinusSubmodule) : P.gJ u v = 0 := by
  rw [gJ_apply]
  exact P.nullPlus_isotropic hu (P.J_mem_nullPlus_of_mem_nullMinus hv)

theorem b_eq_gJ_J (u v : V) : P.b u v = P.gJ u (P.J v) := by
  simp [gJ_apply]

theorem symplecticForm_skew (u v : V) : P.symplecticForm u v = -P.symplecticForm v u := by
  simp only [symplecticForm_apply]
  have h := P.b_Γ_anti u (P.Γ v)
  rw [P.Γ_apply_Γ] at h
  rw [h, P.b_symm u (P.Γ v)]

theorem complexStructure_sq : P.complexStructure.comp P.complexStructure = -LinearMap.id := by
  ext u
  simp [complexStructure, P.Γ_J_apply]

theorem J_ne_Γ [Nontrivial V] : P.J ≠ P.Γ := by
  intro hEq
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have h2 : P.Γ.comp P.Γ = -(P.Γ.comp P.Γ) := by
    have h := P.Γ_J_anticomm
    rwa [hEq] at h
  have hsq : (LinearMap.id : Module.End ℝ V) = -LinearMap.id := by
    simpa [P.Γ_sq] using h2
  have hu0 : u = -u := congrArg (fun T : Module.End ℝ V => T u) hsq
  have hsum : (2 : ℝ) • u = 0 := by
    rw [two_smul]
    conv_lhs => rhs; rw [hu0]
    exact add_neg_cancel u
  exact hu ((smul_eq_zero.mp hsum).resolve_left (by norm_num))

/-- Replacing `J` by `-J` preserves all `NullPolarizationData` axioms while flipping the sign of
`g_J`. -/
def negMirror : NullPolarizationData V where
  b := P.b
  Γ := P.Γ
  J := -P.J
  b_symm := P.b_symm
  b_nondegenerate := P.b_nondegenerate
  Γ_sq := P.Γ_sq
  J_sq := by
    ext u
    simp [P.J_apply_J]
  Γ_J_anticomm := by
    ext u
    simp [P.Γ_J_apply]
  b_Γ_anti := P.b_Γ_anti
  b_J_invariant := by
    intro u v
    simp [P.b_J_invariant]

@[simp] theorem negMirror_b : P.negMirror.b = P.b := rfl
@[simp] theorem negMirror_Γ : P.negMirror.Γ = P.Γ := rfl
@[simp] theorem negMirror_J : P.negMirror.J = -P.J := rfl

theorem negMirror_gJ (u v : V) : P.negMirror.gJ u v = -P.gJ u v := by
  simp [gJ_apply, negMirror]

/-- Generalization of the R5 nullcone separation: any orthogonal nonzero pair in `N₊` produces a
nonzero null vector `e₁ + J e₂` lying outside both `N₊` and `N₋`. -/
theorem exists_null_outside_chiral_of_orthogonal
    {e₁ e₂ : V} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0)
    (h₁ : e₁ ∈ P.nullPlusSubmodule) (h₂ : e₂ ∈ P.nullPlusSubmodule)
    (horth : P.b e₁ (P.J e₂) = 0) :
    let u : V := e₁ + P.J e₂
    u ≠ 0 ∧ P.b u u = 0 ∧ P.projPlus u ≠ u ∧ P.projMinus u ≠ u := by
  intro u
  have hJ₂ : P.J e₂ ∈ P.nullMinusSubmodule := P.J_mem_nullMinus_of_mem_nullPlus h₂
  have h1Γ : P.Γ e₁ = e₁ := (P.mem_nullPlusSubmodule_iff e₁).mp h₁
  have hJ₂Γ : P.Γ (P.J e₂) = -P.J e₂ := (P.mem_nullMinusSubmodule_iff (P.J e₂)).mp hJ₂
  have hp1 : P.projPlus e₁ = e₁ := by
    simp only [projPlus_apply, h1Γ, ← two_smul ℝ e₁, smul_smul]
    norm_num
  have hpJ₂ : P.projPlus (P.J e₂) = 0 := by
    simp [projPlus_apply, hJ₂Γ]
  have hm1 : P.projMinus e₁ = 0 := by
    simp [projMinus_apply, h1Γ]
  have hmJ₂ : P.projMinus (P.J e₂) = P.J e₂ := by
    simp only [projMinus_apply, hJ₂Γ, sub_neg_eq_add, ← two_smul ℝ (P.J e₂), smul_smul]
    norm_num
  have hJ₂_ne : P.J e₂ ≠ 0 := by
    intro h0
    apply he₂
    calc
      e₂ = P.J (P.J e₂) := (P.J_apply_J e₂).symm
      _ = P.J 0 := by rw [h0]
      _ = 0 := map_zero P.J
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hu0
    have heq : e₁ = -(P.J e₂) := eq_neg_of_add_eq_zero_left hu0
    have hmem : e₁ ∈ P.nullMinusSubmodule := by
      rw [heq]
      exact Submodule.neg_mem _ hJ₂
    have hbot : e₁ ∈ P.nullPlusSubmodule ⊓ P.nullMinusSubmodule := ⟨h₁, hmem⟩
    rw [P.isCompl_nullSubmodules.inf_eq_bot, Submodule.mem_bot] at hbot
    exact he₁ hbot
  · have h11 : P.b e₁ e₁ = 0 := P.nullPlus_isotropic h₁ h₁
    have h22 : P.b (P.J e₂) (P.J e₂) = 0 := P.nullMinus_isotropic hJ₂ hJ₂
    have h21 : P.b (P.J e₂) e₁ = 0 := by rw [P.b_symm]; exact horth
    change P.b (e₁ + P.J e₂) (e₁ + P.J e₂) = 0
    have hexp : P.b (e₁ + P.J e₂) (e₁ + P.J e₂) =
        P.b e₁ e₁ + P.b e₁ (P.J e₂) + P.b (P.J e₂) e₁ + P.b (P.J e₂) (P.J e₂) := by
      simp only [map_add, LinearMap.add_apply]
      abel
    rw [hexp, h11, horth, h21, h22, add_zero, add_zero, add_zero]
  · intro hfix
    have hval : P.projPlus u = e₁ := by
      simp only [u, map_add, hp1, hpJ₂, add_zero]
    rw [hval] at hfix
    have h0 : P.J e₂ = 0 := by
      have hsub := congrArg (fun x : V => x - e₁) hfix
      simpa [u] using hsub.symm
    exact hJ₂_ne h0
  · intro hfix
    have hval : P.projMinus u = P.J e₂ := by
      simp only [u, map_add, hm1, hmJ₂, zero_add]
    rw [hval] at hfix
    have h0 : e₁ = 0 := by
      have hsub := congrArg (fun x : V => x - P.J e₂) hfix
      simpa [u] using hsub.symm
    exact he₁ h0

end AlgebraicLaws

/-- Canonical `NullPolarizationData` instance on `DoubledSpace E`. -/
def doubledNullPolarization (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NullPolarizationData (DoubledSpace E) where
  b := chiralKreinBilin (E := E)
  Γ := (gamma5 (E := E)).toLinearMap
  J := (etaChiral (E := E)).toLinearMap
  b_symm := chiralKreinBilin_symmetric (E := E)
  b_nondegenerate := chiralKreinBilin_nondegenerate (E := E)
  Γ_sq := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [gamma5, spectral_epsilon]
  J_sq := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [etaChiral, modular_j]
  Γ_J_anticomm := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [gamma5, etaChiral, spectral_epsilon, modular_j]
  b_Γ_anti := chiralKreinForm_gamma5_anti_invariant (E := E)
  b_J_invariant := chiralKreinForm_etaChiral_invariant (E := E)

/-- Algebraic `NullPolarizationData` instance on `NullconeCarrier H`. -/
def nullconeNullPolarization {H : Type*} [AddCommGroup H] [Module ℝ H]
    (b : LinearMap.BilinForm ℝ H) (hsym : ∀ u v : H, b u v = b v u)
    (hnd : IsNondegeneratePairing b) :
    NullPolarizationData (NullconeCarrier H) where
  b := LinearMap.mk₂ ℝ
    (fun x y => nullKreinPairing b x y)
    (fun x₁ x₂ y => by
      simp only [nullKreinPairing, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      abel)
    (fun c x y => by
      simp only [nullKreinPairing, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
        smul_eq_mul, mul_add])
    (fun x y₁ y₂ => by
      simp only [nullKreinPairing, Prod.fst_add, Prod.snd_add, map_add]
      abel)
    (fun c x y => by
      simp only [nullKreinPairing, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, mul_add])
  Γ := cutOp
  J := mirrorOp
  b_symm := fun x y => by
    simp only [LinearMap.mk₂_apply, nullKreinPairing]
    rw [hsym x.1 y.2, hsym x.2 y.1, add_comm]
  b_nondegenerate := by
    intro x y hxy
    have hdiff : ∀ z : NullconeCarrier H, nullKreinPairing b (x - y) z = 0 := by
      intro z
      have hz := congrArg (fun f : Module.Dual ℝ (NullconeCarrier H) => f z) hxy
      change nullKreinPairing b x z = nullKreinPairing b y z at hz
      have hx1 : b (x - y).1 z.2 = b x.1 z.2 - b y.1 z.2 := by
        simp [Prod.fst_sub]
      have hx2 : b (x - y).2 z.1 = b x.2 z.1 - b y.2 z.1 := by
        simp [Prod.snd_sub]
      simp only [nullKreinPairing] at hz ⊢
      rw [hx1, hx2]
      have hscal : (b x.1 z.2 - b y.1 z.2) + (b x.2 z.1 - b y.2 z.1) =
          (b x.1 z.2 + b x.2 z.1) - (b y.1 z.2 + b y.2 z.1) := by abel
      rw [hscal, hz, sub_self]
    have hnd' : ∀ z : NullconeCarrier H,
        (∀ w : NullconeCarrier H, nullKreinPairing b z w = 0) → z = 0 := by
      intro z hz
      have hz1 : z.1 = 0 := by
        apply hnd
        ext v
        have h := hz (nullMinus v)
        simp only [nullKreinPairing, nullMinus_apply, map_zero, add_zero] at h
        change (pairingFlat b z.1) v = (pairingFlat b 0) v
        simp [pairingFlat, h]
      have hz2 : z.2 = 0 := by
        apply hnd
        ext u
        have h := hz (nullPlus u)
        simp only [nullKreinPairing, nullPlus_apply, map_zero, zero_add] at h
        change (pairingFlat b z.2) u = (pairingFlat b 0) u
        simp [pairingFlat, h]
      ext <;> simp [hz1, hz2]
    exact sub_eq_zero.mp (hnd' (x - y) hdiff)
  Γ_sq := by ext x <;> simp
  J_sq := by ext x <;> simp
  Γ_J_anticomm := by ext x <;> simp
  b_Γ_anti := fun x y => by
    simp only [LinearMap.mk₂_apply, nullKreinPairing, cutOp_apply, map_neg, LinearMap.neg_apply]
    abel
  b_J_invariant := fun x y => by
    simp only [LinearMap.mk₂_apply, nullKreinPairing, mirrorOp_apply]
    exact add_comm _ _

end NullPolarizationData

/-! ## 2. Positive Hilbert Compatibility -/

/-- Separate 1-field positivity predicate distinguishing `J` from `-J`: `g_J(u, u) = b(u, J u)`
is strictly positive for all nonzero `u`. -/
structure PositiveHilbertCompatibility
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V) : Prop where
  /-- Strict positivity of `b(u, J u)` on nonzero vectors. -/
  pos_def : ∀ u : V, u ≠ 0 → 0 < P.b u (P.J u)

namespace PositiveHilbertCompatibility

section CompatibilityLaws

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {P : NullPolarizationData V}

theorem gJ_pos (hpos : PositiveHilbertCompatibility P) {u : V} (hu : u ≠ 0) :
    0 < P.gJ u u :=
  hpos.pos_def u hu

theorem gJ_nonneg (hpos : PositiveHilbertCompatibility P) (u : V) :
    0 ≤ P.gJ u u := by
  by_cases hu : u = 0
  · subst hu
    simp
  · exact le_of_lt (hpos.gJ_pos hu)

theorem gJ_eq_zero_iff (hpos : PositiveHilbertCompatibility P) (u : V) :
    P.gJ u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    by_contra hu
    exact absurd h (ne_of_gt (hpos.gJ_pos hu))
  · intro h
    subst h
    simp

theorem cauchy_schwarz (hpos : PositiveHilbertCompatibility P) (u v : V) :
    (P.gJ u v) ^ 2 ≤ P.gJ u u * P.gJ v v := by
  by_cases hu : u = 0
  · subst hu
    simp
  · have huu : 0 < P.gJ u u := hpos.gJ_pos hu
    let t : ℝ := -(P.gJ u v / P.gJ u u)
    have hnonneg : 0 ≤ P.gJ (t • u + v) (t • u + v) := hpos.gJ_nonneg (t • u + v)
    have hexp : P.gJ (t • u + v) (t • u + v) =
        t ^ 2 * P.gJ u u + 2 * t * P.gJ u v + P.gJ v v := by
      have hsymm : P.b v (P.J u) = P.b u (P.J v) := P.gJ_symm v u
      simp only [NullPolarizationData.gJ_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hsymm]
      ring
    rw [hexp] at hnonneg
    have hident : t ^ 2 * P.gJ u u + 2 * t * P.gJ u v + P.gJ v v =
        P.gJ v v - (P.gJ u v) ^ 2 / P.gJ u u := by
      have huu0 : P.gJ u u ≠ 0 := ne_of_gt huu
      dsimp [t]
      field_simp [huu0]
      ring
    rw [hident] at hnonneg
    have hdiv : (P.gJ u v) ^ 2 / P.gJ u u ≤ P.gJ v v := sub_nonneg.mp hnonneg
    have hmul := (div_le_iff₀ huu).mp hdiv
    simpa [mul_comm] using hmul

/-- Non-instance `InnerProductSpace.Core ℝ V` induced by positive Hilbert compatibility. -/
@[instance_reducible]
def toInnerProductCore (hpos : PositiveHilbertCompatibility P) :
    InnerProductSpace.Core ℝ V where
  inner u v := P.gJ u v
  conj_inner_symm u v := by simp [P.gJ_symm v u]
  re_inner_nonneg u := hpos.gJ_nonneg u
  add_left u v w := by simp [map_add]
  smul_left u v r := by simp [map_smul, smul_eq_mul]
  definite u hu := (hpos.gJ_eq_zero_iff u).mp hu

/-- Non-instance `HestenesKreinSpace V` induced by `PositiveHilbertCompatibility`. -/
@[instance_reducible]
def toHestenesKreinSpace (hpos : PositiveHilbertCompatibility P) : HestenesKreinSpace V where
  krein_form := P.b
  J := P.J
  J_involution := P.J_sq
  induced_hilbert_identity := hpos.pos_def

theorem not_negMirror [Nontrivial V] (hpos : PositiveHilbertCompatibility P) :
    ¬ PositiveHilbertCompatibility P.negMirror := by
  intro hneg
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have h1 : 0 < P.gJ u u := hpos.gJ_pos hu
  have h2 : 0 < P.negMirror.gJ u u := hneg.gJ_pos hu
  rw [P.negMirror_gJ u u] at h2
  linarith

theorem J_ne_neg_J [Nontrivial V] (hpos : PositiveHilbertCompatibility P) : P.J ≠ -P.J := by
  intro hEq
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have h1 : 0 < P.b u (P.J u) := hpos.pos_def u hu
  have hJu : P.J u = -P.J u := by
    simpa using congrArg (fun T : Module.End ℝ V => T u) hEq
  have hb : P.b u (P.J u) = -P.b u (P.J u) := by
    calc
      P.b u (P.J u) = P.b u (-P.J u) := by conv_lhs => rw [hJu]
      _ = -P.b u (P.J u) := map_neg (P.b u) (P.J u)
  linarith

end CompatibilityLaws

theorem doubledPositiveHilbertCompatibility (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    PositiveHilbertCompatibility (NullPolarizationData.doubledNullPolarization E) where
  pos_def u hu := by
    change 0 < chiralKreinForm u ((etaChiral (E := E)) u)
    rw [← chiralHilbertForm]
    exact chiralHilbertForm_self_pos (E := E) hu

theorem doubled_gJ_eq_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u v : DoubledSpace E) :
    (NullPolarizationData.doubledNullPolarization E).gJ u v = inner ℝ u v := by
  change chiralKreinForm u ((etaChiral (E := E)) v) = inner ℝ u v
  rw [← chiralHilbertForm, chiralHilbertForm_eq_inner]

end PositiveHilbertCompatibility

/-! ## 3. Diagonal Krein Data and Hadamard Polarization Equivalence -/

/-- Diagonal Krein datum `(V, bDiag, symmDiag, swapDiag)` where `symmDiag` preserves `bDiag` and
`swapDiag` anti-preserves `bDiag`. -/
structure DiagonalKreinData (V : Type u) [AddCommGroup V] [Module ℝ V] : Type u where
  /-- Diagonal indefinite symmetric Krein pairing. -/
  bDiag : LinearMap.BilinForm ℝ V
  /-- Fundamental symmetry preserving `bDiag`. -/
  symmDiag : Module.End ℝ V
  /-- Anticommuting swap involution reversing `bDiag`. -/
  swapDiag : Module.End ℝ V
  /-- `bDiag` is symmetric. -/
  bDiag_symm : ∀ u v : V, bDiag u v = bDiag v u
  /-- `bDiag` is nondegenerate. -/
  bDiag_nondegenerate : IsNondegeneratePairing bDiag
  /-- `symmDiag² = I`. -/
  symmDiag_sq : symmDiag.comp symmDiag = LinearMap.id
  /-- `swapDiag² = I`. -/
  swapDiag_sq : swapDiag.comp swapDiag = LinearMap.id
  /-- `{symmDiag, swapDiag} = 0`. -/
  symmDiag_swapDiag_anticomm : symmDiag.comp swapDiag = -(swapDiag.comp symmDiag)
  /-- `symmDiag` preserves `bDiag`. -/
  bDiag_symmDiag_invariant : ∀ u v : V, bDiag (symmDiag u) (symmDiag v) = bDiag u v
  /-- `swapDiag` anti-preserves `bDiag`. -/
  bDiag_swapDiag_anti : ∀ u v : V, bDiag (swapDiag u) (swapDiag v) = -bDiag u v

namespace DiagonalKreinData

section DiagonalLaws

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (D : DiagonalKreinData V)

/-- Induced Hilbert form `bDiag(u, symmDiag v)` on a diagonal Krein space. -/
def gDiag : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ
    (fun u v => D.bDiag u (D.symmDiag v))
    (fun u₁ u₂ v => by simp [map_add])
    (fun c u v => by simp [map_smul])
    (fun u v₁ v₂ => by simp [map_add])
    (fun c u v => by simp [map_smul])

@[simp] theorem gDiag_apply (u v : V) : D.gDiag u v = D.bDiag u (D.symmDiag v) := rfl

end DiagonalLaws

end DiagonalKreinData

/-- Bilinear-form wrapper for `splitKreinForm` on `DoubledSpace E`. -/
def splitKreinBilin (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    LinearMap.BilinForm ℝ (DoubledSpace E) :=
  LinearMap.mk₂ ℝ
    (fun u v => splitKreinForm u v)
    (fun u₁ u₂ v => by
      simp [splitKreinForm, WithLp.add_fst, WithLp.add_snd, inner_add_left]
      abel)
    (fun c u v => by
      simp [splitKreinForm, WithLp.smul_fst, WithLp.smul_snd, real_inner_smul_left, mul_sub])
    (fun u v₁ v₂ => by
      simp [splitKreinForm, WithLp.add_fst, WithLp.add_snd, inner_add_right]
      abel)
    (fun c u v => by
      simp [splitKreinForm, WithLp.smul_fst, WithLp.smul_snd, real_inner_smul_right, mul_sub])

@[simp] theorem splitKreinBilin_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u v : DoubledSpace E) :
    splitKreinBilin E u v = splitKreinForm u v := rfl

/-- Canonical `DiagonalKreinData` on `DoubledSpace E` for `splitKreinForm`. -/
def doubledDiagonalKreinData (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DiagonalKreinData (DoubledSpace E) where
  bDiag := splitKreinBilin E
  symmDiag := (etaSplit (E := E)).toLinearMap
  swapDiag := (etaChiral (E := E)).toLinearMap
  bDiag_symm := fun u v => by
    simp [splitKreinBilin, splitKreinForm, real_inner_comm]
  bDiag_nondegenerate := by
    intro u v huv
    apply ext_inner_right ℝ
    intro w
    have hw := congrArg (fun f : Module.Dual ℝ (DoubledSpace E) => f (etaSplit (E := E) w)) huv
    change splitKreinForm u (etaSplit (E := E) w) =
      splitKreinForm v (etaSplit (E := E) w) at hw
    have hsplit (a : DoubledSpace E) :
        splitKreinForm a (etaSplit (E := E) w) = inner ℝ a w := by
      simp [splitKreinForm, etaSplit, spectral_epsilon, WithLp.prod_inner_apply]
    rwa [hsplit u, hsplit v] at hw
  symmDiag_sq := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [etaSplit, spectral_epsilon]
  swapDiag_sq := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [etaChiral, modular_j]
  symmDiag_swapDiag_anticomm := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [etaSplit, etaChiral, spectral_epsilon, modular_j]
  bDiag_symmDiag_invariant := fun u v => by
    simp [splitKreinBilin, splitKreinForm, etaSplit, spectral_epsilon]
  bDiag_swapDiag_anti := fun u v => by
    simp [splitKreinBilin, splitKreinForm, etaChiral, modular_j]

/-- Canonical diagonal Krein structure induced on `V` by a `NullPolarizationData V` via
`bDiag(u, v) = b(u, J (Γ v))`, `symmDiag = Γ`, `swapDiag = J`. -/
def NullPolarizationData.toDiagonalKreinData {V : Type u} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V) : DiagonalKreinData V where
  bDiag := LinearMap.mk₂ ℝ
    (fun u v => P.b u (P.J (P.Γ v)))
    (fun u₁ u₂ v => by simp [map_add])
    (fun c u v => by simp [map_smul])
    (fun u v₁ v₂ => by simp [map_add])
    (fun c u v => by simp [map_smul])
  symmDiag := P.Γ
  swapDiag := P.J
  bDiag_symm := fun u v => by
    simp only [LinearMap.mk₂_apply]
    calc
      P.b u (P.J (P.Γ v)) = P.b (P.J (P.Γ v)) u := P.b_symm u (P.J (P.Γ v))
      _ = P.b (P.J (P.J (P.Γ v))) (P.J u) := (P.b_J_invariant (P.J (P.Γ v)) u).symm
      _ = P.b (P.Γ v) (P.J u) := by rw [P.J_apply_J]
      _ = -P.b (P.Γ (P.Γ v)) (P.Γ (P.J u)) := by
            have h := P.b_Γ_anti (P.Γ v) (P.J u)
            rw [P.Γ_apply_Γ] at h
            have hneg := congrArg Neg.neg h
            simpa using hneg.symm
      _ = -P.b v (-P.J (P.Γ u)) := by rw [P.Γ_apply_Γ, P.Γ_J_apply]
      _ = P.b v (P.J (P.Γ u)) := by simp
  bDiag_nondegenerate := fun u v huv => by
    apply P.b_nondegenerate
    ext w
    have hw := congrArg (fun f : Module.Dual ℝ V => f (P.Γ (P.J w))) huv
    change P.b u (P.J (P.Γ (P.Γ (P.J w)))) = P.b v (P.J (P.Γ (P.Γ (P.J w)))) at hw
    change P.b u w = P.b v w
    simpa [P.Γ_apply_Γ, P.J_apply_J] using hw
  symmDiag_sq := P.Γ_sq
  swapDiag_sq := P.J_sq
  symmDiag_swapDiag_anticomm := P.Γ_J_anticomm
  bDiag_symmDiag_invariant := fun u v => by
    simp only [LinearMap.mk₂_apply, P.Γ_apply_Γ]
    have h2 : P.b (P.Γ u) (P.J v) = -P.b u (P.Γ (P.J v)) := by
      have h' := P.b_Γ_anti (P.Γ u) (P.J v)
      rw [P.Γ_apply_Γ] at h'
      have hneg := congrArg Neg.neg h'
      simpa using hneg.symm
    rw [h2, P.Γ_J_apply, map_neg, neg_neg]
  bDiag_swapDiag_anti := fun u v => by
    simp only [LinearMap.mk₂_apply]
    rw [P.Γ_J_apply, map_neg, P.J_apply_J]
    have h := P.b_J_invariant u (P.Γ v)
    have h2 : P.b (P.J u) (-P.Γ v) = -P.b (P.J u) (P.Γ v) := map_neg _ _
    rw [h2]
    have h3 : P.b (P.J u) (P.Γ v) = P.b u (P.J (P.Γ v)) := by
      calc
        P.b (P.J u) (P.Γ v) = P.b (P.J (P.J u)) (P.J (P.Γ v)) :=
          (P.b_J_invariant (P.J u) (P.Γ v)).symm
        _ = P.b u (P.J (P.Γ v)) := by rw [P.J_apply_J]
    rw [h3]

/-- Explicit Hadamard coordinate-change equivalence connecting a diagonal Krein datum `D` to a
null-polarization datum `P`. -/
structure HadamardKreinPolarizationEquiv
    {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (D : DiagonalKreinData V) (P : NullPolarizationData W) : Type (max u v) where
  /-- Linear coordinate change `V ≃ₗ[ℝ] W`. -/
  toLinearEquiv : V ≃ₗ[ℝ] W
  /-- Preservation of the indefinite Krein form. -/
  map_form : ∀ u v : V, P.b (toLinearEquiv u) (toLinearEquiv v) = D.bDiag u v
  /-- Intertwining of the diagonal symmetry with `J`. -/
  intertwines_symm : ∀ u : V, toLinearEquiv (D.symmDiag u) = P.J (toLinearEquiv u)
  /-- Intertwining of the diagonal swap with `Γ`. -/
  intertwines_swap : ∀ u : V, toLinearEquiv (D.swapDiag u) = P.Γ (toLinearEquiv u)

namespace HadamardKreinPolarizationEquiv

theorem map_gJ {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {D : DiagonalKreinData V} {P : NullPolarizationData W}
    (e : HadamardKreinPolarizationEquiv D P) (u v : V) :
    P.gJ (e.toLinearEquiv u) (e.toLinearEquiv v) = D.gDiag u v := by
  simp only [NullPolarizationData.gJ_apply, DiagonalKreinData.gDiag_apply]
  rw [← e.intertwines_symm v, e.map_form]

theorem symm_map_form {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {D : DiagonalKreinData V} {P : NullPolarizationData W}
    (e : HadamardKreinPolarizationEquiv D P) (x y : W) :
    D.bDiag (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y) = P.b x y := by
  have h := e.map_form (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y)
  simpa using h.symm

theorem positivity_transfer {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {D : DiagonalKreinData V} {P : NullPolarizationData W}
    (e : HadamardKreinPolarizationEquiv D P) :
    PositiveHilbertCompatibility P ↔ (∀ u : V, u ≠ 0 → 0 < D.bDiag u (D.symmDiag u)) := by
  constructor
  · intro hpos u hu
    have hne : e.toLinearEquiv u ≠ 0 := by
      intro h0
      exact hu (e.toLinearEquiv.injective (by simpa using h0))
    have hval : D.bDiag u (D.symmDiag u) = P.gJ (e.toLinearEquiv u) (e.toLinearEquiv u) :=
      (e.map_gJ u u).symm
    rw [hval]
    exact hpos.pos_def (e.toLinearEquiv u) hne
  · intro hdiag
    refine ⟨fun x hx => ?_⟩
    have hne : e.toLinearEquiv.symm x ≠ 0 := by
      intro h0
      exact hx (e.toLinearEquiv.symm.injective (by simpa using h0))
    have hval : P.b x (P.J x) = D.bDiag (e.toLinearEquiv.symm x)
        (D.symmDiag (e.toLinearEquiv.symm x)) := by
      have h := e.map_gJ (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm x)
      simpa using h
    rw [hval]
    exact hdiag (e.toLinearEquiv.symm x) hne

/-- Abstract Hadamard equivalence `W = (1 / √2) • (Γ + J)` on any `NullPolarizationData V`. -/
def abstractHadamardEquiv {V : Type u} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V) :
    HadamardKreinPolarizationEquiv P.toDiagonalKreinData P := by
  let W : Module.End ℝ V := (1 / Real.sqrt 2 : ℝ) • (P.Γ + P.J)
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hcoef : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = 1 / 2 := by
    field_simp [hs0]
    rw [hs]
  have hW_apply : ∀ u : V, W u = (1 / Real.sqrt 2 : ℝ) • (P.Γ u + P.J u) := by
    intro u
    simp [W]
  have hW_sq : ∀ u : V, W (W u) = u := by
    intro u
    rw [hW_apply u, map_smul, map_add, hW_apply (P.Γ u), hW_apply (P.J u)]
    simp only [P.Γ_apply_Γ, P.J_apply_J, P.Γ_J_apply, smul_add, smul_smul, hcoef]
    module
  have hW_Γ : ∀ u : V, W (P.Γ u) = P.J (W u) := by
    intro u
    simp only [hW_apply, map_smul, map_add, P.Γ_apply_Γ, P.J_apply_J, P.J_Γ_apply]
    congr 1
    abel
  have hW_J : ∀ u : V, W (P.J u) = P.Γ (W u) := by
    intro u
    simp only [hW_apply, map_smul, map_add, P.Γ_apply_Γ, P.J_apply_J, P.Γ_J_apply]
    congr 1
    abel
  refine
    { toLinearEquiv :=
        { toFun := W
          map_add' := W.map_add
          map_smul' := W.map_smul
          invFun := W
          left_inv := hW_sq
          right_inv := hW_sq }
      map_form := ?_
      intertwines_symm := hW_Γ
      intertwines_swap := hW_J }
  intro u v
  change P.b (W u) (W v) = P.b u (P.J (P.Γ v))
  rw [hW_apply u, hW_apply v]
  have hsmul1 : P.b ((1 / Real.sqrt 2 : ℝ) • (P.Γ u + P.J u))
      ((1 / Real.sqrt 2 : ℝ) • (P.Γ v + P.J v)) =
      (1 / 2 : ℝ) * P.b (P.Γ u + P.J u) (P.Γ v + P.J v) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, hcoef]
  rw [hsmul1]
  have hexp : P.b (P.Γ u + P.J u) (P.Γ v + P.J v) =
      P.b (P.Γ u) (P.Γ v) + P.b (P.Γ u) (P.J v) +
        P.b (P.J u) (P.Γ v) + P.b (P.J u) (P.J v) := by
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [hexp, P.b_Γ_anti u v, P.b_J_invariant u v]
  have h1 : P.b (P.Γ u) (P.J v) = P.b u (P.J (P.Γ v)) := by
    have ha := P.b_Γ_anti (P.Γ u) (P.J v)
    rw [P.Γ_apply_Γ, P.Γ_J_apply, map_neg] at ha
    have ha' : -P.b (P.Γ u) (P.J v) = -P.b u (P.J (P.Γ v)) := ha.symm
    exact neg_inj.mp ha'
  have h2 : P.b (P.J u) (P.Γ v) = P.b u (P.J (P.Γ v)) := by
    calc
      P.b (P.J u) (P.Γ v) = P.b (P.J (P.J u)) (P.J (P.Γ v)) :=
        (P.b_J_invariant (P.J u) (P.Γ v)).symm
      _ = P.b u (P.J (P.Γ v)) := by rw [P.J_apply_J]
  rw [h1, h2]
  have hscal : (1 / 2 : ℝ) * (-P.b u v + P.b u (P.J (P.Γ v)) + P.b u (P.J (P.Γ v)) + P.b u v) =
      P.b u (P.J (P.Γ v)) := by ring
  exact hscal

/-- Concrete Hadamard equivalence on `DoubledSpace E` realizing `hadamardNormalized` as a
`HadamardKreinPolarizationEquiv` from `splitKreinForm` to `chiralKreinForm`. -/
def doubledHadamardKreinPolarizationEquiv (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    HadamardKreinPolarizationEquiv (doubledDiagonalKreinData E)
      (NullPolarizationData.doubledNullPolarization E) where
  toLinearEquiv :=
    { toFun := hadamardNormalized
      invFun := hadamardNormalized
      left_inv := hadamardNormalized_involution
      right_inv := hadamardNormalized_involution
      map_add' := fun u v => by
        apply DoubledSpace.ext <;>
          simp [hadamardNormalized, hadamard, WithLp.add_fst, WithLp.add_snd, smul_add] <;>
          module
      map_smul' := fun c u => by
        apply DoubledSpace.ext <;>
          simp [hadamardNormalized, hadamard, WithLp.smul_fst, WithLp.smul_snd,
            smul_add, smul_sub, smul_comm c] }
  map_form := fun u v => by
    change chiralKreinForm (hadamardNormalized u) (hadamardNormalized v) = splitKreinForm u v
    have h := splitKreinForm_hadamardNormalized (hadamardNormalized u) (hadamardNormalized v)
    simpa [hadamardNormalized_involution] using h.symm
  intertwines_symm := fun u => by
    apply DoubledSpace.ext <;>
      simp [doubledDiagonalKreinData, NullPolarizationData.doubledNullPolarization,
        hadamardNormalized, hadamard, etaSplit, etaChiral, spectral_epsilon, modular_j,
        smul_add, sub_eq_add_neg]
  intertwines_swap := fun u => by
    apply DoubledSpace.ext
    · simp [doubledDiagonalKreinData, NullPolarizationData.doubledNullPolarization,
        hadamardNormalized, hadamard, gamma5, etaChiral, spectral_epsilon, modular_j,
        smul_add, sub_eq_add_neg, add_comm]
    · simp [doubledDiagonalKreinData, NullPolarizationData.doubledNullPolarization,
        hadamardNormalized, hadamard, gamma5, etaChiral, spectral_epsilon, modular_j,
        smul_add, sub_eq_add_neg]

@[simp] theorem doubledHadamard_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : DoubledSpace E) :
    (doubledHadamardKreinPolarizationEquiv E).toLinearEquiv u = hadamardNormalized u := rfl

@[simp] theorem doubledHadamard_symm_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : DoubledSpace E) :
    (doubledHadamardKreinPolarizationEquiv E).toLinearEquiv.symm u = hadamardNormalized u := rfl

end HadamardKreinPolarizationEquiv

/-! ## 4. Explicit Observables and Dynamics Hypotheses -/

/-- Explicit observables and coercivity/mass-gap structure over a positively compatible null
polarization `(P, hpos)`.  All positivity and spectral consequences are proved from these
hypotheses without assuming calibrated readouts. -/
structure ChiralObservablesDynamics
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V)
    (hpos : PositiveHilbertCompatibility P) : Type u where
  /-- Energy / mass-squared observable `H`. -/
  H : Module.End ℝ V
  /-- `H` is self-adjoint with respect to the positive Hilbert form `g_J`. -/
  H_selfAdjoint_gJ : ∀ u v : V, P.gJ (H u) v = P.gJ u (H v)
  /-- `H` preserves the chiral grading (`[H, Γ] = 0`). -/
  H_even : H.comp P.Γ = P.Γ.comp H
  /-- Mass / spectral gap `m₀ > 0`. -/
  m₀ : ℝ
  /-- Positivity of the mass gap `m₀`. -/
  m₀_pos : 0 < m₀
  /-- Coercivity bound `m₀ * g_J(u, u) ≤ g_J(u, H u)`. -/
  coercive : ∀ u : V, m₀ * P.gJ u u ≤ P.gJ u (H u)

namespace ChiralObservablesDynamics

section DynamicsTheorems

variable {V : Type u} [AddCommGroup V] [Module ℝ V]
  {P : NullPolarizationData V} {hpos : PositiveHilbertCompatibility P}
  (dyn : ChiralObservablesDynamics P hpos)

theorem energy_pos {u : V} (hu : u ≠ 0) : 0 < P.gJ u (dyn.H u) := by
  have hm : 0 < dyn.m₀ * P.gJ u u := mul_pos dyn.m₀_pos (hpos.gJ_pos hu)
  exact lt_of_lt_of_le hm (dyn.coercive u)

theorem eigenvalue_ge_gap {μ : ℝ} {u : V} (hu : u ≠ 0) (heig : dyn.H u = μ • u) :
    dyn.m₀ ≤ μ := by
  have hcoerc := dyn.coercive u
  rw [heig, map_smul, smul_eq_mul] at hcoerc
  have huu : 0 < P.gJ u u := hpos.gJ_pos hu
  have hdiff : 0 ≤ (μ - dyn.m₀) * P.gJ u u := by
    have hscal : (μ - dyn.m₀) * P.gJ u u = μ * P.gJ u u - dyn.m₀ * P.gJ u u := by ring
    rw [hscal]
    exact sub_nonneg.mpr hcoerc
  have hmul := nonneg_of_mul_nonneg_left hdiff huu
  exact sub_nonneg.mp hmul

theorem eigenvalue_pos {μ : ℝ} {u : V} (hu : u ≠ 0) (heig : dyn.H u = μ • u) : 0 < μ :=
  lt_of_lt_of_le dyn.m₀_pos (dyn.eigenvalue_ge_gap hu heig)

theorem ker_eq_bot : LinearMap.ker dyn.H = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  by_contra hne
  have hposE := dyn.energy_pos hne
  rw [hu, map_zero] at hposE
  exact lt_irrefl (0 : ℝ) hposE

theorem eigenvectors_orthogonal_gJ {μ₁ μ₂ : ℝ} {u v : V}
    (hu : dyn.H u = μ₁ • u) (hv : dyn.H v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    P.gJ u v = 0 := by
  have hsa := dyn.H_selfAdjoint_gJ u v
  rw [hu, hv, map_smul, map_smul, smul_eq_mul] at hsa
  have hzero : (μ₁ - μ₂) * P.gJ u v = 0 := by
    have hscal : (μ₁ - μ₂) * P.gJ u v = μ₁ * P.gJ u v - μ₂ * P.gJ u v := by ring
    rw [hscal]
    have hl : (μ₁ • P.gJ u) v = μ₁ * P.gJ u v := by
      simp [LinearMap.smul_apply, smul_eq_mul]
    rw [← hl, hsa, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

theorem maps_nullPlus {u : V} (hu : u ∈ P.nullPlusSubmodule) :
    dyn.H u ∈ P.nullPlusSubmodule := by
  rw [P.mem_nullPlusSubmodule_iff] at hu ⊢
  have hcomm := congrArg (fun T : Module.End ℝ V => T u) dyn.H_even
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm, hu]

theorem maps_nullMinus {u : V} (hu : u ∈ P.nullMinusSubmodule) :
    dyn.H u ∈ P.nullMinusSubmodule := by
  rw [P.mem_nullMinusSubmodule_iff] at hu ⊢
  have hcomm := congrArg (fun T : Module.End ℝ V => T u) dyn.H_even
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm, hu, map_neg]

theorem b_expectation_nullPlus_eq_zero {u : V} (hu : u ∈ P.nullPlusSubmodule) :
    P.b u (dyn.H u) = 0 :=
  P.nullPlus_isotropic hu (dyn.maps_nullPlus hu)

theorem b_expectation_nullMinus_eq_zero {u : V} (hu : u ∈ P.nullMinusSubmodule) :
    P.b u (dyn.H u) = 0 :=
  P.nullMinus_isotropic hu (dyn.maps_nullMinus hu)

theorem chiral_energy_split (u : V) :
    P.gJ u (dyn.H u) =
      P.gJ (P.projPlus u) (dyn.H (P.projPlus u)) +
      P.gJ (P.projMinus u) (dyn.H (P.projMinus u)) := by
  have hu : P.projPlus u + P.projMinus u = u := P.projPlus_add_projMinus_apply u
  have h1 : P.projPlus u ∈ P.nullPlusSubmodule := ⟨u, rfl⟩
  have h2 : P.projMinus u ∈ P.nullMinusSubmodule := ⟨u, rfl⟩
  have hcross1 : P.gJ (P.projPlus u) (dyn.H (P.projMinus u)) = 0 :=
    P.gJ_nullPlus_orthogonal_nullMinus h1 (dyn.maps_nullMinus h2)
  have hcross2 : P.gJ (P.projMinus u) (dyn.H (P.projPlus u)) = 0 := by
    rw [P.gJ_symm]
    exact P.gJ_nullPlus_orthogonal_nullMinus (dyn.maps_nullPlus h1) h2
  calc
    P.gJ u (dyn.H u)
        = P.gJ (P.projPlus u + P.projMinus u) (dyn.H (P.projPlus u + P.projMinus u)) := by
            rw [hu]
    _ = P.gJ (P.projPlus u) (dyn.H (P.projPlus u)) +
          P.gJ (P.projPlus u) (dyn.H (P.projMinus u)) +
          (P.gJ (P.projMinus u) (dyn.H (P.projPlus u)) +
          P.gJ (P.projMinus u) (dyn.H (P.projMinus u))) := by
            simp only [map_add, LinearMap.add_apply]
            abel
    _ = P.gJ (P.projPlus u) (dyn.H (P.projPlus u)) +
          P.gJ (P.projMinus u) (dyn.H (P.projMinus u)) := by
            rw [hcross1, hcross2, add_zero, zero_add]

theorem b_expectation_sign_of_J_comm (hJ : dyn.H.comp P.J = P.J.comp dyn.H) :
    (∀ {u : V}, u ≠ 0 → P.J u = u → 0 < P.b u (dyn.H u)) ∧
    (∀ {u : V}, u ≠ 0 → P.J u = -u → P.b u (dyn.H u) < 0) := by
  have _ := hJ
  constructor
  · intro u hu hJu
    have hval : P.b u (dyn.H u) = P.gJ u (dyn.H u) := by
      calc
        P.b u (dyn.H u) = P.gJ u (P.J (dyn.H u)) := P.b_eq_gJ_J u (dyn.H u)
        _ = P.gJ u (dyn.H (P.J u)) := by
          have h := congrArg (fun T : Module.End ℝ V => T u) hJ
          simp only [LinearMap.comp_apply] at h
          rw [← h]
        _ = P.gJ u (dyn.H u) := by rw [hJu]
    rw [hval]
    exact dyn.energy_pos hu
  · intro u hu hJu
    have hval : P.b u (dyn.H u) = -P.gJ u (dyn.H u) := by
      calc
        P.b u (dyn.H u) = P.gJ u (P.J (dyn.H u)) := P.b_eq_gJ_J u (dyn.H u)
        _ = P.gJ u (dyn.H (P.J u)) := by
          have h := congrArg (fun T : Module.End ℝ V => T u) hJ
          simp only [LinearMap.comp_apply] at h
          rw [← h]
        _ = P.gJ u (dyn.H (-u)) := by rw [hJu]
        _ = -P.gJ u (dyn.H u) := by simp [map_neg]
    rw [hval]
    exact neg_lt_zero.mpr (dyn.energy_pos hu)

end DynamicsTheorems

/-- Construct `ChiralObservablesDynamics` from an odd `g_J`-symmetric generator `D`, setting
`H = D² + m₀² I`. -/
def ofOddGenerator
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} (hpos : PositiveHilbertCompatibility P)
    (D : Module.End ℝ V)
    (hD_odd : D.comp P.Γ = -(P.Γ.comp D))
    (hD_symm : ∀ u v : V, P.gJ (D u) v = P.gJ u (D v))
    (m₀ : ℝ) (hm₀ : 0 < m₀) :
    ChiralObservablesDynamics P hpos where
  H := D.comp D + (m₀ ^ 2) • LinearMap.id
  H_selfAdjoint_gJ := fun u v => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul, smul_eq_mul]
    have h1 : P.gJ (D (D u)) v = P.gJ u (D (D v)) := by
      calc
        P.gJ (D (D u)) v = P.gJ (D u) (D v) := hD_symm (D u) v
        _ = P.gJ u (D (D v)) := hD_symm u (D v)
    rw [h1]
  H_even := by
    ext u
    have hDΓ : ∀ x : V, D (P.Γ x) = -P.Γ (D x) := fun x => by
      simpa [LinearMap.comp_apply] using congrArg (fun T : Module.End ℝ V => T x) hD_odd
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul, hDΓ, map_neg, neg_neg]
  m₀ := m₀ ^ 2
  m₀_pos := sq_pos_of_pos hm₀
  coercive := fun u => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul, smul_eq_mul]
    rw [← hD_symm u (D u)]
    have hnonneg : 0 ≤ P.gJ (D u) (D u) := hpos.gJ_nonneg (D u)
    linarith

/-- Construct `ChiralObservablesDynamics` from an odd `g_J`-skew-symmetric generator `D`, setting
`H = -D² + m₀² I`. -/
def ofOddSkewGenerator
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} (hpos : PositiveHilbertCompatibility P)
    (D : Module.End ℝ V)
    (hD_odd : D.comp P.Γ = -(P.Γ.comp D))
    (hD_skew : ∀ u v : V, P.gJ (D u) v = -P.gJ u (D v))
    (m₀ : ℝ) (hm₀ : 0 < m₀) :
    ChiralObservablesDynamics P hpos where
  H := -(D.comp D) + (m₀ ^ 2) • LinearMap.id
  H_selfAdjoint_gJ := fun u v => by
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_add, map_neg, map_smul, smul_eq_mul]
    have h1 : P.gJ (D (D u)) v = P.gJ u (D (D v)) := by
      calc
        P.gJ (D (D u)) v = -P.gJ (D u) (D v) := hD_skew (D u) v
        _ = -(-P.gJ u (D (D v))) := by rw [hD_skew u (D v)]
        _ = P.gJ u (D (D v)) := neg_neg _
    rw [h1]
  H_even := by
    ext u
    have hDΓ : ∀ x : V, D (P.Γ x) = -P.Γ (D x) := fun x => by
      simpa [LinearMap.comp_apply] using congrArg (fun T : Module.End ℝ V => T x) hD_odd
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_add, map_neg, map_smul, hDΓ, neg_neg]
  m₀ := m₀ ^ 2
  m₀_pos := sq_pos_of_pos hm₀
  coercive := fun u => by
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_add, map_neg, map_smul, smul_eq_mul]
    have hD : -P.gJ u (D (D u)) = P.gJ (D u) (D u) := (hD_skew u (D u)).symm
    rw [hD]
    have hnonneg : 0 ≤ P.gJ (D u) (D u) := hpos.gJ_nonneg (D u)
    linarith

end ChiralObservablesDynamics

/-! ## 5. R5 Separation: Nullcone Vectors Outside Chiral Subspaces (`dim E > 1`) -/

/-- Any orthogonal nonzero pair `e₁, e₂ : E` yields a nonzero null vector `to_doubled e₁ e₂`
that lies outside both chiral subspaces `im(leftChiralProjector)` and `im(rightChiralProjector)`.
-/
theorem orthogonal_pair_nullcone_not_in_chiral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {e₁ e₂ : E} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) (horth : inner ℝ e₁ e₂ = 0) :
    let u : DoubledSpace E := to_doubled e₁ e₂
    u ≠ 0 ∧
      chiralKreinForm (E := E) u u = 0 ∧
      leftChiralProjector (E := E) u ≠ u ∧
      rightChiralProjector (E := E) u ≠ u := by
  intro u
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have hfst : e₁ = 0 := by simpa [u] using congrArg WithLp.fst h0
    exact he₁ hfst
  · rw [chiralKreinForm_to_doubled, horth, zero_add, real_inner_comm, horth]
  · rw [leftChiralProjector_to_doubled]
    intro hfix
    have hsnd : (0 : E) = e₂ := by simpa [u] using congrArg WithLp.snd hfix
    exact he₂ hsnd.symm
  · rw [rightChiralProjector_to_doubled]
    intro hfix
    have hfst : (0 : E) = e₁ := by simpa [u] using congrArg WithLp.fst hfix
    exact he₁ hfst.symm

/-- Whenever `1 < Module.finrank ℝ E`, the nullcone of `chiralKreinForm` strictly contains nonzero
vectors outside both chiral projections `leftChiralProjector` and `rightChiralProjector`. -/
theorem dim_gt_one_nullcone_not_in_chiral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hdim : 1 < Module.finrank ℝ E) :
    ∃ u : DoubledSpace E,
      u ≠ 0 ∧
      chiralKreinForm (E := E) u u = 0 ∧
      leftChiralProjector (E := E) u ≠ u ∧
      rightChiralProjector (E := E) u ≠ u := by
  have hpos : 0 < Module.finrank ℝ E := lt_trans Nat.zero_lt_one hdim
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos hpos
  let b := stdOrthonormalBasis ℝ E
  let e₁ : E := b ⟨0, hpos⟩
  let e₂ : E := b ⟨1, hdim⟩
  have he₁ : e₁ ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [b.orthonormal.1 ⟨0, hpos⟩]; exact one_ne_zero)
  have he₂ : e₂ ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [b.orthonormal.1 ⟨1, hdim⟩]; exact one_ne_zero)
  have horth : inner ℝ e₁ e₂ = 0 :=
    b.orthonormal.2 (by simp [Fin.ext_iff])
  exact ⟨to_doubled e₁ e₂, orthogonal_pair_nullcone_not_in_chiral he₁ he₂ horth⟩

/-! ## 6. R5 Separation: Sign-Flip `J ↦ -J` Destroys Positive Compatibility -/

/-- Abstract `J ↦ -J` sign-flip theorem: negating `J` preserves all `NullPolarizationData`
axioms while flipping `g_{-J}(u, v) = -g_J(u, v)` and violating `PositiveHilbertCompatibility` on
any nontrivial space. -/
theorem sign_flip_neg_mirror
    {V : Type u} [AddCommGroup V] [Module ℝ V] [Nontrivial V]
    (P : NullPolarizationData V) (hpos : PositiveHilbertCompatibility P) :
    (P.negMirror.Γ = P.Γ ∧ P.negMirror.J = -P.J) ∧
      (∀ u v : V, P.negMirror.gJ u v = -P.gJ u v) ∧
      ¬ PositiveHilbertCompatibility P.negMirror :=
  ⟨⟨rfl, rfl⟩, P.negMirror_gJ, hpos.not_negMirror⟩

/-- Concrete `RealDoubledChiralKrein` sign-flip witness: `-etaChiral` satisfies all involutive,
anticommutation, and `chiralKreinForm`-invariance axioms, reverses `chiralHilbertForm`, and
attains strictly negative diagonal values on nonzero vectors. -/
theorem realDoubled_sign_flip_neg_mirror
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E] :
    let negEta : DoubledSpace E →L[ℝ] DoubledSpace E := -(etaChiral (E := E))
    (negEta.comp negEta = ContinuousLinearMap.id ℝ (DoubledSpace E)) ∧
      ((gamma5 (E := E)).comp negEta = -(negEta.comp (gamma5 (E := E)))) ∧
      (∀ u v : DoubledSpace E,
        chiralKreinForm (E := E) (negEta u) (negEta v) = chiralKreinForm (E := E) u v) ∧
      (∀ u v : DoubledSpace E,
        chiralKreinForm (E := E) u (negEta v) = -chiralHilbertForm (E := E) u v) ∧
      (∃ u : DoubledSpace E, u ≠ 0 ∧ chiralKreinForm (E := E) u (negEta u) < 0) := by
  intro negEta
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [negEta, etaChiral, modular_j]
  · apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [negEta, gamma5, etaChiral, spectral_epsilon, modular_j]
  · intro u v
    simp [negEta, chiralKreinForm, etaChiral, modular_j, real_inner_comm, add_comm]
  · intro u v
    change chiralKreinBilin (E := E) u (-etaChiral (E := E) v) = -chiralHilbertForm (E := E) u v
    rw [map_neg]
    rfl
  · obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨to_doubled x 0, ?_, ?_⟩
    · intro h0
      have hfst : x = 0 := by simpa using congrArg WithLp.fst h0
      exact hx hfst
    · have hneg : chiralKreinForm (E := E) (to_doubled x 0) (negEta (to_doubled x 0)) =
          -chiralHilbertForm (E := E) (to_doubled x 0) (to_doubled x 0) := by
        change chiralKreinBilin (E := E) (to_doubled x 0)
            (-etaChiral (E := E) (to_doubled x 0)) =
          -chiralHilbertForm (E := E) (to_doubled x 0) (to_doubled x 0)
        rw [map_neg]
        rfl
      rw [hneg, neg_lt_zero]
      apply chiralHilbertForm_self_pos (E := E)
      intro h0
      have hfst : x = 0 := by simpa using congrArg WithLp.fst h0
      exact hx hfst

/-! ## 7. Concrete Zero-Binder Ground Witnesses (T17 Compliance) -/

section ConcreteWitnesses

/-- Concrete zero-binder `NullPolarizationData` witness on `DoubledSpace ℝ`. -/
def concreteDoubledNullPolarizationReal : NullPolarizationData (DoubledSpace ℝ) :=
  NullPolarizationData.doubledNullPolarization ℝ

/-- Concrete zero-binder `PositiveHilbertCompatibility` witness on `DoubledSpace ℝ`. -/
theorem concreteDoubledPositiveHilbertCompatibilityReal :
    PositiveHilbertCompatibility concreteDoubledNullPolarizationReal :=
  PositiveHilbertCompatibility.doubledPositiveHilbertCompatibility ℝ

/-- Concrete zero-binder `DiagonalKreinData` witness on `DoubledSpace ℝ`. -/
def concreteDoubledDiagonalKreinReal : DiagonalKreinData (DoubledSpace ℝ) :=
  doubledDiagonalKreinData ℝ

/-- Concrete zero-binder `HadamardKreinPolarizationEquiv` witness on `DoubledSpace ℝ`. -/
def concreteHadamardEquivReal :
    HadamardKreinPolarizationEquiv concreteDoubledDiagonalKreinReal
      concreteDoubledNullPolarizationReal :=
  HadamardKreinPolarizationEquiv.doubledHadamardKreinPolarizationEquiv ℝ

/-- Concrete zero-binder `ChiralObservablesDynamics` witness on `DoubledSpace ℝ` generated by
the odd `g_J`-symmetric involution `J`. -/
def concreteChiralObservablesDynamicsReal :
    ChiralObservablesDynamics concreteDoubledNullPolarizationReal
      concreteDoubledPositiveHilbertCompatibilityReal :=
  ChiralObservablesDynamics.ofOddGenerator
    concreteDoubledPositiveHilbertCompatibilityReal
    concreteDoubledNullPolarizationReal.J
    (by
      apply LinearMap.ext
      intro u
      simp [NullPolarizationData.J_Γ_apply])
    (fun u v => by
      simp only [NullPolarizationData.gJ_apply, NullPolarizationData.J_apply_J]
      exact concreteDoubledNullPolarizationReal.b_J_invariant u v)
    1
    one_pos

end ConcreteWitnesses

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization
