/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
import InfoGeometry.Canonical.KahlerAtiyahCartanForms
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.IndexTheory.AtiyahSingerDirac

/-!
# M2-Brane Doubled Clifford Forms, Bockstein Obstructions, and Parity Gluing

This module formalizes the algebraic, homological, and exponential-gluing
structures of Witten (2016) §4 ("Anomaly Inflow and the M2-Brane",
arXiv:1508.04715 / Rev. Mod. Phys. 88, 035001) together with the Dai–Freed
phase gluing laws from §2.2:

1. **Part I — Doubled Clifford ↔ Exterior Forms CAR Isomorphism (Eqs. 4.30–4.35, 4.37)**:
   - General `AlgHom` `doubledCliffordToEnd : CliffordAlgebra ((-Q).prod Q) →ₐ[R] Module.End R (ExteriorAlgebra R V)`
     reusing `KahlerDiracWeitzenbockSynthesis` (`exteriorWedge`, `exteriorContract`,
     `exterior_cartan_homotopy_car`) and `KahlerAtiyahCartanForms` (`cartanCliffordAction`,
     `metricQuadraticForm`).
   - Exact `1/2`-normalized creation/annihilation operators `cliffordCreate` and
     `cliffordAnnihilate` in `CliffordAlgebra ((-Q).prod Q)` satisfying the canonical
     anticommutation relations `{c†_u, c†_v} = 0`, `{c_u, c_v} = 0`, and
     `{c†_u, c_v} = g(u, v) • 1` (Eq. 4.31), mapping to `exteriorWedge R v` and
     `exteriorContract (g v)`. We also prove the `1 / Real.sqrt 2` scaling corollary over `ℝ`
     clarifying the factor-of-2 convention between Eq. (4.30) and Eqs. (4.31)–(4.33).
   - Exterior parity grading operator `exteriorGradingOp = (-1)^deg` (Eq. 4.35), its square
     `= 1`, anticommutation with wedge and contraction, spectral `λ ↔ -λ` symmetry
     (`eigenspaceEquivOfAnticomm`), and 9th generator extension `clifford9ToEnd`.
   - 4D real chirality twist `wittenRealChiralityTwist : CliffordAlgebra (Q.prod Q) ≃ₐ[R] CliffordAlgebra ((-Q).prod Q)`
     via `γ = γ₁γ₂γ₃γ₄` (Eq. 4.33), `Γ = γγ̃ ↦ (-1)^deg` (Eq. 4.35), complexified twist
     `wittenComplexTwist` (Eq. 4.32), and the full finite-dimensional orthonormal-frame
     algebra isomorphism `doubledCliffordEquivEnd : CliffordAlgebra ((-Q).prod Q) ≃ₐ[𝕜] Module.End 𝕜 (ExteriorAlgebra 𝕜 V)`.
   - 11D Pauli doubling (`Matrix (Fin 2) (Fin 2) ℂ`, Eq. 4.37) and closed `T16`
     non-commutativity witnesses for all non-commutative operator/matrix carriers.

2. **Part II — Bockstein Exact-Sequence Obstructions (Eqs. 4.10–4.19)**:
   - Exactness of `0 → ℤ →[×2] ℤ → ZMod 2 → 0` (`bocksteinCoeffShortComplex`).
   - General Bockstein connecting homomorphism `bocksteinHom` on `CochainComplex AddCommGrpCat ℕ`
     for any 2-torsion-free integer or twisted-integer cochain complex `C_int`, proving
     `2 • W_3 = 0` (`Spin^c` at `k = 2`), `2 • Wtilde_5 = 0` (`mc`-structure at `k = 4`),
     and integral liftability iff the Bockstein image vanishes.
   - Shifted quantization period phase identity (Eqs. 4.13–4.16) and a concrete non-zero
     Bockstein witness `rp8TwistedCochainComplex` (`H^4 = 0`, `H^5 ≅ ZMod 2`, `β ≠ 0`).

3. **Part III — Abstract `η`-Gluing & `η = 2χ mod 4 → exp(-iπη/2) = (-1)^χ` (Eqs. 2.7–2.8, 4.21–4.40)**:
   - `daiFreedPhase η = Complex.exp (-Complex.I * Real.pi * η / 2)` homomorphism, flip,
     and mod-4 periodicity laws, plus `daiFreedPhase_eq_neg_one_pow_of_two_mul_add_four_mul`.
   - Betti-number derivation of `η = 2χ mod 4` (both untwisted and `α`-twisted Hodge duality).
   - M2-brane measure consistency equivalence (Eqs. 4.21–4.23) and constructive
     `PinPlusEtaGluingSystem` with cobordism propagation and a closed `T17` inhabitant.

## Scope & Mathlib Frontier
Analytical APS spectral `η`-invariants of Dirac operators on Riemannian manifolds,
analytical Dai–Freed elliptic gluing, smooth `Pin⁺` cobordism `Ω_4^{Pin⁺} ≅ ZMod 16`,
and topological twisted sheaf cohomology `H^*(Y; ℤ̃)` on smooth 11-manifolds are
long-term Mathlib frontiers beyond this algebraic, homological, and exponential formalization.
-/

noncomputable section

namespace InfoGeometry.Physics.M2BraneCliffordFormsAndMC

open InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
open InfoGeometry.Canonical.KahlerAtiyahCartanForms
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.IndexTheory.AtiyahSingerDirac

/-!
## Part I: Doubled Clifford ↔ Exterior Forms CAR Isomorphism (Eqs. 4.30–4.35, 4.37)
-/

section DoubledCliffordGeneral

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Negative Cartan action `c_-(v) = e_v - i_{g(v)}` on `ExteriorAlgebra R V`. -/
def negCartanAction (g : LinearMap.BilinForm R V) (v : V) :
    Module.End R (ExteriorAlgebra R V) :=
  exteriorWedge R v - exteriorContract (g v)

/-- Positive Cartan action `c_+(v) = e_v + i_{g(v)}` on `ExteriorAlgebra R V`. -/
def posCartanAction (g : LinearMap.BilinForm R V) (v : V) :
    Module.End R (ExteriorAlgebra R V) :=
  exteriorWedge R v + exteriorContract (g v)

lemma posCartanAction_eq_chevalleyAction (g : LinearMap.BilinForm R V) (v : V) :
    posCartanAction g v = chevalleyAction v (g v) := rfl

lemma posCartanAction_eq_cartanCliffordAction {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : LinearMap.BilinForm ℝ W) (v : W) :
    posCartanAction g v = cartanCliffordAction g v := rfl

/-- Linear map `v ↦ negCartanAction g v`. -/
def negCartanActionMap (g : LinearMap.BilinForm R V) :
    V →ₗ[R] Module.End R (ExteriorAlgebra R V) where
  toFun := negCartanAction g
  map_add' u v := by
    apply LinearMap.ext
    intro ω
    change ExteriorAlgebra.ι R (u + v) * ω - CliffordAlgebra.contractLeft (g (u + v)) ω =
      (ExteriorAlgebra.ι R u * ω - CliffordAlgebra.contractLeft (g u) ω) +
        (ExteriorAlgebra.ι R v * ω - CliffordAlgebra.contractLeft (g v) ω)
    simp only [map_add, add_mul, LinearMap.add_apply]
    abel
  map_smul' c v := by
    apply LinearMap.ext
    intro ω
    change ExteriorAlgebra.ι R (c • v) * ω - CliffordAlgebra.contractLeft (g (c • v)) ω =
      c • (ExteriorAlgebra.ι R v * ω - CliffordAlgebra.contractLeft (g v) ω)
    simp only [map_smul, smul_mul_assoc, LinearMap.smul_apply, smul_sub]

/-- Linear map `v ↦ posCartanAction g v`. -/
def posCartanActionMap (g : LinearMap.BilinForm R V) :
    V →ₗ[R] Module.End R (ExteriorAlgebra R V) where
  toFun := posCartanAction g
  map_add' u v := by
    apply LinearMap.ext
    intro ω
    change ExteriorAlgebra.ι R (u + v) * ω + CliffordAlgebra.contractLeft (g (u + v)) ω =
      (ExteriorAlgebra.ι R u * ω + CliffordAlgebra.contractLeft (g u) ω) +
        (ExteriorAlgebra.ι R v * ω + CliffordAlgebra.contractLeft (g v) ω)
    simp only [map_add, add_mul, LinearMap.add_apply]
    abel
  map_smul' c v := by
    apply LinearMap.ext
    intro ω
    change ExteriorAlgebra.ι R (c • v) * ω + CliffordAlgebra.contractLeft (g (c • v)) ω =
      c • (ExteriorAlgebra.ι R v * ω + CliffordAlgebra.contractLeft (g v) ω)
    simp only [map_smul, smul_mul_assoc, LinearMap.smul_apply, smul_add]

@[simp]
lemma negCartanActionMap_apply (g : LinearMap.BilinForm R V) (v : V) :
    negCartanActionMap g v = negCartanAction g v := rfl

@[simp]
lemma posCartanActionMap_apply (g : LinearMap.BilinForm R V) (v : V) :
    posCartanActionMap g v = posCartanAction g v := rfl

/-- `posCartanAction g v` squares to `g v v • 1`. -/
theorem posCartanAction_sq (g : LinearMap.BilinForm R V) (v : V) :
    posCartanAction g v * posCartanAction g v =
      (g v v) • (1 : Module.End R (ExteriorAlgebra R V)) :=
  chevalleyAction_sq v (g v)

/-- `negCartanAction g v` squares to `-(g v v) • 1`. -/
theorem negCartanAction_sq (g : LinearMap.BilinForm R V) (v : V) :
    negCartanAction g v * negCartanAction g v =
      (-(g v v)) • (1 : Module.End R (ExteriorAlgebra R V)) := by
  calc
    negCartanAction g v * negCartanAction g v =
        exteriorWedge R v * exteriorWedge R v -
          (exteriorContract (g v) * exteriorWedge R v +
            exteriorWedge R v * exteriorContract (g v)) +
          exteriorContract (g v) * exteriorContract (g v) := by
      simp only [negCartanAction, sub_mul, mul_sub]
      abel
    _ = (-(g v v)) • (1 : Module.End R (ExteriorAlgebra R V)) := by
      rw [exteriorWedge_sq, exteriorContract_sq, exterior_cartan_homotopy_car,
        zero_sub, add_zero]
      exact (neg_smul (g v v) (1 : Module.End R (ExteriorAlgebra R V))).symm

/-- For symmetric `g`, `negCartanAction g u` and `posCartanAction g v` anticommute. -/
theorem negCartanAction_posCartanAction_anticomm (g : LinearMap.BilinForm R V)
    (hg : ∀ u v, g u v = g v u) (u v : V) :
    negCartanAction g u * posCartanAction g v +
        posCartanAction g v * negCartanAction g u = 0 := by
  calc
    negCartanAction g u * posCartanAction g v +
          posCartanAction g v * negCartanAction g u =
        (exteriorWedge R u * exteriorWedge R v + exteriorWedge R v * exteriorWedge R u) +
        (exteriorWedge R u * exteriorContract (g v) + exteriorContract (g v) * exteriorWedge R u) -
        (exteriorContract (g u) * exteriorWedge R v + exteriorWedge R v * exteriorContract (g u)) -
        (exteriorContract (g u) * exteriorContract (g v) +
          exteriorContract (g v) * exteriorContract (g u)) := by
      simp only [negCartanAction, posCartanAction, sub_mul, mul_sub, add_mul, mul_add]
      abel
    _ = 0 := by
      rw [exteriorWedge_anticomm, exteriorContract_anticomm,
        add_comm (exteriorWedge R u * exteriorContract (g v)),
        exterior_cartan_homotopy_car (g v) u,
        exterior_cartan_homotopy_car (g u) v,
        hg u v]
      simp

/-- Canonical algebra homomorphism from the doubled Clifford algebra `Cl((-Q) ⊕ Q)`
into `Module.End R (ExteriorAlgebra R V)`, sending `(u, v) ↦ c_-(u) + c_+(v)`. -/
def doubledCliffordToEnd (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) →ₐ[R]
      Module.End R (ExteriorAlgebra R V) :=
  CliffordAlgebra.lift ((-g.toQuadraticMap).prod g.toQuadraticMap)
    ⟨(negCartanActionMap g).coprod (posCartanActionMap g), fun p => by
      simp only [LinearMap.coprod_apply, negCartanActionMap_apply, posCartanActionMap_apply,
        QuadraticMap.prod_apply, neg_apply, LinearMap.BilinMap.toQuadraticMap_apply,
        Algebra.algebraMap_eq_smul_one]
      have hsq1 := negCartanAction_sq g p.1
      have hsq2 := posCartanAction_sq g p.2
      have hanti := negCartanAction_posCartanAction_anticomm g hg p.1 p.2
      calc
        (negCartanAction g p.1 + posCartanAction g p.2) *
            (negCartanAction g p.1 + posCartanAction g p.2) =
            negCartanAction g p.1 * negCartanAction g p.1 +
              (negCartanAction g p.1 * posCartanAction g p.2 +
                posCartanAction g p.2 * negCartanAction g p.1) +
              posCartanAction g p.2 * posCartanAction g p.2 := by
          simp only [add_mul, mul_add]
          abel
        _ = (-(g p.1 p.1) + g p.2 p.2) • (1 : Module.End R (ExteriorAlgebra R V)) := by
          rw [hsq1, hsq2, hanti, add_zero, add_smul]⟩

@[simp]
lemma doubledCliffordToEnd_ι (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (u v : V) :
    doubledCliffordToEnd g hg
        (CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, v)) =
      negCartanAction g u + posCartanAction g v := by
  exact CliffordAlgebra.lift_ι_apply _ _ (u, v)

section InvertibleTwo

variable [Invertible (2 : R)]

/-- `1/2`-normalized creation generator in `Cl((-Q) ⊕ Q)`: `c†(v) = (1/2) • (ι(0, v) + ι(v, 0))`. -/
def cliffordCreate (g : LinearMap.BilinForm R V) (v : V) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  (⅟(2 : R)) •
    (CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) +
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (v, 0))

/-- `1/2`-normalized annihilation generator in `Cl((-Q) ⊕ Q)`: `c(v) = (1/2) • (ι(0, v) - ι(v, 0))`. -/
def cliffordAnnihilate (g : LinearMap.BilinForm R V) (v : V) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  (⅟(2 : R)) •
    (CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) -
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (v, 0))

omit [Invertible (2 : R)] in
private lemma doubled_ι_inl_inr_anticomm (g : LinearMap.BilinForm R V) (u v : V) :
    CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, 0) *
        CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) +
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) *
        CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, 0) = 0 := by
  apply CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
  exact QuadraticMap.IsOrtho.inl_inr u v

omit [Invertible (2 : R)] in
private lemma doubled_ι_inl_anticomm (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (u v : V) :
    CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, 0) *
        CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (v, 0) +
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (v, 0) *
        CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, 0) =
      algebraMap R _ (-(2 * g u v)) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := (-g.toQuadraticMap).prod g.toQuadraticMap) (u, (0 : V)) (v, (0 : V))
  rw [h]
  dsimp [QuadraticMap.polar]
  simp only [QuadraticMap.prod_apply, neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, map_zero, add_zero]
  congr 1
  simp only [map_add, LinearMap.add_apply, hg v u]
  rw [show -((g u) u + (g u) v + ((g u) v + (g v) v)) - -((g u) u) - -((g v) v) =
      -(2 * g u v) by rw [two_mul]; abel]

omit [Invertible (2 : R)] in
private lemma doubled_ι_inr_anticomm (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (u v : V) :
    CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, u) *
        CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) +
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) *
        CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, u) =
      algebraMap R _ (2 * g u v) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := (-g.toQuadraticMap).prod g.toQuadraticMap) ((0 : V), u) ((0 : V), v)
  rw [h]
  dsimp [QuadraticMap.polar]
  simp only [QuadraticMap.prod_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, map_zero, zero_add]
  congr 1
  simp only [map_add, LinearMap.add_apply, hg v u]
  rw [show (g u) u + (g u) v + ((g u) v + (g v) v) - (g u) u - (g v) v = 2 * g u v by
    rw [two_mul]; abel]

/-- Creation operators in `Cl((-Q) ⊕ Q)` anticommute: `{c†_u, c†_v} = 0` (Eq. 4.31). -/
theorem cliffordCreate_anticomm (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (u v : V) :
    cliffordCreate g u * cliffordCreate g v + cliffordCreate g v * cliffordCreate g u = 0 := by
  let Q₂ := (-g.toQuadraticMap).prod g.toQuadraticMap
  have h_sum :
      (CliffordAlgebra.ι Q₂ (0, u) + CliffordAlgebra.ι Q₂ (u, 0)) *
          (CliffordAlgebra.ι Q₂ (0, v) + CliffordAlgebra.ι Q₂ (v, 0)) +
        (CliffordAlgebra.ι Q₂ (0, v) + CliffordAlgebra.ι Q₂ (v, 0)) *
          (CliffordAlgebra.ι Q₂ (0, u) + CliffordAlgebra.ι Q₂ (u, 0)) = 0 := by
    calc
      _ = (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (0, v) +
              CliffordAlgebra.ι Q₂ (0, v) * CliffordAlgebra.ι Q₂ (0, u)) +
            (CliffordAlgebra.ι Q₂ (u, 0) * CliffordAlgebra.ι Q₂ (v, 0) +
              CliffordAlgebra.ι Q₂ (v, 0) * CliffordAlgebra.ι Q₂ (u, 0)) +
            (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (v, 0) +
              CliffordAlgebra.ι Q₂ (v, 0) * CliffordAlgebra.ι Q₂ (0, u)) +
            (CliffordAlgebra.ι Q₂ (u, 0) * CliffordAlgebra.ι Q₂ (0, v) +
              CliffordAlgebra.ι Q₂ (0, v) * CliffordAlgebra.ι Q₂ (u, 0)) := by
          simp only [add_mul, mul_add]
          abel
      _ = algebraMap R _ (2 * g u v) + algebraMap R _ (-(2 * g u v)) + 0 + 0 := by
          rw [doubled_ι_inr_anticomm g hg u v, doubled_ι_inl_anticomm g hg u v]
          rw [add_comm (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (v, 0)),
            doubled_ι_inl_inr_anticomm g v u, doubled_ι_inl_inr_anticomm g u v]
      _ = 0 := by
          rw [add_zero, add_zero, ← map_add, add_neg_cancel, map_zero]
  dsimp only [Q₂] at h_sum
  simp only [cliffordCreate, smul_mul_assoc, mul_smul_comm, ← smul_add, h_sum, smul_zero]

/-- Annihilation operators in `Cl((-Q) ⊕ Q)` anticommute: `{c_u, c_v} = 0` (Eq. 4.31). -/
theorem cliffordAnnihilate_anticomm (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (u v : V) :
    cliffordAnnihilate g u * cliffordAnnihilate g v +
      cliffordAnnihilate g v * cliffordAnnihilate g u = 0 := by
  let Q₂ := (-g.toQuadraticMap).prod g.toQuadraticMap
  have h_sum :
      (CliffordAlgebra.ι Q₂ (0, u) - CliffordAlgebra.ι Q₂ (u, 0)) *
          (CliffordAlgebra.ι Q₂ (0, v) - CliffordAlgebra.ι Q₂ (v, 0)) +
        (CliffordAlgebra.ι Q₂ (0, v) - CliffordAlgebra.ι Q₂ (v, 0)) *
          (CliffordAlgebra.ι Q₂ (0, u) - CliffordAlgebra.ι Q₂ (u, 0)) = 0 := by
    calc
      _ = (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (0, v) +
              CliffordAlgebra.ι Q₂ (0, v) * CliffordAlgebra.ι Q₂ (0, u)) +
            (CliffordAlgebra.ι Q₂ (u, 0) * CliffordAlgebra.ι Q₂ (v, 0) +
              CliffordAlgebra.ι Q₂ (v, 0) * CliffordAlgebra.ι Q₂ (u, 0)) -
            (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (v, 0) +
              CliffordAlgebra.ι Q₂ (v, 0) * CliffordAlgebra.ι Q₂ (0, u)) -
            (CliffordAlgebra.ι Q₂ (u, 0) * CliffordAlgebra.ι Q₂ (0, v) +
              CliffordAlgebra.ι Q₂ (0, v) * CliffordAlgebra.ι Q₂ (u, 0)) := by
          simp only [sub_mul, mul_sub]
          abel
      _ = algebraMap R _ (2 * g u v) + algebraMap R _ (-(2 * g u v)) - 0 - 0 := by
          rw [doubled_ι_inr_anticomm g hg u v, doubled_ι_inl_anticomm g hg u v]
          rw [add_comm (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (v, 0)),
            doubled_ι_inl_inr_anticomm g v u, doubled_ι_inl_inr_anticomm g u v]
      _ = 0 := by
          rw [sub_zero, sub_zero, ← map_add, add_neg_cancel, map_zero]
  dsimp only [Q₂] at h_sum
  simp only [cliffordAnnihilate, smul_mul_assoc, mul_smul_comm, ← smul_add, h_sum, smul_zero]

/-- Canonical anticommutation relation in `Cl((-Q) ⊕ Q)`:
`{c†_u, c_v} = g(u, v) • 1` (Eq. 4.31). -/
theorem cliffordCreate_annihilate_car (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (u v : V) :
    cliffordCreate g u * cliffordAnnihilate g v +
        cliffordAnnihilate g v * cliffordCreate g u =
      algebraMap R _ (g u v) := by
  let Q₂ := (-g.toQuadraticMap).prod g.toQuadraticMap
  have h_sum :
      (CliffordAlgebra.ι Q₂ (0, u) + CliffordAlgebra.ι Q₂ (u, 0)) *
          (CliffordAlgebra.ι Q₂ (0, v) - CliffordAlgebra.ι Q₂ (v, 0)) +
        (CliffordAlgebra.ι Q₂ (0, v) - CliffordAlgebra.ι Q₂ (v, 0)) *
          (CliffordAlgebra.ι Q₂ (0, u) + CliffordAlgebra.ι Q₂ (u, 0)) =
        algebraMap R _ (4 * g u v) := by
    calc
      _ = (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (0, v) +
              CliffordAlgebra.ι Q₂ (0, v) * CliffordAlgebra.ι Q₂ (0, u)) -
            (CliffordAlgebra.ι Q₂ (u, 0) * CliffordAlgebra.ι Q₂ (v, 0) +
              CliffordAlgebra.ι Q₂ (v, 0) * CliffordAlgebra.ι Q₂ (u, 0)) -
            (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (v, 0) +
              CliffordAlgebra.ι Q₂ (v, 0) * CliffordAlgebra.ι Q₂ (0, u)) +
            (CliffordAlgebra.ι Q₂ (u, 0) * CliffordAlgebra.ι Q₂ (0, v) +
              CliffordAlgebra.ι Q₂ (0, v) * CliffordAlgebra.ι Q₂ (u, 0)) := by
          simp only [add_mul, mul_add, sub_mul, mul_sub]
          abel
      _ = algebraMap R _ (2 * g u v) - algebraMap R _ (-(2 * g u v)) - 0 + 0 := by
          rw [doubled_ι_inr_anticomm g hg u v, doubled_ι_inl_anticomm g hg u v]
          rw [add_comm (CliffordAlgebra.ι Q₂ (0, u) * CliffordAlgebra.ι Q₂ (v, 0)),
            doubled_ι_inl_inr_anticomm g v u, doubled_ι_inl_inr_anticomm g u v]
      _ = algebraMap R _ (4 * g u v) := by
          rw [sub_zero, add_zero, ← map_sub]
          congr 1
          rw [sub_neg_eq_add, ← add_mul]
          congr 1
          norm_num
  dsimp only [Q₂] at h_sum
  simp only [cliffordCreate, cliffordAnnihilate, smul_mul_assoc, mul_smul_comm, ← smul_add, h_sum]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul]
  congr 1
  have h4 : (4 : R) * g u v = 2 * (2 * g u v) := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this, mul_assoc]
  rw [h4, mul_assoc (⅟(2 : R)), ← mul_assoc (⅟(2 : R)) 2, invOf_mul_self, one_mul,
    ← mul_assoc (⅟(2 : R)), invOf_mul_self, one_mul]

/-- Under `doubledCliffordToEnd`, `cliffordCreate v` maps literally to `exteriorWedge R v`. -/
@[simp]
theorem doubledCliffordToEnd_create (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (v : V) :
    doubledCliffordToEnd g hg (cliffordCreate g v) = exteriorWedge R v := by
  simp only [cliffordCreate, map_smul, map_add, doubledCliffordToEnd_ι,
    negCartanAction, posCartanAction]
  have h0 : (exteriorWedge R (0 : V) - exteriorContract (g 0) +
      (exteriorWedge R v + exteriorContract (g v))) +
      (exteriorWedge R v - exteriorContract (g v) +
        (exteriorWedge R (0 : V) + exteriorContract (g 0))) =
      (2 : R) • exteriorWedge R v := by
    apply LinearMap.ext
    intro ω
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      exteriorWedge_apply, exteriorContract, map_zero, zero_mul, sub_zero,
      zero_add, LinearMap.zero_apply, two_smul]
    abel
  rw [h0, smul_smul, invOf_mul_self, one_smul]

/-- Under `doubledCliffordToEnd`, `cliffordAnnihilate v` maps literally to `exteriorContract (g v)`. -/
@[simp]
theorem doubledCliffordToEnd_annihilate (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (v : V) :
    doubledCliffordToEnd g hg (cliffordAnnihilate g v) = exteriorContract (g v) := by
  simp only [cliffordAnnihilate, map_smul, map_sub, doubledCliffordToEnd_ι,
    negCartanAction, posCartanAction]
  have h0 : (exteriorWedge R (0 : V) - exteriorContract (g 0) +
      (exteriorWedge R v + exteriorContract (g v))) -
      (exteriorWedge R v - exteriorContract (g v) +
        (exteriorWedge R (0 : V) + exteriorContract (g 0))) =
      (2 : R) • exteriorContract (g v) := by
    apply LinearMap.ext
    intro ω
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      exteriorWedge_apply, exteriorContract, map_zero, zero_mul, sub_zero,
      zero_add, LinearMap.zero_apply, two_smul]
    abel
  rw [h0, smul_smul, invOf_mul_self, one_smul]

end InvertibleTwo

section RealSqrt2Normalization

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Witten's `1 / √2` prefactor creation element in `Cl((-Q) ⊕ Q)` over `ℝ` (Eq. 4.32–4.34). -/
def cliffordCreateSqrt2 (g : LinearMap.BilinForm ℝ W) (v : W) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  (1 / Real.sqrt 2) •
    (CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) +
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (v, 0))

/-- Witten's `1 / √2` prefactor annihilation element in `Cl((-Q) ⊕ Q)` over `ℝ` (Eq. 4.32–4.34). -/
def cliffordAnnihilateSqrt2 (g : LinearMap.BilinForm ℝ W) (v : W) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  (1 / Real.sqrt 2) •
    (CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) -
      CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (v, 0))

private lemma cliffordCreateSqrt2_eq_smul (g : LinearMap.BilinForm ℝ W) (v : W) :
    cliffordCreateSqrt2 g v = Real.sqrt 2 • cliffordCreate g v := by
  simp only [cliffordCreateSqrt2, cliffordCreate, smul_smul]
  congr 1
  have h2 : (⅟(2 : ℝ)) = 2⁻¹ := invOf_eq_inv (2 : ℝ)
  rw [h2]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

private lemma cliffordAnnihilateSqrt2_eq_smul (g : LinearMap.BilinForm ℝ W) (v : W) :
    cliffordAnnihilateSqrt2 g v = Real.sqrt 2 • cliffordAnnihilate g v := by
  simp only [cliffordAnnihilateSqrt2, cliffordAnnihilate, smul_smul]
  congr 1
  have h2 : (⅟(2 : ℝ)) = 2⁻¹ := invOf_eq_inv (2 : ℝ)
  rw [h2]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- Scaling corollary: under `{γ_μ, γ_ν} = 2 g_{μν}`, the `1 / √2` generators
give `{c†_{√2, u}, c_{√2, v}} = 2 g(u, v) • 1` (whereas `1/2` gives `g(u, v) • 1`). -/
theorem cliffordCreateSqrt2_annihilateSqrt2_car (g : LinearMap.BilinForm ℝ W)
    (hg : ∀ u v, g u v = g v u) (u v : W) :
    cliffordCreateSqrt2 g u * cliffordAnnihilateSqrt2 g v +
        cliffordAnnihilateSqrt2 g v * cliffordCreateSqrt2 g u =
      algebraMap ℝ _ (2 * g u v) := by
  rw [cliffordCreateSqrt2_eq_smul, cliffordAnnihilateSqrt2_eq_smul]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add,
    cliffordCreate_annihilate_car g hg u v, smul_smul]
  rw [Algebra.algebraMap_eq_smul_one, smul_smul, Algebra.algebraMap_eq_smul_one]
  congr 1
  rw [Real.mul_self_sqrt (by norm_num)]

end RealSqrt2Normalization

/-!
### Grading Operator `Γ = (-1)^deg` (Eq. 4.35), Spectral Symmetry, and 9th Generator
-/

/-- The parity grading operator `Γ = (-1)^deg` on `ExteriorAlgebra R V`,
realized via `CliffordAlgebra.involute` for `Q = 0`. -/
def exteriorGradingOp : Module.End R (ExteriorAlgebra R V) :=
  (CliffordAlgebra.involute (Q := (0 : QuadraticForm R V))).toLinearMap

@[simp]
lemma exteriorGradingOp_apply (ω : ExteriorAlgebra R V) :
    exteriorGradingOp ω = CliffordAlgebra.involute (Q := (0 : QuadraticForm R V)) ω := rfl

/-- `Γ² = 1` on `ExteriorAlgebra R V`. -/
@[simp]
theorem exteriorGradingOp_sq :
    (exteriorGradingOp : Module.End R (ExteriorAlgebra R V)) * exteriorGradingOp = 1 := by
  apply LinearMap.ext
  intro ω
  simp [CliffordAlgebra.involute_involute]

/-- On `⋀[R]^k V`, `exteriorGradingOp` acts as `(-1 : R) ^ k • ω` (Eq. 4.35). -/
theorem exteriorGradingOp_apply_pow (k : ℕ) {ω : ExteriorAlgebra R V}
    (hω : ω ∈ ExteriorAlgebra.exteriorPower R k V) :
    exteriorGradingOp ω = (-1 : R) ^ k • ω := by
  induction hω using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [exteriorGradingOp_apply, Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      pow_zero, one_smul]
  | add x y n hx hy ihx ihy =>
    simp only [map_add, ihx, ihy, smul_add]
  | mem_mul x hx n y hy ihy =>
    rcases hx with ⟨v, rfl⟩
    simp only [exteriorGradingOp_apply, map_mul, CliffordAlgebra.involute_ι] at ihy ⊢
    rw [ihy, neg_mul, mul_smul_comm, ← neg_smul, pow_succ', neg_one_mul]

/-- `Γ` anticommutes with `exteriorWedge R v` (Eq. 4.35). -/
theorem exteriorGradingOp_anticomm_wedge (v : V) :
    (exteriorGradingOp : Module.End R (ExteriorAlgebra R V)) * exteriorWedge R v +
      exteriorWedge R v * exteriorGradingOp = 0 := by
  apply LinearMap.ext
  intro ω
  simp only [LinearMap.add_apply, Module.End.mul_apply, exteriorGradingOp_apply,
    exteriorWedge_apply, map_mul, CliffordAlgebra.involute_ι, LinearMap.zero_apply]
  rw [neg_mul]
  exact neg_add_cancel _

/-- `Γ` anticommutes with `exteriorContract φ` (Eq. 4.35). -/
theorem exteriorGradingOp_anticomm_contract (φ : Module.Dual R V) :
    (exteriorGradingOp : Module.End R (ExteriorAlgebra R V)) * exteriorContract φ +
      exteriorContract φ * exteriorGradingOp = 0 := by
  apply LinearMap.ext
  intro ω
  simp only [LinearMap.add_apply, Module.End.mul_apply, exteriorGradingOp_apply,
    exteriorContract, LinearMap.zero_apply]
  rw [involute_contractLeft (0 : QuadraticForm R V) φ ω, neg_add_cancel]

/-- Uniqueness of `exteriorGradingOp`: any `Module.End R (ExteriorAlgebra R V)` fixing `1`
and anticommuting with every `exteriorWedge R v` equals `exteriorGradingOp`. -/
theorem eq_exteriorGradingOp_of_anticomm (T : Module.End R (ExteriorAlgebra R V))
    (h1 : T 1 = 1)
    (hanti : ∀ v : V, T * exteriorWedge R v + exteriorWedge R v * T = 0) :
    T = exteriorGradingOp := by
  apply LinearMap.ext
  intro ω
  induction ω using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1]
    simp [exteriorGradingOp]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    have hv : T * exteriorWedge R v = -(exteriorWedge R v * T) :=
      eq_neg_of_add_eq_zero_left (hanti v)
    have hge : (exteriorGradingOp : Module.End R (ExteriorAlgebra R V)) * exteriorWedge R v =
        -(exteriorWedge R v * exteriorGradingOp) :=
      eq_neg_of_add_eq_zero_left (exteriorGradingOp_anticomm_wedge v)
    have hmul : ExteriorAlgebra.ι R v * x = exteriorWedge R v x := rfl
    change T (ExteriorAlgebra.ι R v * x) = exteriorGradingOp (ExteriorAlgebra.ι R v * x)
    rw [hmul]
    change (T * exteriorWedge R v) x =
      ((exteriorGradingOp : Module.End R (ExteriorAlgebra R V)) * exteriorWedge R v) x
    rw [hv, hge]
    change -(exteriorWedge R v (T x)) = -(exteriorWedge R v (exteriorGradingOp x))
    rw [hx]

/-- 9th generator extension (Witten p. 48): `γ_ε = Γ = (-1)^deg` extends `Cl((-Q) ⊕ Q)`
to `Cl(((-Q) ⊕ Q) ⊕ ⟨1⟩)` acting on `ExteriorAlgebra R V`. -/
def clifford9ToEnd (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u) :
    CliffordAlgebra (((-g.toQuadraticMap).prod g.toQuadraticMap).prod (QuadraticMap.sq (R := R))) →ₐ[R]
      Module.End R (ExteriorAlgebra R V) :=
  CliffordAlgebra.lift _
    ⟨((negCartanActionMap g).coprod (posCartanActionMap g)).coprod
        ((LinearMap.id : R →ₗ[R] R).smulRight exteriorGradingOp),
      fun ⟨⟨u, v⟩, t⟩ => by
        simp only [LinearMap.coprod_apply, negCartanActionMap_apply, posCartanActionMap_apply,
          LinearMap.smulRight_apply, LinearMap.id_apply, QuadraticMap.prod_apply,
          neg_apply, LinearMap.BilinMap.toQuadraticMap_apply,
          QuadraticMap.sq_apply, smul_eq_mul, Algebra.algebraMap_eq_smul_one]
        have h_u_anti : negCartanAction g u * exteriorGradingOp +
            exteriorGradingOp * negCartanAction g u = 0 := by
          calc
            _ = (exteriorWedge R u * exteriorGradingOp + exteriorGradingOp * exteriorWedge R u) -
                (exteriorContract (g u) * exteriorGradingOp +
                  exteriorGradingOp * exteriorContract (g u)) := by
              simp only [negCartanAction, sub_mul, mul_sub]
              abel
            _ = 0 := by
              rw [add_comm (exteriorWedge R u * exteriorGradingOp),
                exteriorGradingOp_anticomm_wedge,
                add_comm (exteriorContract (g u) * exteriorGradingOp),
                exteriorGradingOp_anticomm_contract, sub_zero]
        have h_v_anti : posCartanAction g v * exteriorGradingOp +
            exteriorGradingOp * posCartanAction g v = 0 := by
          calc
            _ = (exteriorWedge R v * exteriorGradingOp + exteriorGradingOp * exteriorWedge R v) +
                (exteriorContract (g v) * exteriorGradingOp +
                  exteriorGradingOp * exteriorContract (g v)) := by
              simp only [posCartanAction, add_mul, mul_add]
              abel
            _ = 0 := by
              rw [add_comm (exteriorWedge R v * exteriorGradingOp),
                exteriorGradingOp_anticomm_wedge,
                add_comm (exteriorContract (g v) * exteriorGradingOp),
                exteriorGradingOp_anticomm_contract, add_zero]
        have h_uv_anti : (negCartanAction g u + posCartanAction g v) * exteriorGradingOp +
            exteriorGradingOp * (negCartanAction g u + posCartanAction g v) = 0 := by
          calc
            _ = (negCartanAction g u * exteriorGradingOp +
                  exteriorGradingOp * negCartanAction g u) +
                (posCartanAction g v * exteriorGradingOp +
                  exteriorGradingOp * posCartanAction g v) := by
              simp only [add_mul, mul_add]
              abel
            _ = 0 := by rw [h_u_anti, h_v_anti, add_zero]
        have h_uv_sq : (negCartanAction g u + posCartanAction g v) *
            (negCartanAction g u + posCartanAction g v) =
            (-(g u u) + g v v) • (1 : Module.End R (ExteriorAlgebra R V)) := by
          calc
            _ = negCartanAction g u * negCartanAction g u +
                  (negCartanAction g u * posCartanAction g v +
                    posCartanAction g v * negCartanAction g u) +
                  posCartanAction g v * posCartanAction g v := by
              simp only [add_mul, mul_add]
              abel
            _ = (-(g u u) + g v v) • (1 : Module.End R (ExteriorAlgebra R V)) := by
              rw [negCartanAction_sq, posCartanAction_sq,
                negCartanAction_posCartanAction_anticomm g hg, add_zero, add_smul]
        calc
          ((negCartanAction g u + posCartanAction g v) + t • exteriorGradingOp) *
              ((negCartanAction g u + posCartanAction g v) + t • exteriorGradingOp) =
              (negCartanAction g u + posCartanAction g v) *
                  (negCartanAction g u + posCartanAction g v) +
                t • ((negCartanAction g u + posCartanAction g v) * exteriorGradingOp +
                  exteriorGradingOp * (negCartanAction g u + posCartanAction g v)) +
                (t * t) • (exteriorGradingOp * exteriorGradingOp) := by
            simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
            abel
          _ = (-(g u u) + g v v + t * t) • (1 : Module.End R (ExteriorAlgebra R V)) := by
            rw [h_uv_sq, h_uv_anti, exteriorGradingOp_sq, smul_zero, add_zero, ← add_smul]⟩

end DoubledCliffordGeneral

section SpectralSymmetry

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- If `D` anticommutes with `Γ`, then `Γ` maps any `μ`-eigenvector of `D` to a `(-μ)`-eigenvector
(Witten §4.3, p. 50). -/
theorem eigenspace_flip_of_anticomm {D Γ : Module.End 𝕜 E}
    (h_anti : D * Γ + Γ * D = 0) {μ : 𝕜} {x : E}
    (hx : x ∈ Module.End.eigenspace D μ) :
    Γ x ∈ Module.End.eigenspace D (-μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hDΓ : D * Γ = -(Γ * D) := eq_neg_of_add_eq_zero_left h_anti
  calc
    D (Γ x) = (D * Γ) x := rfl
    _ = (-(Γ * D)) x := by rw [hDΓ]
    _ = -(Γ (D x)) := rfl
    _ = -(Γ (μ • x)) := by rw [hx]
    _ = (-μ) • Γ x := by rw [map_smul, neg_smul]

/-- Spectral symmetry equivalence `eigenspace D μ ≃ₗ[𝕜] eigenspace D (-μ)` induced by an
involutive grading operator `Γ` anticommuting with `D`. -/
def eigenspaceEquivOfAnticomm (D Γ : Module.End 𝕜 E)
    (hΓ : Γ * Γ = 1) (h_anti : D * Γ + Γ * D = 0) (μ : 𝕜) :
    Module.End.eigenspace D μ ≃ₗ[𝕜] Module.End.eigenspace D (-μ) where
  toFun x := ⟨Γ x.1, eigenspace_flip_of_anticomm h_anti x.2⟩
  map_add' x y := by ext; exact map_add Γ x.1 y.1
  map_smul' c x := by ext; exact map_smul Γ c x.1
  invFun y := ⟨Γ y.1, by
    simpa [neg_neg] using eigenspace_flip_of_anticomm h_anti y.2⟩
  left_inv x := by
    ext
    change (Γ * Γ) x.1 = x.1
    rw [hΓ]
    rfl
  right_inv y := by
    ext
    change (Γ * Γ) y.1 = y.1
    rw [hΓ]
    rfl

/-- `D²` commutes with `Γ`, reusing `AtiyahSingerDirac.dirac_square_grading_commutes`. -/
theorem dirac_square_comm_grading (D Γ : Module.End 𝕜 E) (h_anti : D * Γ + Γ * D = 0) :
    D * D * Γ - Γ * (D * D) = 0 :=
  dirac_square_grading_commutes h_anti

end SpectralSymmetry

/-!
### Complexified Twist (Eq. 4.32) & 4D Real Chirality Twist (Eqs. 4.33–4.35)
-/

section ComplexTwist

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Complexified Clifford twist `Cl(Q ⊕ Q) ≃ₐ[ℂ] Cl((-Q) ⊕ Q)` sending
`γ_μ ↦ i γ_μ'`, `γ̃_μ ↦ γ̃_μ'` (Witten Eq. 4.32). -/
def wittenComplexTwist (Q : QuadraticForm ℂ V) :
    CliffordAlgebra (Q.prod Q) ≃ₐ[ℂ] CliffordAlgebra ((-Q).prod Q) :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (Q.prod Q)
      ⟨LinearMap.coprod
          ((CliffordAlgebra.ι ((-Q).prod Q)).comp (LinearMap.inl ℂ V V) |>.comp (Complex.I • LinearMap.id))
          ((CliffordAlgebra.ι ((-Q).prod Q)).comp (LinearMap.inr ℂ V V)),
        fun ⟨u, v⟩ => by
          simp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
            LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply,
            QuadraticMap.prod_apply, Algebra.algebraMap_eq_smul_one]
          have hortho :
              CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, (0 : V)) *
                  CliffordAlgebra.ι ((-Q).prod Q) ((0 : V), v) +
                CliffordAlgebra.ι ((-Q).prod Q) ((0 : V), v) *
                  CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, (0 : V)) = 0 :=
            CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
              (QuadraticMap.IsOrtho.inl_inr (Complex.I • u) v)
          calc
            (CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, 0) +
                CliffordAlgebra.ι ((-Q).prod Q) (0, v)) *
                (CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, 0) +
                  CliffordAlgebra.ι ((-Q).prod Q) (0, v)) =
                (CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, 0) *
                    CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, 0)) +
                  (CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, 0) *
                      CliffordAlgebra.ι ((-Q).prod Q) (0, v) +
                    CliffordAlgebra.ι ((-Q).prod Q) (0, v) *
                      CliffordAlgebra.ι ((-Q).prod Q) (Complex.I • u, 0)) +
                  (CliffordAlgebra.ι ((-Q).prod Q) (0, v) *
                    CliffordAlgebra.ι ((-Q).prod Q) (0, v)) := by
              simp only [add_mul, mul_add]
              abel
            _ = algebraMap ℂ _ (((-Q).prod Q) (Complex.I • u, 0)) + 0 +
                  algebraMap ℂ _ (((-Q).prod Q) (0, v)) := by
              rw [CliffordAlgebra.ι_sq_scalar, hortho, CliffordAlgebra.ι_sq_scalar]
            _ = (Q u + Q v) • (1 : CliffordAlgebra ((-Q).prod Q)) := by
              simp only [QuadraticMap.prod_apply, neg_apply, QuadraticMap.map_smul, map_zero,
                smul_eq_mul, Complex.I_mul_I, neg_mul, one_mul, neg_neg, add_zero, zero_add,
                Algebra.algebraMap_eq_smul_one, ← add_smul]⟩)
    (CliffordAlgebra.lift ((-Q).prod Q)
      ⟨LinearMap.coprod
          ((CliffordAlgebra.ι (Q.prod Q)).comp (LinearMap.inl ℂ V V) |>.comp ((-Complex.I) • LinearMap.id))
          ((CliffordAlgebra.ι (Q.prod Q)).comp (LinearMap.inr ℂ V V)),
        fun ⟨u, v⟩ => by
          simp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
            LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply,
            QuadraticMap.prod_apply, neg_apply, Algebra.algebraMap_eq_smul_one]
          have hortho :
              CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, (0 : V)) *
                  CliffordAlgebra.ι (Q.prod Q) ((0 : V), v) +
                CliffordAlgebra.ι (Q.prod Q) ((0 : V), v) *
                  CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, (0 : V)) = 0 :=
            CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
              (QuadraticMap.IsOrtho.inl_inr ((-Complex.I) • u) v)
          calc
            (CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, 0) +
                CliffordAlgebra.ι (Q.prod Q) (0, v)) *
                (CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, 0) +
                  CliffordAlgebra.ι (Q.prod Q) (0, v)) =
                (CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, 0) *
                    CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, 0)) +
                  (CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, 0) *
                      CliffordAlgebra.ι (Q.prod Q) (0, v) +
                    CliffordAlgebra.ι (Q.prod Q) (0, v) *
                      CliffordAlgebra.ι (Q.prod Q) ((-Complex.I) • u, 0)) +
                  (CliffordAlgebra.ι (Q.prod Q) (0, v) *
                    CliffordAlgebra.ι (Q.prod Q) (0, v)) := by
              simp only [add_mul, mul_add]
              abel
            _ = algebraMap ℂ _ ((Q.prod Q) ((-Complex.I) • u, 0)) + 0 +
                  algebraMap ℂ _ ((Q.prod Q) (0, v)) := by
              rw [CliffordAlgebra.ι_sq_scalar, hortho, CliffordAlgebra.ι_sq_scalar]
            _ = (-Q u + Q v) • (1 : CliffordAlgebra (Q.prod Q)) := by
              simp only [QuadraticMap.prod_apply, QuadraticMap.map_smul, map_zero, smul_eq_mul,
                neg_mul, mul_neg, neg_neg, Complex.I_mul_I, one_mul, add_zero, zero_add,
                Algebra.algebraMap_eq_smul_one, ← add_smul]⟩)
    (by
      ext x
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply]
        rw [CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        rw [map_add, Prod.mk_zero_zero, map_zero, map_zero, add_zero]
        have hmk₁ : ((-Complex.I) • x, (0 : V)) = (-Complex.I) • (x, (0 : V)) := by
          apply Prod.ext <;> simp
        rw [hmk₁, map_smul, map_smul, CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        rw [Prod.mk_zero_zero, map_zero, add_zero]
        have hmk₂ : (Complex.I • x, (0 : V)) = Complex.I • (x, (0 : V)) := by
          apply Prod.ext <;> simp
        rw [hmk₂, map_smul, smul_smul]
        norm_num [Complex.I_mul_I]
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply]
        rw [CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        rw [map_add, smul_zero, Prod.mk_zero_zero, map_zero, map_zero, zero_add,
          CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        simp only [smul_zero, Prod.mk_zero_zero, map_zero, zero_add])
    (by
      ext x
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply]
        rw [CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        rw [map_add, Prod.mk_zero_zero, map_zero, map_zero, add_zero]
        have hmk₁ : (Complex.I • x, (0 : V)) = Complex.I • (x, (0 : V)) := by
          apply Prod.ext <;> simp
        rw [hmk₁, map_smul, map_smul, CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        rw [Prod.mk_zero_zero, map_zero, add_zero]
        have hmk₂ : ((-Complex.I) • x, (0 : V)) = (-Complex.I) • (x, (0 : V)) := by
          apply Prod.ext <;> simp
        rw [hmk₂, map_smul, smul_smul]
        norm_num [Complex.I_mul_I]
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply]
        rw [CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        rw [map_add, smul_zero, Prod.mk_zero_zero, map_zero, map_zero, zero_add,
          CliffordAlgebra.lift_ι_apply]
        dsimp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.id_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        simp only [smul_zero, Prod.mk_zero_zero, map_zero, zero_add])

end ComplexTwist

section Real4DChiralityTwist

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- 4D left chiral product `γ = γ₀ γ₁ γ₂ γ₃` in `Cl(Q ⊕ Q)`. -/
def gammaLeft (g : LinearMap.BilinForm R V) (b : Module.Basis (Fin 4) R V) :
    CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) :=
  CliffordAlgebra.ι _ (b 0, 0) * CliffordAlgebra.ι _ (b 1, 0) *
    CliffordAlgebra.ι _ (b 2, 0) * CliffordAlgebra.ι _ (b 3, 0)

/-- 4D right chiral product `γ̃ = γ̃₀ γ̃₁ γ̃₂ γ̃₃` in `Cl(Q ⊕ Q)`. -/
def gammaRight (g : LinearMap.BilinForm R V) (b : Module.Basis (Fin 4) R V) :
    CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) :=
  CliffordAlgebra.ι _ (0, b 0) * CliffordAlgebra.ι _ (0, b 1) *
    CliffordAlgebra.ι _ (0, b 2) * CliffordAlgebra.ι _ (0, b 3)

/-- 4D total chirality `Γ_cl = γ γ̃` in `Cl(Q ⊕ Q)` (Eq. 4.35). -/
def gammaTotal (g : LinearMap.BilinForm R V) (b : Module.Basis (Fin 4) R V) :
    CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) :=
  gammaLeft g b * gammaRight g b

/-- 4D left chiral product `γ'` in `Cl((-Q) ⊕ Q)`. -/
def gammaLeftNeg (g : LinearMap.BilinForm R V) (b : Module.Basis (Fin 4) R V) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  CliffordAlgebra.ι _ (b 0, 0) * CliffordAlgebra.ι _ (b 1, 0) *
    CliffordAlgebra.ι _ (b 2, 0) * CliffordAlgebra.ι _ (b 3, 0)

private lemma clifford_inl_sq_of_orth {Q₁ Q₂ : QuadraticForm R V}
    (u : V) (hu : Q₁ u = 1) :
    CliffordAlgebra.ι (Q₁.prod Q₂) (u, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (u, 0) = 1 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [QuadraticMap.prod_apply, hu]

private lemma clifford_inl_sq_neg_of_orth {Q₁ Q₂ : QuadraticForm R V}
    (u : V) (hu : Q₁ u = 1) :
    CliffordAlgebra.ι ((-Q₁).prod Q₂) (u, 0) * CliffordAlgebra.ι ((-Q₁).prod Q₂) (u, 0) = -1 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [QuadraticMap.prod_apply, hu]

private lemma clifford_inl_anticomm_of_orth (g : LinearMap.BilinForm R V)
    (hg : ∀ u v, g u v = g v u) (b : Module.Basis (Fin 4) R V)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (Q₁ Q₂ : QuadraticForm R V) (hQ₁ : Q₁ = g.toQuadraticMap ∨ Q₁ = -g.toQuadraticMap)
    {i j : Fin 4} (hij : i ≠ j) :
    CliffordAlgebra.ι (Q₁.prod Q₂) (b i, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b j, 0) =
      -(CliffordAlgebra.ι (Q₁.prod Q₂) (b j, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b i, 0)) := by
  apply eq_neg_of_add_eq_zero_left
  apply CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
  rw [QuadraticMap.isOrtho_def]
  simp only [QuadraticMap.prod_apply, add_zero, map_zero]
  rcases hQ₁ with rfl | rfl
  · simp only [LinearMap.BilinMap.toQuadraticMap_apply, Prod.fst_add, Prod.snd_add,
      map_add, LinearMap.add_apply]
    rw [horth i i, horth j j, horth i j, if_neg hij, hg (b j) (b i), horth i j, if_neg hij]
    simp only [add_zero, map_zero]
    abel
  · simp only [QuadraticMap.neg_apply, LinearMap.BilinMap.toQuadraticMap_apply, Prod.fst_add,
      Prod.snd_add, map_add, LinearMap.add_apply]
    rw [horth i i, horth j j, horth i j, if_neg hij, hg (b j) (b i), horth i j, if_neg hij]
    simp only [add_zero, map_zero]
    abel

/-- Generic 4-factor product square: if `a₀, a₁, a₂, a₃` pairwise anticommute and `aᵢ² = s`,
then `(a₀ a₁ a₂ a₃)² = s⁴`. -/
private lemma four_anticomm_prod_sq {A : Type*} [Ring A] {a₀ a₁ a₂ a₃ s : A}
    (hs : ∀ x, x * s = s * x)
    (h0sq : a₀ * a₀ = s) (h1sq : a₁ * a₁ = s) (h2sq : a₂ * a₂ = s) (h3sq : a₃ * a₃ = s)
    (h01 : a₀ * a₁ = -(a₁ * a₀)) (h02 : a₀ * a₂ = -(a₂ * a₀)) (h03 : a₀ * a₃ = -(a₃ * a₀))
    (h12 : a₁ * a₂ = -(a₂ * a₁)) (h13 : a₁ * a₃ = -(a₃ * a₁)) (h23 : a₂ * a₃ = -(a₃ * a₂)) :
    (a₀ * a₁ * a₂ * a₃) * (a₀ * a₁ * a₂ * a₃) = s * s * s * s := by
  have h30 : a₃ * a₀ = -(a₀ * a₃) := by rw [h03, neg_neg]
  have h20 : a₂ * a₀ = -(a₀ * a₂) := by rw [h02, neg_neg]
  have h10 : a₁ * a₀ = -(a₀ * a₁) := by rw [h01, neg_neg]
  have h31 : a₃ * a₁ = -(a₁ * a₃) := by rw [h13, neg_neg]
  have h21 : a₂ * a₁ = -(a₁ * a₂) := by rw [h12, neg_neg]
  have h32 : a₃ * a₂ = -(a₂ * a₃) := by rw [h23, neg_neg]
  have hswap0 : a₁ * a₂ * a₃ * a₀ = -(a₀ * a₁ * a₂ * a₃) := by
    calc
      a₁ * a₂ * a₃ * a₀ = a₁ * a₂ * (a₃ * a₀) := by simp only [mul_assoc]
      _ = -(a₁ * (a₂ * a₀) * a₃) := by rw [h30]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = a₁ * a₀ * a₂ * a₃ := by rw [h20]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(a₀ * a₁ * a₂ * a₃) := by rw [h10]; simp only [mul_neg, neg_mul, mul_assoc]
  have hswap1 : a₂ * a₃ * a₁ = a₁ * a₂ * a₃ := by
    calc
      a₂ * a₃ * a₁ = a₂ * (a₃ * a₁) := by simp only [mul_assoc]
      _ = -(a₂ * a₁ * a₃) := by rw [h31]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = a₁ * a₂ * a₃ := by rw [h21]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
  calc
    (a₀ * a₁ * a₂ * a₃) * (a₀ * a₁ * a₂ * a₃) =
        a₀ * (a₁ * a₂ * a₃ * a₀) * (a₁ * a₂ * a₃) := by simp only [mul_assoc]
    _ = -(a₀ * (a₀ * a₁ * a₂ * a₃) * (a₁ * a₂ * a₃)) := by
      rw [hswap0, mul_neg, neg_mul]
    _ = -(s * (a₁ * (a₂ * a₃ * a₁) * a₂ * a₃)) := by
      have h00 : a₀ * (a₀ * a₁ * a₂ * a₃) * (a₁ * a₂ * a₃) =
          (a₀ * a₀) * (a₁ * (a₂ * a₃ * a₁) * a₂ * a₃) := by simp only [mul_assoc]
      rw [h00, h0sq]
    _ = -(s * ((a₁ * a₁) * (a₂ * a₃ * a₂) * a₃)) := by
      rw [hswap1]
      simp only [mul_assoc]
    _ = -(s * (s * (-(s * (a₃ * a₃))))) := by
      rw [h1sq, show a₂ * a₃ * a₂ = -(a₂ * a₂ * a₃) by
        rw [mul_assoc, h32, mul_neg, mul_assoc], h2sq]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = s * s * s * s := by
      rw [h3sq]
      simp only [mul_neg, neg_mul, neg_neg, mul_assoc]

theorem gammaLeft_sq (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    gammaLeft g b * gammaLeft g b = 1 := by
  dsimp [gammaLeft]
  have h := four_anticomm_prod_sq (s := (1 : CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap)))
    (fun x => by simp)
    (clifford_inl_sq_of_orth (b 0) (by simp [horth]))
    (clifford_inl_sq_of_orth (b 1) (by simp [horth]))
    (clifford_inl_sq_of_orth (b 2) (by simp [horth]))
    (clifford_inl_sq_of_orth (b 3) (by simp [horth]))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inl rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inl rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inl rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inl rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inl rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inl rfl) (by decide))
  simpa using h

theorem gammaLeftNeg_sq (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    gammaLeftNeg g b * gammaLeftNeg g b = 1 := by
  dsimp [gammaLeftNeg]
  have h := four_anticomm_prod_sq (s := (-1 : CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)))
    (fun x => by simp)
    (clifford_inl_sq_neg_of_orth (b 0) (by simp [horth]))
    (clifford_inl_sq_neg_of_orth (b 1) (by simp [horth]))
    (clifford_inl_sq_neg_of_orth (b 2) (by simp [horth]))
    (clifford_inl_sq_neg_of_orth (b 3) (by simp [horth]))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inr rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inr rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inr rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inr rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inr rfl) (by decide))
    (clifford_inl_anticomm_of_orth g hg b horth _ _ (Or.inr rfl) (by decide))
  simpa using h

/-- `γ` anticommutes with any left generator `ι (b k, 0)`. -/
private lemma gamma_anticomm_basis_inl (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (Q₁ Q₂ : QuadraticForm R V) (hQ₁ : Q₁ = g.toQuadraticMap ∨ Q₁ = -g.toQuadraticMap)
    (k : Fin 4) :
    (CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
        CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0)) *
      CliffordAlgebra.ι (Q₁.prod Q₂) (b k, 0) =
      -(CliffordAlgebra.ι (Q₁.prod Q₂) (b k, 0) *
        (CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
          CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0))) := by
  have h01 := clifford_inl_anticomm_of_orth g hg b horth Q₁ Q₂ hQ₁ (by decide : (0 : Fin 4) ≠ 1)
  have h02 := clifford_inl_anticomm_of_orth g hg b horth Q₁ Q₂ hQ₁ (by decide : (0 : Fin 4) ≠ 2)
  have h03 := clifford_inl_anticomm_of_orth g hg b horth Q₁ Q₂ hQ₁ (by decide : (0 : Fin 4) ≠ 3)
  have h12 := clifford_inl_anticomm_of_orth g hg b horth Q₁ Q₂ hQ₁ (by decide : (1 : Fin 4) ≠ 2)
  have h13 := clifford_inl_anticomm_of_orth g hg b horth Q₁ Q₂ hQ₁ (by decide : (1 : Fin 4) ≠ 3)
  have h23 := clifford_inl_anticomm_of_orth g hg b horth Q₁ Q₂ hQ₁ (by decide : (2 : Fin 4) ≠ 3)
  let e (i : Fin 4) := CliffordAlgebra.ι (Q₁.prod Q₂) (b i, 0)
  change (e 0 * e 1 * e 2 * e 3) * e k = -(e k * (e 0 * e 1 * e 2 * e 3))
  have h10 : e 1 * e 0 = -(e 0 * e 1) := by rw [h01, neg_neg]
  have h20 : e 2 * e 0 = -(e 0 * e 2) := by rw [h02, neg_neg]
  have h21 : e 2 * e 1 = -(e 1 * e 2) := by rw [h12, neg_neg]
  have h30 : e 3 * e 0 = -(e 0 * e 3) := by rw [h03, neg_neg]
  have h31 : e 3 * e 1 = -(e 1 * e 3) := by rw [h13, neg_neg]
  have h32 : e 3 * e 2 = -(e 2 * e 3) := by rw [h23, neg_neg]
  fin_cases k
  · calc
      (e 0 * e 1 * e 2 * e 3) * e 0 = e 0 * e 1 * e 2 * (e 3 * e 0) := by simp only [mul_assoc]
      _ = -(e 0 * e 1 * (e 2 * e 0) * e 3) := by
        conv_lhs => rw [h30]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = e 0 * (e 1 * e 0) * e 2 * e 3 := by
        conv_lhs => rw [h20]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(e 0 * (e 0 * e 1 * e 2 * e 3)) := by
        conv_lhs => rw [h10]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
  · calc
      (e 0 * e 1 * e 2 * e 3) * e 1 = e 0 * e 1 * e 2 * (e 3 * e 1) := by simp only [mul_assoc]
      _ = -(e 0 * e 1 * (e 2 * e 1) * e 3) := by
        conv_lhs => rw [h31]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = (e 0 * e 1) * e 1 * e 2 * e 3 := by
        conv_lhs => rw [h21]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(e 1 * (e 0 * e 1 * e 2 * e 3)) := by
        conv_lhs => rw [h01]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
  · calc
      (e 0 * e 1 * e 2 * e 3) * e 2 = e 0 * e 1 * e 2 * (e 3 * e 2) := by simp only [mul_assoc]
      _ = -(e 0 * (e 1 * e 2) * e 2 * e 3) := by
        conv_lhs => rw [h32]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = (e 0 * e 2) * e 1 * e 2 * e 3 := by
        conv_lhs => rw [h12]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(e 2 * (e 0 * e 1 * e 2 * e 3)) := by
        conv_lhs => rw [h02]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
  · calc
      (e 0 * e 1 * e 2 * e 3) * e 3 = e 0 * e 1 * (e 2 * e 3) * e 3 := by simp only [mul_assoc]
      _ = -(e 0 * (e 1 * e 3) * e 2 * e 3) := by
        conv_lhs => rw [h23]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = (e 0 * e 3) * e 1 * e 2 * e 3 := by
        conv_lhs => rw [h13]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(e 3 * (e 0 * e 1 * e 2 * e 3)) := by
        conv_lhs => rw [h03]
        simp only [e, mul_neg, neg_mul, neg_neg, mul_assoc]

theorem gammaLeft_anticomm_inl (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (u : V) :
    gammaLeft g b * CliffordAlgebra.ι _ (u, 0) =
      -(CliffordAlgebra.ι _ (u, 0) * gammaLeft g b) := by
  have hu : u = ∑ i : Fin 4, b.repr u i • b i := (b.sum_repr u).symm
  rw [hu]
  rw [show (∑ i : Fin 4, b.repr u i • b i, (0 : V)) =
      ∑ i : Fin 4, b.repr u i • (b i, (0 : V)) by
        apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := gamma_anticomm_basis_inl g hg b horth g.toQuadraticMap g.toQuadraticMap (Or.inl rfl) k
  dsimp [gammaLeft]
  rw [hk, smul_neg]

theorem gammaLeftNeg_anticomm_inl (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (u : V) :
    gammaLeftNeg g b * CliffordAlgebra.ι _ (u, 0) =
      -(CliffordAlgebra.ι _ (u, 0) * gammaLeftNeg g b) := by
  have hu : u = ∑ i : Fin 4, b.repr u i • b i := (b.sum_repr u).symm
  rw [hu]
  rw [show (∑ i : Fin 4, b.repr u i • b i, (0 : V)) =
      ∑ i : Fin 4, b.repr u i • (b i, (0 : V)) by
        apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := gamma_anticomm_basis_inl g hg b horth (-g.toQuadraticMap) g.toQuadraticMap (Or.inr rfl) k
  dsimp [gammaLeftNeg]
  rw [hk, smul_neg]

private lemma gamma_comm_inr {Q₁ Q₂ : QuadraticForm R V}
    (b : Module.Basis (Fin 4) R V) (v : V) :
    (CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
        CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0)) *
      CliffordAlgebra.ι (Q₁.prod Q₂) (0, v) =
      CliffordAlgebra.ι (Q₁.prod Q₂) (0, v) *
        (CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
          CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0)) := by
  have hswap (w : V) :
      CliffordAlgebra.ι (Q₁.prod Q₂) (w, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (0, v) =
        -(CliffordAlgebra.ι (Q₁.prod Q₂) (0, v) * CliffordAlgebra.ι (Q₁.prod Q₂) (w, 0)) := by
    apply eq_neg_of_add_eq_zero_left
    exact CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (QuadraticMap.IsOrtho.inl_inr w v)
  calc
    (CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
        CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0)) *
      CliffordAlgebra.ι (Q₁.prod Q₂) (0, v) =
        -(CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
          (CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (0, v)) *
          CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0)) := by
      rw [mul_assoc, hswap (b 3)]; noncomm_ring
    _ = CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) *
          (CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (0, v)) *
          CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0) := by
      rw [hswap (b 2)]; noncomm_ring
    _ = -(CliffordAlgebra.ι (Q₁.prod Q₂) (b 0, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (0, v)) *
          CliffordAlgebra.ι (Q₁.prod Q₂) (b 1, 0) *
          CliffordAlgebra.ι (Q₁.prod Q₂) (b 2, 0) * CliffordAlgebra.ι (Q₁.prod Q₂) (b 3, 0) := by
      rw [hswap (b 1)]; noncomm_ring
    _ = _ := by
      rw [hswap (b 0)]; noncomm_ring

theorem gammaLeft_comm_inr (g : LinearMap.BilinForm R V) (b : Module.Basis (Fin 4) R V) (v : V) :
    gammaLeft g b * CliffordAlgebra.ι _ (0, v) =
      CliffordAlgebra.ι _ (0, v) * gammaLeft g b :=
  gamma_comm_inr b v

theorem gammaLeftNeg_comm_inr (g : LinearMap.BilinForm R V) (b : Module.Basis (Fin 4) R V) (v : V) :
    gammaLeftNeg g b * CliffordAlgebra.ι _ (0, v) =
      CliffordAlgebra.ι _ (0, v) * gammaLeftNeg g b :=
  gamma_comm_inr b v

/-- Forward algebra map for the 4D real chirality twist (Witten Eq. 4.33). -/
private def wittenRealChiralityTwistFwd (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) →ₐ[R]
      CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  let γ' := gammaLeftNeg g b
  CliffordAlgebra.lift (g.toQuadraticMap.prod g.toQuadraticMap)
    ⟨LinearMap.coprod
        ((LinearMap.mulLeft R γ').comp
          ((CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap)).comp (LinearMap.inl R V V)))
        ((CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap)).comp (LinearMap.inr R V V)),
      fun ⟨u, v⟩ => by
        simp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.inl_apply, LinearMap.inr_apply, QuadraticMap.prod_apply,
          Algebra.algebraMap_eq_smul_one]
        have h_anti : CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, 0) * γ' =
            -(γ' * CliffordAlgebra.ι _ (u, 0)) := by
          rw [gammaLeftNeg_anticomm_inl g hg b horth u, neg_neg]
        have h1 : (γ' * CliffordAlgebra.ι _ (u, 0)) * (γ' * CliffordAlgebra.ι _ (u, 0)) =
            algebraMap R _ (g.toQuadraticMap u) := by
          calc
            _ = γ' * (CliffordAlgebra.ι _ (u, 0) * γ') * CliffordAlgebra.ι _ (u, 0) := by
              simp only [mul_assoc]
            _ = -(γ' * γ' * (CliffordAlgebra.ι _ (u, 0) * CliffordAlgebra.ι _ (u, 0))) := by
              rw [h_anti]; noncomm_ring
            _ = -(1 * algebraMap R _ (-g.toQuadraticMap u)) := by
              rw [gammaLeftNeg_sq g hg b horth, CliffordAlgebra.ι_sq_scalar]
              simp [QuadraticMap.prod_apply]
            _ = algebraMap R _ (g.toQuadraticMap u) := by simp
        have h2 : CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) *
            CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (0, v) =
            algebraMap R _ (g.toQuadraticMap v) := by
          rw [CliffordAlgebra.ι_sq_scalar]
          simp [QuadraticMap.prod_apply]
        have h12 : (γ' * CliffordAlgebra.ι _ (u, 0)) * CliffordAlgebra.ι _ (0, v) +
            CliffordAlgebra.ι _ (0, v) * (γ' * CliffordAlgebra.ι _ (u, 0)) = 0 := by
          have hcomm : CliffordAlgebra.ι _ (0, v) * γ' = γ' * CliffordAlgebra.ι _ (0, v) :=
            (gammaLeftNeg_comm_inr g b v).symm
          have horthuv : CliffordAlgebra.ι ((-g.toQuadraticMap).prod g.toQuadraticMap) (u, 0) *
              CliffordAlgebra.ι _ (0, v) +
              CliffordAlgebra.ι _ (0, v) * CliffordAlgebra.ι _ (u, 0) = 0 :=
            CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (QuadraticMap.IsOrtho.inl_inr u v)
          calc
            _ = γ' * (CliffordAlgebra.ι _ (u, 0) * CliffordAlgebra.ι _ (0, v) +
                CliffordAlgebra.ι _ (0, v) * CliffordAlgebra.ι _ (u, 0)) := by
              rw [mul_assoc, ← mul_assoc (CliffordAlgebra.ι _ (0, v)) γ', hcomm]
              noncomm_ring
            _ = 0 := by rw [horthuv, mul_zero]
        calc
          _ = (γ' * CliffordAlgebra.ι _ (u, 0)) * (γ' * CliffordAlgebra.ι _ (u, 0)) +
                ((γ' * CliffordAlgebra.ι _ (u, 0)) * CliffordAlgebra.ι _ (0, v) +
                  CliffordAlgebra.ι _ (0, v) * (γ' * CliffordAlgebra.ι _ (u, 0))) +
                CliffordAlgebra.ι _ (0, v) * CliffordAlgebra.ι _ (0, v) := by
            simp only [add_mul, mul_add]
            abel
          _ = (g.toQuadraticMap u + g.toQuadraticMap v) •
              (1 : CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)) := by
            rw [h1, h12, h2, add_zero, ← map_add, Algebra.algebraMap_eq_smul_one]⟩

/-- Inverse algebra map for the 4D real chirality twist (Witten Eq. 4.33). -/
private def wittenRealChiralityTwistBwd (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) →ₐ[R]
      CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) :=
  let γ := gammaLeft g b
  CliffordAlgebra.lift ((-g.toQuadraticMap).prod g.toQuadraticMap)
    ⟨LinearMap.coprod
        ((LinearMap.mulLeft R γ).comp
          ((CliffordAlgebra.ι (g.toQuadraticMap.prod g.toQuadraticMap)).comp (LinearMap.inl R V V)))
        ((CliffordAlgebra.ι (g.toQuadraticMap.prod g.toQuadraticMap)).comp (LinearMap.inr R V V)),
      fun ⟨u, v⟩ => by
        simp only [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.inl_apply, LinearMap.inr_apply, QuadraticMap.prod_apply,
          neg_apply, Algebra.algebraMap_eq_smul_one]
        have h_anti : CliffordAlgebra.ι (g.toQuadraticMap.prod g.toQuadraticMap) (u, 0) * γ =
            -(γ * CliffordAlgebra.ι _ (u, 0)) := by
          rw [gammaLeft_anticomm_inl g hg b horth u, neg_neg]
        have h1 : (γ * CliffordAlgebra.ι _ (u, 0)) * (γ * CliffordAlgebra.ι _ (u, 0)) =
            algebraMap R _ (-g.toQuadraticMap u) := by
          calc
            _ = γ * (CliffordAlgebra.ι _ (u, 0) * γ) * CliffordAlgebra.ι _ (u, 0) := by
              simp only [mul_assoc]
            _ = -(γ * γ * (CliffordAlgebra.ι _ (u, 0) * CliffordAlgebra.ι _ (u, 0))) := by
              rw [h_anti]; noncomm_ring
            _ = -(1 * algebraMap R _ (g.toQuadraticMap u)) := by
              rw [gammaLeft_sq g hg b horth, CliffordAlgebra.ι_sq_scalar]
              simp [QuadraticMap.prod_apply]
            _ = algebraMap R _ (-g.toQuadraticMap u) := by simp
        have h2 : CliffordAlgebra.ι (g.toQuadraticMap.prod g.toQuadraticMap) (0, v) *
            CliffordAlgebra.ι (g.toQuadraticMap.prod g.toQuadraticMap) (0, v) =
            algebraMap R _ (g.toQuadraticMap v) := by
          rw [CliffordAlgebra.ι_sq_scalar]
          simp [QuadraticMap.prod_apply]
        have h12 : (γ * CliffordAlgebra.ι _ (u, 0)) * CliffordAlgebra.ι _ (0, v) +
            CliffordAlgebra.ι _ (0, v) * (γ * CliffordAlgebra.ι _ (u, 0)) = 0 := by
          have hcomm : CliffordAlgebra.ι _ (0, v) * γ = γ * CliffordAlgebra.ι _ (0, v) :=
            (gammaLeft_comm_inr g b v).symm
          have horthuv : CliffordAlgebra.ι (g.toQuadraticMap.prod g.toQuadraticMap) (u, 0) *
              CliffordAlgebra.ι _ (0, v) +
              CliffordAlgebra.ι _ (0, v) * CliffordAlgebra.ι _ (u, 0) = 0 :=
            CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (QuadraticMap.IsOrtho.inl_inr u v)
          calc
            _ = γ * (CliffordAlgebra.ι _ (u, 0) * CliffordAlgebra.ι _ (0, v) +
                CliffordAlgebra.ι _ (0, v) * CliffordAlgebra.ι _ (u, 0)) := by
              rw [mul_assoc, ← mul_assoc (CliffordAlgebra.ι _ (0, v)) γ, hcomm]
              noncomm_ring
            _ = 0 := by rw [horthuv, mul_zero]
        calc
          _ = (γ * CliffordAlgebra.ι _ (u, 0)) * (γ * CliffordAlgebra.ι _ (u, 0)) +
                ((γ * CliffordAlgebra.ι _ (u, 0)) * CliffordAlgebra.ι _ (0, v) +
                  CliffordAlgebra.ι _ (0, v) * (γ * CliffordAlgebra.ι _ (u, 0))) +
                CliffordAlgebra.ι _ (0, v) * CliffordAlgebra.ι _ (0, v) := by
            simp only [add_mul, mul_add]
            abel
          _ = (-g.toQuadraticMap u + g.toQuadraticMap v) •
              (1 : CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap)) := by
            rw [h1, h12, h2, add_zero, ← map_add, Algebra.algebraMap_eq_smul_one]⟩

@[simp]
private lemma wittenRealChiralityTwistFwd_ι (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (u v : V) :
    wittenRealChiralityTwistFwd g hg b horth (CliffordAlgebra.ι _ (u, v)) =
      gammaLeftNeg g b * CliffordAlgebra.ι _ (u, 0) + CliffordAlgebra.ι _ (0, v) := by
  exact CliffordAlgebra.lift_ι_apply _ _ (u, v)

@[simp]
private lemma wittenRealChiralityTwistBwd_ι (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (u v : V) :
    wittenRealChiralityTwistBwd g hg b horth (CliffordAlgebra.ι _ (u, v)) =
      gammaLeft g b * CliffordAlgebra.ι _ (u, 0) + CliffordAlgebra.ι _ (0, v) := by
  exact CliffordAlgebra.lift_ι_apply _ _ (u, v)

/-- 4D real chirality twist `Cl(Q ⊕ Q) ≃ₐ[R] Cl((-Q) ⊕ Q)` (Witten Eq. 4.33):
`ι(u, v) ↦ γ' * ι'(u, 0) + ι'(0, v)` with inverse `ι'(u, v) ↦ γ * ι(u, 0) + ι(0, v)`. -/
def wittenRealChiralityTwist (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) ≃ₐ[R]
      CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
  let fwd := wittenRealChiralityTwistFwd g hg b horth
  let bwd := wittenRealChiralityTwistBwd g hg b horth
  have hγ_fwd : fwd (gammaLeft g b) = gammaLeftNeg g b := by
    dsimp [fwd, gammaLeft]
    rw [map_mul, map_mul, map_mul,
      wittenRealChiralityTwistFwd_ι g hg b horth (b 0) 0,
      wittenRealChiralityTwistFwd_ι g hg b horth (b 1) 0,
      wittenRealChiralityTwistFwd_ι g hg b horth (b 2) 0,
      wittenRealChiralityTwistFwd_ι g hg b horth (b 3) 0]
    simp only [Prod.mk_zero_zero, map_zero, add_zero]
    have h0 : CliffordAlgebra.ι _ (b 0, 0) * gammaLeftNeg g b =
        -(gammaLeftNeg g b * CliffordAlgebra.ι _ (b 0, 0)) := by
      rw [gammaLeftNeg_anticomm_inl g hg b horth (b 0), neg_neg]
    have h2 : CliffordAlgebra.ι _ (b 2, 0) * gammaLeftNeg g b =
        -(gammaLeftNeg g b * CliffordAlgebra.ι _ (b 2, 0)) := by
      rw [gammaLeftNeg_anticomm_inl g hg b horth (b 2), neg_neg]
    have hγsq := gammaLeftNeg_sq g hg b horth
    calc
      (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 0, 0)) *
          (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 1, 0)) *
          (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 2, 0)) *
          (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 3, 0)) =
          gammaLeftNeg g b * (CliffordAlgebra.ι _ (b 0, 0) * gammaLeftNeg g b) *
            CliffordAlgebra.ι _ (b 1, 0) * gammaLeftNeg g b *
            (CliffordAlgebra.ι _ (b 2, 0) * gammaLeftNeg g b) *
            CliffordAlgebra.ι _ (b 3, 0) := by
        simp only [mul_assoc]
      _ = (gammaLeftNeg g b * gammaLeftNeg g b) *
            (CliffordAlgebra.ι _ (b 0, 0) * CliffordAlgebra.ι _ (b 1, 0)) *
            (gammaLeftNeg g b * gammaLeftNeg g b) *
            (CliffordAlgebra.ι _ (b 2, 0) * CliffordAlgebra.ι _ (b 3, 0)) := by
        rw [h0, h2]
        simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = gammaLeftNeg g b := by
        rw [hγsq, one_mul, mul_one, ← mul_assoc]
        rfl
  have hγ_bwd : bwd (gammaLeftNeg g b) = gammaLeft g b := by
    dsimp [bwd, gammaLeftNeg]
    rw [map_mul, map_mul, map_mul,
      wittenRealChiralityTwistBwd_ι g hg b horth (b 0) 0,
      wittenRealChiralityTwistBwd_ι g hg b horth (b 1) 0,
      wittenRealChiralityTwistBwd_ι g hg b horth (b 2) 0,
      wittenRealChiralityTwistBwd_ι g hg b horth (b 3) 0]
    simp only [Prod.mk_zero_zero, map_zero, add_zero]
    have h0 : CliffordAlgebra.ι _ (b 0, 0) * gammaLeft g b =
        -(gammaLeft g b * CliffordAlgebra.ι _ (b 0, 0)) := by
      rw [gammaLeft_anticomm_inl g hg b horth (b 0), neg_neg]
    have h2 : CliffordAlgebra.ι _ (b 2, 0) * gammaLeft g b =
        -(gammaLeft g b * CliffordAlgebra.ι _ (b 2, 0)) := by
      rw [gammaLeft_anticomm_inl g hg b horth (b 2), neg_neg]
    have hγsq := gammaLeft_sq g hg b horth
    calc
      (gammaLeft g b * CliffordAlgebra.ι _ (b 0, 0)) *
          (gammaLeft g b * CliffordAlgebra.ι _ (b 1, 0)) *
          (gammaLeft g b * CliffordAlgebra.ι _ (b 2, 0)) *
          (gammaLeft g b * CliffordAlgebra.ι _ (b 3, 0)) =
          gammaLeft g b * (CliffordAlgebra.ι _ (b 0, 0) * gammaLeft g b) *
            CliffordAlgebra.ι _ (b 1, 0) * gammaLeft g b *
            (CliffordAlgebra.ι _ (b 2, 0) * gammaLeft g b) *
            CliffordAlgebra.ι _ (b 3, 0) := by
        simp only [mul_assoc]
      _ = (gammaLeft g b * gammaLeft g b) *
            (CliffordAlgebra.ι _ (b 0, 0) * CliffordAlgebra.ι _ (b 1, 0)) *
            (gammaLeft g b * gammaLeft g b) *
            (CliffordAlgebra.ι _ (b 2, 0) * CliffordAlgebra.ι _ (b 3, 0)) := by
        rw [h0, h2]
        simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = gammaLeft g b := by
        rw [hγsq, one_mul, mul_one, ← mul_assoc]
        rfl
  AlgEquiv.ofAlgHom fwd bwd
    (by
      ext x
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply]
        have hb : bwd (CliffordAlgebra.ι _ (x, (0 : V))) =
            gammaLeft g b * CliffordAlgebra.ι _ (x, 0) := by
          dsimp [bwd]
          rw [wittenRealChiralityTwistBwd_ι g hg b horth x 0]
          simp only [Prod.mk_zero_zero, map_zero, add_zero]
        have hf : fwd (CliffordAlgebra.ι _ (x, (0 : V))) =
            gammaLeftNeg g b * CliffordAlgebra.ι _ (x, 0) := by
          dsimp [fwd]
          rw [wittenRealChiralityTwistFwd_ι g hg b horth x 0]
          simp only [Prod.mk_zero_zero, map_zero, add_zero]
        rw [hb, map_mul, hγ_fwd, hf, ← mul_assoc, gammaLeftNeg_sq g hg b horth, one_mul]
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply]
        have hb : bwd (CliffordAlgebra.ι _ ((0 : V), x)) = CliffordAlgebra.ι _ (0, x) := by
          dsimp [bwd]
          rw [wittenRealChiralityTwistBwd_ι g hg b horth 0 x]
          simp only [Prod.mk_zero_zero, map_zero, mul_zero, zero_add]
        have hf : fwd (CliffordAlgebra.ι _ ((0 : V), x)) = CliffordAlgebra.ι _ (0, x) := by
          dsimp [fwd]
          rw [wittenRealChiralityTwistFwd_ι g hg b horth 0 x]
          simp only [Prod.mk_zero_zero, map_zero, mul_zero, zero_add]
        rw [hb, hf])
    (by
      ext x
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply]
        have hf : fwd (CliffordAlgebra.ι _ (x, (0 : V))) =
            gammaLeftNeg g b * CliffordAlgebra.ι _ (x, 0) := by
          dsimp [fwd]
          rw [wittenRealChiralityTwistFwd_ι g hg b horth x 0]
          simp only [Prod.mk_zero_zero, map_zero, add_zero]
        have hb : bwd (CliffordAlgebra.ι _ (x, (0 : V))) =
            gammaLeft g b * CliffordAlgebra.ι _ (x, 0) := by
          dsimp [bwd]
          rw [wittenRealChiralityTwistBwd_ι g hg b horth x 0]
          simp only [Prod.mk_zero_zero, map_zero, add_zero]
        rw [hf, map_mul, hγ_bwd, hb, ← mul_assoc, gammaLeft_sq g hg b horth, one_mul]
      · dsimp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply]
        have hf : fwd (CliffordAlgebra.ι _ ((0 : V), x)) = CliffordAlgebra.ι _ (0, x) := by
          dsimp [fwd]
          rw [wittenRealChiralityTwistFwd_ι g hg b horth 0 x]
          simp only [Prod.mk_zero_zero, map_zero, mul_zero, zero_add]
        have hb : bwd (CliffordAlgebra.ι _ ((0 : V), x)) = CliffordAlgebra.ι _ (0, x) := by
          dsimp [bwd]
          rw [wittenRealChiralityTwistBwd_ι g hg b horth 0 x]
          simp only [Prod.mk_zero_zero, map_zero, mul_zero, zero_add]
        rw [hf, hb])

/-- On a 4D orthonormal frame, `doubledCliffordToEnd (wittenRealChiralityTwist Γ_cl)` equals
`exteriorGradingOp = (-1)^deg` (Witten Eq. 4.35). -/
theorem doubledCliffordToEnd_wittenRealChiralityTwist_gammaTotal
    (g : LinearMap.BilinForm R V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) R V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    doubledCliffordToEnd g hg
        (wittenRealChiralityTwist g hg b horth (gammaTotal g b)) = exteriorGradingOp := by
  have htwist : wittenRealChiralityTwist g hg b horth (gammaTotal g b) =
      gammaLeftNeg g b *
        (CliffordAlgebra.ι _ (0, b 0) * CliffordAlgebra.ι _ (0, b 1) *
          CliffordAlgebra.ι _ (0, b 2) * CliffordAlgebra.ι _ (0, b 3)) := by
    dsimp [gammaTotal, gammaLeft, gammaRight, wittenRealChiralityTwist]
    simp only [map_mul, AlgEquiv.ofAlgHom_apply, wittenRealChiralityTwistFwd_ι,
      show ((0 : V), (0 : V)) = (0 : V × V) from rfl, map_zero, mul_zero, add_zero, zero_add]
    have h0 : CliffordAlgebra.ι _ (b 0, 0) * gammaLeftNeg g b =
        -(gammaLeftNeg g b * CliffordAlgebra.ι _ (b 0, 0)) := by
      rw [gammaLeftNeg_anticomm_inl g hg b horth (b 0), neg_neg]
    have h2 : CliffordAlgebra.ι _ (b 2, 0) * gammaLeftNeg g b =
        -(gammaLeftNeg g b * CliffordAlgebra.ι _ (b 2, 0)) := by
      rw [gammaLeftNeg_anticomm_inl g hg b horth (b 2), neg_neg]
    have hγsq := gammaLeftNeg_sq g hg b horth
    congr 1
    calc
      (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 0, 0)) *
            (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 1, 0)) *
            (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 2, 0)) *
            (gammaLeftNeg g b * CliffordAlgebra.ι _ (b 3, 0)) =
          gammaLeftNeg g b * (CliffordAlgebra.ι _ (b 0, 0) * gammaLeftNeg g b) *
            CliffordAlgebra.ι _ (b 1, 0) * gammaLeftNeg g b *
            (CliffordAlgebra.ι _ (b 2, 0) * gammaLeftNeg g b) *
            CliffordAlgebra.ι _ (b 3, 0) := by
        simp only [mul_assoc]
      _ = (gammaLeftNeg g b * gammaLeftNeg g b) *
            (CliffordAlgebra.ι _ (b 0, 0) * CliffordAlgebra.ι _ (b 1, 0)) *
            (gammaLeftNeg g b * gammaLeftNeg g b) *
            (CliffordAlgebra.ι _ (b 2, 0) * CliffordAlgebra.ι _ (b 3, 0)) := by
        rw [h0, h2]
        simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = gammaLeftNeg g b := by
        rw [hγsq, one_mul, mul_one, ← mul_assoc]
        rfl
  rw [htwist]
  let P (k : Fin 4) : Module.End R (ExteriorAlgebra R V) :=
    negCartanAction g (b k) * posCartanAction g (b k)
  have h_rearrange :
      doubledCliffordToEnd g hg
          (gammaLeftNeg g b *
            (CliffordAlgebra.ι _ (0, b 0) * CliffordAlgebra.ι _ (0, b 1) *
              CliffordAlgebra.ι _ (0, b 2) * CliffordAlgebra.ι _ (0, b 3))) =
        P 0 * P 1 * P 2 * P 3 := by
    dsimp [gammaLeftNeg]
    simp only [map_mul, doubledCliffordToEnd_ι,
      show negCartanAction g 0 = 0 from (negCartanActionMap g).map_zero,
      show posCartanAction g 0 = 0 from (posCartanActionMap g).map_zero,
      add_zero, zero_add]
    have h_np (a c : Fin 4) : negCartanAction g (b a) * posCartanAction g (b c) =
        -(posCartanAction g (b c) * negCartanAction g (b a)) :=
      eq_neg_of_add_eq_zero_left (negCartanAction_posCartanAction_anticomm g hg (b a) (b c))
    dsimp [P]
    have h30 := h_np 3 0
    have h31 := h_np 3 1
    have h32 := h_np 3 2
    have h20 := h_np 2 0
    have h21 := h_np 2 1
    have h10 := h_np 1 0
    calc
      (negCartanAction g (b 0) * negCartanAction g (b 1) *
            negCartanAction g (b 2) * negCartanAction g (b 3)) *
          (posCartanAction g (b 0) * posCartanAction g (b 1) *
            posCartanAction g (b 2) * posCartanAction g (b 3)) =
          negCartanAction g (b 0) * negCartanAction g (b 1) * negCartanAction g (b 2) *
            (negCartanAction g (b 3) * posCartanAction g (b 0)) *
            posCartanAction g (b 1) * posCartanAction g (b 2) * posCartanAction g (b 3) := by
        simp only [mul_assoc]
      _ = -(negCartanAction g (b 0) * negCartanAction g (b 1) * negCartanAction g (b 2) *
            posCartanAction g (b 0) * (negCartanAction g (b 3) * posCartanAction g (b 1)) *
            posCartanAction g (b 2) * posCartanAction g (b 3)) := by
        rw [h30]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      _ = negCartanAction g (b 0) * negCartanAction g (b 1) * negCartanAction g (b 2) *
            posCartanAction g (b 0) * posCartanAction g (b 1) *
            (negCartanAction g (b 3) * posCartanAction g (b 2)) *
            posCartanAction g (b 3) := by
        rw [h31]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      _ = -(negCartanAction g (b 0) * negCartanAction g (b 1) *
            (negCartanAction g (b 2) * posCartanAction g (b 0)) * posCartanAction g (b 1) *
            posCartanAction g (b 2) * (negCartanAction g (b 3) * posCartanAction g (b 3))) := by
        rw [h32]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      _ = negCartanAction g (b 0) * negCartanAction g (b 1) * posCartanAction g (b 0) *
            (negCartanAction g (b 2) * posCartanAction g (b 1)) *
            posCartanAction g (b 2) * (negCartanAction g (b 3) * posCartanAction g (b 3)) := by
        rw [h20]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      _ = -(negCartanAction g (b 0) * (negCartanAction g (b 1) * posCartanAction g (b 0)) *
            posCartanAction g (b 1) * (negCartanAction g (b 2) * posCartanAction g (b 2)) *
            (negCartanAction g (b 3) * posCartanAction g (b 3))) := by
        rw [h21]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      _ = (negCartanAction g (b 0) * posCartanAction g (b 0)) *
            (negCartanAction g (b 1) * posCartanAction g (b 1)) *
            (negCartanAction g (b 2) * posCartanAction g (b 2)) *
            (negCartanAction g (b 3) * posCartanAction g (b 3)) := by
        rw [h10]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
  rw [h_rearrange]
  have hP_one (k : Fin 4) : P k 1 = -(1 : ExteriorAlgebra R V) := by
    dsimp [P, negCartanAction, posCartanAction]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      exteriorWedge_apply, mul_one, exteriorContract_one, add_zero, exteriorContract_iota,
      horth k k, ite_true, one_smul]
    rw [show ExteriorAlgebra.ι R (b k) * ExteriorAlgebra.ι R (b k) = 0 by
      exact ExteriorAlgebra.ι_sq_zero (b k)]
    simp
  have hP_wedge_diag (k : Fin 4) :
      P k * exteriorWedge R (b k) = -(exteriorWedge R (b k) * P k) := by
    dsimp [P, negCartanAction, posCartanAction]
    have h_ew : exteriorWedge R (b k) * exteriorWedge R (b k) = 0 := exteriorWedge_sq R (b k)
    have h_ic : exteriorContract (g (b k)) * exteriorContract (g (b k)) = 0 :=
      exteriorContract_sq (g (b k))
    have h_car : exteriorContract (g (b k)) * exteriorWedge R (b k) +
        exteriorWedge R (b k) * exteriorContract (g (b k)) = 1 := by
      simpa [horth k k] using exterior_cartan_homotopy_car (g (b k)) (b k)
    have h_ei : exteriorWedge R (b k) * exteriorContract (g (b k)) * exteriorWedge R (b k) =
        exteriorWedge R (b k) := by
      rw [mul_assoc, eq_sub_of_add_eq h_car, mul_sub, mul_one, ← mul_assoc, h_ew, zero_mul,
        sub_zero]
    have h_lhs : (exteriorWedge R (b k) - exteriorContract (g (b k))) *
        (exteriorWedge R (b k) + exteriorContract (g (b k))) * exteriorWedge R (b k) =
        exteriorWedge R (b k) := by
      calc
        _ = exteriorWedge R (b k) * exteriorContract (g (b k)) * exteriorWedge R (b k) +
              (exteriorWedge R (b k) * exteriorWedge R (b k)) * exteriorWedge R (b k) -
              exteriorContract (g (b k)) * (exteriorWedge R (b k) * exteriorWedge R (b k)) -
              (exteriorContract (g (b k)) * exteriorContract (g (b k))) * exteriorWedge R (b k) := by
          simp only [sub_mul, mul_add, add_mul, mul_assoc]
          abel
        _ = exteriorWedge R (b k) := by
          rw [h_ei, h_ew, h_ic, zero_mul, mul_zero, add_zero, sub_zero, sub_zero]
    have h_rhs : exteriorWedge R (b k) *
        ((exteriorWedge R (b k) - exteriorContract (g (b k))) *
          (exteriorWedge R (b k) + exteriorContract (g (b k)))) = -exteriorWedge R (b k) := by
      calc
        _ = (exteriorWedge R (b k) * exteriorWedge R (b k)) * exteriorWedge R (b k) +
              (exteriorWedge R (b k) * exteriorWedge R (b k)) * exteriorContract (g (b k)) -
              exteriorWedge R (b k) * exteriorContract (g (b k)) * exteriorWedge R (b k) -
              exteriorWedge R (b k) * (exteriorContract (g (b k)) * exteriorContract (g (b k))) := by
          apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub]; abel
        _ = -exteriorWedge R (b k) := by
          simp only [h_ew, h_ic, zero_mul, mul_zero, zero_add, sub_zero, zero_sub, h_ei]
    rw [h_lhs, h_rhs, neg_neg]
  have hP_wedge_off {k j : Fin 4} (hkj : k ≠ j) :
      P k * exteriorWedge R (b j) = exteriorWedge R (b j) * P k := by
    dsimp [P, negCartanAction, posCartanAction]
    have h_ew : exteriorWedge R (b k) * exteriorWedge R (b j) =
        -(exteriorWedge R (b j) * exteriorWedge R (b k)) :=
      eq_neg_of_add_eq_zero_left (exteriorWedge_anticomm R (b k) (b j))
    have h_ic : exteriorContract (g (b k)) * exteriorWedge R (b j) =
        -(exteriorWedge R (b j) * exteriorContract (g (b k))) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [horth k j, hkj] using exterior_cartan_homotopy_car (g (b k)) (b j)
    have h_mul_ew : exteriorWedge R (b k) * exteriorWedge R (b j) =
        -(exteriorWedge R (b j) * exteriorWedge R (b k)) := h_ew
    have h_comm_sum :
        (exteriorWedge R (b k) + exteriorContract (g (b k))) * exteriorWedge R (b j) =
          -(exteriorWedge R (b j) * (exteriorWedge R (b k) + exteriorContract (g (b k)))) := by
      rw [add_mul, h_ew, h_ic, mul_add]; abel
    have h_comm_sub :
        (exteriorWedge R (b k) - exteriorContract (g (b k))) * exteriorWedge R (b j) =
          -(exteriorWedge R (b j) * (exteriorWedge R (b k) - exteriorContract (g (b k)))) := by
      rw [sub_mul, h_ew, h_ic, mul_sub]; abel
    calc
      (exteriorWedge R (b k) - exteriorContract (g (b k))) *
          (exteriorWedge R (b k) + exteriorContract (g (b k))) * exteriorWedge R (b j) =
          (exteriorWedge R (b k) - exteriorContract (g (b k))) *
            ((exteriorWedge R (b k) + exteriorContract (g (b k))) * exteriorWedge R (b j)) := by
        rw [mul_assoc]
      _ = -(((exteriorWedge R (b k) - exteriorContract (g (b k))) * exteriorWedge R (b j)) *
            (exteriorWedge R (b k) + exteriorContract (g (b k)))) := by
        rw [h_comm_sum]; apply LinearMap.ext; intro ω
        simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply, map_neg, map_add, map_sub, neg_neg]
      _ = exteriorWedge R (b j) *
          ((exteriorWedge R (b k) - exteriorContract (g (b k))) *
            (exteriorWedge R (b k) + exteriorContract (g (b k)))) := by
        rw [h_comm_sub]; apply LinearMap.ext; intro ω
        simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply, map_neg, map_add, map_sub, neg_neg]
        abel
  apply eq_exteriorGradingOp_of_anticomm
  · simp only [Module.End.mul_apply, hP_one 3, map_neg, hP_one 2, neg_neg, hP_one 1,
      hP_one 0]
  · intro v
    have hv : v = ∑ j : Fin 4, b.repr v j • b j := (b.sum_repr v).symm
    rw [hv]
    have hex : exteriorWedge R (∑ j : Fin 4, b.repr v j • b j) =
        ∑ j : Fin 4, b.repr v j • exteriorWedge R (b j) := by
      apply LinearMap.ext
      intro ω
      simp only [exteriorWedge_apply, map_sum, map_smul, Finset.sum_mul, smul_mul_assoc,
        LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hex, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add]
    have hj_anti : (P 0 * P 1 * P 2 * P 3) * exteriorWedge R (b j) +
        exteriorWedge R (b j) * (P 0 * P 1 * P 2 * P 3) = 0 := by
      rw [add_eq_zero_iff_eq_neg]
      fin_cases j
      · calc
          P 0 * P 1 * P 2 * P 3 * exteriorWedge R (b 0) =
              P 0 * P 1 * P 2 * (exteriorWedge R (b 0) * P 3) := by
            rw [mul_assoc (P 0 * P 1 * P 2), hP_wedge_off (by decide : (3 : Fin 4) ≠ 0)]
          _ = P 0 * P 1 * (exteriorWedge R (b 0) * P 2) * P 3 := by
            rw [← mul_assoc (P 0 * P 1 * P 2), mul_assoc (P 0 * P 1),
              hP_wedge_off (by decide : (2 : Fin 4) ≠ 0), ← mul_assoc (P 0 * P 1)]
          _ = P 0 * (exteriorWedge R (b 0) * P 1) * P 2 * P 3 := by
            rw [← mul_assoc (P 0 * P 1), mul_assoc (P 0) (P 1),
              hP_wedge_off (by decide : (1 : Fin 4) ≠ 0), ← mul_assoc (P 0)]
          _ = -(exteriorWedge R (b 0) * (P 0 * P 1 * P 2 * P 3)) := by
            rw [← mul_assoc (P 0), hP_wedge_diag 0]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      · calc
          P 0 * P 1 * P 2 * P 3 * exteriorWedge R (b 1) =
              P 0 * P 1 * P 2 * (exteriorWedge R (b 1) * P 3) := by
            rw [mul_assoc (P 0 * P 1 * P 2), hP_wedge_off (by decide : (3 : Fin 4) ≠ 1)]
          _ = P 0 * P 1 * (exteriorWedge R (b 1) * P 2) * P 3 := by
            rw [← mul_assoc (P 0 * P 1 * P 2), mul_assoc (P 0 * P 1),
              hP_wedge_off (by decide : (2 : Fin 4) ≠ 1), ← mul_assoc (P 0 * P 1)]
          _ = -(P 0 * (exteriorWedge R (b 1) * P 1) * P 2 * P 3) := by
            rw [← mul_assoc (P 0 * P 1), mul_assoc (P 0) (P 1), hP_wedge_diag 1]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
          _ = -(exteriorWedge R (b 1) * (P 0 * P 1 * P 2 * P 3)) := by
            rw [← mul_assoc (P 0), hP_wedge_off (by decide : (0 : Fin 4) ≠ 1)]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      · calc
          P 0 * P 1 * P 2 * P 3 * exteriorWedge R (b 2) =
              P 0 * P 1 * P 2 * (exteriorWedge R (b 2) * P 3) := by
            rw [mul_assoc (P 0 * P 1 * P 2), hP_wedge_off (by decide : (3 : Fin 4) ≠ 2)]
          _ = -(P 0 * P 1 * (exteriorWedge R (b 2) * P 2) * P 3) := by
            rw [← mul_assoc (P 0 * P 1 * P 2), mul_assoc (P 0 * P 1), hP_wedge_diag 2]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
          _ = -(P 0 * (exteriorWedge R (b 2) * P 1) * P 2 * P 3) := by
            rw [← mul_assoc (P 0 * P 1), mul_assoc (P 0) (P 1),
              hP_wedge_off (by decide : (1 : Fin 4) ≠ 2), ← mul_assoc (P 0)]
          _ = -(exteriorWedge R (b 2) * (P 0 * P 1 * P 2 * P 3)) := by
            rw [← mul_assoc (P 0), hP_wedge_off (by decide : (0 : Fin 4) ≠ 2)]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
      · calc
          P 0 * P 1 * P 2 * P 3 * exteriorWedge R (b 3) =
              -(P 0 * P 1 * P 2 * (exteriorWedge R (b 3) * P 3)) := by
            rw [mul_assoc (P 0 * P 1 * P 2), hP_wedge_diag 3]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
          _ = -(P 0 * P 1 * (exteriorWedge R (b 3) * P 2) * P 3) := by
            rw [← mul_assoc (P 0 * P 1 * P 2), mul_assoc (P 0 * P 1),
              hP_wedge_off (by decide : (2 : Fin 4) ≠ 3), ← mul_assoc (P 0 * P 1)]
          _ = -(P 0 * (exteriorWedge R (b 3) * P 1) * P 2 * P 3) := by
            rw [← mul_assoc (P 0 * P 1), mul_assoc (P 0) (P 1),
              hP_wedge_off (by decide : (1 : Fin 4) ≠ 3), ← mul_assoc (P 0)]
          _ = -(exteriorWedge R (b 3) * (P 0 * P 1 * P 2 * P 3)) := by
            rw [← mul_assoc (P 0), hP_wedge_off (by decide : (0 : Fin 4) ≠ 3)]
            apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
    rw [hj_anti, smul_zero]

end Real4DChiralityTwist

/-!
### Full `AlgEquiv`: `Cl((-Q) ⊕ Q) ≃ₐ[𝕜] Module.End 𝕜 (ExteriorAlgebra 𝕜 V)`
-/

section DoubledCliffordEquiv

variable {𝕜 : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {I : Type*} [Fintype I] [LinearOrder I]

private def createList (g : LinearMap.BilinForm 𝕜 V) (b : Module.Basis I 𝕜 V) :
    List I → CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)
  | [] => 1
  | i :: L => cliffordCreate g (b i) * createList g b L

private def annihilateList (g : LinearMap.BilinForm 𝕜 V) (b : Module.Basis I 𝕜 V) :
    List I → CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)
  | [] => 1
  | i :: L => cliffordAnnihilate g (b i) * annihilateList g b L

private def vacuumProjList (g : LinearMap.BilinForm 𝕜 V) (b : Module.Basis I 𝕜 V) :
    List I → CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)
  | [] => 1
  | i :: L => (cliffordAnnihilate g (b i) * cliffordCreate g (b i)) * vacuumProjList g b L

private def wedgeList (b : Module.Basis I 𝕜 V) : List I → ExteriorAlgebra 𝕜 V
  | [] => 1
  | i :: L => ExteriorAlgebra.ι 𝕜 (b i) * wedgeList b L

private lemma doubledCliffordToEnd_createList (g : LinearMap.BilinForm 𝕜 V)
    (hg : ∀ u v, g u v = g v u) (b : Module.Basis I 𝕜 V) (L : List I) (ω : ExteriorAlgebra 𝕜 V) :
    doubledCliffordToEnd g hg (createList g b L) ω = wedgeList b L * ω := by
  induction L with
  | nil => simp [createList, wedgeList]
  | cons i L ih =>
    simp only [createList, map_mul, doubledCliffordToEnd_create, Module.End.mul_apply,
      exteriorWedge_apply, ih, wedgeList, mul_assoc]

private lemma exteriorContract_wedgeList_notMem (g : LinearMap.BilinForm 𝕜 V)
    (b : Module.Basis I 𝕜 V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    {i : I} {L : List I} (hi : i ∉ L) :
    exteriorContract (g (b i)) (wedgeList b L) = 0 := by
  induction L with
  | nil => simp [wedgeList]
  | cons j L ih =>
    have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
    have hiL : i ∉ L := fun h => hi (List.mem_cons_of_mem j h)
    simp only [wedgeList]
    change exteriorContract (g (b i)) (exteriorWedge 𝕜 (b j) (wedgeList b L)) = 0
    rw [exteriorContract_wedge_apply, horth i j, if_neg hij, zero_smul, zero_sub, ih hiL,
      map_zero, neg_zero]

private lemma exteriorWedge_wedgeList_mem (b : Module.Basis I 𝕜 V)
    {i : I} {L : List I} (hi : i ∈ L) :
    ExteriorAlgebra.ι 𝕜 (b i) * wedgeList b L = 0 := by
  induction L with
  | nil => cases hi
  | cons j L ih =>
    simp only [wedgeList]
    rcases List.mem_cons.mp hi with rfl | hiL
    · rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    · have hswap : ExteriorAlgebra.ι 𝕜 (b i) * ExteriorAlgebra.ι 𝕜 (b j) =
          -(ExteriorAlgebra.ι 𝕜 (b j) * ExteriorAlgebra.ι 𝕜 (b i)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b i) (b j))
      rw [← mul_assoc, hswap, neg_mul, mul_assoc, ih hiL, mul_zero, neg_zero]

private lemma vacuumProjList_apply_subset (g : LinearMap.BilinForm 𝕜 V)
    (hg : ∀ u v, g u v = g v u) (b : Module.Basis I 𝕜 V)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (K L : List I) :
    doubledCliffordToEnd g hg (vacuumProjList g b K) (wedgeList b L) =
      if ∀ k ∈ K, k ∉ L then wedgeList b L else 0 := by
  induction K with
  | nil => simp [vacuumProjList]
  | cons k K ih =>
    simp only [vacuumProjList, map_mul, doubledCliffordToEnd_annihilate,
      doubledCliffordToEnd_create, Module.End.mul_apply, ih]
    by_cases hK : ∀ k' ∈ K, k' ∉ L
    · rw [if_pos hK]
      by_cases hk : k ∈ L
      · have hk_all : ¬ ∀ k' ∈ k :: K, k' ∉ L := fun h => h k List.mem_cons_self hk
        rw [if_neg hk_all]
        change exteriorContract (g (b k)) (ExteriorAlgebra.ι 𝕜 (b k) * wedgeList b L) = 0
        rw [exteriorWedge_wedgeList_mem b hk, map_zero]
      · have hk_all : ∀ k' ∈ k :: K, k' ∉ L := by
          intro k' hk'
          rcases List.mem_cons.mp hk' with rfl | hk'K
          · exact hk
          · exact hK k' hk'K
        rw [if_pos hk_all]
        change exteriorContract (g (b k)) (exteriorWedge 𝕜 (b k) (wedgeList b L)) = wedgeList b L
        rw [exteriorContract_wedge_apply, horth k k, if_pos rfl, one_smul,
          exteriorContract_wedgeList_notMem g b horth hk, map_zero, sub_zero]
    · rw [if_neg hK]
      have hk_all : ¬ ∀ k' ∈ k :: K, k' ∉ L := fun h => hK (fun k' hk' => h k' (List.mem_cons_of_mem k hk'))
      rw [if_neg hk_all, map_zero, map_zero]

private lemma annihilateList_wedgeList_eq (g : LinearMap.BilinForm 𝕜 V)
    (hg : ∀ u v, g u v = g v u) (b : Module.Basis I 𝕜 V)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    {L : List I} (hL : L.Nodup) :
    doubledCliffordToEnd g hg (annihilateList g b L.reverse) (wedgeList b L) = 1 := by
  induction L with
  | nil => simp [annihilateList, wedgeList]
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.reverse_cons]
    have happ (A B : List I) :
        annihilateList g b (A ++ B) = annihilateList g b A * annihilateList g b B := by
      induction A with
      | nil => simp [annihilateList]
      | cons x A ihA => simp [annihilateList, ihA, mul_assoc]
    rw [happ, map_mul, Module.End.mul_apply]
    have hi_one : doubledCliffordToEnd g hg (annihilateList g b [i]) (wedgeList b (i :: L)) =
        wedgeList b L := by
      simp only [annihilateList, mul_one, doubledCliffordToEnd_annihilate, wedgeList]
      change exteriorContract (g (b i)) (exteriorWedge 𝕜 (b i) (wedgeList b L)) = wedgeList b L
      rw [exteriorContract_wedge_apply, horth i i, if_pos rfl, one_smul,
        exteriorContract_wedgeList_notMem g b horth hL.1, map_zero, sub_zero]
    rw [hi_one]
    exact ih hL.2

private lemma annihilateList_mem_notMem_zero (g : LinearMap.BilinForm 𝕜 V)
    (hg : ∀ u v, g u v = g v u) (b : Module.Basis I 𝕜 V)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    {T U : List I} {i : I} (hiT : i ∈ T) (hiU : i ∉ U) :
    doubledCliffordToEnd g hg (annihilateList g b T) (wedgeList b U) = 0 := by
  induction T with
  | nil => cases hiT
  | cons j T ih =>
    simp only [annihilateList, map_mul, Module.End.mul_apply, doubledCliffordToEnd_annihilate]
    rcases List.mem_cons.mp hiT with rfl | hiT'
    · have hswap : ∀ (A : List I) (ω : ExteriorAlgebra 𝕜 V),
          doubledCliffordToEnd g hg (annihilateList g b A) (exteriorContract (g (b i)) ω) =
            (-1 : 𝕜) ^ A.length •
              exteriorContract (g (b i)) (doubledCliffordToEnd g hg (annihilateList g b A) ω) := by
        intro A ω
        induction A with
        | nil => simp [annihilateList]
        | cons k A ihA =>
          simp only [annihilateList, map_mul, doubledCliffordToEnd_annihilate,
            Module.End.mul_apply, List.length_cons]
          have hanti : exteriorContract (g (b k)) * exteriorContract (g (b i)) =
              -(exteriorContract (g (b i)) * exteriorContract (g (b k))) :=
            eq_neg_of_add_eq_zero_left (exteriorContract_anticomm (g (b k)) (g (b i)))
          rw [ihA]
          simp only [map_smul]
          have hstep : exteriorContract (g (b k)) (exteriorContract (g (b i))
              (doubledCliffordToEnd g hg (annihilateList g b A) ω)) =
              -(exteriorContract (g (b i)) (exteriorContract (g (b k))
                (doubledCliffordToEnd g hg (annihilateList g b A) ω))) := by
            change (exteriorContract (g (b k)) * exteriorContract (g (b i))) _ = _
            rw [hanti]
            rfl
          rw [hstep, smul_neg, ← neg_smul, pow_succ', neg_one_mul]
      have hcomm : exteriorContract (g (b i))
          (doubledCliffordToEnd g hg (annihilateList g b T) (wedgeList b U)) =
          (-1 : 𝕜) ^ T.length •
            doubledCliffordToEnd g hg (annihilateList g b T)
              (exteriorContract (g (b i)) (wedgeList b U)) := by
        rw [hswap T (wedgeList b U), smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow,
          one_smul]
      rw [hcomm, exteriorContract_wedgeList_notMem g b horth hiU, map_zero, smul_zero]
    · rw [ih hiT', map_zero]

private lemma annihilate_wedge_move_head (g : LinearMap.BilinForm 𝕜 V)
    (b : Module.Basis I 𝕜 V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (T : List I) {j : I} (hjT : j ∉ T) (R_tail : ExteriorAlgebra 𝕜 V)
    (hg : ∀ u v, g u v = g v u) :
    doubledCliffordToEnd g hg (annihilateList g b T) (ExteriorAlgebra.ι 𝕜 (b j) * R_tail) =
      (-1 : 𝕜) ^ T.length •
        (ExteriorAlgebra.ι 𝕜 (b j) * doubledCliffordToEnd g hg (annihilateList g b T) R_tail) := by
  induction T with
  | nil => simp [annihilateList]
  | cons t T ih =>
    have hjt : t ≠ j := fun h => hjT (h ▸ List.mem_cons_self)
    have hjT' : j ∉ T := fun h => hjT (List.mem_cons_of_mem t h)
    simp only [annihilateList, map_mul, doubledCliffordToEnd_annihilate, Module.End.mul_apply,
      List.length_cons, ih hjT', map_smul]
    have hcj : exteriorContract (g (b t))
        (ExteriorAlgebra.ι 𝕜 (b j) * doubledCliffordToEnd g hg (annihilateList g b T) R_tail) =
        -(ExteriorAlgebra.ι 𝕜 (b j) *
          exteriorContract (g (b t)) (doubledCliffordToEnd g hg (annihilateList g b T) R_tail)) := by
      change exteriorContract (g (b t)) (exteriorWedge 𝕜 (b j) _) = _
      rw [exteriorContract_wedge_apply, horth t j, if_neg hjt, zero_smul, zero_sub,
        exteriorWedge_apply]
    rw [hcj, smul_neg, ← neg_smul, pow_succ', neg_one_mul]

private lemma wedgeList_extract_unit (b : Module.Basis I 𝕜 V) {j : I} {U : List I}
    (hjU : j ∈ U) :
    ∃ (c : 𝕜) (U' : List I), c ≠ 0 ∧ (∀ x ∈ U', x ∈ U) ∧ U'.length + 1 = U.length ∧
      wedgeList b U = c • (ExteriorAlgebra.ι 𝕜 (b j) * wedgeList b U') := by
  induction U with
  | nil => cases hjU
  | cons u U ih =>
    rcases List.mem_cons.mp hjU with rfl | hjU'
    · exact ⟨1, U, one_ne_zero, fun x hx => List.mem_cons_of_mem j hx, rfl, by simp [wedgeList]⟩
    · obtain ⟨c, U', hc, hsub, hlen, heq⟩ := ih hjU'
      refine ⟨-c, u :: U', neg_ne_zero.mpr hc, ?_, by simp [hlen], ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxU'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem u (hsub x hxU')
      · simp only [wedgeList, heq, mul_smul_comm]
        have hswap : ExteriorAlgebra.ι 𝕜 (b u) * ExteriorAlgebra.ι 𝕜 (b j) =
            -(ExteriorAlgebra.ι 𝕜 (b j) * ExteriorAlgebra.ι 𝕜 (b u)) :=
          eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b u) (b j))
        rw [← mul_assoc, hswap, neg_mul, mul_assoc, smul_neg, ← neg_smul]

private lemma annihilateList_vacuumProj_off_diag (g : LinearMap.BilinForm 𝕜 V)
    (hg : ∀ u v, g u v = g v u) (b : Module.Basis I 𝕜 V)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (K T U : List I) (hK : ∀ i : I, i ∈ K)
    (hne : T.toFinset ≠ U.toFinset) :
    doubledCliffordToEnd g hg
        (vacuumProjList g b K * annihilateList g b T.reverse) (wedgeList b U) = 0 := by
  by_cases hsub : T.toFinset ⊆ U.toFinset
  · have hstrict : T.toFinset ⊂ U.toFinset := ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    obtain ⟨j, hjU_fs, hjT_fs⟩ := Finset.exists_of_ssubset hstrict
    have hjU : j ∈ U := List.mem_toFinset.mp hjU_fs
    have hjT : j ∉ T.reverse := by
      rw [List.mem_reverse]
      exact fun h => hjT_fs (List.mem_toFinset.mpr h)
    obtain ⟨c, U', _, _, _, hUeq⟩ := wedgeList_extract_unit b hjU
    rw [map_mul, Module.End.mul_apply, hUeq, map_smul,
      annihilate_wedge_move_head g b horth T.reverse hjT (wedgeList b U') hg,
      map_smul, map_smul]
    suffices hkill :
        doubledCliffordToEnd g hg (vacuumProjList g b K)
          (ExteriorAlgebra.ι 𝕜 (b j) *
            doubledCliffordToEnd g hg (annihilateList g b T.reverse) (wedgeList b U')) = 0 by
      rw [hkill, smul_zero, smul_zero]
    have hjK : j ∈ K := hK j
    have h_op_comm (k₁ k₂ : I) :
        (exteriorContract (g (b k₁)) * exteriorWedge 𝕜 (b k₁)) *
            (exteriorContract (g (b k₂)) * exteriorWedge 𝕜 (b k₂)) =
          (exteriorContract (g (b k₂)) * exteriorWedge 𝕜 (b k₂)) *
            (exteriorContract (g (b k₁)) * exteriorWedge 𝕜 (b k₁)) := by
      by_cases h12 : k₁ = k₂
      · subst h12; rfl
      · have h_ii : exteriorContract (g (b k₁)) * exteriorContract (g (b k₂)) =
            -(exteriorContract (g (b k₂)) * exteriorContract (g (b k₁))) :=
          eq_neg_of_add_eq_zero_left (exteriorContract_anticomm (g (b k₁)) (g (b k₂)))
        have h_ee : exteriorWedge 𝕜 (b k₁) * exteriorWedge 𝕜 (b k₂) =
            -(exteriorWedge 𝕜 (b k₂) * exteriorWedge 𝕜 (b k₁)) :=
          eq_neg_of_add_eq_zero_left (exteriorWedge_anticomm 𝕜 (b k₁) (b k₂))
        have h_ie (a c : I) (hac : a ≠ c) :
            exteriorContract (g (b a)) * exteriorWedge 𝕜 (b c) =
              -(exteriorWedge 𝕜 (b c) * exteriorContract (g (b a))) := by
          apply eq_neg_of_add_eq_zero_left
          simpa [horth a c, hac] using exterior_cartan_homotopy_car (g (b a)) (b c)
        have h_ei : exteriorWedge 𝕜 (b k₁) * exteriorContract (g (b k₂)) =
            -(exteriorContract (g (b k₂)) * exteriorWedge 𝕜 (b k₁)) := by
          rw [h_ie k₂ k₁ (Ne.symm h12), neg_neg]
        calc
          (exteriorContract (g (b k₁)) * exteriorWedge 𝕜 (b k₁)) *
              (exteriorContract (g (b k₂)) * exteriorWedge 𝕜 (b k₂)) =
              exteriorContract (g (b k₁)) *
                (exteriorWedge 𝕜 (b k₁) * exteriorContract (g (b k₂))) *
                exteriorWedge 𝕜 (b k₂) := by simp only [mul_assoc]
          _ = -((exteriorContract (g (b k₁)) * exteriorContract (g (b k₂))) *
                (exteriorWedge 𝕜 (b k₁) * exteriorWedge 𝕜 (b k₂))) := by
            rw [h_ei]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
          _ = -((exteriorContract (g (b k₂)) * exteriorContract (g (b k₁))) *
                (exteriorWedge 𝕜 (b k₂) * exteriorWedge 𝕜 (b k₁))) := by
            rw [h_ii, h_ee]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
          _ = -(exteriorContract (g (b k₂)) *
                (exteriorContract (g (b k₁)) * exteriorWedge 𝕜 (b k₂)) *
                exteriorWedge 𝕜 (b k₁)) := by simp only [mul_assoc]
          _ = (exteriorContract (g (b k₂)) * exteriorWedge 𝕜 (b k₂)) *
              (exteriorContract (g (b k₁)) * exteriorWedge 𝕜 (b k₁)) := by
            rw [h_ie k₁ k₂ h12]; apply LinearMap.ext; intro ω; simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
    have h_move_vac (A : List I) (ω : ExteriorAlgebra 𝕜 V) :
        doubledCliffordToEnd g hg (vacuumProjList g b A)
            ((exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j)) ω) =
          (exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j))
            (doubledCliffordToEnd g hg (vacuumProjList g b A) ω) := by
      induction A with
      | nil => simp [vacuumProjList]
      | cons a A ihA =>
        simp only [vacuumProjList, map_mul, doubledCliffordToEnd_annihilate,
          doubledCliffordToEnd_create]
        change (exteriorContract (g (b a)) * exteriorWedge 𝕜 (b a))
            (doubledCliffordToEnd g hg (vacuumProjList g b A)
              ((exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j)) ω)) =
          (exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j))
            ((exteriorContract (g (b a)) * exteriorWedge 𝕜 (b a))
              (doubledCliffordToEnd g hg (vacuumProjList g b A) ω))
        rw [ihA]
        change ((exteriorContract (g (b a)) * exteriorWedge 𝕜 (b a)) *
            (exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j))) _ =
          ((exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j)) *
            (exteriorContract (g (b a)) * exteriorWedge 𝕜 (b a))) _
        rw [h_op_comm a j]
    have h_vac_kill (A : List I) (hjA : j ∈ A) (ω : ExteriorAlgebra 𝕜 V) :
        doubledCliffordToEnd g hg (vacuumProjList g b A) (ExteriorAlgebra.ι 𝕜 (b j) * ω) = 0 := by
      induction A with
      | nil => cases hjA
      | cons a A ihA =>
        simp only [vacuumProjList, map_mul, doubledCliffordToEnd_annihilate,
          doubledCliffordToEnd_create]
        rcases List.mem_cons.mp hjA with rfl | hjA'
        · change (exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j))
              (doubledCliffordToEnd g hg (vacuumProjList g b A) (ExteriorAlgebra.ι 𝕜 (b j) * ω)) = 0
          rw [← h_move_vac A (ExteriorAlgebra.ι 𝕜 (b j) * ω)]
          have hw0 : (exteriorContract (g (b j)) * exteriorWedge 𝕜 (b j))
              (ExteriorAlgebra.ι 𝕜 (b j) * ω) = 0 := by
            change exteriorContract (g (b j)) (ExteriorAlgebra.ι 𝕜 (b j) *
              (ExteriorAlgebra.ι 𝕜 (b j) * ω)) = 0
            rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, map_zero]
          rw [hw0, map_zero]
        · change (exteriorContract (g (b a)) * exteriorWedge 𝕜 (b a))
              (doubledCliffordToEnd g hg (vacuumProjList g b A) (ExteriorAlgebra.ι 𝕜 (b j) * ω)) = 0
          rw [ihA hjA', map_zero]
    exact h_vac_kill K hjK _
  · rw [Finset.not_subset] at hsub
    obtain ⟨i, hiT, hiU⟩ := hsub
    have hiT' : i ∈ T.reverse := List.mem_reverse.mpr (List.mem_toFinset.mp hiT)
    have hiU' : i ∉ U := fun h => hiU (List.mem_toFinset.mpr h)
    rw [map_mul, Module.End.mul_apply,
      annihilateList_mem_notMem_zero g hg b horth hiT' hiU', map_zero]

private lemma list_prod_iota_eq_wedgeList (b : Module.Basis I 𝕜 V) :
    ∀ (n : ℕ) (f : Fin n → I),
      (List.ofFn fun i : Fin n => ExteriorAlgebra.ι 𝕜 (b (f i))).prod = wedgeList b (List.ofFn f)
  | 0, _ => by simp [wedgeList]
  | n + 1, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, wedgeList]
    rw [list_prod_iota_eq_wedgeList b n (fun j => f j.succ)]

private lemma basis_exteriorAlgebra_eq_wedgeList (b : Module.Basis I 𝕜 V) (S : Finset I) :
    b.ExteriorAlgebra S = wedgeList b (List.ofFn (fun j : Fin S.card => S.orderEmbOfFin rfl j)) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (n := S.card) rfl]
  dsimp [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_apply]
  exact list_prod_iota_eq_wedgeList b S.card (fun j => S.orderEmbOfFin rfl j)

/-- Surjectivity of `doubledCliffordToEnd` for any finite orthonormal basis `b`. -/
theorem doubledCliffordToEnd_surjective (g : LinearMap.BilinForm 𝕜 V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis I 𝕜 V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    Function.Surjective (doubledCliffordToEnd g hg) := by
  intro F
  let ord (S : Finset I) : List I := List.ofFn (fun j : Fin S.card => S.orderEmbOfFin rfl j)
  have hord_nodup (S : Finset I) : (ord S).Nodup := by
    rw [List.nodup_ofFn]
    exact (S.orderEmbOfFin rfl).injective
  have hord_mem (S : Finset I) (i : I) : i ∈ ord S ↔ i ∈ S := by
    simp only [ord, List.mem_ofFn]
    constructor
    · rintro ⟨j, rfl⟩
      exact Finset.orderEmbOfFin_mem S rfl j
    · intro hi
      have hrange := Finset.range_orderEmbOfFin S rfl
      rw [← Set.mem_range, hrange]
      exact Finset.mem_coe.mpr hi
  have hord_toFinset (S : Finset I) : (ord S).toFinset = S := by
    ext i
    simp [List.mem_toFinset, hord_mem]
  let K : List I := Finset.univ.toList
  have hK : ∀ i : I, i ∈ K := fun i => Finset.mem_toList.mpr (Finset.mem_univ i)
  let E_unit (S T : Finset I) : CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
    createList g b (ord S) * vacuumProjList g b K * annihilateList g b (ord T).reverse
  have hE_diag (S T : Finset I) :
      doubledCliffordToEnd g hg (E_unit S T) (b.ExteriorAlgebra T) = b.ExteriorAlgebra S := by
    dsimp [E_unit]
    rw [mul_assoc, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      basis_exteriorAlgebra_eq_wedgeList b T,
      annihilateList_wedgeList_eq g hg b horth (hord_nodup T)]
    have hvac1 : doubledCliffordToEnd g hg (vacuumProjList g b K) 1 = 1 := by
      have h1 : (1 : ExteriorAlgebra 𝕜 V) = wedgeList b [] := rfl
      rw [h1, vacuumProjList_apply_subset g hg b horth K []]
      simp [wedgeList]
    rw [hvac1, doubledCliffordToEnd_createList, mul_one, ← basis_exteriorAlgebra_eq_wedgeList b S]
  have hE_off (S T U : Finset I) (hTU : T ≠ U) :
      doubledCliffordToEnd g hg (E_unit S T) (b.ExteriorAlgebra U) = 0 := by
    dsimp [E_unit]
    rw [mul_assoc, map_mul, Module.End.mul_apply, basis_exteriorAlgebra_eq_wedgeList b U]
    have hne : (ord T).toFinset ≠ (ord U).toFinset := by
      rwa [hord_toFinset, hord_toFinset]
    rw [annihilateList_vacuumProj_off_diag g hg b horth K (ord T) (ord U) hK hne, map_zero]
  let x : CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) :=
    ∑ T : Finset I, ∑ S : Finset I, ((b.ExteriorAlgebra).repr (F (b.ExteriorAlgebra T)) S) • E_unit S T
  refine ⟨x, ?_⟩
  apply (b.ExteriorAlgebra).ext
  intro U
  simp only [x, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have hU_term (T : Finset I) :
      (∑ S : Finset I, ((b.ExteriorAlgebra).repr (F (b.ExteriorAlgebra T)) S) •
        doubledCliffordToEnd g hg (E_unit S T) (b.ExteriorAlgebra U)) =
        if T = U then F (b.ExteriorAlgebra U) else 0 := by
    split_ifs with hTU
    · subst hTU
      simp only [hE_diag _ T]
      exact (b.ExteriorAlgebra).sum_repr (F (b.ExteriorAlgebra T))
    · refine Finset.sum_eq_zero fun S _ => ?_
      rw [hE_off S T U hTU, smul_zero]
  simp_rw [hU_term]
  simp

/-- Full algebra isomorphism `Cl(V ⊕ V, (-Q) ⊕ Q) ≃ₐ[𝕜] Module.End 𝕜 (ExteriorAlgebra 𝕜 V)`
for any finite orthonormal basis `b` over a field `𝕜` with `Invertible (2 : 𝕜)`. -/
def doubledCliffordEquivEnd (g : LinearMap.BilinForm 𝕜 V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis I 𝕜 V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap) ≃ₐ[𝕜]
      Module.End 𝕜 (ExteriorAlgebra 𝕜 V) :=
  let φ := doubledCliffordToEnd g hg
  have hsurj : Function.Surjective φ := doubledCliffordToEnd_surjective g hg b horth
  have hfin_ext : Module.finrank 𝕜 (ExteriorAlgebra 𝕜 V) = 2 ^ Fintype.card I := by
    rw [Module.finrank_eq_card_basis b.ExteriorAlgebra, Fintype.card_finset]
  have hfin_cl :
      Module.finrank 𝕜 (CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)) =
        2 ^ (2 * Fintype.card I) := by
    letI : LinearOrder (I ⊕ I) := LinearOrder.lift'
      (fun x : I ⊕ I => match x with | Sum.inl i => toLex (false, i) | Sum.inr i => toLex (true, i))
      (by rintro (a | a) (b | b) h <;> simp_all)
    rw [(CliffordAlgebra.equivExterior ((-g.toQuadraticMap).prod g.toQuadraticMap)).finrank_eq]
    rw [Module.finrank_eq_card_basis (b.prod b).ExteriorAlgebra, Fintype.card_finset,
      Fintype.card_sum, two_mul]
  haveI : Module.Finite 𝕜 (ExteriorAlgebra 𝕜 V) := Module.Finite.of_basis b.ExteriorAlgebra
  have hfin_end :
      Module.finrank 𝕜 (Module.End 𝕜 (ExteriorAlgebra 𝕜 V)) = 2 ^ (2 * Fintype.card I) := by
    rw [Module.finrank_linearMap, hfin_ext, ← pow_add, two_mul]
  letI : LinearOrder (I ⊕ I) := LinearOrder.lift'
    (fun x : I ⊕ I => match x with | Sum.inl i => toLex (false, i) | Sum.inr i => toLex (true, i))
    (by rintro (a | a) (b | b) h <;> simp_all)
  haveI : Module.Finite 𝕜 (ExteriorAlgebra 𝕜 (V × V)) :=
    Module.Finite.of_basis (b.prod b).ExteriorAlgebra
  haveI :
      Module.Finite 𝕜 (CliffordAlgebra ((-g.toQuadraticMap).prod g.toQuadraticMap)) :=
    Module.Finite.equiv (CliffordAlgebra.equivExterior ((-g.toQuadraticMap).prod g.toQuadraticMap)).symm
  have hbij : Function.Bijective φ :=
    OrzechProperty.bijective_of_surjective_of_finrank_le φ.toLinearMap hsurj
      (hfin_cl.trans hfin_end.symm).le
  AlgEquiv.ofBijective φ hbij

/-- 4D Witten doubled Clifford isomorphism `Cl(Q ⊕ Q) ≃ₐ[𝕜] Module.End 𝕜 (ExteriorAlgebra 𝕜 V)`
combining `wittenRealChiralityTwist` and `doubledCliffordEquivEnd` (Eqs. 4.33, 4.35). -/
def witten4DDoubledCliffordEquivEnd (g : LinearMap.BilinForm 𝕜 V) (hg : ∀ u v, g u v = g v u)
    (b : Module.Basis (Fin 4) 𝕜 V) (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    CliffordAlgebra (g.toQuadraticMap.prod g.toQuadraticMap) ≃ₐ[𝕜]
      Module.End 𝕜 (ExteriorAlgebra 𝕜 V) :=
  (wittenRealChiralityTwist g hg b horth).trans (doubledCliffordEquivEnd g hg b horth)

end DoubledCliffordEquiv

/-!
### 11D Pauli Doubling (Witten Eq. 4.37) & Closed `T16` Non-Commutativity Witnesses
-/

section PauliDoubling11D

/-- Pauli `σ₁` matrix in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauliX2C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `σ₂` matrix in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauliY2C : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `σ₃` matrix in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauliZ2C : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauliX2C_sq : pauliX2C * pauliX2C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX2C, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY2C_sq : pauliY2C * pauliY2C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY2C, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ2C_sq : pauliZ2C * pauliZ2C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ2C, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX2C_pauliY2C_anticomm : pauliX2C * pauliY2C + pauliY2C * pauliX2C = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX2C, pauliY2C]

theorem pauliX2C_pauliZ2C_anticomm : pauliX2C * pauliZ2C + pauliZ2C * pauliX2C = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX2C, pauliZ2C]

theorem pauliY2C_pauliZ2C_anticomm : pauliY2C * pauliZ2C + pauliZ2C * pauliY2C = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY2C, pauliZ2C]

/-- Closed `T16` non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem pauli2C_noncomm_witness : pauliY2C * pauliZ2C ≠ pauliZ2C * pauliY2C := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) h
  simp [pauliY2C, pauliZ2C, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- 11D Pauli doubling (Witten Eq. 4.37): given 9D Clifford matrices `Γ' : Fin 9 → Matrix n n ℂ`
satisfying `{Γ'_I, Γ'_J} = 2 δ_{IJ} I`, the 11D matrices `Γ_I := Γ'_I ⊗ σ₂`, `Γ₁₀ := I ⊗ σ₃`,
`Γ₁₁ := I ⊗ σ₁` satisfy the 11D Clifford relations `{Γ_A, Γ_B} = 2 δ_{AB} I`. -/
def pauliDoubled11D {n : Type*} [Fintype n] [DecidableEq n]
    (Γ9 : Fin 9 → Matrix n n ℂ) : Fin 11 → Matrix (n × Fin 2) (n × Fin 2) ℂ
  | ⟨k, _⟩ =>
    if h9 : k < 9 then Matrix.kroneckerMap (· * ·) (Γ9 ⟨k, h9⟩) pauliY2C
    else if k = 9 then Matrix.kroneckerMap (· * ·) (1 : Matrix n n ℂ) pauliZ2C
    else Matrix.kroneckerMap (· * ·) (1 : Matrix n n ℂ) pauliX2C

theorem pauliDoubled11D_sq_first9 {n : Type*} [Fintype n] [DecidableEq n]
    (Γ9 : Fin 9 → Matrix n n ℂ) (hsq : ∀ i : Fin 9, Γ9 i * Γ9 i = 1) (k : Fin 9) :
    pauliDoubled11D Γ9 ⟨k.1, by omega⟩ * pauliDoubled11D Γ9 ⟨k.1, by omega⟩ = 1 := by
  simp only [pauliDoubled11D, k.isLt, ↓reduceDIte]
  rw [← Matrix.mul_kronecker_mul, hsq k, pauliY2C_sq, Matrix.one_kronecker_one]

theorem pauliDoubled11D_sq_ten {n : Type*} [Fintype n] [DecidableEq n]
    (Γ9 : Fin 9 → Matrix n n ℂ) :
    pauliDoubled11D Γ9 9 * pauliDoubled11D Γ9 9 = 1 := by
  have h : pauliDoubled11D Γ9 9 = Matrix.kroneckerMap (· * ·) (1 : Matrix n n ℂ) pauliZ2C := by
    simp [pauliDoubled11D]
  rw [h, ← Matrix.mul_kronecker_mul, mul_one, pauliZ2C_sq, Matrix.one_kronecker_one]

theorem pauliDoubled11D_sq_eleven {n : Type*} [Fintype n] [DecidableEq n]
    (Γ9 : Fin 9 → Matrix n n ℂ) :
    pauliDoubled11D Γ9 10 * pauliDoubled11D Γ9 10 = 1 := by
  have h : pauliDoubled11D Γ9 10 = Matrix.kroneckerMap (· * ·) (1 : Matrix n n ℂ) pauliX2C := by
    simp [pauliDoubled11D]
  rw [h, ← Matrix.mul_kronecker_mul, mul_one, pauliX2C_sq, Matrix.one_kronecker_one]

theorem pauliDoubled11D_anticomm_ten_eleven {n : Type*} [Fintype n] [DecidableEq n]
    (Γ9 : Fin 9 → Matrix n n ℂ) :
    pauliDoubled11D Γ9 9 * pauliDoubled11D Γ9 10 +
      pauliDoubled11D Γ9 10 * pauliDoubled11D Γ9 9 = 0 := by
  have h9 : pauliDoubled11D Γ9 9 = Matrix.kroneckerMap (· * ·) (1 : Matrix n n ℂ) pauliZ2C := by
    simp [pauliDoubled11D]
  have h10 : pauliDoubled11D Γ9 10 = Matrix.kroneckerMap (· * ·) (1 : Matrix n n ℂ) pauliX2C := by
    simp [pauliDoubled11D]
  rw [h9, h10, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one,
    ← Matrix.kronecker_add, add_comm (pauliZ2C * pauliX2C), pauliX2C_pauliZ2C_anticomm,
    Matrix.kronecker_zero]

end PauliDoubling11D

section T16Witnesses

/-- Euclidean bilinear form on `Fin 4 → ℝ` used for closed `T16` witnesses. -/
def euclidBilin4R : LinearMap.BilinForm ℝ (Fin 4 → ℝ) :=
  Matrix.toBilin' (1 : Matrix (Fin 4) (Fin 4) ℝ)

private lemma euclidBilin4R_symm (u v : Fin 4 → ℝ) : euclidBilin4R u v = euclidBilin4R v u := by
  simp only [euclidBilin4R, Matrix.toBilin'_apply', Matrix.one_mulVec]
  exact dotProduct_comm u v

/-- Concrete creation operator in `Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ))`. -/
def m2Wedge0 : Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
  exteriorWedge ℝ (Pi.single 0 1)

/-- Concrete annihilation operator in `Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ))`. -/
def m2Contract0 : Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
  exteriorContract (euclidBilin4R (Pi.single 0 1))

/-- Concrete `c†_0` in `CliffordAlgebra ((-Q).prod Q)` on `Fin 4 → ℝ`. -/
def m2CliffordCreate0 :
    CliffordAlgebra ((-euclidBilin4R.toQuadraticMap).prod euclidBilin4R.toQuadraticMap) :=
  cliffordCreate euclidBilin4R (Pi.single 0 1)

/-- Concrete `c_0` in `CliffordAlgebra ((-Q).prod Q)` on `Fin 4 → ℝ`. -/
def m2CliffordAnnihilate0 :
    CliffordAlgebra ((-euclidBilin4R.toQuadraticMap).prod euclidBilin4R.toQuadraticMap) :=
  cliffordAnnihilate euclidBilin4R (Pi.single 0 1)

/-- Concrete `γ_0` in `CliffordAlgebra (Q.prod Q)` on `Fin 4 → ℝ`. -/
def m2CliffordPos0 :
    CliffordAlgebra (euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap) :=
  CliffordAlgebra.ι _ (Pi.single 0 1, 0)

/-- Concrete `γ_1` in `CliffordAlgebra (Q.prod Q)` on `Fin 4 → ℝ`. -/
def m2CliffordPos1 :
    CliffordAlgebra (euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap) :=
  CliffordAlgebra.ι _ (Pi.single 1 1, 0)

/-- Closed `T16` non-commutativity witness on `Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ))`. -/
theorem m2Forms_car_noncomm_witness : m2Contract0 * m2Wedge0 ≠ m2Wedge0 * m2Contract0 := by
  intro h
  have h1 := congrArg (fun f : Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) => f 1) h
  have heval : euclidBilin4R (Pi.single 0 1) (Pi.single 0 1) = (1 : ℝ) := by
    simp [euclidBilin4R, Matrix.toBilin'_apply', Matrix.one_mulVec]
  simp only [m2Contract0, m2Wedge0, Module.End.mul_apply, exteriorWedge_apply, mul_one,
    exteriorContract_iota, exteriorContract_one, map_zero, heval, one_smul] at h1
  exact one_ne_zero h1

/-- Closed `T16` non-commutativity witness on `CliffordAlgebra ((-Q).prod Q)`. -/
theorem m2DoubledClifford_noncomm_witness :
    m2CliffordCreate0 * m2CliffordAnnihilate0 ≠ m2CliffordAnnihilate0 * m2CliffordCreate0 := by
  intro h
  have hmap := congrArg (doubledCliffordToEnd euclidBilin4R euclidBilin4R_symm) h
  simp only [m2CliffordCreate0, m2CliffordAnnihilate0, map_mul,
    doubledCliffordToEnd_create, doubledCliffordToEnd_annihilate] at hmap
  exact m2Forms_car_noncomm_witness hmap.symm

/-- Closed `T16` non-commutativity witness on `CliffordAlgebra (Q.prod Q)`. -/
theorem m2DoubledCliffordPos_noncomm_witness :
    m2CliffordPos0 * m2CliffordPos1 ≠ m2CliffordPos1 * m2CliffordPos0 := by
  intro h
  have hsum := CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
    (Q := euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap)
    (a := (Pi.single (0 : Fin 4) (1 : ℝ), (0 : Fin 4 → ℝ)))
    (b := (Pi.single (1 : Fin 4) (1 : ℝ), (0 : Fin 4 → ℝ)))
    (by
      rw [QuadraticMap.isOrtho_def]
      simp [euclidBilin4R, Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_four])
  have h2 : (2 : ℝ) • (m2CliffordPos0 * m2CliffordPos1) = 0 := by
    calc
      (2 : ℝ) • (m2CliffordPos0 * m2CliffordPos1) =
          m2CliffordPos0 * m2CliffordPos1 + m2CliffordPos0 * m2CliffordPos1 := two_smul _ _
      _ = m2CliffordPos0 * m2CliffordPos1 + m2CliffordPos1 * m2CliffordPos0 := by rw [← h]
      _ = 0 := hsum
  have hzero : m2CliffordPos0 * m2CliffordPos1 = 0 := by
    have := congrArg (fun x => (⅟(2 : ℝ)) • x) h2
    simpa [smul_smul] using this
  have hsq : (m2CliffordPos0 * m2CliffordPos1) * (m2CliffordPos1 * m2CliffordPos0) = 1 := by
    have hp1 : m2CliffordPos1 * m2CliffordPos1 = 1 := by
      rw [m2CliffordPos1, CliffordAlgebra.ι_sq_scalar]
      have hval : (euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap)
          (Pi.single (1 : Fin 4) (1 : ℝ), (0 : Fin 4 → ℝ)) = 1 := by
        simp [euclidBilin4R, Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_four]
      rw [hval]
      exact RingHom.map_one (algebraMap ℝ
        (CliffordAlgebra (euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap)))
    have hp0 : m2CliffordPos0 * m2CliffordPos0 = 1 := by
      rw [m2CliffordPos0, CliffordAlgebra.ι_sq_scalar]
      have hval : (euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap)
          (Pi.single (0 : Fin 4) (1 : ℝ), (0 : Fin 4 → ℝ)) = 1 := by
        simp [euclidBilin4R, Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_four]
      rw [hval]
      exact RingHom.map_one (algebraMap ℝ
        (CliffordAlgebra (euclidBilin4R.toQuadraticMap.prod euclidBilin4R.toQuadraticMap)))
    calc
      (m2CliffordPos0 * m2CliffordPos1) * (m2CliffordPos1 * m2CliffordPos0) =
          m2CliffordPos0 * (m2CliffordPos1 * m2CliffordPos1) * m2CliffordPos0 := by
        simp only [mul_assoc]
      _ = 1 := by rw [hp1, mul_one, hp0]
  rw [hzero, zero_mul] at hsq
  exact zero_ne_one hsq

end T16Witnesses

/-!
## Part II: Bockstein Exact-Sequence Obstructions (Eqs. 4.10–4.19)
-/

section BocksteinObstructions

open CategoryTheory CategoryTheory.Limits

/-- The coefficient short exact sequence `0 → ℤ →[×2] ℤ → ZMod 2 → 0` (Witten Eq. 4.17). -/
def bocksteinCoeffShortComplex : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of ℤ
  X₂ := AddCommGrpCat.of ℤ
  X₃ := AddCommGrpCat.of (ZMod 2)
  f := AddCommGrpCat.ofHom ((2 : ℤ) • AddMonoidHom.id ℤ)
  g := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))
  zero := by
    apply ConcreteCategory.hom_ext
    intro (x : ℤ)
    change (((2 : ℤ) • x : ℤ) : ZMod 2) = 0
    rw [zsmul_eq_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right 2 x

/-- Exactness of `0 → ℤ →[×2] ℤ → ZMod 2 → 0` (Eq. 4.17). -/
theorem bocksteinCoeffShortComplex_shortExact : bocksteinCoeffShortComplex.ShortExact where
  mono_f := (AddCommGrpCat.mono_iff_injective _).2 fun a b hab => by
    dsimp [bocksteinCoeffShortComplex] at a b hab ⊢
    change (2 : ℤ) * a = (2 : ℤ) * b at hab
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) hab
  epi_g := (AddCommGrpCat.epi_iff_surjective _).2 fun (y : ZMod 2) => by
    refine ⟨(y.val : ℤ), ?_⟩
    change ((y.val : ℤ) : ZMod 2) = y
    simp
  exact := (ShortComplex.ab_exact_iff _).2 fun (x : ℤ) hx => by
    change (x : ZMod 2) = 0 at hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    rcases hx with ⟨k, rfl⟩
    exact ⟨k, by change (2 : ℤ) • k = 2 * k; rw [zsmul_eq_mul]; norm_num⟩

/-- Mod-2 quotient subgroup `(2 : ℤ) • ⊤` on an abelian group. -/
private def twoMulSubgroup (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  AddMonoidHom.range ((2 : ℤ) • AddMonoidHom.id A)

/-- Mod-2 quotient cochain complex `C ⊗ (ℤ/2ℤ)` for any cochain complex `C_int` of abelian groups. -/
def mod2QuotientComplex (C_int : CochainComplex AddCommGrpCat ℕ) :
    CochainComplex AddCommGrpCat ℕ where
  X n := AddCommGrpCat.of (C_int.X n ⧸ twoMulSubgroup (C_int.X n))
  d i j := AddCommGrpCat.ofHom (QuotientAddGroup.map (twoMulSubgroup (C_int.X i))
    (twoMulSubgroup (C_int.X j)) (C_int.d i j).hom (by
      rintro _ ⟨y, rfl⟩
      refine ⟨(C_int.d i j) y, ?_⟩
      change (2 : ℤ) • (C_int.d i j).hom y = (C_int.d i j).hom ((2 : ℤ) • y)
      exact (map_zsmul (C_int.d i j).hom 2 y).symm))
  shape i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk ((C_int.d i j) a) = 0
      rw [C_int.shape i j hij]
      simp
  d_comp_d' i j k _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk ((C_int.d j k) ((C_int.d i j) a)) = 0
      have hcomp : (C_int.d j k) ((C_int.d i j) a) = 0 := by
        rw [← ConcreteCategory.comp_apply, C_int.d_comp_d]
        rfl
      rw [hcomp]
      rfl

/-- Short exact cochain complex `0 → C_int →[×2] C_int → mod2QuotientComplex C_int → 0`
for any integer or orientation-twisted integer cochain complex `C_int` (Eqs. 4.18–4.19). -/
def mod2ShortComplex (C_int : CochainComplex AddCommGrpCat ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat ℕ) where
  X₁ := C_int
  X₂ := C_int
  X₃ := mod2QuotientComplex C_int
  f := (2 : ℤ) • 𝟙 C_int
  g :=
    { f := fun n => AddCommGrpCat.ofHom (QuotientAddGroup.mk' (twoMulSubgroup (C_int.X n)))
      comm' := fun _ _ _ => by
        apply ConcreteCategory.hom_ext
        intro a
        rfl }
  zero := by
    ext n x
    change QuotientAddGroup.mk (((2 : ℤ) • x : C_int.X n)) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩

/-- Whenever `C_int` is 2-torsion-free degreewise, `mod2ShortComplex C_int` is short exact. -/
theorem mod2ShortComplex_shortExact (C_int : CochainComplex AddCommGrpCat ℕ)
    (h_tf : ∀ n (x : C_int.X n), (2 : ℤ) • x = 0 → x = 0) :
    (mod2ShortComplex C_int).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine
    { mono_f := (AddCommGrpCat.mono_iff_injective _).2 fun a b hab => by
        have hsub : (2 : ℤ) • (a - b) = 0 := by
          rw [smul_sub]
          exact sub_eq_zero.mpr hab
        exact sub_eq_zero.mp (h_tf n (a - b) hsub)
      epi_g := (AddCommGrpCat.epi_iff_surjective _).2 fun q => by
        induction q using QuotientAddGroup.induction_on with
        | H a => exact ⟨a, rfl⟩
      exact := (ShortComplex.ab_exact_iff _).2 fun (x : C_int.X n) hx => by
        change QuotientAddGroup.mk (s := twoMulSubgroup (C_int.X n)) x = 0 at hx
        rw [QuotientAddGroup.eq_zero_iff] at hx
        exact hx }

/-- The Bockstein connecting homomorphism `β : H^k(C; ℤ₂) ⟶ H^{k+1}(C; ℤ)` (or twisted `ℤ̃`). -/
noncomputable def bocksteinHom {S : ShortComplex (CochainComplex AddCommGrpCat ℕ)}
    (hS : S.ShortExact) (k : ℕ) : S.X₃.homology k ⟶ S.X₁.homology (k + 1) :=
  hS.δ k (k + 1) rfl

/-- `Spin^c` integral Stiefel–Whitney obstruction `W_3 = β(w_2)` (Witten Eq. 4.18). -/
noncomputable def W3 {S : ShortComplex (CochainComplex AddCommGrpCat ℕ)}
    (hS : S.ShortExact) (w2 : S.X₃.homology 2) : S.X₁.homology 3 :=
  bocksteinHom hS 2 w2

/-- `mc`-structure twisted integral obstruction `W̃_5 = β(w_4)` (Witten Eq. 4.19). -/
noncomputable def Wtilde5 {S : ShortComplex (CochainComplex AddCommGrpCat ℕ)}
    (hS : S.ShortExact) (w4 : S.X₃.homology 4) : S.X₁.homology 5 :=
  bocksteinHom hS 4 w4

/-- Exactness of the Bockstein sequence gives `2 • β(w) = 0` for every class `w`. -/
theorem two_zsmul_bocksteinHom {C_int : CochainComplex AddCommGrpCat ℕ}
    (hS : (mod2ShortComplex C_int).ShortExact) (k : ℕ)
    (w : (mod2QuotientComplex C_int).homology k) :
    (2 : ℤ) • bocksteinHom hS k w = 0 := by
  have hcomp := hS.δ_comp k (k + 1) rfl
  have hf : HomologicalComplex.homologyMap (mod2ShortComplex C_int).f (k + 1) =
      (2 : ℤ) • 𝟙 (C_int.homology (k + 1)) := by
    dsimp [mod2ShortComplex]
    rw [two_zsmul (𝟙 C_int), HomologicalComplex.homologyMap_add (𝟙 C_int) (𝟙 C_int) (k + 1),
      HomologicalComplex.homologyMap_id, ← two_zsmul]
  have h0 : (HomologicalComplex.homologyMap (mod2ShortComplex C_int).f (k + 1))
      (hS.δ k (k + 1) rfl w) = 0 := by
    change (hS.δ k (k + 1) rfl ≫
      HomologicalComplex.homologyMap (mod2ShortComplex C_int).f (k + 1)) w = 0
    rw [hcomp]
    rfl
  rw [hf] at h0
  exact h0

/-- `2 • W_3 = 0` for the `Spin^c` obstruction `W_3 = β(w_2)` (Eq. 4.18). -/
theorem two_zsmul_W3 {C_int : CochainComplex AddCommGrpCat ℕ}
    (hS : (mod2ShortComplex C_int).ShortExact)
    (w2 : (mod2QuotientComplex C_int).homology 2) :
    (2 : ℤ) • W3 hS w2 = 0 :=
  two_zsmul_bocksteinHom hS 2 w2

/-- `2 • W̃_5 = 0` for the `mc`-structure obstruction `W̃_5 = β(w_4)` (Eq. 4.19). -/
theorem two_zsmul_Wtilde5 {C_int : CochainComplex AddCommGrpCat ℕ}
    (hS : (mod2ShortComplex C_int).ShortExact)
    (w4 : (mod2QuotientComplex C_int).homology 4) :
    (2 : ℤ) • Wtilde5 hS w4 = 0 :=
  two_zsmul_bocksteinHom hS 4 w4

/-- A mod-2 cohomology class `w ∈ H^k(-; ℤ₂)` lifts to `H^k(-; ℤ)` (or `ℤ̃`)
if and only if its Bockstein obstruction `β(w)` vanishes. -/
theorem exists_lift_iff_bocksteinHom_eq_zero {S : ShortComplex (CochainComplex AddCommGrpCat ℕ)}
    (hS : S.ShortExact) (k : ℕ) (w : S.X₃.homology k) :
    (∃ x_hat : S.X₂.homology k, HomologicalComplex.homologyMap S.g k x_hat = w) ↔
      bocksteinHom hS k w = 0 := by
  have hex := (ShortComplex.ab_exact_iff _).1 (hS.homology_exact₃ k (k + 1) rfl)
  constructor
  · rintro ⟨x_hat, rfl⟩
    have hcomp := ConcreteCategory.congr_hom (hS.comp_δ k (k + 1) rfl) x_hat
    simpa [bocksteinHom] using hcomp
  · intro hw
    exact hex w hw

/-- `Spin^c` liftability criterion: `w_2` lifts to `c_1 ∈ H^2(X; ℤ)` iff `W_3 = 0` (Eq. 4.15, 4.18). -/
theorem spinc_lift_iff_W3_eq_zero {S : ShortComplex (CochainComplex AddCommGrpCat ℕ)}
    (hS : S.ShortExact) (w2 : S.X₃.homology 2) :
    (∃ c1 : S.X₂.homology 2, HomologicalComplex.homologyMap S.g 2 c1 = w2) ↔ W3 hS w2 = 0 :=
  exists_lift_iff_bocksteinHom_eq_zero hS 2 w2

/-- `mc`-structure liftability criterion: `w_4` lifts to `x̂ ∈ H^4(Y; ℤ̃)` iff `W̃_5 = 0` (Eq. 4.16, 4.19). -/
theorem mc_lift_iff_Wtilde5_eq_zero {S : ShortComplex (CochainComplex AddCommGrpCat ℕ)}
    (hS : S.ShortExact) (w4 : S.X₃.homology 4) :
    (∃ x_hat : S.X₂.homology 4, HomologicalComplex.homologyMap S.g 4 x_hat = w4) ↔
      Wtilde5 hS w4 = 0 :=
  exists_lift_iff_bocksteinHom_eq_zero hS 4 w4

/-- Difference of any two integral lifts with the same mod-2 reduction is divisible by 2. -/
theorem lift_sub_mem_two_mul_of_eq_mod2 {C_int : CochainComplex AddCommGrpCat ℕ}
    (hS : (mod2ShortComplex C_int).ShortExact) (k : ℕ)
    {x₁ x₂ : C_int.homology k}
    (heq : HomologicalComplex.homologyMap (mod2ShortComplex C_int).g k x₁ =
      HomologicalComplex.homologyMap (mod2ShortComplex C_int).g k x₂) :
    ∃ y : C_int.homology k, (2 : ℤ) • y = x₁ - x₂ := by
  have hex := (ShortComplex.ab_exact_iff _).1 (hS.homology_exact₂ k)
  have hsub : HomologicalComplex.homologyMap (mod2ShortComplex C_int).g k (x₁ - x₂) = 0 := by
    change ((HomologicalComplex.homologyMap (mod2ShortComplex C_int).g k).hom) (x₁ - x₂) = 0
    exact (map_sub (HomologicalComplex.homologyMap (mod2ShortComplex C_int).g k).hom x₁ x₂).trans
      (sub_eq_zero.mpr heq)
  obtain ⟨y, hy⟩ := hex (x₁ - x₂) hsub
  change (HomologicalComplex.homologyMap (mod2ShortComplex C_int).f k) y = x₁ - x₂ at hy
  have hf : HomologicalComplex.homologyMap (mod2ShortComplex C_int).f k =
      (2 : ℤ) • 𝟙 (C_int.homology k) := by
    dsimp [mod2ShortComplex]
    rw [two_zsmul (𝟙 C_int), HomologicalComplex.homologyMap_add (𝟙 C_int) (𝟙 C_int) k,
      HomologicalComplex.homologyMap_id, ← two_zsmul]
  rw [hf] at hy
  exact ⟨y, hy⟩

/-- Shifted quantization period phase identity (Witten Eqs. 4.13–4.16):
if `∫ G / 2π = x̂ / 2` with `x̂ ≡ w₄ (mod 2)`, then `∫ G / 2π ≡ w₄ / 2 (mod ℤ)` and
`exp(i ∫ G) = (-1)^{w₄}`. -/
theorem shifted_quantization_period_phase {periodG : ℝ} {xHatPeriod : ℤ} {w4Period : ZMod 2}
    (h_twice : periodG = (xHatPeriod : ℝ) / 2)
    (h_mod2 : (xHatPeriod : ZMod 2) = w4Period) :
    Complex.exp (Complex.I * (2 * Real.pi * periodG)) = (-1 : ℂ) ^ w4Period.val ∧
      ∃ k : ℤ, periodG - (w4Period.val : ℝ) / 2 = k := by
  have h_even : ((xHatPeriod - (w4Period.val : ℤ) : ℤ) : ZMod 2) = 0 := by
    push_cast [h_mod2]
    simp [ZMod.natCast_zmod_val]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_even
  rcases h_even with ⟨k, hk⟩
  have h_diff : xHatPeriod = (w4Period.val : ℤ) + 2 * k := by omega
  refine ⟨?_, k, ?_⟩
  · have harg : Complex.I * (2 * Real.pi * periodG) =
        (w4Period.val : ℂ) * (Real.pi * Complex.I) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [h_twice, h_diff]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · rw [h_twice, h_diff]
    push_cast
    ring

/-!
### Concrete Non-Zero Bockstein Witness (`rp8TwistedCochainComplex`, Witten p. 43)
-/

/-- Concrete 2-torsion-free integer cochain complex modeling twisted integer cochains with
`d^{2m} = 2 • id` and `d^{2m+1} = 0` (so `H^{4} = 0`, `H^{5} ≅ ZMod 2`, and `β : H^4(-; ZMod 2) → H^5(-; ℤ̃)`
is an isomorphism sending `[1] ↦ [1] ≠ 0`, as in `ℝP^8` twisted cohomology). -/
def rp8TwistedCochainComplex : CochainComplex AddCommGrpCat ℕ where
  X _ := AddCommGrpCat.of ℤ
  d i j := if i + 1 = j ∧ Even i then (2 : ℤ) • 𝟙 (AddCommGrpCat.of ℤ) else 0
  shape i j hij := by
    have hneq : i + 1 ≠ j := hij
    simp [hneq]
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    subst hij' hjk'
    by_cases he : Even i
    · have ho : ¬ Even (i + 1) := by
        rw [Nat.even_add_one]
        exact not_not.mpr he
      simp [he, ho]
    · simp [he]

lemma rp8TwistedCochainComplex_torsionFree (n : ℕ) (x : rp8TwistedCochainComplex.X n)
    (hx : (2 : ℤ) • x = 0) : x = 0 := by
  dsimp [rp8TwistedCochainComplex] at x hx ⊢
  change (2 : ℤ) * (x : ℤ) = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left (by decide)

/-- The short complex `mod2ShortComplex rp8TwistedCochainComplex` is short exact. -/
theorem rp8TwistedCochainComplex_shortExact :
    (mod2ShortComplex rp8TwistedCochainComplex).ShortExact :=
  mod2ShortComplex_shortExact rp8TwistedCochainComplex rp8TwistedCochainComplex_torsionFree

/-- Concrete cocycle generator in `H^4(rp8Twisted; ZMod 2)` whose Bockstein image in `H^5` is non-zero. -/
noncomputable def rp8Mod2Generator4 :
    (mod2QuotientComplex rp8TwistedCochainComplex).homology 4 :=
  ((mod2QuotientComplex rp8TwistedCochainComplex).liftCycles
    (AddCommGrpCat.ofHom (QuotientAddGroup.mk' (twoMulSubgroup ℤ))) 5 (by simp) (by
      apply ConcreteCategory.hom_ext
      intro (x : ℤ)
      change QuotientAddGroup.mk (rp8TwistedCochainComplex.d 4 5 x) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      refine ⟨x, ?_⟩
      change ((2 : ℤ) • AddMonoidHom.id ℤ) x = rp8TwistedCochainComplex.d 4 5 x
      dsimp [rp8TwistedCochainComplex]
      rw [if_pos ⟨rfl, by decide⟩]
      rfl) ≫
    (mod2QuotientComplex rp8TwistedCochainComplex).homologyπ 4) (1 : ℤ)

/-- Witness that `W̃_5 = β(rp8Mod2Generator4) ≠ 0` while `2 • W̃_5 = 0` (Witten p. 43). -/
theorem rp8Twisted_Wtilde5_ne_zero :
    Wtilde5 rp8TwistedCochainComplex_shortExact rp8Mod2Generator4 ≠ 0 ∧
      (2 : ℤ) • Wtilde5 rp8TwistedCochainComplex_shortExact rp8Mod2Generator4 = 0 := by
  refine ⟨?_, two_zsmul_Wtilde5 rp8TwistedCochainComplex_shortExact rp8Mod2Generator4⟩
  intro hzero
  let x₃ : AddCommGrpCat.of ℤ ⟶ (mod2QuotientComplex rp8TwistedCochainComplex).X 4 :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' (twoMulSubgroup ℤ))
  have hx₃ : x₃ ≫ (mod2QuotientComplex rp8TwistedCochainComplex).d 4 5 = 0 := by
    apply ConcreteCategory.hom_ext
    intro (x : ℤ)
    change QuotientAddGroup.mk (rp8TwistedCochainComplex.d 4 5 x) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨x, ?_⟩
    change ((2 : ℤ) • AddMonoidHom.id ℤ) x = rp8TwistedCochainComplex.d 4 5 x
    dsimp [rp8TwistedCochainComplex]
    rw [if_pos ⟨rfl, by decide⟩]
    rfl
  let x₂ : AddCommGrpCat.of ℤ ⟶ rp8TwistedCochainComplex.X 4 := 𝟙 (AddCommGrpCat.of ℤ)
  have hx₂ : x₂ ≫ (mod2ShortComplex rp8TwistedCochainComplex).g.f 4 = x₃ := rfl
  let x₁ : AddCommGrpCat.of ℤ ⟶ rp8TwistedCochainComplex.X 5 := 𝟙 (AddCommGrpCat.of ℤ)
  have hx₁ : x₁ ≫ (mod2ShortComplex rp8TwistedCochainComplex).f.f 5 =
      x₂ ≫ rp8TwistedCochainComplex.d 4 5 := by
    apply ConcreteCategory.hom_ext
    intro (x : ℤ)
    simp [x₁, x₂, mod2ShortComplex, rp8TwistedCochainComplex, show Even 4 from by decide]
  have hδ := rp8TwistedCochainComplex_shortExact.δ_eq 4 5 rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ 6 (by simp)
  dsimp [mod2ShortComplex] at hδ
  have hd56 : x₁ ≫ rp8TwistedCochainComplex.d 5 6 = 0 := by
    apply ConcreteCategory.hom_ext
    intro (x : ℤ)
    change (rp8TwistedCochainComplex.d 5 6) x = (0 : ℤ)
    dsimp [rp8TwistedCochainComplex]
    rw [if_neg (fun h => absurd h.2 (by decide))]
    rfl
  have hgen : Wtilde5 rp8TwistedCochainComplex_shortExact rp8Mod2Generator4 =
      (rp8TwistedCochainComplex.liftCycles x₁ 6 (by simp) hd56 ≫
        rp8TwistedCochainComplex.homologyπ 5) (1 : ℤ) := by
    have hpt := ConcreteCategory.congr_hom hδ (1 : ℤ)
    dsimp only [Wtilde5, bocksteinHom, rp8Mod2Generator4]
    exact hpt
  rw [hgen] at hzero
  let ψ_sc : (rp8TwistedCochainComplex.sc 5).X₂ ⟶ AddCommGrpCat.of (ZMod 2) :=
    AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))
  have hψ : (rp8TwistedCochainComplex.sc 5).f ≫ ψ_sc = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    have hprev : (ComplexShape.up ℕ).prev 5 = 4 :=
      (ComplexShape.up ℕ).prev_eq' (rfl : 4 + 1 = 5)
    change (Int.castAddHom (ZMod 2)) ((rp8TwistedCochainComplex.d ((ComplexShape.up ℕ).prev 5) 5) x) = 0
    rw [hprev]
    dsimp [rp8TwistedCochainComplex]
    rw [if_pos ⟨rfl, by decide⟩]
    let z : ℤ := x
    change (((2 : ℤ) • z : ℤ) : ZMod 2) = 0
    rw [zsmul_eq_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right 2 z
  let ψ : rp8TwistedCochainComplex.homology 5 ⟶ AddCommGrpCat.of (ZMod 2) :=
    (rp8TwistedCochainComplex.sc 5).descHomology ((rp8TwistedCochainComplex.sc 5).iCycles ≫ ψ_sc)
      (by rw [ShortComplex.toCycles_i_assoc, hψ])
  have heval : ψ ((rp8TwistedCochainComplex.liftCycles x₁ 6 (by simp) hd56 ≫
        rp8TwistedCochainComplex.homologyπ 5) (1 : ℤ)) = (1 : ZMod 2) := by
    have hcomp :
        rp8TwistedCochainComplex.liftCycles x₁ 6 (by simp) hd56 ≫
          rp8TwistedCochainComplex.homologyπ 5 ≫ ψ = ψ_sc := by
      change (rp8TwistedCochainComplex.sc 5).liftCycles x₁ _ ≫
          (rp8TwistedCochainComplex.sc 5).homologyπ ≫
          (rp8TwistedCochainComplex.sc 5).descHomology ((rp8TwistedCochainComplex.sc 5).iCycles ≫ ψ_sc) _ =
        ψ_sc
      rw [ShortComplex.π_descHomology, ← Category.assoc]
      erw [ShortComplex.liftCycles_i, Category.id_comp]
    have hpt := ConcreteCategory.congr_hom hcomp (1 : ℤ)
    simpa [ψ_sc] using hpt
  have hzero' : (rp8TwistedCochainComplex.liftCycles x₁ 6 (by simp) hd56 ≫
      rp8TwistedCochainComplex.homologyπ 5) (1 : ℤ) = 0 := hzero
  rw [hzero', map_zero] at heval
  exact zero_ne_one heval

end BocksteinObstructions

/-!
## Part III: Abstract `η`-Gluing & `η = 2χ mod 4 → exp(-iπη/2) = (-1)^χ` (Eqs. 2.7–2.8, 4.21–4.40)
-/

section DaiFreedPhaseAndGluing

/-- Dai–Freed anomaly phase `exp(-i π η / 2)` (Witten Eqs. 2.5, 2.7–2.8, 4.21–4.23, 4.39). -/
def daiFreedPhase (η : ℝ) : ℂ :=
  Complex.exp (-Complex.I * Real.pi * η / 2)

@[simp]
theorem daiFreedPhase_zero : daiFreedPhase 0 = 1 := by
  simp [daiFreedPhase]

theorem daiFreedPhase_ne_zero (η : ℝ) : daiFreedPhase η ≠ 0 :=
  Complex.exp_ne_zero _

/-- Gluing additivity of the Dai–Freed phase (Eq. 2.7). -/
theorem daiFreedPhase_add (η₁ η₂ : ℝ) :
    daiFreedPhase (η₁ + η₂) = daiFreedPhase η₁ * daiFreedPhase η₂ := by
  simp only [daiFreedPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Orientation / `Pin⁺` reversal inverts the Dai–Freed phase (Eq. 2.8 fn. 16). -/
theorem daiFreedPhase_neg (η : ℝ) :
    daiFreedPhase (-η) = (daiFreedPhase η)⁻¹ := by
  simp only [daiFreedPhase, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- Difference gluing law `exp(-iπ(η₁ - η₂)/2) = exp(-iπη₁/2) / exp(-iπη₂/2)` (Eq. 2.8). -/
theorem daiFreedPhase_sub (η₁ η₂ : ℝ) :
    daiFreedPhase (η₁ - η₂) = daiFreedPhase η₁ / daiFreedPhase η₂ := by
  rw [sub_eq_add_neg, daiFreedPhase_add, daiFreedPhase_neg, div_eq_mul_inv]

/-- Mod-4 periodicity of the Dai–Freed phase (Witten p. 9 fn. 13). -/
theorem daiFreedPhase_add_four_mul_int (η : ℝ) (k : ℤ) :
    daiFreedPhase (η + 4 * k) = daiFreedPhase η := by
  have h4 : daiFreedPhase (4 * (k : ℝ)) = 1 := by
    simp only [daiFreedPhase]
    have harg : -Complex.I * Real.pi * ↑(4 * (k : ℝ)) / 2 = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  rw [daiFreedPhase_add, h4, mul_one]

/-- Main exponential theorem (Witten Eqs. 4.38–4.40):
if `η = 2χ + 4k`, then `exp(-i π η / 2) = (-1)^χ`. -/
theorem daiFreedPhase_eq_neg_one_pow_of_two_mul_add_four_mul
    {η : ℝ} {χ k : ℤ} (hη : η = 2 * (χ : ℝ) + 4 * (k : ℝ)) :
    daiFreedPhase η = (-1 : ℂ) ^ χ := by
  rw [hη, daiFreedPhase_add_four_mul_int]
  simp only [daiFreedPhase]
  have harg : -Complex.I * Real.pi * ↑(2 * (χ : ℝ)) / 2 = (χ : ℂ) * (-(Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_neg_pi_mul_I]

/-- Parity corollary connecting `η = 2χ mod 4` with `χ ≡ w₄ (mod 2)` (Eq. 4.40). -/
theorem daiFreedPhase_eq_neg_one_pow_w4
    {η : ℝ} {χ k : ℤ} {w4 : ZMod 2}
    (hη : η = 2 * (χ : ℝ) + 4 * (k : ℝ)) (hw4 : (χ : ZMod 2) = w4) :
    daiFreedPhase η = (-1 : ℂ) ^ w4.val := by
  rw [daiFreedPhase_eq_neg_one_pow_of_two_mul_add_four_mul hη]
  have h_even : ((χ - (w4.val : ℤ) : ℤ) : ZMod 2) = 0 := by
    push_cast [hw4]
    simp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_even
  rcases h_even with ⟨m, hm⟩
  have hχ : χ = (w4.val : ℤ) + 2 * m := by omega
  rw [hχ, zpow_add₀ (by norm_num), zpow_natCast, zpow_mul, show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num,
    one_zpow, mul_one]

/-- 4D Euler characteristic `χ = ∑_{i=0}^4 (-1)^i b_i` from Betti numbers `b : Fin 5 → ℕ`. -/
def eulerChar4D (b : Fin 5 → ℕ) : ℤ :=
  ∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) * (b i : ℤ)

/-- Doubled zero-mode sum `η = 2 ∑_{i=0}^4 b_i` on `Ω^*(X) ⊕ Ω^*_ε(X)` (Witten §4.3). -/
def doubledBettiSum4D (b : Fin 5 → ℕ) : ℤ :=
  2 * ∑ i : Fin 5, (b i : ℤ)

/-- Exact Betti-number identity `η = 2χ + 4(b₁ + b₃)` verifying `η ≡ 2χ (mod 4)` (Eq. 4.38). -/
theorem doubledBettiSum4D_eq_two_mul_eulerChar4D_add_four_mul (b : Fin 5 → ℕ) :
    doubledBettiSum4D b = 2 * eulerChar4D b + 4 * ((b 1 : ℤ) + (b 3 : ℤ)) := by
  simp only [doubledBettiSum4D, eulerChar4D, Fin.sum_univ_five]
  norm_num
  ring

/-- Exponential identity for the untwisted Betti zero-mode sum (Eq. 4.39). -/
theorem daiFreedPhase_doubledBettiSum4D (b : Fin 5 → ℕ) :
    daiFreedPhase (doubledBettiSum4D b : ℝ) = (-1 : ℂ) ^ eulerChar4D b := by
  apply daiFreedPhase_eq_neg_one_pow_of_two_mul_add_four_mul (k := (b 1 : ℤ) + (b 3 : ℤ))
  exact_mod_cast doubledBettiSum4D_eq_two_mul_eulerChar4D_add_four_mul b

/-- `α`-twisted Hodge-duality identity (Witten fn. 47, p. 50):
when twisted Betti numbers satisfy `b_{α⊗ε}(i) = b_α(4 - i)`, the total zero-mode count
`∑ b_α(i) + ∑ b_{α⊗ε}(i)` equals `2 ∑ b_α(i)` and hence yields `exp(-iπη/2) = (-1)^{χ(X)}`. -/
theorem daiFreedPhase_twistedSum_eq_neg_one_pow (b_α b_αε : Fin 5 → ℕ)
    (h_duality : ∀ i : Fin 5, b_αε i = b_α ⟨4 - i.1, by omega⟩) :
    (∑ i : Fin 5, (b_α i : ℤ) + ∑ i : Fin 5, (b_αε i : ℤ) = doubledBettiSum4D b_α) ∧
      daiFreedPhase ((∑ i : Fin 5, b_α i + ∑ i : Fin 5, b_αε i : ℕ) : ℝ) =
        (-1 : ℂ) ^ eulerChar4D b_α := by
  have hsum : ∑ i : Fin 5, (b_αε i : ℤ) = ∑ i : Fin 5, (b_α i : ℤ) := by
    simp only [h_duality, Fin.sum_univ_five]
    change (b_α 4 : ℤ) + (b_α 3 : ℤ) + (b_α 2 : ℤ) + (b_α 1 : ℤ) + (b_α 0 : ℤ) =
      (b_α 0 : ℤ) + (b_α 1 : ℤ) + (b_α 2 : ℤ) + (b_α 3 : ℤ) + (b_α 4 : ℤ)
    ring
  have htot : ∑ i : Fin 5, (b_α i : ℤ) + ∑ i : Fin 5, (b_αε i : ℤ) = doubledBettiSum4D b_α := by
    rw [hsum, doubledBettiSum4D]
    ring
  refine ⟨htot, ?_⟩
  have hcast : ((∑ i : Fin 5, b_α i + ∑ i : Fin 5, b_αε i : ℕ) : ℝ) =
      (doubledBettiSum4D b_α : ℝ) := by
    exact_mod_cast htot
  rw [hcast]
  exact daiFreedPhase_doubledBettiSum4D b_α

/-- M2-brane anomaly-inflow measure `Z_U = |Pf(D)| exp(-i π η_U / 2) exp(i ∫_U G)` (Eq. 4.21). -/
def m2BraneMeasure (pfAbs ηU intG : ℝ) : ℂ :=
  (pfAbs : ℂ) * daiFreedPhase ηU * Complex.exp (Complex.I * intG)

/-- Gluing consistency equivalence for the M2-brane measure (Eqs. 2.7–2.8, 4.21–4.22):
for `|Pf(D)| ≠ 0`, `Z_U = Z_{U'}` holds iff the closed glued anomaly factor on `U^* = U ∪ (-U')`
equals `1`. -/
theorem m2BraneMeasure_eq_iff_glued_anomaly_one
    {pfAbs ηU ηU' ηUstar intG intG' intGstar : ℝ}
    (h_pf : pfAbs ≠ 0)
    (h_eta : ∃ k : ℤ, ηUstar = ηU - ηU' + 4 * k)
    (h_G : ∃ m : ℤ, intGstar = intG - intG' + 2 * Real.pi * m) :
    m2BraneMeasure pfAbs ηU intG = m2BraneMeasure pfAbs ηU' intG' ↔
      daiFreedPhase ηUstar * Complex.exp (Complex.I * intGstar) = 1 := by
  rcases h_eta with ⟨k, hk⟩
  rcases h_G with ⟨m, hm⟩
  have heta_eq : daiFreedPhase ηUstar = daiFreedPhase ηU / daiFreedPhase ηU' := by
    rw [hk, daiFreedPhase_add_four_mul_int, daiFreedPhase_sub]
  have hG_eq : Complex.exp (Complex.I * intGstar) =
      Complex.exp (Complex.I * intG) / Complex.exp (Complex.I * intG') := by
    rw [hm]
    have harg : Complex.I * (intG - intG' + 2 * Real.pi * m : ℝ) =
        (Complex.I * intG - Complex.I * intG') + (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub]
  have hpfC : (pfAbs : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h_pf
  have hden1 : daiFreedPhase ηU' ≠ 0 := daiFreedPhase_ne_zero ηU'
  have hden2 : Complex.exp (Complex.I * intG') ≠ 0 := Complex.exp_ne_zero _
  rw [heta_eq, hG_eq]
  simp only [m2BraneMeasure]
  constructor
  · intro h
    have h' : daiFreedPhase ηU * Complex.exp (Complex.I * intG) =
        daiFreedPhase ηU' * Complex.exp (Complex.I * intG') := by
      apply mul_left_cancel₀ hpfC
      simpa [mul_assoc] using h
    rw [div_mul_div_comm, h', div_self (mul_ne_zero hden1 hden2)]
  · intro h
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hden1 hden2)] at h
    calc
      (pfAbs : ℂ) * daiFreedPhase ηU * Complex.exp (Complex.I * intG) =
          (pfAbs : ℂ) * (daiFreedPhase ηU * Complex.exp (Complex.I * intG)) := by ring
      _ = (pfAbs : ℂ) * (daiFreedPhase ηU' * Complex.exp (Complex.I * intG')) := by rw [h]
      _ = (pfAbs : ℂ) * daiFreedPhase ηU' * Complex.exp (Complex.I * intG') := by ring

/-- Reduction of Eq. (4.22) to Eq. (4.23) under shifted flux quantization
`∫_{U^*} G = π w₄ + 2π m`. -/
theorem m2BraneMeasure_glued_shifted_quantization_iff
    {ηUstar intGstar : ℝ} {w4 : ZMod 2}
    (h_quant : ∃ m : ℤ, intGstar = Real.pi * (w4.val : ℝ) + 2 * Real.pi * m) :
    daiFreedPhase ηUstar * Complex.exp (Complex.I * intGstar) = 1 ↔
      daiFreedPhase ηUstar = (-1 : ℂ) ^ w4.val := by
  rcases h_quant with ⟨m, hm⟩
  have hG : Complex.exp (Complex.I * intGstar) = (-1 : ℂ) ^ w4.val := by
    rw [hm]
    have harg : Complex.I * (Real.pi * (w4.val : ℝ) + 2 * Real.pi * m : ℝ) =
        (w4.val : ℂ) * (Real.pi * Complex.I) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hG]
  have hsign_sq : ((-1 : ℂ) ^ w4.val) * ((-1 : ℂ) ^ w4.val) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  constructor
  · intro h
    calc
      daiFreedPhase ηUstar =
          (daiFreedPhase ηUstar * (-1 : ℂ) ^ w4.val) * (-1 : ℂ) ^ w4.val := by
        rw [mul_assoc, hsign_sq, mul_one]
      _ = (-1 : ℂ) ^ w4.val := by rw [h, one_mul]
  · intro h
    rw [h, hsign_sq]

/-- Abstract `Pin⁺` `η`-gluing & cobordism system (Witten §4.3, p. 51). -/
structure PinPlusEtaGluingSystem where
  Closed : Type
  etaVal : Closed → ℝ
  w4Parity : Closed → ZMod 2
  disjointUnion : Closed → Closed → Closed
  connectSum : Closed → Closed → Closed
  eta_disjointUnion_mod4 :
    ∀ X Y, ∃ k : ℤ, etaVal (disjointUnion X Y) = etaVal X + etaVal Y + 4 * k
  eta_connectSum_mod4 :
    ∀ X Y, ∃ k : ℤ, etaVal (connectSum X Y) = etaVal (disjointUnion X Y) + 4 * k
  w4_connectSum : ∀ X Y, w4Parity (connectSum X Y) = w4Parity X + w4Parity Y

/-- Cobordism propagation of Eq. (4.23): if `exp(-iπη/2) = (-1)^{w_4}` holds on `X` and `S4`,
it holds on `X # S4` (Witten p. 51). -/
theorem m2_consistency_propagates_along_connectSum (S : PinPlusEtaGluingSystem)
    {X S4 : S.Closed}
    (hX : daiFreedPhase (S.etaVal X) = (-1 : ℂ) ^ (S.w4Parity X).val)
    (hS4 : daiFreedPhase (S.etaVal S4) = (-1 : ℂ) ^ (S.w4Parity S4).val) :
    daiFreedPhase (S.etaVal (S.connectSum X S4)) =
      (-1 : ℂ) ^ (S.w4Parity (S.connectSum X S4)).val := by
  rcases S.eta_connectSum_mod4 X S4 with ⟨k₁, hk₁⟩
  rcases S.eta_disjointUnion_mod4 X S4 with ⟨k₂, hk₂⟩
  rw [hk₁, daiFreedPhase_add_four_mul_int, hk₂, daiFreedPhase_add_four_mul_int,
    daiFreedPhase_add, hX, hS4, S.w4_connectSum X S4]
  set q : ℤ := ((S.w4Parity X).val + (S.w4Parity S4).val : ℤ) / 2
  have hsum : ((S.w4Parity X).val + (S.w4Parity S4).val : ℕ) =
      (S.w4Parity X + S.w4Parity S4).val + 2 * q.toNat := by
    have hval : (S.w4Parity X + S.w4Parity S4).val =
        ((S.w4Parity X).val + (S.w4Parity S4).val) % 2 := ZMod.val_add _ _
    omega
  rw [← pow_add, hsum, pow_add, pow_mul, show (-1 : ℂ) ^ 2 = 1 by norm_num, one_pow, mul_one]

/-- Closed variable-free `T17` constructive inhabitant for `PinPlusEtaGluingSystem`
built from 4D Betti profiles `Fin 5 → ℕ`. -/
instance instInhabitedPinPlusEtaGluingSystem : Inhabited PinPlusEtaGluingSystem where
  default :=
    { Closed := Fin 5 → ℕ
      etaVal := fun b => (doubledBettiSum4D b : ℝ)
      w4Parity := fun b => (eulerChar4D b : ZMod 2)
      disjointUnion := fun b₁ b₂ i => b₁ i + b₂ i
      connectSum := fun b₁ b₂ i => b₁ i + b₂ i
      eta_disjointUnion_mod4 := fun b₁ b₂ => ⟨0, by
        simp only [doubledBettiSum4D, Nat.cast_add, Finset.sum_add_distrib]
        push_cast
        ring⟩
      eta_connectSum_mod4 := fun _ _ => ⟨0, by simp⟩
      w4_connectSum := fun b₁ b₂ => by
        simp only [eulerChar4D, Nat.cast_add, mul_add, Finset.sum_add_distrib]
        push_cast
        rfl }

end DaiFreedPhaseAndGluing

end InfoGeometry.Physics.M2BraneCliffordFormsAndMC
