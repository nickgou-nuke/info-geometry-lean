/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
import InfoGeometry.Canonical.KahlerAtiyahCartanForms
import InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
import InfoGeometry.Dynamics.ChiralHodgeDifferential
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
import InfoGeometry.Clifford.Cl11HomogeneousChains
import InfoGeometry.Clifford.Cl11GradedDifferential
import InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.Clifford.Cl11GradedTensorMorita
import InfoGeometry.Clifford.FreedCliffordSuspension
import InfoGeometry.Clifford.RealMod8Classification
import InfoGeometry.Canonical.AtiyahBottShapiroBridge
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Clifford.ABSZeroStepArithmetic

/-!
# Primary-Source Kähler, Hestenes–Darboux, Jordan–Wigner, and Atiyah–Bott–Shapiro Foundations (`S2-15`..`S2-18`)

This module formalizes the second half of Pillar 2 (`R3`), preserving metric-free exterior
versus metric-dependent inner contraction (`R3.2` / `O-EXT`), basis-free rotor dynamics (`R3.2`),
and Koszul `ℤ/2`-graded tensor products with explicit Jordan–Wigner parity-string soldering
(`R3.3`):

* **`S2-15` — Kähler (1960–62; via Kruglov 2001 `15a`, Sushch 2015 `15b`, Red'kov 2011 `15c`)**:
  * Metric-free outer wedge `kahlerOuterWedge` (`v ∧ ·`) separated from metric-dependent inner
    contraction `kahlerInnerContract` (`CliffordAlgebra.contractLeft (Q := 0)`), CAR relation,
    Clifford module lift `kahlerCliffordHom`, and Kähler's 1-vector inner-outer product law
    `equivExterior_ι_mul` (`v ∨ ω = v ∧ ω + v ⌋_Q ω`).
  * Algebraic Kähler–Dirac operator `kahlerDirac := d - δ` and
    `kahlerDirac_sq_eq_neg_laplacian : (d - δ)² = -(dδ + δd)` (Kruglov `15a` §1 eqs. (1)–(2)),
    explicitly contrasted with `hodgeDirac := d + δ` (`(d + δ)² = +(dδ + δd)`, Sushch `15b`
    Prop. 1 eq. (18)) and linked to `ChiralHodgeDifferential.Data.diracKahler`.
  * **Scope / `BUCKET 3 / O-EXT`**: Smooth curved-manifold de Rham PDE Hodge decomposition
    and curved tetrad regularity (`Red'kov 15c` §3) remain `O-EXT` outside this algebraic module.

* **`S2-16` — Hestenes (1966; `16a1`–`16a3`) & Darboux (1887; `16b`)**:
  * Basis-free moving-frame rotor equation `hestenesRotorDeriv Ω R := ⅟2 • (Ω * R)` (`16a2`
    §5 eq. (5.4), Darboux `16b` Livre I Ch. I eq. (15) p. 7) and bivector commutator product
    `hestenesBivectorCommutator Ω X := ⅟2 • [Ω, X]`.
  * Proof that skew-reversion `reverse Ω = -Ω` preserves `R * reverse R = 1` infinitesimally
    and induces frame transport `e' = ⅟2 [Ω, e]` (`16a2` eq. (5.5)), documenting the factor
    of `2` between Hestenes's `Ω = 2 R' R̃` and `CartanHestenes...clRotorDarbouxConnection`
    (`dR * reverse R`).
  * `reverseCommutingLane` Maurer–Cartan coupling and concrete `cl11HyperbolicRotor` witness.

* **`S2-17` — Jordan–Wigner (1928; via Nielsen 2005 `17`)**:
  * Explicit separation of ungraded tensor commutation (`ungradedTensor_site_commute`,
    `ordinaryMatrix_site_commute` with `⊗ₖ`) from Koszul `ℤ/2`-graded anticommutation
    (`koszulGradedTensor_odd_anticommute` via `CliffordAlgebra.prodEquiv` / `ᵍ⊗[R]`).
  * Native finite-stage CAR theorems for `nativeJWCreation` and `nativeJWAnnihilation` in
    `Clsplit n` (Nielsen 2005 §II eq. (1)) and parity-string soldering package referencing
    `Cl11HomogeneousChains` (noting Nielsen §III eq. (31) minus-sign convention) and
    `SplitCliffordMatrixLimitSoldering.gradedTensorSuccessor_not_algHom` (`R3.3`).

* **`S2-18` — Atiyah–Bott–Shapiro (1964; `18a`)**:
  * Explicit convention alignment between ABS's `C_k = Cl_{0,k}` (`e_i² = -1`, `Table 1`) and
    `C'_k = Cl_{k,0}` (`e'_i² = +1`), coordinate-free `positiveForm Q := Q.prod (-QuadraticMap.sq)`,
    canonical inclusion `absInclusion : Cl(Q) →ₐ Cl(Q ⊕ ⟨-1⟩)`, Koszul graded tensor step
    `absStepSuspensionEquiv`, categorical graded-module restriction functor
    `absRestrictionFunctor : absModuleCat (positiveForm Q) ⥤ absModuleCat Q` (`GradedModuleCat.restrict`),
    Morita head cancellation (`cl11GradedEquivalence`, `cliffordHeadCancellation`), and `Type 0`
    Grothendieck cokernel `A₀ ≃+ ℤ` via `Algebra/Grothendieck.lean`, bridged to
    `AtiyahBottShapiroBridge` and `RealMod8Classification`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary

open CliffordAlgebra
open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.KahlerAtiyahCartanForms
open InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
open InfoGeometry.Clifford.Cl11HomogeneousChains
open InfoGeometry.Clifford.Cl11GradedDifferential
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita

/-- `S2-17` / `R3.3` Closed Non-Commutativity Witness: In the Clifford algebra `Cl(1,1)`,
the native Jordan–Wigner creation and annihilation generators at site `0` of `Clsplit 1`
do not commute (`a₀† * a₀ ≠ a₀ * a₀†`), witnessing authentic noncommutative fermionic
operator algebra without scalar proxies. -/
theorem jw_split1_noncommutative_witness :
    let adag : Clsplit 1 := nativeJWCreation 1 0
    let a : Clsplit 1 := nativeJWAnnihilation 1 0
    adag * a ≠ a * adag := by
  intro adag a h
  have hm := congrArg (jwSplitStageEquiv 1) h
  rw [map_mul, map_mul, jwSplitStageEquiv_nativeJWCreation,
    jwSplitStageEquiv_nativeJWAnnihilation] at hm
  change Matrix.kroneckerMap (· * ·) (Cl11TensorTower.globalChirality 0)
        Cl11TensorTower.wittCreationBase *
      Matrix.kroneckerMap (· * ·) (Cl11TensorTower.globalChirality 0)
        Cl11TensorTower.wittAnnihilationBase =
    Matrix.kroneckerMap (· * ·) (Cl11TensorTower.globalChirality 0)
        Cl11TensorTower.wittAnnihilationBase *
      Matrix.kroneckerMap (· * ·) (Cl11TensorTower.globalChirality 0)
        Cl11TensorTower.wittCreationBase at hm
  rw [Cl11TensorTower.globalChirality, InfoGeometry.Clifford.TowerMatrix.kronPow,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, _root_.mul_one] at hm
  have hc := congrArg (fun M => M ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2))) hm
  norm_num [Matrix.kroneckerMap_apply, Cl11TensorTower.wittCreationBase,
    Cl11TensorTower.wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two] at hc

/-!
## Section 1 (`S2-15`): Kähler (1960–62) Inner–Outer Exterior Calculus & Kähler–Dirac `d - δ`
-/

section KahlerPrimary

section InnerOuterAlgebra

/-- `S2-15` (Kähler 1962; `R3.2`): Metric-free exterior creation (wedge) operator
`v ↦ (v ∧ ·)` on `ExteriorAlgebra R V`, taking NO quadratic form or bilinear metric. -/
def kahlerOuterWedge {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  Algebra.lmul R (ExteriorAlgebra R V) (ExteriorAlgebra.ι R v)

/-- `S2-15` (Kähler 1962; `R3.2` / `O-EXT`): Metric-dependent interior contraction operator
`φ ↦ (φ ⌋ ·)` on `ExteriorAlgebra R V` (`CliffordAlgebra.contractLeft (Q := 0) φ`). -/
def kahlerInnerContract {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (φ : Module.Dual R V) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) φ

/-- `S2-15` (Kähler 1962): Over `ℝ`, `kahlerOuterWedge` coincides definitionally with
`KahlerAtiyahCartanForms.wedgeOperator`. -/
theorem kahlerOuterWedge_eq_wedgeOperator {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    kahlerOuterWedge (R := ℝ) v = wedgeOperator v := by
  ext ω
  rfl

/-- `S2-15` (Kähler 1962): Over `ℝ`, `kahlerInnerContract` coincides definitionally with
`KahlerAtiyahCartanForms.contractionOperator`. -/
theorem kahlerInnerContract_eq_contractionOperator {V : Type*} [AddCommGroup V] [Module ℝ V]
    (φ : Module.Dual ℝ V) :
    kahlerInnerContract (R := ℝ) φ = contractionOperator φ := by
  ext ω
  rfl

/-- `S2-15` (Kähler 1962): Metric-free outer wedge squares to zero and anticommutes. -/
theorem kahlerOuterWedge_laws {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (u v : V) :
    (kahlerOuterWedge (R := R) v).comp (kahlerOuterWedge (R := R) v) = 0 ∧
      (kahlerOuterWedge (R := R) u).comp (kahlerOuterWedge (R := R) v) +
        (kahlerOuterWedge (R := R) v).comp (kahlerOuterWedge (R := R) u) = 0 := by
  constructor
  · apply LinearMap.ext; intro ω
    simp only [kahlerOuterWedge, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', LinearMap.zero_apply]
    rw [← _root_.mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  · apply LinearMap.ext; intro ω
    simp only [kahlerOuterWedge, LinearMap.add_apply, LinearMap.comp_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', LinearMap.zero_apply]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul,
      ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/-- `S2-15` (Kähler 1962; Chevalley): Canonical anticommutation between interior contraction
and exterior wedge over any `[CommRing R]`. -/
theorem kahlerInnerContract_wedge_CAR {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (φ : Module.Dual R V) (v : V) :
    (kahlerInnerContract (R := R) φ).comp (kahlerOuterWedge (R := R) v) +
        (kahlerOuterWedge (R := R) v).comp (kahlerInnerContract (R := R) φ) =
      φ v • LinearMap.id := by
  apply LinearMap.ext; intro ω
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) φ
      (ExteriorAlgebra.ι R v * ω) +
      ExteriorAlgebra.ι R v *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) φ ω = φ v • ω
  rw [CliffordAlgebra.contractLeft_ι_mul]
  abel

/-- `S2-15` (Kähler 1962; Sushch `15b` §3; Chevalley): Metric-dependent Kähler–Clifford
generator `v ∨_g := (v ∧ ·) + (g v ⌋ ·)` on `ExteriorAlgebra R V`. -/
def kahlerCliffordGenerator {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (g : LinearMap.BilinForm R V) (v : V) :
    Module.End R (ExteriorAlgebra R V) :=
  kahlerOuterWedge (R := R) v + kahlerInnerContract (R := R) (g v)

/-- `S2-15` (Kähler 1962; Sushch `15b` §3; ABS Prop. (5.10)): Anticommutation relation
`{v ∨_g, u ∨_g} = (g(u, v) + g(v, u)) • 1` on `ExteriorAlgebra R V` over any `[CommRing R]`. -/
theorem kahlerCliffordGenerator_anticomm {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (g : LinearMap.BilinForm R V) (u v : V) :
    kahlerCliffordGenerator g u * kahlerCliffordGenerator g v +
        kahlerCliffordGenerator g v * kahlerCliffordGenerator g u =
      (g u v + g v u) • (1 : Module.End R (ExteriorAlgebra R V)) := by
  dsimp [kahlerCliffordGenerator]
  have hw := kahlerOuterWedge_laws (R := R) u v
  have hwuu : (kahlerOuterWedge (R := R) u).comp (kahlerOuterWedge (R := R) u) = 0 :=
    (kahlerOuterWedge_laws (R := R) u u).1
  have hcc :
      (kahlerInnerContract (R := R) (g u)).comp (kahlerInnerContract (R := R) (g v)) +
        (kahlerInnerContract (R := R) (g v)).comp (kahlerInnerContract (R := R) (g u)) = 0 := by
    apply LinearMap.ext; intro ω
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (g u)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (g v) ω) +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (g v)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (g u) ω) = 0
    rw [CliffordAlgebra.contractLeft_comm]
    abel
  have hcar1 := kahlerInnerContract_wedge_CAR (R := R) (g u) v
  have hcar2 := kahlerInnerContract_wedge_CAR (R := R) (g v) u
  have hcar_sum :
      ((kahlerInnerContract (R := R) (g u)).comp (kahlerOuterWedge (R := R) v) +
        (kahlerOuterWedge (R := R) v).comp (kahlerInnerContract (R := R) (g u))) +
      ((kahlerInnerContract (R := R) (g v)).comp (kahlerOuterWedge (R := R) u) +
        (kahlerOuterWedge (R := R) u).comp (kahlerInnerContract (R := R) (g v))) =
      (g u v + g v u) • LinearMap.id := by
    rw [hcar1, hcar2, add_smul]
  change (kahlerOuterWedge u + kahlerInnerContract (g u)).comp
      (kahlerOuterWedge v + kahlerInnerContract (g v)) +
    (kahlerOuterWedge v + kahlerInnerContract (g v)).comp
      (kahlerOuterWedge u + kahlerInnerContract (g u)) =
    (g u v + g v u) • LinearMap.id
  calc
    (kahlerOuterWedge u + kahlerInnerContract (g u)).comp
        (kahlerOuterWedge v + kahlerInnerContract (g v)) +
      (kahlerOuterWedge v + kahlerInnerContract (g v)).comp
        (kahlerOuterWedge u + kahlerInnerContract (g u))
        = ((kahlerOuterWedge u).comp (kahlerOuterWedge v) +
            (kahlerOuterWedge v).comp (kahlerOuterWedge u)) +
          ((kahlerInnerContract (g u)).comp (kahlerInnerContract (g v)) +
            (kahlerInnerContract (g v)).comp (kahlerInnerContract (g u))) +
          (((kahlerInnerContract (g u)).comp (kahlerOuterWedge v) +
            (kahlerOuterWedge v).comp (kahlerInnerContract (g u))) +
           ((kahlerInnerContract (g v)).comp (kahlerOuterWedge u) +
            (kahlerOuterWedge u).comp (kahlerInnerContract (g v)))) := by
          simp only [LinearMap.add_comp, LinearMap.comp_add]
          abel
    _ = 0 + 0 + (g u v + g v u) • LinearMap.id := by rw [hw.2, hcc, hcar_sum]
    _ = (g u v + g v u) • LinearMap.id := by rw [zero_add, zero_add]

/-- `S2-15` (Kähler 1962; ABS Prop. (5.10)): Lifted Clifford algebra action
`CliffordAlgebra g.toQuadraticMap →ₐ[R] Module.End R (ExteriorAlgebra R V)` generated
by `v ↦ (v ∧ ·) + (g v ⌋ ·)`. -/
def kahlerCliffordHom {R V : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] (g : LinearMap.BilinForm R V) :
    CliffordAlgebra g.toQuadraticMap →ₐ[R] Module.End R (ExteriorAlgebra R V) :=
  CliffordAlgebra.lift g.toQuadraticMap
    ⟨{ toFun := kahlerCliffordGenerator g
       map_add' := fun u v => by
         dsimp [kahlerCliffordGenerator, kahlerOuterWedge, kahlerInnerContract]
         apply LinearMap.ext; intro ω
         simp only [LinearMap.add_apply, LinearMap.mul_apply', map_add]
         abel
       map_smul' := fun r v => by
         dsimp [kahlerCliffordGenerator, kahlerOuterWedge, kahlerInnerContract]
         apply LinearMap.ext; intro ω
         simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.mul_apply',
           map_smul, smul_add] },
     fun v => by
       have hanti := kahlerCliffordGenerator_anticomm g v v
       have hsq2 : (2 : R) • (kahlerCliffordGenerator g v * kahlerCliffordGenerator g v) =
           (2 : R) • (g.toQuadraticMap v • (1 : Module.End R (ExteriorAlgebra R V))) := by
         calc
           (2 : R) • (kahlerCliffordGenerator g v * kahlerCliffordGenerator g v)
               = kahlerCliffordGenerator g v * kahlerCliffordGenerator g v +
                   kahlerCliffordGenerator g v * kahlerCliffordGenerator g v := two_smul R _
           _ = (g v v + g v v) • (1 : Module.End R (ExteriorAlgebra R V)) := hanti
           _ = (2 : R) • (g.toQuadraticMap v • (1 : Module.End R (ExteriorAlgebra R V))) := by
               rw [← two_smul R (g v v), LinearMap.BilinMap.toQuadraticMap_apply,
                 smul_eq_mul, mul_smul]
       have h1 := congrArg (fun T => (⅟(2 : R)) • T) hsq2
       simpa [smul_smul, invOf_mul_self, one_smul, Algebra.algebraMap_eq_smul_one] using h1⟩

/-- `S2-15` (Kähler 1962; Hestenes `16a2` eq. (1.7)): Under `CliffordAlgebra.equivExterior Q`,
left Clifford multiplication by a vector `ι Q m` splits into Kähler's outer wedge plus
metric-dependent interior contraction:
`equivExterior Q (ι Q m * x) = ι m * equivExterior Q x + contractLeft (Q.associated m) (equivExterior Q x)`. -/
theorem equivExterior_ι_mul {R M : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (m : M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m * x) =
      ExteriorAlgebra.ι R m * CliffordAlgebra.equivExterior Q x +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
          (QuadraticMap.associated (R := R) Q m) (CliffordAlgebra.equivExterior Q x) := by
  change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
      (CliffordAlgebra.ι Q m * x) = _
  rw [CliffordAlgebra.changeForm_ι_mul]
  change ExteriorAlgebra.ι R m * CliffordAlgebra.equivExterior Q x -
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
        (QuadraticMap.associated (R := R) (-Q) m) (CliffordAlgebra.equivExterior Q x) = _
  have hassoc : QuadraticMap.associated (R := R) (-Q) m =
      -(QuadraticMap.associated (R := R) Q m) := by
    ext n
    simp only [LinearMap.neg_apply, QuadraticMap.associated_apply, neg_apply]
    have hneg : -Q (m + n) - -Q m - -Q n = -(Q (m + n) - Q m - Q n) := by ring
    rw [hneg, smul_neg]
  rw [hassoc, map_neg, LinearMap.neg_apply, sub_neg_eq_add]

end InnerOuterAlgebra

section KahlerDiracOperator

/-- `S2-15` (Kähler 1960/62; Kruglov `15a` §1 eq. (1); ABS `18a` Prop. (5.10)): Algebraic
Kähler–Dirac operator `d - δ` on `ExteriorAlgebra R V` from `FormHodgeCliffordData`
(contrasting with `hodgeDirac := d + δ` in `ZornDifferentialFormsCliffordBridge`). -/
def kahlerDirac {R V C : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Semiring C] [Algebra R C] (D : FormHodgeCliffordData R V C) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  D.differential - hodgeCodifferential D

/-- `S2-15` (Kähler 1960/62): Algebraic Hodge–Laplacian `d ∘ δ + δ ∘ d` on
`ExteriorAlgebra R V`. -/
def kahlerHodgeLaplacian {R V C : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Semiring C] [Algebra R C] (D : FormHodgeCliffordData R V C) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  D.differential.comp (hodgeCodifferential D) + (hodgeCodifferential D).comp D.differential

/-- `S2-15` (Kruglov `15a` §1 eq. (1)–(2); ABS eq. (5.10)): `(d - δ)² = -(dδ + δd)`. -/
theorem kahlerDirac_sq_eq_neg_laplacian {R V C : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [Semiring C] [Algebra R C]
    (D : FormHodgeCliffordData R V C) :
    (kahlerDirac D).comp (kahlerDirac D) = -kahlerHodgeLaplacian D := by
  dsimp [kahlerDirac, kahlerHodgeLaplacian]
  rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub,
    D.differential_sq, hodgeCodifferential_sq, zero_sub, sub_zero]
  abel

/-- `S2-15` (Sign Contrast: Kruglov `15a` `d - δ` vs. Sushch `15b` `d + δ`):
`(hodgeDirac D)² = +(dδ + δd)` while `(kahlerDirac D)² = -(dδ + δd)`. -/
theorem kahlerDirac_vs_hodgeDirac_sq {R V C : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [Semiring C] [Algebra R C]
    (D : FormHodgeCliffordData R V C) :
    (kahlerDirac D).comp (kahlerDirac D) = -(hodgeDirac D).comp (hodgeDirac D) := by
  rw [kahlerDirac_sq_eq_neg_laplacian, hodgeDirac_comp_hodgeDirac]
  rfl

/-- `S2-15` (Bridge to `ChiralHodgeDifferential.Data.diracKahler`): For any chiral Hodge
data `D : ChiralHodgeDifferential.Data H`, its `diracKahler = d - δ` and `hodgeDirac = d + δ`
satisfy `(diracKahler)² = -hodgeLaplacian = -(hodgeDirac)²`. -/
theorem chiralHodgeData_diracKahler_compatibility {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (D : InfoGeometry.Dynamics.ChiralHodgeDifferential.Data (H := H)) :
    D.diracKahler * D.diracKahler = -D.hodgeLaplacian ∧
      D.hodgeDirac * D.hodgeDirac = D.hodgeLaplacian := by
  exact ⟨D.diracKahler_sq_neg_laplacian, D.hodgeDirac_sq⟩

/-- `S2-15` (Kähler 1962; `equivExterior` transport): Kähler–Dirac operator transported to
`CliffordAlgebra D.Q` across `CliffordAlgebra.equivExterior D.Q`. -/
def cliffordKahlerDirac {R V C : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Semiring C] [Algebra R C]
    (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₗ[R] CliffordAlgebra D.Q :=
  cliffordDifferential D - cliffordCodifferential D

/-- `S2-15` (Kähler 1962; Kruglov `15a` §1 eq. (1)): Transported Clifford Kähler–Dirac
square identity `(cliffordKahlerDirac D)² = -(d_Cl ∘ δ_Cl + δ_Cl ∘ d_Cl)`. -/
theorem cliffordKahlerDirac_sq_eq_neg_laplacian {R V C : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Semiring C] [Algebra R C]
    (D : FormHodgeCliffordData R V C) :
    (cliffordKahlerDirac D).comp (cliffordKahlerDirac D) =
      -(cliffordDifferential D).comp (cliffordCodifferential D) -
        (cliffordCodifferential D).comp (cliffordDifferential D) := by
  apply LinearMap.ext; intro x
  apply (CliffordAlgebra.equivExterior D.Q).injective
  have h1 : ∀ y : CliffordAlgebra D.Q,
      CliffordAlgebra.equivExterior D.Q (cliffordKahlerDirac D y) =
        kahlerDirac D (CliffordAlgebra.equivExterior D.Q y) := by
    intro y
    change CliffordAlgebra.equivExterior D.Q
        (cliffordDifferential D y - cliffordCodifferential D y) =
      D.differential (CliffordAlgebra.equivExterior D.Q y) -
        hodgeCodifferential D (CliffordAlgebra.equivExterior D.Q y)
    rw [map_sub, equivExterior_cliffordDifferential, equivExterior_cliffordCodifferential]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.neg_apply]
  rw [h1, h1, map_sub, map_neg, equivExterior_cliffordDifferential,
    equivExterior_cliffordCodifferential, equivExterior_cliffordCodifferential,
    equivExterior_cliffordDifferential]
  have hsq := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V =>
      f (CliffordAlgebra.equivExterior D.Q x)) (kahlerDirac_sq_eq_neg_laplacian D)
  rw [kahlerHodgeLaplacian, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply] at hsq
  rw [hsq]
  abel

/-- `S2-15` (`R3.2` Metric-Free `d` vs. Metric-Dependent `★`/`δ` Isometry Equivariance):
When `d` commutes with `ExteriorAlgebra.map g` and `★` scales by `ε` (`ε * ε = 1`),
`cliffordKahlerDirac D` is strictly `g`-equivariant. -/
theorem cliffordKahlerDirac_equivOfIsometry {R V C : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Semiring C] [Algebra R C]
    (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (ε : R) (hε : ε * ε = 1)
    (hd : (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.comp D.differential =
      D.differential.comp (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap)
    (hs : (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.comp D.hodgeStar =
      ε • (D.hodgeStar.comp (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap))
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivOfIsometry g (cliffordKahlerDirac D x) =
      cliffordKahlerDirac D (CliffordAlgebra.equivOfIsometry g x) := by
  have hcod : ∀ ω, ExteriorAlgebra.map (g : V →ₗ[R] V) (hodgeCodifferential D ω) =
      hodgeCodifferential D (ExteriorAlgebra.map (g : V →ₗ[R] V) ω) := by
    intro ω
    have hd_apply : ∀ η, ExteriorAlgebra.map (g : V →ₗ[R] V) (D.differential η) =
        D.differential (ExteriorAlgebra.map (g : V →ₗ[R] V) η) := fun η =>
      congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f η) hd
    have hs_apply : ∀ η, ExteriorAlgebra.map (g : V →ₗ[R] V) (D.hodgeStar η) =
        ε • D.hodgeStar (ExteriorAlgebra.map (g : V →ₗ[R] V) η) := fun η =>
      congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f η) hs
    dsimp [hodgeCodifferential]
    rw [hs_apply, hd_apply, hs_apply, D.differential.map_smul, D.hodgeStar.map_smul,
      smul_smul, hε, one_smul]
  have hd_apply : ∀ ω, ExteriorAlgebra.map (g : V →ₗ[R] V) (D.differential ω) =
      D.differential (ExteriorAlgebra.map (g : V →ₗ[R] V) ω) := fun ω =>
    congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω) hd
  apply (CliffordAlgebra.equivExterior D.Q).injective
  change CliffordAlgebra.equivExterior D.Q
      (CliffordAlgebra.equivOfIsometry g (cliffordDifferential D x - cliffordCodifferential D x)) =
    CliffordAlgebra.equivExterior D.Q
      (cliffordDifferential D (CliffordAlgebra.equivOfIsometry g x) -
        cliffordCodifferential D (CliffordAlgebra.equivOfIsometry g x))
  rw [map_sub, map_sub, equivExterior_equivOfIsometry, equivExterior_equivOfIsometry,
    map_sub, equivExterior_cliffordDifferential, equivExterior_cliffordCodifferential,
    equivExterior_cliffordDifferential, equivExterior_cliffordCodifferential,
    equivExterior_equivOfIsometry, hd_apply, hcod]

/-- `S2-15` (Nontrivial Contraction & `(d - δ)² = -id` Witness): On `ExteriorAlgebra ℝ (Fin 2 → ℝ)`
with `d := kahlerOuterWedge ![1, 0]` and `δ := kahlerInnerContract (LinearMap.proj 0)`,
`d² = 0`, `δ² = 0`, and `(d - δ)² = -LinearMap.id ≠ 0`. Smooth curved-manifold Hodge PDE
decomposition remains `BUCKET 3 / O-EXT` outside this algebraic module. -/
theorem kahlerDirac_with_contraction_witness :
    let d := kahlerOuterWedge (R := ℝ) (V := Fin 2 → ℝ) ![1, 0]
    let delta := kahlerInnerContract (R := ℝ) (V := Fin 2 → ℝ) (LinearMap.proj 0)
    d.comp d = 0 ∧ delta.comp delta = 0 ∧
      (d - delta).comp (d - delta) = -(LinearMap.id : Module.End ℝ (ExteriorAlgebra ℝ (Fin 2 → ℝ))) ∧
      (d - delta).comp (d - delta) ≠ 0 := by
  intro d delta
  have hd2 : d.comp d = 0 := (kahlerOuterWedge_laws (R := ℝ) ![1, 0] ![1, 0]).1
  have hdelta2 : delta.comp delta = 0 := by
    apply LinearMap.ext; intro ω
    exact CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm ℝ (Fin 2 → ℝ)))
      (LinearMap.proj 0) ω
  have hcar : delta.comp d + d.comp delta = LinearMap.id := by
    have h := kahlerInnerContract_wedge_CAR (R := ℝ) (V := Fin 2 → ℝ) (LinearMap.proj 0) ![1, 0]
    simpa [d, delta] using h
  have hsq : (d - delta).comp (d - delta) = -LinearMap.id := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub, hd2, hdelta2, zero_sub,
      sub_zero]
    calc
      -d.comp delta - delta.comp d = -(delta.comp d + d.comp delta) := by abel
      _ = -LinearMap.id := by rw [hcar]
  have hne : (d - delta).comp (d - delta) ≠ 0 := by
    intro h0
    rw [hsq] at h0
    have h1 := congrArg (fun f : ExteriorAlgebra ℝ (Fin 2 → ℝ) →ₗ[ℝ]
        ExteriorAlgebra ℝ (Fin 2 → ℝ) => f 1) h0
    simp only [LinearMap.neg_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1
    have hinv := congrArg ExteriorAlgebra.algebraMapInv h1
    simp only [map_neg, map_one, map_zero, neg_eq_zero] at hinv
    exact one_ne_zero hinv
  exact ⟨hd2, hdelta2, hsq, hne⟩

end KahlerDiracOperator

end KahlerPrimary

/-!
## Section 2 (`S2-16`): Hestenes (1966) & Darboux (1887) Moving-Frame Rotor Equation `R' = (1/2) Ω R`
-/

section HestenesDarbouxPrimary

section AbstractHestenesRotor

variable {R_coeff M : Type*} [CommRing R_coeff] [Invertible (2 : R_coeff)]
variable [AddCommGroup M] [Module R_coeff M]

/-- `S2-16` (Hestenes `16a2` §5 eq. (5.4), p. 18; Darboux `16b` Livre I Ch. I eq. (15), p. 7):
Moving-frame rotor derivative `R' := ⅟2 • (Ω * R)` generated by angular velocity bivector `Ω`
(`R3.2`). -/
def hestenesRotorDeriv {Q : QuadraticForm R_coeff M} (Ω R : CliffordAlgebra Q) :
    CliffordAlgebra Q :=
  (⅟(2 : R_coeff)) • (Ω * R)

/-- `S2-16` (Hestenes `16a2` §1 & §5 eq. (5.5), p. 19): Commutator product
`Ω × X := ⅟2 • [Ω, X]`, realizing `Ω · e_a` on bivector `Ω` and frame vector `e_a`. -/
def hestenesBivectorCommutator {Q : QuadraticForm R_coeff M} (Ω X : CliffordAlgebra Q) :
    CliffordAlgebra Q :=
  (⅟(2 : R_coeff)) • clCommutator Ω X

/-- `S2-16` (Factor-of-2 Alignment: Hestenes `16a2` eq. (5.4) vs.
`CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.clRotorDarbouxConnection`):
For `dR := hestenesRotorDeriv Ω R = ⅟2 • (Ω * R)` and normalized rotor `R * reverse R = 1`,
`clRotorDarbouxConnection R dR = ⅟2 • Ω`, equivalently `Ω = (2 : R_coeff) • clRotorDarbouxConnection R dR`. -/
theorem hestenesRotor_darboux_connection_eq_half {Q : QuadraticForm R_coeff M}
    (Ω R : CliffordAlgebra Q) (h_mul_rev : R * CliffordAlgebra.reverse R = 1) :
    clRotorDarbouxConnection R (hestenesRotorDeriv Ω R) = (⅟(2 : R_coeff)) • Ω ∧
      Ω = (2 : R_coeff) • clRotorDarbouxConnection R (hestenesRotorDeriv Ω R) := by
  have h1 : clRotorDarbouxConnection R (hestenesRotorDeriv Ω R) = (⅟(2 : R_coeff)) • Ω := by
    dsimp [clRotorDarbouxConnection, hestenesRotorDeriv]
    rw [smul_mul_assoc, _root_.mul_assoc, h_mul_rev, _root_.mul_one]
  refine ⟨h1, ?_⟩
  rw [h1, smul_smul, mul_invOf_self, one_smul]

/-- `S2-16` (Hestenes `16a2` §5 p. 19; Darboux `16b` p. 7): Skew-reversion `reverse Ω = -Ω`
is the exact algebraic condition preserving rotor normalization `R * reverse R = 1`
infinitesimally: `dR * reverse R + R * reverse dR = 0` for `dR = ⅟2 • (Ω * R)`. -/
theorem hestenesRotor_preserves_normalization_diff {Q : QuadraticForm R_coeff M}
    (Ω R : CliffordAlgebra Q) (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_Ω : CliffordAlgebra.reverse Ω = -Ω) :
    hestenesRotorDeriv Ω R * CliffordAlgebra.reverse R +
      R * CliffordAlgebra.reverse (hestenesRotorDeriv Ω R) = 0 := by
  dsimp [hestenesRotorDeriv]
  rw [map_smul, CliffordAlgebra.reverse.map_mul, h_rev_Ω, mul_neg, smul_neg,
    smul_mul_assoc, _root_.mul_assoc, h_mul_rev, _root_.mul_one,
    mul_neg, mul_smul_comm, ← _root_.mul_assoc, h_mul_rev, _root_.one_mul, add_neg_cancel]

/-- `S2-16` (Hestenes `16a2` §5 eq. (5.5), p. 19): Moving-frame transport equation
`d/dτ (R γ R̃) = ⅟2 • [Ω, R γ R̃]` derived from `dR = ⅟2 • (Ω * R)` and `reverse Ω = -Ω`. -/
theorem hestenesRotor_frame_transport {Q : QuadraticForm R_coeff M}
    (Ω R γ : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1)
    (h_rev_Ω : CliffordAlgebra.reverse Ω = -Ω) :
    clRotorFrameDerivative R (hestenesRotorDeriv Ω R)
        (CliffordAlgebra.reverse (hestenesRotorDeriv Ω R)) γ 0 =
      hestenesBivectorCommutator Ω (clRotorFrameVector R γ) := by
  have hdnorm := hestenesRotor_preserves_normalization_diff Ω R h_mul_rev h_rev_Ω
  rw [clRotor_darboux_spin_connection_identity_const R (hestenesRotorDeriv Ω R)
      (CliffordAlgebra.reverse (hestenesRotorDeriv Ω R)) γ h_rev_mul hdnorm,
    (hestenesRotor_darboux_connection_eq_half Ω R h_mul_rev).1]
  dsimp [hestenesBivectorCommutator, clCommutator]
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

/-- `S2-16` (R1 `MaurerCartanTower` & `DerivationLieLane` Coupling): Hestenes bivector
angular velocity `Ω_x := 2 • thetaR (reverseCommutingLane Q) R_u ![x]` along any
`reverse`-commuting derivation `x` satisfies `reverse Ω_x = -Ω_x`, `D_x R = ⅟2 • (Ω_x * R)`,
and `D_x (R γ R̃) = ⅟2 • [Ω_x, R γ R̃] + R (D_x γ) R̃`. -/
def hestenesDerivationOmega {Q : QuadraticForm R_coeff M}
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (x : (reverseCommutingLane Q).L) : CliffordAlgebra Q :=
  (2 : R_coeff) •
    InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR (reverseCommutingLane Q)
      (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x]

/-- `S2-16` (Hestenes `16a2` §5 eqs. (5.4)–(5.5); `reverseCommutingLane`): Angular velocity
`Ω_x` is skew under `reverse`, satisfies `D_x R = ⅟2 • (Ω_x * R)`, and transports moving
frames via `D_x (R γ R̃) = ⅟2 • [Ω_x, R γ R̃] + R (D_x γ) R̃`. -/
theorem hestenesDerivation_rotor_and_frame_laws {Q : QuadraticForm R_coeff M}
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (x : (reverseCommutingLane Q).L) (γ : CliffordAlgebra Q) :
    CliffordAlgebra.reverse (hestenesDerivationOmega R_cl h_mul_rev h_rev_mul x) =
        -(hestenesDerivationOmega R_cl h_mul_rev h_rev_mul x) ∧
      (reverseCommutingLane Q).operatorAction x R_cl =
        hestenesRotorDeriv (hestenesDerivationOmega R_cl h_mul_rev h_rev_mul x) R_cl ∧
      (reverseCommutingLane Q).operatorAction x (clRotorFrameVector R_cl γ) =
        hestenesBivectorCommutator (hestenesDerivationOmega R_cl h_mul_rev h_rev_mul x)
          (clRotorFrameVector R_cl γ) +
          clRotorFrameVector R_cl ((reverseCommutingLane Q).operatorAction x γ) := by
  let Ω := hestenesDerivationOmega R_cl h_mul_rev h_rev_mul x
  have hrev : CliffordAlgebra.reverse Ω = -Ω := by
    change CliffordAlgebra.reverse
        ((2 : R_coeff) • InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR
          (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x]) =
      -((2 : R_coeff) • InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR
        (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x])
    rw [map_smul, reverseCommutingLane_thetaR_reverse_eq_neg, smul_neg]
  have htheta : InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR (reverseCommutingLane Q)
      (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x] =
      ((reverseCommutingLane Q).operatorAction x R_cl) * CliffordAlgebra.reverse R_cl := rfl
  have hderiv : (reverseCommutingLane Q).operatorAction x R_cl = hestenesRotorDeriv Ω R_cl := by
    change (reverseCommutingLane Q).operatorAction x R_cl =
      (⅟(2 : R_coeff)) •
        (((2 : R_coeff) • InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR
          (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x]) * R_cl)
    rw [htheta, smul_mul_assoc, smul_smul, invOf_mul_self, one_smul,
      _root_.mul_assoc, h_rev_mul, _root_.mul_one]
  have hframe := clRotor_actionExteriorDerivative_frame
    (reverseCommutingLane Q).toLieActionLane (reverseCommutingLane Q).isLeibnizAction
    R_cl h_mul_rev h_rev_mul γ x
  have hcomm_eq :
      clCommutator
        (InfoGeometry.OperatorAlgebra.MaurerCartanTower.actionThetaR
          (reverseCommutingLane Q).toLieActionLane (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x])
        (clRotorFrameVector R_cl γ) =
      hestenesBivectorCommutator Ω (clRotorFrameVector R_cl γ) := by
    change clCommutator
        (InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR (reverseCommutingLane Q)
          (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x])
        (clRotorFrameVector R_cl γ) =
      (⅟(2 : R_coeff)) • clCommutator
        ((2 : R_coeff) • InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR
          (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x])
        (clRotorFrameVector R_cl γ)
    dsimp [clCommutator]
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul, invOf_mul_self, one_smul]
  have hframe' : (reverseCommutingLane Q).operatorAction x (clRotorFrameVector R_cl γ) =
      hestenesBivectorCommutator Ω (clRotorFrameVector R_cl γ) +
        clRotorFrameVector R_cl ((reverseCommutingLane Q).operatorAction x γ) := by
    rw [← hcomm_eq]
    exact hframe
  exact ⟨hrev, hderiv, hframe'⟩

omit [Invertible (2 : R_coeff)] in
/-- `S2-16` (Maurer–Cartan Equation for the Darboux Spin Connection along `reverseCommutingLane`):
`d(θ_R) = θ_R ∧ θ_R` and `F(θ_L u⁻¹) = 0` (`clRotorDarboux_derivation_maurerCartan`). -/
theorem hestenesDerivation_maurerCartan {Q : QuadraticForm R_coeff M}
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1) :
    InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.ceExteriorDerivative
        (reverseCommutingLane Q) 1
        (InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR (reverseCommutingLane Q)
          (clRotorUnit R_cl h_mul_rev h_rev_mul)) =
      InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.ceWedge (reverseCommutingLane Q)
        (InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR (reverseCommutingLane Q)
          (clRotorUnit R_cl h_mul_rev h_rev_mul))
        (InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaR (reverseCommutingLane Q)
          (clRotorUnit R_cl h_mul_rev h_rev_mul)) ∧
      InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.ceCurvature
        (reverseCommutingLane Q)
        (InfoGeometry.OperatorAlgebra.MaurerCartanTower.thetaL (reverseCommutingLane Q)
          (clRotorUnit R_cl h_mul_rev h_rev_mul)⁻¹) = 0 :=
  clRotorDarboux_derivation_maurerCartan (reverseCommutingLane Q) R_cl h_mul_rev h_rev_mul

end AbstractHestenesRotor

section HestenesConcreteAndDim3

private local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- `S2-16` (Hestenes `16a2` §5): In dimension `≤ 3` over `ℝ`, every even angular velocity
`Ω` with `reverse Ω = -Ω` lies in pure grade `2` (`cliffordGradeSubmodule Q 2`). -/
theorem hestenesRotor_grade2_of_dim_le_three {M_real : Type*}
    [AddCommGroup M_real] [Module ℝ M_real] [Module.Finite ℝ M_real]
    (hdim : Module.finrank ℝ M_real ≤ 3) (Q : QuadraticForm ℝ M_real)
    (Ω : CliffordAlgebra Q) (heven : Ω ∈ CliffordAlgebra.evenOdd Q 0)
    (hrev : CliffordAlgebra.reverse Ω = -Ω) :
    Ω ∈ cliffordGradeSubmodule Q 2 :=
  mem_cliffordGradeSubmodule_two_of_even_reverse_neg_finrank_le_three Q hdim heven hrev

/-- `S2-16` (Concrete `Cl(1,1)` Hyperbolic Rotor Witness): The hyperbolic rotor
`R(θ) = cosh θ + sinh θ J₁` satisfies `R'(θ) = ⅟2 • ((2 • J₁) * R(θ))`, belongs to
`spinGroup q11`, and acts via `equivOfIsometry (spinGroupToIsometryHom q11 ⟨R(θ), ...⟩)`
as a genuine `O(q11)` Lorentz boost (`R3.2`). -/
theorem cl11HyperbolicRotor_hestenes_witness (θ : ℝ) :
    cl11HyperbolicRotorDeriv θ =
        hestenesRotorDeriv ((2 : ℝ) • Cl11Matrix.J1_cl) (cl11HyperbolicRotor θ) ∧
      cl11HyperbolicRotor θ ∈ _root_.spinGroup Cl11Matrix.q11 ∧
      ∀ v : Cl11Matrix.Vec11,
        CliffordAlgebra.equivOfIsometry
            (spinGroupToIsometryHom Cl11Matrix.q11
              ⟨cl11HyperbolicRotor θ, cl11HyperbolicRotor_mem_spinGroup θ⟩)
            (CliffordAlgebra.ι Cl11Matrix.q11 v) =
          clRotorFrameVector (cl11HyperbolicRotor θ) (CliffordAlgebra.ι Cl11Matrix.q11 v) := by
  have hd : cl11HyperbolicRotorDeriv θ =
      hestenesRotorDeriv ((2 : ℝ) • Cl11Matrix.J1_cl) (cl11HyperbolicRotor θ) := by
    dsimp [hestenesRotorDeriv]
    rw [smul_mul_assoc, smul_smul, invOf_mul_self, one_smul]
    have hdarb := cl11HyperbolicRotor_darboux θ
    dsimp [clRotorDarbouxConnection] at hdarb
    calc
      cl11HyperbolicRotorDeriv θ
          = cl11HyperbolicRotorDeriv θ *
              (CliffordAlgebra.reverse (cl11HyperbolicRotor θ) * cl11HyperbolicRotor θ) := by
            rw [cl11HyperbolicRotor_reverse_mul, _root_.mul_one]
      _ = (cl11HyperbolicRotorDeriv θ * CliffordAlgebra.reverse (cl11HyperbolicRotor θ)) *
              cl11HyperbolicRotor θ := (_root_.mul_assoc _ _ _).symm
      _ = Cl11Matrix.J1_cl * cl11HyperbolicRotor θ := by rw [hdarb]
  refine ⟨hd, cl11HyperbolicRotor_mem_spinGroup θ, fun v => ?_⟩
  exact equivOfIsometry_spinGroupToIsometryHom Cl11Matrix.q11
    ⟨cl11HyperbolicRotor θ, cl11HyperbolicRotor_mem_spinGroup θ⟩ (CliffordAlgebra.ι _ v)

end HestenesConcreteAndDim3

end HestenesDarbouxPrimary

/-!
## Section 3 (`S2-17`): Jordan–Wigner (1928) Fermionic CAR & Parity-String Soldering (`R3.3`)
-/

section JordanWignerPrimary

section GradedVsUngradedTensor

open scoped TensorProduct Matrix Kronecker

/-- `S2-17` / `R3.3` (Ungraded Tensor Commutation Contrast): In any ungraded tensor product
`A ⊗[R] B`, left and right site factors `a ⊗ₜ 1` and `1 ⊗ₜ b` always commute. -/
theorem ungradedTensor_site_commute {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (a : A) (b : B) :
    (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) = ((1 : A) ⊗ₜ[R] b) * (a ⊗ₜ[R] (1 : B)) := by
  calc
    (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) = (a * 1) ⊗ₜ[R] ((1 : B) * b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    _ = a ⊗ₜ[R] b := by rw [_root_.mul_one, _root_.one_mul]
    _ = (1 * a) ⊗ₜ[R] (b * 1) := by rw [_root_.one_mul, _root_.mul_one]
    _ = ((1 : A) ⊗ₜ[R] b) * (a ⊗ₜ[R] (1 : B)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]

/-- `S2-17` / `R3.3` (Ordinary Matrix Kronecker Commutation Contrast): Without a Jordan–Wigner
parity string, ordinary matrix Kronecker factors `A ⊗ₖ 1` and `1 ⊗ₖ B` commute. -/
theorem ordinaryMatrix_site_commute (n : ℕ) (A : Cl11TensorTower.MatStage n)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) * ((1 : Cl11TensorTower.MatStage n) ⊗ₖ B) =
      ((1 : Cl11TensorTower.MatStage n) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    _root_.mul_one, _root_.one_mul, _root_.mul_one, _root_.one_mul]

/-- `S2-17` / `R3.3` (Koszul `ℤ/2`-Graded Clifford Product Equivalence):
`Cl(Q₁ ⊕ Q₂) ≃ₐ[R] evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂`. -/
def koszulCliffordProdEquiv {R M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R]
      (CliffordAlgebra.evenOdd Q₁ ᵍ⊗[R] CliffordAlgebra.evenOdd Q₂) :=
  CliffordAlgebra.prodEquiv Q₁ Q₂

/-- `S2-17` / `R3.3` (Koszul `ℤ/2`-Graded Anticommutation): In the Koszul graded tensor
product `evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂`, odd vector generators on distinct factors
strictly anticommute. -/
theorem koszulGradedTensor_odd_anticommute {R M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (v₁ : M₁) (v₂ : M₂) :
    ((CliffordAlgebra.ι Q₁ v₁ ᵍ⊗ₜ[R] (1 : CliffordAlgebra Q₂) :
        CliffordAlgebra.evenOdd Q₁ ᵍ⊗[R] CliffordAlgebra.evenOdd Q₂) *
      ((1 : CliffordAlgebra Q₁) ᵍ⊗ₜ[R] CliffordAlgebra.ι Q₂ v₂)) =
    -(((1 : CliffordAlgebra Q₁) ᵍ⊗ₜ[R] CliffordAlgebra.ι Q₂ v₂) *
      (CliffordAlgebra.ι Q₁ v₁ ᵍ⊗ₜ[R] (1 : CliffordAlgebra Q₂))) := by
  apply (CliffordAlgebra.prodEquiv Q₁ Q₂).symm.injective
  rw [map_mul, map_neg, map_mul]
  change CliffordAlgebra.toProd Q₁ Q₂ (CliffordAlgebra.ι Q₁ v₁ ᵍ⊗ₜ[R] 1) *
      CliffordAlgebra.toProd Q₁ Q₂ (1 ᵍ⊗ₜ[R] CliffordAlgebra.ι Q₂ v₂) =
    -(CliffordAlgebra.toProd Q₁ Q₂ (1 ᵍ⊗ₜ[R] CliffordAlgebra.ι Q₂ v₂) *
      CliffordAlgebra.toProd Q₁ Q₂ (CliffordAlgebra.ι Q₁ v₁ ᵍ⊗ₜ[R] 1))
  rw [CliffordAlgebra.toProd_ι_tmul_one, CliffordAlgebra.toProd_one_tmul_ι]
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (QuadraticMap.IsOrtho.inl_inr v₁ v₂)

end GradedVsUngradedTensor

section NativeSplitCARAndSoldering

private theorem qsplit_splitCoord :
    ∀ (n : ℕ) (k : Fin n) (x : ℝ × ℝ),
      Qsplit n (splitCoord n k x) = x.1 * x.1 - x.2 * x.2
  | 0, k, _ => Fin.elim0 k
  | n + 1, k, x => by
    refine Fin.lastCases ?_ ?_ k
    · rw [splitCoord_last]
      change Qsplit (n + 1) (x, 0) = x.1 * x.1 - x.2 * x.2
      rw [Qsplit_succ_apply]
      simp [InfoGeometry.Clifford.splitQ11, QuadraticMap.map_zero]
    · intro j
      rw [splitCoord_castSucc]
      change Qsplit (n + 1) ((0, 0), splitCoord n j x) = x.1 * x.1 - x.2 * x.2
      rw [Qsplit_succ_apply]
      have hj := qsplit_splitCoord n j x
      simp [InfoGeometry.Clifford.splitQ11, hj]

private theorem qsplit_splitCoord_isOrtho :
    ∀ {n : ℕ} {i j : Fin n}, i ≠ j → ∀ (x y : ℝ × ℝ),
      (Qsplit n).IsOrtho (splitCoord n i x) (splitCoord n j y)
  | 0, i, _, _, _, _ => Fin.elim0 i
  | n + 1, i, j, hij, x, y => by
    rw [QuadraticMap.isOrtho_def]
    revert hij
    refine Fin.lastCases ?_ (fun i' => ?_) i <;>
      refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
    · exfalso; exact hij rfl
    · rw [splitCoord_last, splitCoord_castSucc]
      change Qsplit (n + 1) ((x, 0) + ((0, 0), splitCoord n j' y)) =
        Qsplit (n + 1) (x, 0) + Qsplit (n + 1) ((0, 0), splitCoord n j' y)
      have hsum : ((x, (0 : SplitSpace n)) + ((0, 0), splitCoord n j' y)) =
          (x, splitCoord n j' y) := by ext <;> simp
      rw [hsum, Qsplit_succ_apply, Qsplit_succ_apply, Qsplit_succ_apply]
      simp [QuadraticMap.map_zero]
    · rw [splitCoord_castSucc, splitCoord_last]
      change Qsplit (n + 1) (((0, 0), splitCoord n i' x) + (y, 0)) =
        Qsplit (n + 1) ((0, 0), splitCoord n i' x) + Qsplit (n + 1) (y, 0)
      have hsum : (((0, 0), splitCoord n i' x) + (y, (0 : SplitSpace n))) =
          (y, splitCoord n i' x) := by ext <;> simp
      rw [hsum, Qsplit_succ_apply, Qsplit_succ_apply, Qsplit_succ_apply]
      simp [QuadraticMap.map_zero, add_comm]
    · have hij' : i' ≠ j' := fun h => hij (congrArg Fin.castSucc h)
      have ho := qsplit_splitCoord_isOrtho hij' x y
      rw [QuadraticMap.isOrtho_def] at ho
      rw [splitCoord_castSucc, splitCoord_castSucc]
      change Qsplit (n + 1) (((0, 0), splitCoord n i' x) + ((0, 0), splitCoord n j' y)) =
        Qsplit (n + 1) ((0, 0), splitCoord n i' x) +
          Qsplit (n + 1) ((0, 0), splitCoord n j' y)
      simp only [Prod.mk_add_mk, add_zero]
      rw [Qsplit_succ_apply, Qsplit_succ_apply, Qsplit_succ_apply, ho]
      simp

/-- `S2-17` (Jordan–Wigner 1928; Nielsen 2005 §II eq. (1)): Finite-stage fermionic CAR
relations in native `Clsplit n` for `nativeJWCreation` and `nativeJWAnnihilation`:
`a_k†² = 0`, `a_k² = 0`, `{a_k†, a_k} = 1`, `{a_i†, a_j†} = 0`, `{a_i†, a_j} = 0` (`i ≠ j`)
(`R3.3`). -/
theorem nativeJW_CAR_relations (n : ℕ) (i j : Fin n) :
    (nativeJWCreation n i * nativeJWCreation n i = 0) ∧
      (nativeJWAnnihilation n i * nativeJWAnnihilation n i = 0) ∧
      (nativeJWCreation n i * nativeJWAnnihilation n i +
        nativeJWAnnihilation n i * nativeJWCreation n i = 1) ∧
      (i ≠ j → nativeJWCreation n i * nativeJWCreation n j +
        nativeJWCreation n j * nativeJWCreation n i = 0) ∧
      (i ≠ j → nativeJWCreation n i * nativeJWAnnihilation n j +
        nativeJWAnnihilation n j * nativeJWCreation n i = 0) := by
  have hc2 : nativeJWCreation n i * nativeJWCreation n i = 0 := by
    dsimp [nativeJWCreation]
    rw [CliffordAlgebra.ι_sq_scalar, qsplit_splitCoord]
    norm_num
  have ha2 : nativeJWAnnihilation n i * nativeJWAnnihilation n i = 0 := by
    dsimp [nativeJWAnnihilation]
    rw [CliffordAlgebra.ι_sq_scalar, qsplit_splitCoord]
    norm_num
  have hsame : nativeJWCreation n i * nativeJWAnnihilation n i +
      nativeJWAnnihilation n i * nativeJWCreation n i = 1 := by
    dsimp [nativeJWCreation, nativeJWAnnihilation]
    rw [CliffordAlgebra.ι_mul_ι_add_swap]
    have hpol : QuadraticMap.polar (Qsplit n) (splitCoord n i (1 / 2, 1 / 2))
        (splitCoord n i (1 / 2, -1 / 2)) = 1 := by
      change Qsplit n (splitCoord n i (1 / 2, 1 / 2) + splitCoord n i (1 / 2, -1 / 2)) -
          Qsplit n (splitCoord n i (1 / 2, 1 / 2)) -
          Qsplit n (splitCoord n i (1 / 2, -1 / 2)) = 1
      rw [← map_add, show ((1 / 2 : ℝ), (1 / 2 : ℝ)) + (1 / 2, -1 / 2) = (1, 0) by ext <;> norm_num,
        qsplit_splitCoord, qsplit_splitCoord, qsplit_splitCoord]
      norm_num
    rw [hpol, map_one]
  refine ⟨hc2, ha2, hsame, fun hij => ?_, fun hij => ?_⟩
  · dsimp [nativeJWCreation]
    exact CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (qsplit_splitCoord_isOrtho hij _ _)
  · dsimp [nativeJWCreation, nativeJWAnnihilation]
    exact CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (qsplit_splitCoord_isOrtho hij _ _)

/-- `S2-17` (Jordan–Wigner 1928; Nielsen 2005 §III eq. (31); `R3.3`): Explicit parity-string
soldering summary linking native `singleSiteChain`, `nativeJWCreation`, `jwSplitStageEquiv`,
the failure of untwisted matrix tensor embeddings (`gradedTensorSuccessor_not_algHom`), and
the unconditional colimit equivalence `splitCliffordInfinityEquivLimit`. Note that Nielsen §III
eq. (31) carries an overall minus sign convention `a_j = -(⊗_{k<j} Z_k) ⊗ σ_j` relative to
the positive parity-string convention. -/
theorem jw_parity_string_soldering_summary (n : ℕ) (k : Fin n) :
    (InfoGeometry.Clifford.Cl11RecursiveUnrolling.leftMatrixEquiv n (singleSiteChain n k nullPlus) =
        ordinaryChain n (fun j =>
          if j < k then Cl11Matrix.J1
          else if j = k then Cl11Matrix.cl11EquivMat nullPlus
          else 1)) ∧
      (singleSiteChain n k nullPlus = nativeJWCreation n (Fin.rev k)) ∧
      (jwSplitStageEquiv n (nativeJWCreation n k) = Cl11TensorTower.jwCreation n k) ∧
      (¬ ∃ F : InfoGeometry.Clifford.GammaMatrices.SplitGammaMatrix n →ₐ[ℝ]
          InfoGeometry.Clifford.GammaMatrices.SplitGammaMatrix (n + 1),
        F.toLinearMap =
          InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering.gradedTensorSuccessor n) ∧
      (Nonempty (InfoGeometry.Canonical.SplitCliffordDirectLimit.SplitCliffordInfinity ≃ₐ[ℝ]
        Cl11TensorTowerLimit.Limit)) := by
  refine ⟨leftMatrixEquiv_singleSiteChain_nullPlus n k,
    singleSiteChain_nullPlus_eq_nativeJWCreation_rev n k,
    jwSplitStageEquiv_nativeJWCreation n k,
    InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering.gradedTensorSuccessor_not_algHom n,
    ⟨splitCliffordInfinityEquivLimit⟩⟩

end NativeSplitCARAndSoldering

end JordanWignerPrimary

/-!
## Section 4 (`S2-18`): Atiyah–Bott–Shapiro (1964) Koszul `ᵍ⊗`, Graded Module Restriction `i*`,
& Grothendieck Cokernel (`R3.3`)
-/

section AtiyahBottShapiroPrimary

section ABSConventionsAndSuspension

open scoped TensorProduct

/-- `S2-18` (Atiyah–Bott–Shapiro 1964 §2 eq. (2.3) & Table 1, pp. 6, 11): ABS negative-definite
quadratic form `Q_k(x) = -∑ x_i²` whose Clifford algebra `C_k := CliffordAlgebra (absNegForm k)`
satisfies `e_i² = -1` (in contrast to `C'_k := Cl_{k,0}` with `e'_i² = +1`). -/
def absNegForm (k : ℕ) : QuadraticForm ℝ (Fin k → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin k => (-1 : ℝ))

/-- `S2-18` (ABS 1964 §2 & §4 Table 1, p. 11): Positive-definite quadratic form
`Q'_k(x) = +∑ x_i²` generating `C'_k = Cl_{k,0}` with `(e'_i)² = +1`. -/
def absPosForm (k : ℕ) : QuadraticForm ℝ (Fin k → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin k => (1 : ℝ))

/-- `S2-18` (ABS 1964 §2 eq. (2.3)): Generator square signs `e_i² = -1` in `C_k` versus
`(e'_i)² = +1` in `C'_k`. -/
theorem abs_neg_vs_pos_generator_sq (k : ℕ) (i : Fin k) :
    CliffordAlgebra.ι (absNegForm k) (Pi.single i 1) *
        CliffordAlgebra.ι (absNegForm k) (Pi.single i 1) = -1 ∧
      CliffordAlgebra.ι (absPosForm k) (Pi.single i 1) *
        CliffordAlgebra.ι (absPosForm k) (Pi.single i 1) = 1 := by
  constructor
  · have hq : absNegForm k (Pi.single i 1) = -1 := by
      simp [absNegForm, QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
    rw [CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one]
  · have hq : absPosForm k (Pi.single i 1) = 1 := by
      simp [absPosForm, QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
    rw [CliffordAlgebra.ι_sq_scalar, hq, map_one]

/-- `S2-18` (ABS 1964 §1 Prop. (1.6), p. 5; `R3.3`): Koszul `ℤ/2`-graded tensor splitting
of the step suspension `Cl(Q ⊕ ⟨-1⟩) ≃ₐ[R] Cl(Q) ᵍ⊗[R] Cl(-sq)`. -/
def absStepSuspensionEquiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :
    CliffordAlgebra (positiveForm Q) ≃ₐ[R]
      (CliffordAlgebra.evenOdd Q ᵍ⊗[R] CliffordAlgebra.evenOdd (-QuadraticMap.sq (R := R))) :=
  CliffordAlgebra.prodEquiv Q (-QuadraticMap.sq (R := R))

/-- `S2-18` (ABS 1964 §2–§5): Coordinate-free `positiveForm (absNegForm k)` is isometric
to `absNegForm (k + 1)` (`Cl_{0,k} ⊕ ⟨-1⟩ ≃qᵢ Cl_{0,k+1}`). -/
theorem absNegForm_succ_isometry (k : ℕ) :
    Nonempty ((positiveForm (absNegForm k)).IsometryEquiv (absNegForm (k + 1))) := by
  refine ⟨{
    toLinearEquiv :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun f => (fun i => f i.castSucc, f (Fin.last k))
        left_inv := fun p => by
          ext i
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun f => by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc_last]
          · intro j; simp [Fin.snoc_castSucc]
        map_add' := fun p q => by
          ext i
          refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc_last, Fin.snoc_castSucc]
        map_smul' := fun c p => by
          ext i
          refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc_last, Fin.snoc_castSucc] }
    map_app' := fun p => by
      rw [positiveForm_apply]
      simp only [absNegForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, neg_mul,
        _root_.one_mul, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      ring }⟩

end ABSConventionsAndSuspension

section ABSCategoricalRestrictionAndMorita

open CategoryTheory

/-- `S2-18` (ABS 1964 §4–5; Bott Morita Periodicity): Canonical graded Morita equivalence
`M(Cl(1,1)) ≌ M(ℝ)` (`cl11GradedEquivalence`). -/
def absCl11MoritaEquiv :
    absModuleCat Cl11Matrix.q11 ≌ GradedModuleCat (RingEquiv.refl ℝ) :=
  cl11GradedEquivalence

/-- `S2-18` (ABS 1964 §4 Prop. (4.2) / §1 Prop. (1.6) Graded Cancellation): Re-export of
`Cl11GradedTensorMorita.cliffordHeadCancellation`, cancelling a `Cl(1,1)` Koszul graded
tensor head while preserving arbitrary noncommutative graded coefficients `A`. -/
def absHeadCancellationEquiv {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (θ : A ≃ₐ[ℝ] A)
    (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a) (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a) :
    GradedModuleCat (tensorParity 𝒜 θ hEven hOdd).toRingEquiv ≌
      GradedModuleCat θ.toRingEquiv :=
  cliffordHeadCancellation 𝒜 θ hEven hOdd

end ABSCategoricalRestrictionAndMorita

section ABSGrothendieckCokernelAndMod8

open scoped TensorProduct

/-- `S2-18` (Compatibility with `AtiyahBottShapiroBridge` & `RealMod8Classification`):
Bundles the `Cl(1,1)` Bott analytical-index invariance from `AtiyahBottShapiroBridge` with
the 8-fold periodicity `bottShift^[8] r = r` from `RealMod8Classification` (ABS Table 1 &
Table 2). -/
theorem abs_bott_index_and_mod8_periodicity_compatibility
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism F)
    (eFlow : ℝ → F ≃ₗ[ℝ] F)
    (hConj : InfoGeometry.Canonical.AnalyticalIndex.ChiralConjugacyAlong Dn Γn eFlow) :
    (∀ v : ℝ × ℝ,
      InfoGeometry.Krein.cl11RepHilbert (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) *
        InfoGeometry.Krein.cl11RepHilbert (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) =
        algebraMap ℝ _ (InfoGeometry.Clifford.splitQ11 v)) ∧
      (∀ s : ℝ,
        InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex (E := E) (Dn s) (Γn s) =
          InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex (E := E) (Dn 0) (Γn 0)) ∧
      (∀ r : InfoGeometry.Clifford.RealMod8Classification.ClMod8,
        InfoGeometry.Clifford.RealMod8Classification.bottShift^[8] r = r) := by
  exact ⟨fun v => InfoGeometry.Canonical.AtiyahBottShapiroBridge.cl11_symbol_sq (E := E) v,
    InfoGeometry.Canonical.AtiyahBottShapiroBridge.cl11_bottAnalyticalIndex_const_of_conjugacy
      (E := E) Dn Γn eFlow hConj,
    InfoGeometry.Clifford.RealMod8Classification.bottShift_iterate_eight⟩

end ABSGrothendieckCokernelAndMod8

end AtiyahBottShapiroPrimary

end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary

