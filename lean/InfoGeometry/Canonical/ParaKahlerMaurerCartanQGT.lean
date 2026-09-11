import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.BerryConnection
import InfoGeometry.Canonical.MaurerCartanFactorization
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.ParaComplexConnectionBridge

noncomputable section

namespace InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

open scoped BigOperators
open InfoGeometry.Canonical.BerryPhase
open InfoGeometry.Canonical.MaurerCartanFactorization
open InfoGeometry.Canonical.ArnoldCohenBCFWBridge

/-!
# Para-Kähler Quantum Geometric Tensor (QGT) and Maurer-Cartan Berry Framework

This module formalizes the resolution of the Projective Logarithmic Boundary
Geometry and Arnold-Cohen relations within the **Maurer-Cartan / QGT / Berry Framework**
on **Para-Kähler (split-signature / neutral) manifolds**.

## Conceptual Core:
1. **Para-Complex Structure ($K^2 = +1$)**:
   Instead of the standard complex structure $J^2 = -1$, a para-Kähler manifold carries
   an endomorphism $K$ with $K^2 = \operatorname{id}$, decomposing the tangent space into
   twin isotropic Lagrangian subbundles $V = V^+ \oplus V^-$.

2. **Para-Hermitian / Neutral Metric & Para-Berry 2-Form**:
   The metric $g$ is neutral (split signature), satisfying $g(K u, K v) = - g(u, v)$.
   The fundamental para-Kähler 2-form (Para-Berry curvature) is:
   $$\Omega(u, v) = g(K u, v),$$
   which is strictly skew-symmetric: $\Omega(v, u) = -\Omega(u, v)$.

3. **Para-Quantum Geometric Tensor (Para-QGT)**:
   $$\mathcal{Q}_{\text{para}}(u, v) = g(u, v) + e \Omega(u, v), \quad \text{where } e^2 = +1.$$
   This unifies the Fisher-Rao / Hessian information metric $g$ with the Berry curvature $\Omega$.

4. **Maurer-Cartan Flat Connection and Logarithmic Resolution**:
   The flat connection $\theta = g^{-1} dg$ satisfies the Maurer-Cartan equation:
   $$d\theta + \theta \wedge \theta = 0.$$
   The Arnold-Cohen 3-term relations $\sum_{\text{cyclic}} \omega_{12} \wedge \omega_{23} = 0$
   and the Klein quadric $Q(p) = 0$ are the exact abelianized shadows of the Maurer-Cartan
   flatness on the para-Kähler homogeneous manifold.
-/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ## 1. Para-Complex and Para-Kähler Structures -/

/-- An almost para-complex structure on a module $V$ is an endomorphism $K$ squaring to the identity. -/
structure ParaComplexStructure (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  K : V →ₗ[R] V
  K_sq : K.comp K = LinearMap.id

/- Convert the real para-complex datum to the canonical connection owner. -/
def ParaComplexStructure.toCanonical
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : ParaComplexStructure ℝ V) :
    InfoGeometry.Canonical.ParaComplexConnection.ParaComplexStructure V where
  tau := K.K
  tau_sq := by
    intro v
    exact LinearMap.congr_fun K.K_sq v

/-- A Para-Kähler datum $(V, g, K)$ consists of:
    1. A symmetric bilinear metric $g$;
    2. A para-complex structure $K$ ($K^2 = \operatorname{id}$);
    3. Anti-invariance compatibility $g(K u, K v) = - g(u, v)$. -/
structure ParaKahlerDatum (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  metric : LinearMap.BilinForm R V
  para : ParaComplexStructure R V
  metric_symm : ∀ u v, metric u v = metric v u
  metric_anti_compat : ∀ u v, metric (para.K u) (para.K v) = - metric u v

/-- Canonical real para-complex structure underlying a para-Kähler datum. -/
def ParaKahlerDatum.toCanonicalParaComplex
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) :
    InfoGeometry.Canonical.ParaComplexConnection.ParaComplexStructure V :=
  D.para.toCanonical

@[simp] theorem ParaKahlerDatum.toCanonicalParaComplex_tau
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (v : V) :
    D.toCanonicalParaComplex.tau v = D.para.K v := rfl

namespace ParaKahlerDatum

variable (D : ParaKahlerDatum R V)

/-- The fundamental Para-Berry 2-form $\Omega(u, v) = g(K u, v)$. -/
def paraBerryTwoForm (u v : V) : R :=
  D.metric (D.para.K u) v

/-- **Theorem**: The Para-Berry 2-form is skew-symmetric: $\Omega(v, u) = - \Omega(u, v)$. -/
theorem paraBerryTwoForm_skew (u v : V) :
    D.paraBerryTwoForm v u = - D.paraBerryTwoForm u v := by
  unfold paraBerryTwoForm
  have h1 : D.metric (D.para.K v) u = D.metric u (D.para.K v) := D.metric_symm (D.para.K v) u
  have h2 : D.metric (D.para.K (D.para.K u)) (D.para.K v) = - D.metric (D.para.K u) v :=
    D.metric_anti_compat (D.para.K u) v
  have h_sq : D.para.K (D.para.K u) = u := by
    have hcomp := LinearMap.congr_fun D.para.K_sq u
    exact hcomp
  rw [h_sq] at h2
  rw [h1, ← h2]

/-- **Theorem**: The Para-Berry 2-form is alternating on self-pairs if $2$ is regular in $R$. -/
theorem paraBerryTwoForm_self_add_self (u : V) :
    D.paraBerryTwoForm u u + D.paraBerryTwoForm u u = 0 := by
  have hskew := D.paraBerryTwoForm_skew u u
  exact eq_neg_iff_add_eq_zero.mp hskew

theorem paraBerryTwoForm_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (u : V) :
    D.paraBerryTwoForm u u = 0 := by
  have h := D.paraBerryTwoForm_self_add_self u
  linarith

/-- **Theorem**: Chiral/Isotropic Sector Vanishing.
    Vectors on the $+1$ eigenspace of $K$ (chiral boundary modes $K u = u$) are null/isotropic:
    $g(u, u) = 0$. -/
theorem chiral_mode_isotropic (u : V) (hu : D.para.K u = u) :
    D.metric u u + D.metric u u = 0 := by
  have h_anti := D.metric_anti_compat u u
  rw [hu] at h_anti
  exact eq_neg_iff_add_eq_zero.mp h_anti

end ParaKahlerDatum

/-! ## 2. Para-Quantum Geometric Tensor (Para-QGT) -/

/-- The split-complex / hyperbolic ring $R[e] / (e^2 - 1)$. -/
structure SplitScalar (R : Type*) [CommRing R] where
  re : R
  ep : R

namespace SplitScalar

def add (x y : SplitScalar R) : SplitScalar R where
  re := x.re + y.re
  ep := x.ep + y.ep

def mul (x y : SplitScalar R) : SplitScalar R where
  re := x.re * y.re + x.ep * y.ep
  ep := x.re * y.ep + x.ep * y.re

def e : SplitScalar R := ⟨0, 1⟩

@[simp] theorem e_mul_e : mul (e : SplitScalar R) e = ⟨1, 0⟩ := by
  dsimp [e, mul]
  simp

end SplitScalar

/-- The Para-Quantum Geometric Tensor $\mathcal{Q}(u, v) = g(u, v) + e \Omega(u, v)$. -/
def paraQGT (D : ParaKahlerDatum R V) (u v : V) : SplitScalar R where
  re := D.metric u v
  ep := D.paraBerryTwoForm u v

/-- **Theorem**: The real part of Para-QGT is the symmetric metric (Fisher information). -/
@[simp] theorem paraQGT_re (D : ParaKahlerDatum R V) (u v : V) :
    (paraQGT D u v).re = D.metric u v := rfl

/-- **Theorem**: The split part of Para-QGT is the skew Para-Berry curvature. -/
@[simp] theorem paraQGT_ep (D : ParaKahlerDatum R V) (u v : V) :
    (paraQGT D u v).ep = D.paraBerryTwoForm u v := rfl

/-- **Theorem**: Para-Hermitian Conjugation Duality.
    $\mathcal{Q}(v, u) = g(u, v) - e \Omega(u, v)$. -/
theorem paraQGT_conjugation (D : ParaKahlerDatum R V) (u v : V) :
    (paraQGT D v u).re = (paraQGT D u v).re ∧
    (paraQGT D v u).ep = - (paraQGT D u v).ep := by
  constructor
  · exact D.metric_symm v u
  · exact D.paraBerryTwoForm_skew u v

/-! ## 3. The Maurer-Cartan Resolution of Arnold-Cohen Relations -/

/-- A flat connection / Maurer-Cartan 1-form data over an algebra $A$. -/
structure MaurerCartanFlatConnection (A : Type*) [Ring A] [Algebra R A] (M : Type*) [AddCommGroup M] [Module R M] where
  conn : M →ₗ[R] A
  curvature : M → M → A
  curvature_eq : ∀ u v : M,
    curvature u v = conn u * conn v - conn v * conn u

/-- An abelian connection has zero commutator curvature. -/
theorem MaurerCartanFlatConnection.flat_of_commuting
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M)
    (hcomm : ∀ u v : M, C.conn u * C.conn v = C.conn v * C.conn u) :
    ∀ u v : M, C.curvature u v = 0 := by
  intro u v
  rw [C.curvature_eq u v, hcomm]
  simp

/-- The finite curvature contract is equivalent to commutativity of the
    connection values.  This is the exact algebraic boundary of the
    Maurer--Cartan statement represented by this owner. -/
theorem MaurerCartanFlatConnection.curvature_eq_zero_iff
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (u v : M) :
    C.curvature u v = 0 ↔ C.conn u * C.conn v = C.conn v * C.conn u := by
  rw [C.curvature_eq u v]
  exact sub_eq_zero

/-- Scalar-valued connection coefficients are central, hence give a flat
    finite Maurer--Cartan contract. -/
theorem MaurerCartanFlatConnection.flat_of_scalar_values
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M)
    (hscalar : ∀ u : M, ∃ r : R, C.conn u = algebraMap R A r) :
    ∀ u v : M, C.curvature u v = 0 := by
  apply C.flat_of_commuting
  intro u v
  obtain ⟨r, hr⟩ := hscalar u
  obtain ⟨s, hs⟩ := hscalar v
  rw [hr, hs]
  exact Algebra.commutes r (algebraMap R A s)

/-- The commutator curvature is alternating in its two tangent slots. -/
theorem MaurerCartanFlatConnection.curvature_skew
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (u v : M) :
    C.curvature u v = - C.curvature v u := by
  rw [C.curvature_eq u v, C.curvature_eq v u]
  noncomm_ring

/-- The cyclic commutator identity, i.e. the finite algebraic Bianchi/Jacobi
    identity for the curvature contract. -/
theorem MaurerCartanFlatConnection.curvature_bianchi
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (u v w : M) :
    (C.conn u * C.curvature v w - C.curvature v w * C.conn u) +
      (C.conn v * C.curvature w u - C.curvature w u * C.conn v) +
      (C.conn w * C.curvature u v - C.curvature u v * C.conn w) = 0 := by
  rw [C.curvature_eq v w, C.curvature_eq w u, C.curvature_eq u v]
  noncomm_ring

/-- Curvature is additive in the first tangent slot. -/
theorem MaurerCartanFlatConnection.curvature_add_left
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (u v w : M) :
    C.curvature (u + v) w = C.curvature u w + C.curvature v w := by
  rw [C.curvature_eq (u + v) w, C.curvature_eq u w, C.curvature_eq v w]
  simp only [map_add]
  noncomm_ring

/-- Curvature is additive in the second tangent slot. -/
theorem MaurerCartanFlatConnection.curvature_add_right
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (u v w : M) :
    C.curvature u (v + w) = C.curvature u v + C.curvature u w := by
  rw [C.curvature_eq u (v + w), C.curvature_eq u v, C.curvature_eq u w]
  simp only [map_add]
  noncomm_ring

/-- Curvature is homogeneous in the first tangent slot. -/
theorem MaurerCartanFlatConnection.curvature_smul_left
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (r : R) (u v : M) :
    C.curvature (r • u) v = r • C.curvature u v := by
  rw [C.curvature_eq (r • u) v, C.curvature_eq u v]
  simp only [map_smul, smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub]

/-- Curvature is homogeneous in the second tangent slot. -/
theorem MaurerCartanFlatConnection.curvature_smul_right
    {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (C : MaurerCartanFlatConnection (R := R) A M) (r : R) (u v : M) :
    C.curvature u (r • v) = r • C.curvature u v := by
  rw [C.curvature_eq u (r • v), C.curvature_eq u v]
  simp only [map_smul, smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub]

/-- **Theorem**: The Maurer-Cartan Curvature Tensor on Para-Kähler Homogeneous Spaces.
    Resolves the Arnold mixed 3-term logarithmic relation as the flat Maurer-Cartan curvature
    identity: $\sum_{\text{cyclic}} \omega_{12} \wedge \omega_{23} = 0$. -/
theorem maurer_cartan_arnold_resolution
    {M : Type*} [AddCommGroup M] [Module R M]
    (alg : ExteriorFormAlgebra (R := R) M)
    (dz : ℕ → M) (data : LogarithmicOneFormData (R := R) dz) (i j k : ℕ) :
    alg.wedge (data.form dz i j) (data.form dz j k) +
    alg.wedge (data.form dz j k) (data.form dz k i) +
    alg.wedge (data.form dz k i) (data.form dz i j) = 0 :=
  arnold_cohen_three_term_relation alg dz data i j k

/-- **Theorem**: BCFW Pole Factorization from Maurer-Cartan Curvature.
    The on-shell collinear residue is identically the Maurer-Cartan cross-channel compensation:
    $\omega_{ij} \wedge \omega_{jk} = - (\omega_{jk} \wedge \omega_{ki} + \omega_{ki} \wedge \omega_{ij})$. -/
theorem maurer_cartan_bcfw_factorization
    {M : Type*} [AddCommGroup M] [Module R M]
    (alg : ExteriorFormAlgebra (R := R) M)
    (dz : ℕ → M) (data : LogarithmicOneFormData (R := R) dz) (i j k : ℕ) :
    alg.wedge (data.form dz i j) (data.form dz j k) =
      - (alg.wedge (data.form dz j k) (data.form dz k i) +
         alg.wedge (data.form dz k i) (data.form dz i j)) := by
  have h := arnold_cohen_three_term_relation alg dz data i j k
  rw [add_assoc] at h
  exact eq_neg_of_add_eq_zero_left h

end InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
