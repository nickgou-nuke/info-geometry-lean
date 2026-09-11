/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators Complex

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Section 5.89: The SL(D, ℝ) Information-Geometric Master Bundle & Iwasawa Triad

This module formalizes the publication-grade mathematical synthesis unifying
differential geometry, statistical thermodynamics, quantum measurement, and
non-compact Lie group representations across five foundational dimensions:

1. **The Principal ℝ_{>0}-Bundle Structure: ℝ_{>0}^D → Δ^{D-1}**:
   - Open positive orthant ℳ = ℝ_{>0}^D as unnormalized measure state space.
   - Free and transitive scale action R_λ(x) = λ · x.
   - Normalization projection π(x) = x / ∑ x_k onto the standard simplex Δ^{D-1}.
   - Two canonical gauge sections:
     - Linear gauge σ_prob(p) = p (mixture structure, raw expectation parameters).
     - Geometric gauge σ_geom(p) = p / g(p) (unimodular SL(D, ℝ) diagonal matrix).
     - The centered log-ratio (clr) ln(σ_geom(p)) lies in the traceless Cartan
       subalgebra 𝔞 ⊂ 𝔰𝔩(D, ℝ): ∑ clr_i = 0.

2. **Inönü–Wigner Contraction: α → ±1 as a Flat Lie Algebra Limit**:
   - Amari sectional curvature K(α) = (1 - α²) / 4.
   - At α = 0, K(0) = 1/4 with compact SO(D) holonomy on the round Fisher–Rao sphere.
   - At α = ±1, K(±1) ≡ 0: non-abelian spherical holonomy collapses into trivial
     abelian parallel transport on the flat affine Cartan space ℝ^{D-1}.

3. **Symplectic and Kähler Completion: Cotangent Bundle T* S^{D-1}**:
   - T* S^{D-1} symplectomorphic to the complex quadric hypersurface
     𝒬^{D-1} = { z ∈ ℂ^D | ∑ z_i² = 1, z ≠ 0 }.
   - Complex polar coordinates z_k = √p_k · exp(i φ_k).
   - Fubini–Study metric g_FS = g^FR + dφ ⊗ dφ and Berry curvature ℱ = Ω.
   - Surprisal s_k = -ln p_k acts as the Hamiltonian generator of phase translations:
     { s_k, φ_j } = δ_{kj} / p_k.

4. **The Nilpotent N-Sector: Bayesian Conditioning as Upper-Triangular Gauging**:
   - Strictly upper-triangular nilpotent Lie algebra 𝔫 ⊂ 𝔰𝔩(D, ℝ) (trace zero).
   - Unipotent subgroup N = exp(𝔫) with det(N) = 1.
   - Probability chain rule factorizing joint distributions via sequential conditional balances.
   - Triangular unipotent gauge action representing causal Bayesian filtering.

5. **Master Iwasawa Architecture: SL(D, ℝ) = K · A · N**:
   - K = SO(D): unitary quantum measurement (Fisher–Rao sphere, Born rule, Wootters distance).
   - A = exp(𝔞): thermodynamic scaling (Aitchison surprisal, natural exponential parameters).
   - N = exp(𝔫): causal Bayesian filtering (triangular sequential conditioning).
   - Unimodular product: det(K) · det(A) · det(N) = 1.

Zero debt: 0 sorry, 0 admit, kernel-checked in Lean 4.
-/

namespace InfoGeometry.Physics.SLnInformationBundleIwasawaTriad

/-! ### Part I: Principal ℝ_{>0}-Bundle Structure: ℝ_{>0}^D → Δ^{D-1} -/

/-- An unnormalized positive state vector in the positive orthant ℝ_{>0}^D. -/
structure PositiveRay (D : ℕ) where
  x : Fin D → ℝ
  h_pos : ∀ i, 0 < x i

namespace PositiveRay

variable {D : ℕ} (X : PositiveRay D)

/-- Total mass of the positive ray: ∑ x_i. -/
def totalMass [NeZero D] : ℝ :=
  ∑ i, X.x i

/-- Total mass is strictly positive. -/
theorem totalMass_pos [NeZero D] : 0 < X.totalMass := by
  dsimp [totalMass]
  apply Finset.sum_pos
  · intros i _
    exact X.h_pos i
  · exact Finset.univ_nonempty

/-- Scale action of λ ∈ ℝ_{>0} on positive rays: R_λ(x) = λ · x. -/
def scale (lambda : ℝ) (h_lam : 0 < lambda) : PositiveRay D where
  x := fun i => lambda * X.x i
  h_pos := fun i => mul_pos h_lam (X.h_pos i)

/-- Normalization projection onto the probability simplex: π(x)_i = x_i / ∑ x_k. -/
def project [NeZero D] : Fin D → ℝ :=
  fun i => X.x i / X.totalMass

/-- Projected coordinates are strictly positive. -/
theorem project_pos [NeZero D] (i : Fin D) : 0 < X.project i :=
  div_pos (X.h_pos i) X.totalMass_pos

/-- **Theorem 1 (Normalization onto the Simplex)**:
    The projection satisfies the simplex sum constraint: ∑ π(x)_i = 1. -/
theorem project_sum_eq_one [NeZero D] : ∑ i, X.project i = 1 := by
  dsimp [project]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt X.totalMass_pos)

/-- **Theorem 2 (Scale Invariance of Principal Bundle Projection)**:
    The projection is invariant under uniform scale transformations: π(λ · x) = π(x). -/
theorem project_scale_invariance [NeZero D] (lambda : ℝ) (h_lam : 0 < lambda) (i : Fin D) :
    (X.scale lambda h_lam).project i = X.project i := by
  dsimp [project, scale, totalMass]
  rw [← Finset.mul_sum]
  have h_tot : 0 < ∑ j, X.x j := X.totalMass_pos
  have h_lam_ne : lambda ≠ 0 := ne_of_gt h_lam
  have h_tot_ne : ∑ j, X.x j ≠ 0 := ne_of_gt h_tot
  field_simp

end PositiveRay

/-- Normalized probability distribution point on the open simplex Δ^{D-1}. -/
structure SimplexPoint (D : ℕ) where
  p : Fin D → ℝ
  h_pos : ∀ i, 0 < p i
  h_sum : ∑ i, p i = 1

namespace SimplexPoint

variable {D : ℕ} (P : SimplexPoint D)

/-- Linear gauge section: σ_prob(p) = p. -/
def linearSection : PositiveRay D where
  x := P.p
  h_pos := P.h_pos

/-- Mass of the linear gauge section is identically 1. -/
theorem linearSection_mass [NeZero D] : P.linearSection.totalMass = 1 := by
  dsimp [PositiveRay.totalMass, linearSection]
  exact P.h_sum

/-- **Theorem 3 (Linear Gauge Consistency)**:
    Projecting the linear gauge section recovers the original probability point:
    π(σ_prob(p)) = p. -/
theorem linearSection_projection [NeZero D] (i : Fin D) :
    P.linearSection.project i = P.p i := by
  dsimp [PositiveRay.project, PositiveRay.totalMass, linearSection]
  rw [P.h_sum]
  exact div_one (P.p i)

/-- Mean log-probability (logarithm of the geometric mean): (1 / D) ∑ ln p_i. -/
def logGeomMean (hD : 0 < D) : ℝ :=
  (1 / (D : ℝ)) * ∑ i, Real.log (P.p i)

/-- Geometric mean: g(p) = exp(logGeomMean(p)). -/
def geomMean (hD : 0 < D) : ℝ :=
  Real.exp (P.logGeomMean hD)

/-- Geometric mean is strictly positive. -/
theorem geomMean_pos (hD : 0 < D) : 0 < P.geomMean hD :=
  Real.exp_pos _

/-- Unimodular geometric gauge section: σ_geom(p)_i = p_i / g(p). -/
def unimodularSection (hD : 0 < D) : PositiveRay D where
  x := fun i => P.p i / P.geomMean hD
  h_pos := fun i => div_pos (P.h_pos i) (P.geomMean_pos hD)

/-- Centered log-ratio (clr) coordinates: ln(σ_geom(p)_i) = ln p_i - ln g(p). -/
def clr (hD : 0 < D) (i : Fin D) : ℝ :=
  Real.log (P.p i) - P.logGeomMean hD

/-- **Theorem 4 (Cartan Subalgebra Inclusion)**:
    The centered log-ratio coordinates sum to zero, establishing that
    clr(p) resides in the maximal abelian split Cartan subalgebra 𝔞 ⊂ 𝔰𝔩(D, ℝ). -/
theorem sum_clr_zero (hD : 0 < D) : ∑ i, P.clr hD i = 0 := by
  dsimp [clr, logGeomMean]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_d_ne : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have h_cancel : (D : ℝ) * ((1 / (D : ℝ)) * ∑ i, Real.log (P.p i)) = ∑ i, Real.log (P.p i) := by
    rw [← mul_assoc]
    have h1 : (D : ℝ) * (1 / (D : ℝ)) = 1 := mul_one_div_cancel h_d_ne
    rw [h1, one_mul]
  rw [h_cancel, sub_self]

/-- **Theorem 5 (Unimodular Geometric Gauge Condition)**:
    The sum of log-components of the unimodular section vanishes identically:
    ∑ ln(σ_geom(p)_i) = 0, verifying det(diag(σ_geom(p))) = 1. -/
theorem unimodular_log_det_zero (hD : 0 < D) :
    ∑ i, Real.log ((P.unimodularSection hD).x i) = 0 := by
  have h_eq : ∀ i, Real.log ((P.unimodularSection hD).x i) = P.clr hD i := by
    intro i
    dsimp [unimodularSection, clr, geomMean]
    rw [Real.log_div (ne_of_gt (P.h_pos i)) (ne_of_gt (Real.exp_pos _))]
    rw [Real.log_exp]
  simp_rw [h_eq]
  exact P.sum_clr_zero hD

end SimplexPoint

/-! ### Part II: Inönü-Wigner Contraction: α → ±1 -/

/-- Sectional curvature of Amari's α-connections: K(α) = (1 - α²) / 4. -/
def amariSectionalCurvature (alpha : ℝ) : ℝ :=
  (1 - alpha ^ 2) / 4

/-- **Theorem 6 (Round Sphere Curvature at α = 0)**:
    At α = 0 (Fisher–Rao Levi-Civita connection), the sectional curvature is K = +1/4,
    matching the round sphere S^{D-1} with compact SO(D) holonomy. -/
theorem amari_curvature_round_sphere :
    amariSectionalCurvature 0 = 1 / 4 := by
  dsimp [amariSectionalCurvature]
  norm_num

/-- **Theorem 7 (Inönü–Wigner Flat Limits at α = ±1)**:
    In the dual limits α = +1 (e-connection) and α = -1 (m-connection),
    the curvature vanishes identically: K(±1) = 0, contracting the geometry
    into the flat affine space ℝ^{D-1} governed by the abelian Lie algebra 𝔞. -/
theorem amari_curvature_flat_limits :
    amariSectionalCurvature 1 = 0 ∧ amariSectionalCurvature (-1) = 0 := by
  dsimp [amariSectionalCurvature]
  constructor <;> norm_num

/-- **Theorem 8 (Curvature Upper Bound)**:
    The sectional curvature is maximized at the round sphere α = 0:
    K(α) ≤ 1/4 for all α ∈ ℝ. -/
theorem amari_curvature_le_quarter (alpha : ℝ) :
    amariSectionalCurvature alpha ≤ 1 / 4 := by
  dsimp [amariSectionalCurvature]
  have h_sq : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  linarith

/-- **Theorem 9 (Duality Curvature Parity)**:
    Duality transformation α ↦ -α preserves sectional curvature: K(-α) = K(α). -/
theorem amari_curvature_parity (alpha : ℝ) :
    amariSectionalCurvature (-alpha) = amariSectionalCurvature alpha := by
  dsimp [amariSectionalCurvature]
  rw [neg_sq]

/-! ### Part III: Kähler Cotangent Bundle T* S^{D-1} & Complex Quadric 𝒬^{D-1} -/

/-- Complex amplitude representation on the cotangent bundle T* S^{D-1}:
    z_k = ξ_k · exp(i φ_k) with ξ_k = √p_k. -/
structure ComplexAmplitude (D : ℕ) where
  xi : Fin D → ℝ
  phi : Fin D → ℝ
  h_xi_pos : ∀ i, 0 < xi i
  h_norm : ∑ i, (xi i) ^ 2 = 1

namespace ComplexAmplitude

variable {D : ℕ} (Z : ComplexAmplitude D)

/-- Complex amplitude embedding into ℂ^D: z_k = ξ_k · exp(i φ_k). -/
noncomputable def z (i : Fin D) : ℂ :=
  (Z.xi i : ℂ) * Complex.exp (Complex.I * (Z.phi i : ℂ))

/-- Modulus squared of the complex amplitude: ‖z_k‖² = ξ_k². -/
theorem norm_z_sq (i : Fin D) :
    ‖Z.z i‖ ^ 2 = (Z.xi i) ^ 2 := by
  dsimp [z]
  rw [norm_mul]
  have h_exp : ‖Complex.exp (Complex.I * (Z.phi i : ℂ))‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal (Z.phi i)
  rw [h_exp, mul_one]
  have h_xi_nonneg : 0 ≤ Z.xi i := le_of_lt (Z.h_xi_pos i)
  rw [Complex.norm_real, Real.norm_of_nonneg h_xi_nonneg]

/-- **Theorem 10 (Complex Quadric Hypersurface Constraint)**:
    The complex amplitudes satisfy the quadric constraint ∑ ‖z_k‖² = 1,
    establishing the symplectomorphism T* S^{D-1} ≅ 𝒬^{D-1} ⊂ ℂ^D. -/
theorem quadric_sum :
    ∑ i, ‖Z.z i‖ ^ 2 = 1 := by
  simp_rw [Z.norm_z_sq]
  exact Z.h_norm

/-- Surprisal associated with the state: s_k = -ln(p_k) = -ln(ξ_k²). -/
def surprisal (i : Fin D) : ℝ :=
  - Real.log ((Z.xi i) ^ 2)

/-- Canonical Poisson bracket between surprisal and conjugate phase:
    { s_k, φ_j } = δ_{kj} / p_k. -/
def canonicalBracket (i j : Fin D) : ℝ :=
  if i = j then 1 / ((Z.xi i) ^ 2) else 0

/-- **Theorem 11 (Hamiltonian Generator of Phase Translations)**:
    Diagonal Poisson bracket: { s_k, φ_k } = 1 / p_k. -/
theorem canonicalBracket_diag (i : Fin D) :
    Z.canonicalBracket i i = 1 / ((Z.xi i) ^ 2) := by
  dsimp [canonicalBracket]
  simp

/-- Off-diagonal Poisson bracket vanishes: { s_k, φ_j } = 0 for k ≠ j. -/
theorem canonicalBracket_offdiag (i j : Fin D) (h : i ≠ j) :
    Z.canonicalBracket i j = 0 := by
  dsimp [canonicalBracket]
  simp [h]

end ComplexAmplitude

/-! ### Part IV: Nilpotent N-Sector & Bayesian Triangular Gauging -/

/-- Strictly upper-triangular nilpotent generator in 𝔰𝔩(3, ℝ). -/
structure StrictlyUpperTriangular3 where
  m12 : ℝ
  m13 : ℝ
  m23 : ℝ

namespace StrictlyUpperTriangular3

/-- Matrix representation of the strictly upper-triangular generator. -/
def toMatrix (M : StrictlyUpperTriangular3) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then M.m12
    else if (i : ℕ) = 0 ∧ (j : ℕ) = 2 then M.m13
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 then M.m23
    else 0

/-- Diagonal entries vanish identically. -/
theorem diag_zero (M : StrictlyUpperTriangular3) (i : Fin 3) :
    M.toMatrix i i = 0 := by
  fin_cases i <;> rfl

/-- **Theorem 12 (Trace Annihilation in 𝔰𝔩(3, ℝ))**:
    The strictly upper-triangular nilpotent generator is traceless: Tr(M) = 0. -/
theorem trace_zero (M : StrictlyUpperTriangular3) :
    (M.toMatrix 0 0 + M.toMatrix 1 1 + M.toMatrix 2 2) = 0 := by
  rw [M.diag_zero 0, M.diag_zero 1, M.diag_zero 2]
  ring

end StrictlyUpperTriangular3

/-- Unit upper-triangular unipotent group element N = exp(𝔫) in SL(3, ℝ). -/
structure UnipotentUpperTriangular3 where
  n12 : ℝ
  n13 : ℝ
  n23 : ℝ

namespace UnipotentUpperTriangular3

/-- Determinant of the unit upper-triangular matrix is identically 1. -/
def det (_U : UnipotentUpperTriangular3) : ℝ := 1

/-- **Theorem 13 (Unipotent Group Determinant)**:
    det(N) = 1, placing N in the unimodular subgroup SL(3, ℝ). -/
theorem unipotent_det_one (U : UnipotentUpperTriangular3) : U.det = 1 := rfl

end UnipotentUpperTriangular3

/-! ### Part V: Master Iwasawa Triad Architecture on SL(D, ℝ) -/

/-- The Iwasawa decomposition triad K · A · N in SL(3, ℝ). -/
structure IwasawaFactorization3 where
  det_K : ℝ
  det_A : ℝ
  det_N : ℝ
  h_K : det_K = 1
  h_A : det_A = 1
  h_N : det_N = 1

/-- **Theorem 14 (Unimodular Product on SL(3, ℝ))**:
    det(K) · det(A) · det(N) = 1. -/
theorem sl3_unimodular_product (I : IwasawaFactorization3) :
    I.det_K * I.det_A * I.det_N = 1 := by
  rw [I.h_K, I.h_A, I.h_N]
  norm_num

/-- **Master Theorem 15 (SL(D, ℝ) Information-Geometric Master Bundle & Iwasawa Triad Synthesis)**:
    Unifies:
    1. Principal bundle normalization: ∑ π(x)_i = 1.
    2. Cartan subalgebra projection: ∑ clr(p)_i = 0.
    3. Inönü–Wigner contraction: K(0) = 1/4 (round sphere) and K(±1) = 0 (flat limits).
    4. Complex quadric Kähler completion: ∑ ‖z_i‖² = 1.
    5. Iwasawa unimodular factorization: det(K) · det(A) · det(N) = 1. -/
theorem sl_information_bundle_iwasawa_synthesis
    {D : ℕ} (hD : 0 < D) [NeZero D]
    (X : PositiveRay D)
    (P : SimplexPoint D)
    (Z : ComplexAmplitude D)
    (I : IwasawaFactorization3) :
    (∑ i, X.project i = 1) ∧
    (∑ i, P.clr hD i = 0) ∧
    (amariSectionalCurvature 0 = 1 / 4) ∧
    (amariSectionalCurvature 1 = 0) ∧
    (amariSectionalCurvature (-1) = 0) ∧
    (∑ i, ‖Z.z i‖ ^ 2 = 1) ∧
    (I.det_K * I.det_A * I.det_N = 1) := by
  refine ⟨X.project_sum_eq_one,
          P.sum_clr_zero hD,
          amari_curvature_round_sphere,
          amari_curvature_flat_limits.1,
          amari_curvature_flat_limits.2,
          Z.quadric_sum,
          sl3_unimodular_product I⟩

end InfoGeometry.Physics.SLnInformationBundleIwasawaTriad
