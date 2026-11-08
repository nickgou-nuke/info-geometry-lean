/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
import InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

/-!
# 3-Parameter $\mathfrak{so}(2,1)$ Socle Derivation Family, Joint 17-Parameter Product Action, and KKS Pairing

This module bridges the 14-parameter diagonally lifted $G_2$ split-sedenion derivation family
`sedenionG2Derivation` from `InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge` with the
3-parameter $\mathfrak{so}(2,1) \cong \mathfrak{sl}(2, \mathbb{R})$ matrix and coordinate-algebra
derivation family from `InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly`:

1. **Section 1 — 3-Parameter $\mathfrak{so}(2,1) \cong \mathfrak{sl}(2, \mathbb{R})$ Linear Combination Family & Coordinate Readout**:
   - Defines `so21LinearComb (c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ` as the general
     3-parameter linear combination $c_0 J_{12} + c_1 K_{13} + c_2 K_{23}$.
   - Proves $\eta_{(2,1)}$-skew-adjointness (`so21LinearComb_etaSkewAdjoint`), trace-vanishing
     (`so21LinearComb_trace_zero`), quadratic adjoint eigenvalue `2`
     (`so21LinearComb_adjoint_casimir_eq_two`), and the Leibniz derivation law on the
     4D coordinate algebra `socleDoublingMul` (`so21LinearComb_socleDerivation_leibniz`).
   - Defines coordinate readouts `readSo21Params` (on $3 \times 3$ matrices) and
     `readSocleDerivationParams` (on 4D coordinate-algebra maps), proving exact parameter
     recovery (`readSo21Params_so21LinearComb`, `readSocleDerivationParams_socleDerivation`)
     and injectivity (`so21LinearComb_injective`).

2. **Section 2 — Joint 17-Parameter Product Action (`14 + 3 = 17`) & Parameter Equivalence**:
   - Defines `split17Params` and `combine17Params` establishing the explicit coordinate
     equivalence `params14Prod3EquivFin17 : (Params × (Fin 3 → ℝ)) ≃ (Fin 17 → ℝ)`.
   - Defines the joint 17-parameter product action `jointG2So21Action` on a pair of
     distinct carriers (split-sedenions and the 4D socle coordinate algebra), and readout
     `readJoint17Params`, proving `readJoint17Params_jointG2So21Action` and
     `jointG2So21Action_injective`. This is an injective parameterization of a product of
     actions; it does not define a direct sum of derivation spaces or a 17-parameter
     derivation of one shared algebra.
   - Proves `sedenionG2Derivation_annihilates_ell_vs_socleDerivation_active`, contrasting the
     annihilation of the Cayley–Dickson doubling unit `sedenionEll` by every diagonal $G_2$
     derivation with the non-trivial action of `socleDerivation (so21LinearComb c)` on the
     first coordinate-algebra basis vector.

3. **Section 3 — Alternating Cross-Product Pairing on the $\mathfrak{so}(2,1)$ Socle & Zero-Divisor Tangent Locus**:
   - Defines the coordinate pairing
     `so21KKSForm μ ξ η = ⟨μ, ξ ×_{(2,1)} η⟩_{(2,1)}` on `Fin 3 → ℝ`.
     Identifying it with a KKS form requires a separate theorem relating the displayed
     cross product to the chosen matrix Lie bracket.
   - Proves alternating skew-symmetry (`so21KKSForm_self_zero`, `so21KKSForm_skew`),
     radial basepoint degeneracy (`so21KKSForm_kernel_basepoint`), non-vanishing on the
     hyperbolic/transverse basis (`so21KKSForm_nondegenerate_witness`), and infinitesimal
     $\mathfrak{so}(2,1)$-invariance (`so21KKSForm_infinitesimal_invariance`).
   - Proves that every concrete 14-parameter split-sedenion derivation `sedenionG2Derivation p`
     annihilates `sedenionZero` (`sedenionG2Derivation_sedenionZero`) and preserves the
     first-order zero-divisor tangent equation (`sedenionG2Derivation_preserves_zero_divisor_tangent`),
     evaluated explicitly on the Peirce zero-divisor pair `((zornE0, 0), (zornE1, 0))`
     (`sedenionG2Derivation_peirce_zero_divisor_tangent`).
-/

noncomputable section

namespace InfoGeometry.Synthesis.G2Sl2SeventeenParameterProductActionBridge

open Matrix
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

/-!
## Section 1: 3-Parameter $\mathfrak{so}(2,1) \cong \mathfrak{sl}(2, \mathbb{R})$ Linear Combination Family & Coordinate Readout
-/

/-- Real $3 \times 3$ specialization of the compact rotation generator $J_{12}$. -/
abbrev sl2GenJ12R : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenJ12 (R := ℝ)

/-- Real $3 \times 3$ specialization of the first hyperbolic boost generator $K_{13}$. -/
abbrev sl2GenK13R : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenK13 (R := ℝ)

/-- Real $3 \times 3$ specialization of the second hyperbolic boost generator $K_{23}$. -/
abbrev sl2GenK23R : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenK23 (R := ℝ)

/-- Explicit non-commutativity witness for the real $3 \times 3$ matrix carrier
`Matrix (Fin 3) (Fin 3) ℝ`: $J_{12} K_{13} \neq K_{13} J_{12}$. -/
theorem so21_generators_noncommute_real :
    sl2GenJ12R * sl2GenK13R ≠ sl2GenK13R * sl2GenJ12R :=
  sl2_generator_products_noncommute

/-- The general 3-parameter $\mathfrak{so}(2,1) \cong \mathfrak{sl}(2, \mathbb{R})$ matrix
linear combination $c_0 J_{12} + c_1 K_{13} + c_2 K_{23} \in \operatorname{Mat}_{3 \times 3}(\mathbb{R})$. -/
def so21LinearComb (c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  c 0 • sl2GenJ12 + c 1 • sl2GenK13 + c 2 • sl2GenK23

/-- Every 3-parameter linear combination `so21LinearComb c` is skew-adjoint with respect to
the $(2,1)$ metric `eta21`: $M^T \eta_{(2,1)} + \eta_{(2,1)} M = 0$. -/
theorem so21LinearComb_etaSkewAdjoint (c : Fin 3 → ℝ) :
    so21EtaSkewAdjoint (so21LinearComb c) := by
  dsimp [so21EtaSkewAdjoint, so21LinearComb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta21, sl2GenJ12, sl2GenK13, sl2GenK23, Matrix.mul_apply, Fin.sum_univ_three]

/-- Every 3-parameter linear combination `so21LinearComb c` has trace zero. -/
theorem so21LinearComb_trace_zero (c : Fin 3 → ℝ) :
    Matrix.trace (so21LinearComb c) = 0 := by
  simp [so21LinearComb, sl2GenJ12, sl2GenK13, sl2GenK23,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three]

/-- Every 3-parameter linear combination `so21LinearComb c` lies in the eigenvalue-`2`
eigenspace of the quadratic adjoint operator `so21AdjointQuadraticAction`. -/
theorem so21LinearComb_adjoint_casimir_eq_two (c : Fin 3 → ℝ) :
    so21AdjointQuadraticAction (so21LinearComb c) = (2 : ℝ) • so21LinearComb c :=
  so21_adjoint_quadratic_action_eq_two_of_eta_skew
    (so21LinearComb c) (so21LinearComb_etaSkewAdjoint c)

/-- For every parameter vector `c : Fin 3 → ℝ`, `socleDerivation (so21LinearComb c)` acts as a
derivation of the 4D coordinate multiplication `socleDoublingMul`. -/
theorem so21LinearComb_socleDerivation_leibniz (c : Fin 3 → ℝ)
    (x y : ℝ × (Fin 3 → ℝ)) :
    socleDerivation (so21LinearComb c) (socleDoublingMul x y) =
      socleDoublingMul (socleDerivation (so21LinearComb c) x) y +
        socleDoublingMul x (socleDerivation (so21LinearComb c) y) := by
  ext i
  · simp [socleDerivation, socleDoublingMul, so21BilinearForm, so21LinearComb,
      sl2GenJ12, sl2GenK13, sl2GenK23, dotProduct, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      (simp [socleDerivation, socleDoublingMul, so21CrossProduct, so21LinearComb,
        sl2GenJ12, sl2GenK13, sl2GenK23, dotProduct, Fin.sum_univ_three];
       ring)

/-- Coordinate readout extracting the 3 parameters $(c_0, c_1, c_2)$ from a $3 \times 3$
matrix $M$ via $(-M_{0,1},\, M_{0,2},\, M_{1,2})$. -/
def readSo21Params (M : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![-M 0 1, M 0 2, M 1 2]

/-- Reading the 3 coordinates from `so21LinearComb c` recovers `c` identically. -/
theorem readSo21Params_so21LinearComb (c : Fin 3 → ℝ) :
    readSo21Params (so21LinearComb c) = c := by
  funext i
  fin_cases i <;>
    simp [readSo21Params, so21LinearComb, sl2GenJ12, sl2GenK13, sl2GenK23]

/-- The 3-parameter $\mathfrak{so}(2,1)$ matrix parameterization `so21LinearComb` is injective. -/
theorem so21LinearComb_injective :
    Function.Injective so21LinearComb := by
  intro c₁ c₂ h
  have h' := congrArg readSo21Params h
  rw [readSo21Params_so21LinearComb c₁, readSo21Params_so21LinearComb c₂] at h'
  exact h'

/-- Coordinate readout extracting the 3 parameters $(c_0, c_1, c_2)$ directly from a 4D
coordinate-algebra map `F : ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ)`. -/
def readSocleDerivationParams
    (F : ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  ![(F (0, ![1, 0, 0])).2 1,
    (F (0, ![1, 0, 0])).2 2,
    (F (0, ![0, 1, 0])).2 2]

/-- Evaluating `readSocleDerivationParams` on `socleDerivation (so21LinearComb c)` recovers `c`. -/
theorem readSocleDerivationParams_socleDerivation (c : Fin 3 → ℝ) :
    readSocleDerivationParams (socleDerivation (so21LinearComb c)) = c := by
  funext i
  fin_cases i <;>
    simp [readSocleDerivationParams, socleDerivation, so21LinearComb,
      sl2GenJ12, sl2GenK13, sl2GenK23, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- A single evaluation probe at the null vector `(0, ![0, 1, 1])` has a non-trivial kernel
inside the 3-parameter $\mathfrak{so}(2,1)$ family: the non-zero parameter vector
`c = ![1, 1, 0]` satisfies `socleDerivation (so21LinearComb ![1, 1, 0]) (0, ![0, 1, 1]) = (0, 0)`. -/
theorem so21LinearComb_single_probe_011_nontrivial_kernel :
    (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 ∧
    socleDerivation (so21LinearComb (![1, 1, 0] : Fin 3 → ℝ)) (0, ![0, 1, 1]) = (0, 0) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : (![1, 1, 0] : Fin 3 → ℝ) 0 = (0 : Fin 3 → ℝ) 0 := congrFun h 0
    norm_num at h0
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [socleDerivation, so21LinearComb, sl2GenJ12, sl2GenK13, sl2GenK23,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- In contrast to a single probe at `(0, ![0, 1, 1])`, evaluating `socleDerivation (so21LinearComb c)`
at the two probes `(0, ![1, 0, 0])` and `(0, ![0, 1, 0])` has trivial kernel: both vanish if and
only if `c = 0`. -/
theorem so21LinearComb_two_probe_zero_iff_eq_zero (c : Fin 3 → ℝ) :
    (socleDerivation (so21LinearComb c) (0, ![1, 0, 0]) = (0, 0) ∧
     socleDerivation (so21LinearComb c) (0, ![0, 1, 0]) = (0, 0)) ↔ c = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [← readSocleDerivationParams_socleDerivation c]
    funext i
    fin_cases i <;>
      simp [readSocleDerivationParams, h1, h2]
  · intro hc
    subst c
    constructor
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;>
          simp [socleDerivation, so21LinearComb, sl2GenJ12, sl2GenK13, sl2GenK23,
            Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;>
          simp [socleDerivation, so21LinearComb, sl2GenJ12, sl2GenK13, sl2GenK23,
            Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-!
## Section 1b: Probe separation on the FULL nine-dimensional matrix family

`so21LinearComb_two_probe_zero_iff_eq_zero` above is a statement about the
three-dimensional `so21LinearComb` subspace, and it says so. This section records the
corresponding facts for the **unrestricted** nine-dimensional family
`Matrix (Fin 3) (Fin 3) ℝ`, where that two-probe argument **fails**.

The practical consequence: injectivity arguments in this area that are stated for the
three-dimensional subspace must not be silently reused for the full family.
-/

/-- A nonzero matrix whose three rows are all equal to $(-1, 1, -1)$. Every row annihilates
both $(0, 1, 1)^{\mathsf T}$ and $(1, 1, 0)^{\mathsf T}$, so this matrix lies in the kernel
of $X \mapsto \bigl(X(0,1,1)^{\mathsf T},\, X(1,1,0)^{\mathsf T}\bigr)$. -/
def so21FullMatrix_nonSeparating : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 1, -1;
     -1, 1, -1;
     -1, 1, -1]

theorem so21FullMatrix_nonSeparating_ne_zero :
    so21FullMatrix_nonSeparating ≠ (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
  intro h
  have h00 := congrFun (congrFun h 0) (0 : Fin 3)
  norm_num [so21FullMatrix_nonSeparating] at h00

/-- **Two probes do NOT separate the full nine-dimensional matrix family.**
`so21FullMatrix_nonSeparating ≠ 0`, yet both of its images at $(0,1,1)^{\mathsf T}$ and
$(1,1,0)^{\mathsf T}$ vanish. Only the third probe $(1,0,1)^{\mathsf T}$ detects it. This is
the obstruction to transplanting `so21LinearComb_two_probe_zero_iff_eq_zero` from the
three-dimensional subspace to the unrestricted family. -/
theorem so21FullMatrix_two_probes_do_not_separate :
    so21FullMatrix_nonSeparating.mulVec ![0, 1, 1] = (fun _ => (0 : ℝ)) ∧
      so21FullMatrix_nonSeparating.mulVec ![1, 1, 0] = (fun _ => (0 : ℝ)) ∧
      so21FullMatrix_nonSeparating.mulVec ![1, 0, 1] ≠ (fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [so21FullMatrix_nonSeparating, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [so21FullMatrix_nonSeparating, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro hh
    have hh' := congrFun hh 0
    norm_num [so21FullMatrix_nonSeparating, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at hh'

/-- **Three independent probes force the full matrix to vanish.** The map
$X \mapsto (X e_0,\, X e_1,\, X e_2)$ is injective on `Matrix (Fin 3) (Fin 3) ℝ`.
The cited two-probe counterexample proves failure only for its specific pair; this theorem
proves sufficiency of the three coordinate probes. -/
theorem so21FullMatrix_three_probes_eq_zero (X : Matrix (Fin 3) (Fin 3) ℝ)
    (h0 : X.mulVec (Pi.single 0 1) = fun _ => 0)
    (h1 : X.mulVec (Pi.single 1 1) = fun _ => 0)
    (h2 : X.mulVec (Pi.single 2 1) = fun _ => 0) : X = 0 := by
  ext i j
  fin_cases j
  · have h := congrFun h0 i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    exact h
  · have h := congrFun h1 i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    exact h
  · have h := congrFun h2 i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    exact h

/-!
## Section 2: Joint 17-Parameter Product Action (`14 + 3 = 17`) & Parameter Equivalence
-/

/-- Splits a 17-parameter vector `q : Fin 17 → ℝ` into its first 14 coordinates
(`Params = Fin 14 → ℝ`) and its last 3 coordinates (`Fin 3 → ℝ`). -/
def split17Params (q : Fin 17 → ℝ) : Params × (Fin 3 → ℝ) :=
  (fun i : Fin 14 => q ⟨i.val, by omega⟩,
   fun j : Fin 3 => q ⟨14 + j.val, by omega⟩)

/-- Combines a 14-parameter vector and a 3-parameter vector into a single
17-parameter vector `Fin 17 → ℝ`. -/
def combine17Params (pc : Params × (Fin 3 → ℝ)) : Fin 17 → ℝ := fun k =>
  if hk : k.val < 14 then
    pc.1 ⟨k.val, hk⟩
  else
    pc.2 ⟨k.val - 14, by omega⟩

/-- `split17Params` is a left inverse to `combine17Params`. -/
theorem split17Params_combine17Params (pc : Params × (Fin 3 → ℝ)) :
    split17Params (combine17Params pc) = pc := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext j
    fin_cases j <;> rfl

/-- `combine17Params` is a left inverse to `split17Params`. -/
theorem combine17Params_split17Params (q : Fin 17 → ℝ) :
    combine17Params (split17Params q) = q := by
  funext k
  fin_cases k <;> rfl

/-- Explicit equivalence `(Params × (Fin 3 → ℝ)) ≃ (Fin 17 → ℝ)` witnessing the
`14 + 3 = 17` parameter space decomposition. -/
def params14Prod3EquivFin17 : (Params × (Fin 3 → ℝ)) ≃ (Fin 17 → ℝ) where
  toFun := combine17Params
  invFun := split17Params
  left_inv := split17Params_combine17Params
  right_inv := combine17Params_split17Params

/-- The joint 17-parameter action pair combining the 14-parameter diagonal $G_2$
split-sedenion derivation `sedenionG2Derivation` with the 3-parameter $\mathfrak{so}(2,1)$
coordinate-algebra derivation `socleDerivation (so21LinearComb _)`. -/
def jointG2So21Action (q : Fin 17 → ℝ) :
    (SplitSedenion ℝ → SplitSedenion ℝ) × (ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ)) :=
  (sedenionG2Derivation (split17Params q).1,
   socleDerivation (so21LinearComb (split17Params q).2))

/-- Coordinate readout extracting all 17 parameters `Fin 17 → ℝ` from a pair of
split-sedenion and 4D coordinate-algebra operators. -/
def readJoint17Params
    (pair : (SplitSedenion ℝ → SplitSedenion ℝ) × (ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ))) :
    Fin 17 → ℝ :=
  combine17Params (readSedenionG2Params pair.1, readSocleDerivationParams pair.2)

/-- Reading the 17 parameters from `jointG2So21Action q` recovers `q` identically. -/
theorem readJoint17Params_jointG2So21Action (q : Fin 17 → ℝ) :
    readJoint17Params (jointG2So21Action q) = q := by
  dsimp [readJoint17Params, jointG2So21Action]
  rw [readSedenionG2Params_sedenionG2Derivation,
      readSocleDerivationParams_socleDerivation,
      combine17Params_split17Params]

/-- The joint 17-parameter action map `jointG2So21Action` is injective. -/
theorem jointG2So21Action_injective :
    Function.Injective jointG2So21Action := by
  intro q₁ q₂ h
  have h' := congrArg readJoint17Params h
  rw [readJoint17Params_jointG2So21Action q₁,
      readJoint17Params_jointG2So21Action q₂] at h'
  exact h'

/-- Separation between the 14-parameter diagonal $G_2$ lift and the 3-parameter
$\mathfrak{so}(2,1)$ coordinate-algebra action: every `sedenionG2Derivation p`
annihilates the Cayley–Dickson doubling generator `sedenionEll = (0, 1)`, whereas
`socleDerivation (so21LinearComb c)` maps `(0, ![1, 0, 0])` to `(0, ![0, c 0, c 1])`. -/
theorem sedenionG2Derivation_annihilates_ell_vs_socleDerivation_active
    (p : Params) (c : Fin 3 → ℝ) :
    sedenionG2Derivation p sedenionEll = sedenionZero ∧
    socleDerivation (so21LinearComb c) (0, ![1, 0, 0]) = (0, ![0, c 0, c 1]) := by
  refine ⟨sedenionG2Derivation_sedenionEll_zero p, ?_⟩
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [socleDerivation, so21LinearComb, sl2GenJ12, sl2GenK13, sl2GenK23,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-!
## Section 3: Alternating Cross-Product Pairing on the $\mathfrak{so}(2,1)$ Socle & Zero-Divisor Tangent Locus
-/

/-- Coordinate alternating pairing $\omega_\mu(\xi, \eta) = \langle \mu, \xi \times_{(2,1)} \eta \rangle_{(2,1)}$
on the 3D $(2,1)$-signature socle carrier `Fin 3 → ℝ`. Its identification with a KKS form
requires a separate proof relating this cross product to the chosen matrix Lie bracket. -/
def so21KKSForm (μ ξ η : Fin 3 → ℝ) : ℝ :=
  so21BilinearForm μ (so21CrossProduct ξ η)

/-- `so21KKSForm μ` vanishes on identical tangent vectors: $\omega_\mu(\xi, \xi) = 0$. -/
theorem so21KKSForm_self_zero (μ ξ : Fin 3 → ℝ) :
    so21KKSForm μ ξ ξ = 0 := by
  dsimp [so21KKSForm, so21BilinearForm, so21CrossProduct]
  ring

/-- `so21KKSForm μ` is alternating / skew-symmetric: $\omega_\mu(\xi, \eta) = -\omega_\mu(\eta, \xi)$. -/
theorem so21KKSForm_skew (μ ξ η : Fin 3 → ℝ) :
    so21KKSForm μ ξ η = -so21KKSForm μ η ξ := by
  dsimp [so21KKSForm, so21BilinearForm, so21CrossProduct]
  ring

/-- The radial vector $\mu$ lies in the kernel of `so21KKSForm μ`: $\omega_\mu(\mu, \eta) = 0$. -/
theorem so21KKSForm_kernel_basepoint (μ η : Fin 3 → ℝ) :
    so21KKSForm μ μ η = 0 := by
  dsimp [so21KKSForm, so21BilinearForm, so21CrossProduct]
  ring

/-- A nonzero evaluation witness at basepoint $\mu = (0, 0, 1)$:
$\omega_{(0,0,1)}((1,0,0), (0,1,0)) = 1$. -/
theorem so21KKSForm_nondegenerate_witness :
    so21KKSForm ![0, 0, 1] ![1, 0, 0] ![0, 1, 0] = 1 := by
  norm_num [so21KKSForm, so21BilinearForm, so21CrossProduct]

/-- Infinitesimal $\mathfrak{so}(2,1)$ invariance of the KKS trilinear pairing:
for every $M = \operatorname{so21LinearComb}(c)$,
$\omega_{M\mu}(\xi, \eta) + \omega_\mu(M\xi, \eta) + \omega_\mu(\xi, M\eta) = 0$. -/
theorem so21KKSForm_infinitesimal_invariance (c μ ξ η : Fin 3 → ℝ) :
    so21KKSForm ((so21LinearComb c).mulVec μ) ξ η +
      so21KKSForm μ ((so21LinearComb c).mulVec ξ) η +
      so21KKSForm μ ξ ((so21LinearComb c).mulVec η) = 0 := by
  simp [so21KKSForm, so21BilinearForm, so21CrossProduct, so21LinearComb,
    sl2GenJ12, sl2GenK13, sl2GenK23, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Every concrete 14-parameter split-sedenion derivation `sedenionG2Derivation p`
annihilates `sedenionZero`. -/
theorem sedenionG2Derivation_sedenionZero (p : Params) :
    sedenionG2Derivation p sedenionZero = sedenionZero := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionZero]
    exact zornG2Derivation_zornZero p
  · dsimp [sedenionG2Derivation, cdLift, sedenionZero]
    exact zornG2Derivation_zornZero p

/-- Every concrete 14-parameter split-sedenion derivation `sedenionG2Derivation p` maps any
zero-divisor pair $(X, Y)$ satisfying $X \circ Y = 0$ into the first-order zero-divisor
tangent locus $(D_p X) \circ Y + X \circ (D_p Y) = 0$. -/
theorem sedenionG2Derivation_preserves_zero_divisor_tangent
    (p : Params) (X Y : SplitSedenion ℝ) (hXY : sedenionMul X Y = sedenionZero) :
    sedenionAdd (sedenionMul (sedenionG2Derivation p X) Y)
      (sedenionMul X (sedenionG2Derivation p Y)) = sedenionZero := by
  rw [← sedenionG2Derivation_leibniz p X Y, hXY, sedenionG2Derivation_sedenionZero p]

/-- Concrete instantiation of the zero-divisor tangent identity on the non-zero Peirce
zero-divisor pair $((e_0, 0), (e_1, 0))$ from `Cl44LeftIdealSplitSedenionSynthesis`. -/
theorem sedenionG2Derivation_peirce_zero_divisor_tangent (p : Params) :
    sedenionAdd
      (sedenionMul
        (sedenionG2Derivation p ((zornE0 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)))
        ((zornE1 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)))
      (sedenionMul
        ((zornE0 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ))
        (sedenionG2Derivation p ((zornE1 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)))) =
      sedenionZero :=
  sedenionG2Derivation_preserves_zero_divisor_tangent p
    ((zornE0 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ))
    ((zornE1 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ))
    splitSedenion_explicit_zero_divisors_and_null_norm.1

end InfoGeometry.Synthesis.G2Sl2SeventeenParameterProductActionBridge
