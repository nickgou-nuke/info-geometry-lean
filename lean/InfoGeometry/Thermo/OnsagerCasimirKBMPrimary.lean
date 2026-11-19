/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Canonical.BKMOnsagerMobilityBridge
import InfoGeometry.Canonical.KuboMoriBogoliubovMetric
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.Canonical.SouriauOnsagerBKMCauchySchwarz
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity
import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity
import InfoGeometry.Optics.FiniteBKMDiracMetricReadout
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge
import InfoGeometry.Thermo.OnsagerOperatorClosure
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms

/-!
# Pillar 3 (`R1`) Primary-Source Formalization: Fréchet, H. Cartan, Onsager–Casimir, Kubo–Bogoliubov–Mori

Formalizes primary-source archetypes `S3-11`..`S3-17` atop native Mathlib v4.34.1 and existing
repository owners, preserving `R3.1` and `R3.4` throughout:
1. `S3-11` M. Fréchet (1925): coordinate-free normed differential `fderiv`, `o(‖h‖)` remainder
   bound, `ε-δ` uniform remainder, chain rule, and symmetric vs. alternating 2nd-order contrast.
2. `S3-12` H. Cartan (1967; OA sub: Kriegl–Michor 1997 `§§33.14–33.18`): kinematic Banach
   differential forms (`OperatorFrechetFormK`), interior contraction `banachInteriorProduct`
   (`ι_X² = 0`), Cartan magic operator `banachCartanMagicForm`, pullback naturality, and explicit
   `O-EXT` / `BUCKET 3` boundary documentation for Kriegl–Michor `§§33.14, 33.16` Banach `d_loc`
   failure and infinite-dimensional Frobenius (`§32.12`).
3. `S3-13` & `S3-14` L. Onsager (1931) & H. B. G. Casimir (1945; OA sub: Brechet 2022 `§4`,
   Gaspard 2012): matrix Casimir `J`-reciprocity `Lᵀ = J L J` (`J² = 1, Jᵀ = J`), even/odd
   parity decomposition, `ParityOnsagerSystem` correspondence, and explicit `2×2` mixed-parity
   counterexample `Lᵀ ≠ L` (`J ≠ I`, `R3.1`).
4. `S3-15` & `S3-16` R. Kubo (1957; OA sub: Carlen–Maas, Tonchev) & N. N. Bogoliubov (1961/1970;
   OA sub: Wreszinski–Zagrebnov, Chatterjee): Kubo–Duhamel BKM pairing symmetry/positivity,
   centered BKM covariance Cauchy–Schwarz, Bogoliubov first-moment variance inequality
   `(E[A])² ≤ g_BKM(A, A)`, spectral BKM Cauchy–Schwarz, and `O-EXT` Type III / thermodynamic-limit
   boundary notes.
5. `S3-17` H. Mori (1965; OA sub: te Vrugt–Wittkowski 2020 `§II.B`): rank-1 (`moriProjector1`,
   `bkmMoriProjector1`) and multi-variable (`MoriSlowVariables.projector`) orthogonal slow-variable
   projectors satisfying idempotence `P² = P`, BKM self-adjointness, fast-variable orthogonality,
   Pythagorean variance decomposition, and Bessel contraction (`O-EXT` Volterra memory kernel noted).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Thermo.OnsagerCasimirKBMPrimary

open InfoGeometry.Algebra
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge
open InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
open SouriauOnsagerBKM
open scoped Matrix

/-! ## Section 1: Fréchet (1925) & H. Cartan (1967) / Kriegl–Michor (1997) (`S3-11`..`S3-12`) -/

/-- `[S3-11]` M. Fréchet (1925) Ch. I–II pp. 307–309: Coordinate-free Fréchet differentiability
expressed as the `o(‖h‖)` linear approximation remainder `(f(x + h) - f x - L h) =o[𝓝 0] id`. -/
theorem frechet_littleO_remainder
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {L : E →L[𝕜] F} {x : E} (hf : HasFDerivAt f L x) :
    (fun h' : E => f (x + h') - f x - L h') =o[nhds (0 : E)] id := by
  have ht0 : ContinuousAt (fun h' : E => x + h') 0 :=
    continuousAt_const.add continuousAt_id
  have ht : Filter.Tendsto (fun h' : E => x + h') (nhds (0 : E)) (nhds x) := by
    have ht1 := ht0.tendsto
    rwa [add_zero] at ht1
  have h : (fun h' : E => f (x + h') - f x - L (x + h' - x)) =o[nhds (0 : E)]
      (fun h' : E => x + h' - x) :=
    hf.isLittleO.comp_tendsto ht
  have hcongr : (fun h' : E => f (x + h') - f x - L (x + h' - x)) =
      (fun h' : E => f (x + h') - f x - L h') := by
    funext h'
    rw [add_sub_cancel_left]
  have hid : (fun h' : E => x + h' - x) = id := by
    funext h'
    exact add_sub_cancel_left x h'
  rw [hcongr, hid] at h
  exact h

/-- `[S3-11]` M. Fréchet (1925) Ch. II p. 308: Explicit `ε-δ` uniform remainder corollary of
`HasFDerivAt`: for every `ε > 0`, `‖f (x + h) - f x - L h‖ ≤ ε * ‖h‖` near `h = 0`. -/
theorem frechet_eps_delta_remainder
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {L : E →L[𝕜] F} {x : E} (hf : HasFDerivAt f L x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : E in nhds (0 : E), ‖f (x + h) - f x - L h‖ ≤ ε * ‖h‖ :=
  (frechet_littleO_remainder hf).bound hε

/-- `[S3-11]` M. Fréchet (1925) Ch. II p. 307: Chain rule `fderiv 𝕜 (g ∘ f) x = g'.comp f'`
for normed spaces over `𝕜`. -/
theorem frechet_chain_rule
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {g : F → G} {f' : E →L[𝕜] F} {g' : F →L[𝕜] G} {x : E}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) :
    fderiv 𝕜 (g ∘ f) x = g'.comp f' :=
  (hg.comp x hf).fderiv

/-- `[S3-11]` M. Fréchet (1925) Ch. II: Contrasts symmetric 2nd Fréchet differentials
(`operatorFrechetJet 2 f x`, symmetric for `C^2` maps) with alternating 2-forms
(`OperatorFrechetForm ℂ ℂ ℂ 2`, vanishing on the diagonal). -/
theorem frechet_second_differential_symm_vs_alternating
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {r : WithTop ℕ∞} {f : E → F} {x : E}
    (hf : ContDiffAt ℂ r f x) (hr : minSmoothness ℂ 2 ≤ r) (u v : E) :
    operatorFrechetJet 2 f x ![u, v] = operatorFrechetJet 2 f x ![v, u] ∧
    (∃ g : ℂ → ℂ, operatorFrechetJet 2 g 0 (![1, 1] : Fin 2 → ℂ) ≠ 0 ∧
      ∀ ω : OperatorFrechetForm ℂ ℂ ℂ 2, ω 0 (![1, 1] : Fin 2 → ℂ) = 0) :=
  ⟨operatorFrechetJet_two_symm hf hr u v, operatorFrechetJet_two_diag_nonzero_witness⟩

/-- `[S3-12]` H. Cartan (1967); OA sub: Kriegl–Michor (1997) Ch. VII §33.12 & `§33.18`:
Banach interior contraction `ι_X : OperatorFrechetFormK 𝕜 E E F (n + 1) → OperatorFrechetFormK 𝕜 E E F n`
on kinematic alternating differential forms (`R3.4`).
**`O-EXT` / `BUCKET 3` boundary (Kriegl–Michor `§§33.14, 33.16`)**: Mathlib's `extDeriv` and
`OperatorFrechetFormK` stay strictly on the kinematic bundle `E → (E [⋀^Fin n]→L[𝕜] F)` rather
than operational forms `C^∞(U, L(E'', ℝ))`, where local `d_loc` fails both pullback naturality
(`§33.14`: `d_loc f^* ω ≠ f^* d_loc ω`) and `d_loc² = 0` (`§33.16`) on non-reflexive Banach
spaces `E`; infinite-dimensional Frobenius ODEs (`§32.12`) also remain `O-EXT`. -/
def banachInteriorProduct
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (X : E → E) (ω : OperatorFrechetFormK 𝕜 E E F (n + 1)) :
    OperatorFrechetFormK 𝕜 E E F n :=
  fun x => (ω x).curryLeft (X x)

@[simp] theorem banachInteriorProduct_apply
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (X : E → E) (ω : OperatorFrechetFormK 𝕜 E E F (n + 1)) (x : E) :
    banachInteriorProduct X ω x = (ω x).curryLeft (X x) :=
  rfl

/-- `[S3-12]` Kriegl–Michor (1997) §33.18(7): Nilpotence `ι_X ∘ ι_X = 0` on Banach forms. -/
theorem banachInteriorProduct_sq_zero
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (X : E → E) (ω : OperatorFrechetFormK 𝕜 E E F (n + 2)) :
    banachInteriorProduct X (banachInteriorProduct X ω) = 0 := by
  funext x
  exact (ω x).curryLeft_same (X x)

/-- `[S3-12]` Kriegl–Michor (1997) §33.18: Additivity of `banachInteriorProduct`. -/
theorem banachInteriorProduct_add
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (X : E → E) (ω₁ ω₂ : OperatorFrechetFormK 𝕜 E E F (n + 1)) :
    banachInteriorProduct X (ω₁ + ω₂) =
      banachInteriorProduct X ω₁ + banachInteriorProduct X ω₂ := by
  funext x
  rfl

/-- `[S3-12]` Kriegl–Michor (1997) §33.18: `𝕜`-homogeneity of `banachInteriorProduct`. -/
theorem banachInteriorProduct_smul
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (c : 𝕜) (X : E → E) (ω : OperatorFrechetFormK 𝕜 E E F (n + 1)) :
    banachInteriorProduct X (c • ω) = c • banachInteriorProduct X ω := by
  funext x
  rfl

/-- `[S3-12]` H. Cartan (1967); OA sub: Kriegl–Michor (1997) §33.18(6): Cartan magic operator
`L_X ω := ι_X (d_Fr ω) + d_Fr (ι_X ω)` on kinematic Banach differential forms
(`O-EXT` boundary noted for operational `d_loc` per `§§33.14, 33.16`). -/
def banachCartanMagicForm
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (X : E → E) (ω : OperatorFrechetFormK 𝕜 E E F (n + 1)) :
    OperatorFrechetFormK 𝕜 E E F (n + 1) :=
  banachInteriorProduct X (frechetExtDerivK ω) + frechetExtDerivK (banachInteriorProduct X ω)

/-- `[S3-12]` Kriegl–Michor (1997) §33.18(6): Degree-0 directional derivative identity
`ι_X (d_Fr f) x = constOfIsEmpty (fderiv 𝕜 f x (X x))` on kinematic `0`-forms. -/
theorem banachCartanMagicForm_degree_zero
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (X : E → E) (f : E → F) (x : E) :
    banachInteriorProduct X
        (frechetExtDerivK (fun y => ContinuousAlternatingMap.constOfIsEmpty 𝕜 E (Fin 0) (f y))) x =
      ContinuousAlternatingMap.constOfIsEmpty 𝕜 E (Fin 0) (fderiv 𝕜 f x (X x)) := by
  ext v
  have hv : v = Fin.elim0 := funext fun i => i.elim0
  subst hv
  simp only [banachInteriorProduct_apply, frechetExtDerivK, extDeriv_constOfIsEmpty,
    ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.constOfIsEmpty_apply]
  rfl

/-- `[S3-12]` H. Cartan (1967); OA sub: Kriegl–Michor (1997) §33.15 & §33.18(1),(4):
On kinematic Banach forms `OperatorFrechetFormK`, `d_Fr² = 0` (`C^2` regularity), paired with
`frechetExtDerivK_pullback_comm` in sharp contrast to the `O-EXT` `d_loc` failures of `§§33.14, 33.16`. -/
theorem frechetExtDerivK_sq_zero_banach
    {𝕜 E M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    {r : WithTop ℕ∞} (ω : OperatorFrechetFormK 𝕜 E E M n)
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    frechetExtDerivK (frechetExtDerivK ω) = 0 :=
  frechetExtDerivK_frechetExtDeriv hω hr

/-- `[S3-12]` Kriegl–Michor (1997) §33.15: Pullback naturality `d_Fr (f^* ω) = f^* (d_Fr ω)`
for `C^2` maps `f : E → F` and differentiable kinematic Banach forms `ω`. -/
theorem frechetExtDerivK_pullback_comm
    {𝕜 E F M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    {ω : OperatorFrechetFormK 𝕜 F F M n} {f : E → F} {x : E}
    (hω : DifferentiableAt 𝕜 ω (f x)) (hf : ContDiffAt 𝕜 (minSmoothness 𝕜 2) f x) :
    frechetExtDerivK (fun y => (ω (f y)).compContinuousLinearMap (fderiv 𝕜 f y)) x =
      (frechetExtDerivK ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x) :=
  extDeriv_pullback hω hf le_rfl

/-! ## Section 2: Onsager (1931) & Casimir (1945) $J$-Reciprocity (`S3-13`..`S3-14`) -/

/-- `[S3-13]` `[S3-14]` Closed noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℝ` (`T16`). -/
theorem matrix_real_two_noncommuting_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨MatrixNoncommutativity.swapMatrix, MatrixNoncommutativity.tiltedMatrix,
    MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne⟩

/-- `[S3-14]` H. B. G. Casimir (1945); OA sub: Brechet (2022) §4 eqs. (26)–(33), Gaspard (2012) §2:
Finite-dimensional matrix Casimir reciprocity system with time-reversal parity matrix `J`
(`J² = 1`, `Jᵀ = J`) and kinetic matrix `L` satisfying `Lᵀ = J * L * J` (`R3.1`). -/
structure MatrixCasimirSystem (n : ℕ) where
  J : Matrix (Fin n) (Fin n) ℝ
  L : Matrix (Fin n) (Fin n) ℝ
  J_sq : J * J = 1
  J_symm : Jᵀ = J
  casimir_reciprocity : Lᵀ = J * L * J

namespace MatrixCasimirSystem

/-- `[S3-13]` `[S3-14]` Symmetric (dissipative) part `L_sym = (1/2) • (L + Lᵀ)`. -/
def symPart {n : ℕ} (C : MatrixCasimirSystem n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (C.L + C.Lᵀ)

/-- `[S3-13]` `[S3-14]` Skew-symmetric (reversible/gyroscopic) part `L_skew = (1/2) • (L - Lᵀ)`. -/
def skewPart {n : ℕ} (C : MatrixCasimirSystem n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (C.L - C.Lᵀ)

/-- `[S3-13]` `[S3-14]` Decomposition `L = L_sym + L_skew`. -/
theorem L_eq_symPart_add_skewPart {n : ℕ} (C : MatrixCasimirSystem n) :
    C.symPart + C.skewPart = C.L := by
  ext i j
  simp only [symPart, skewPart, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

/-- `[S3-13]` Symmetry `(L_sym)ᵀ = L_sym`. -/
theorem symPart_transpose {n : ℕ} (C : MatrixCasimirSystem n) :
    C.symPartᵀ = C.symPart := by
  ext i j
  simp only [symPart, Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- `[S3-13]` Skew-symmetry `(L_skew)ᵀ = -L_skew`. -/
theorem skewPart_transpose {n : ℕ} (C : MatrixCasimirSystem n) :
    C.skewPartᵀ = -C.skewPart := by
  ext i j
  simp only [skewPart, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul]
  ring

/-- `[S3-14]` Casimir conjugation `J * L * J = Lᵀ`. -/
theorem J_conj_L_eq_transpose {n : ℕ} (C : MatrixCasimirSystem n) :
    C.J * C.L * C.J = C.Lᵀ :=
  C.casimir_reciprocity.symm

/-- `[S3-14]` Conjugate transpose identity `J * Lᵀ * J = L`. -/
theorem J_conj_L_transpose {n : ℕ} (C : MatrixCasimirSystem n) :
    C.J * C.Lᵀ * C.J = C.L := by
  rw [C.casimir_reciprocity]
  calc C.J * (C.J * C.L * C.J) * C.J
      = (C.J * C.J) * C.L * (C.J * C.J) := by noncomm_ring
    _ = C.L := by rw [C.J_sq]; noncomm_ring

/-- `[S3-14]` Casimir parity theorem: the dissipative symmetric part `L_sym` is `J`-even
(`J * L_sym * J = L_sym`). -/
theorem symPart_J_even {n : ℕ} (C : MatrixCasimirSystem n) :
    C.J * C.symPart * C.J = C.symPart := by
  dsimp [symPart]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    C.J_conj_L_eq_transpose, C.J_conj_L_transpose, add_comm C.Lᵀ C.L]

/-- `[S3-14]` Casimir parity theorem: the reversible skew part `L_skew` is `J`-odd
(`J * L_skew * J = -L_skew`). -/
theorem skewPart_J_odd {n : ℕ} (C : MatrixCasimirSystem n) :
    C.J * C.skewPart * C.J = -C.skewPart := by
  dsimp [skewPart]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    C.J_conj_L_eq_transpose, C.J_conj_L_transpose, ← neg_sub C.L C.Lᵀ, smul_neg]

/-- `[S3-13]` `[S3-14]` Canonical lift of a dissipative `MatrixCasimirSystem n` to the
repository's `OnsagerClosure.OnsagerCasimirSystem.ParityOnsagerSystem (Fin n → ℝ)`. -/
def toParityOnsagerSystem {n : ℕ} (C : MatrixCasimirSystem n)
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (C.symPart *ᵥ x)) :
    OnsagerCasimirSystem.ParityOnsagerSystem (Fin n → ℝ) where
  dissipative := Matrix.toBilin' C.symPart
  reversible := Matrix.toBilin' C.skewPart
  dissipative_symm x y := by
    simp only [Matrix.toBilin'_apply']
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.symPart_transpose,
      dotProduct_comm]
  reversible_skew x y := by
    simp only [Matrix.toBilin'_apply']
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.skewPart_transpose,
      Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  dissipative_nonneg x := by
    simpa only [Matrix.toBilin'_apply'] using hpsd x
  T :=
    { op := C.J.mulVecLin
      involutive := fun x => by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, C.J_sq, Matrix.one_mulVec] }
  dissipative_T_even x y := by
    simp only [Matrix.toBilin'_apply', Matrix.mulVecLin_apply]
    calc (C.J *ᵥ x) ⬝ᵥ (C.symPart *ᵥ (C.J *ᵥ y))
        = (C.symPart *ᵥ (C.J *ᵥ y)) ⬝ᵥ (C.J *ᵥ x) := dotProduct_comm _ _
      _ = ((C.symPart *ᵥ (C.J *ᵥ y)) ᵥ* C.J) ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
      _ = (C.Jᵀ *ᵥ (C.symPart *ᵥ (C.J *ᵥ y))) ⬝ᵥ x := by rw [← Matrix.mulVec_transpose]
      _ = ((C.J * C.symPart * C.J) *ᵥ y) ⬝ᵥ x := by
          rw [C.J_symm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (C.symPart *ᵥ y) ⬝ᵥ x := by rw [C.symPart_J_even]
      _ = x ⬝ᵥ (C.symPart *ᵥ y) := dotProduct_comm _ _
  reversible_T_odd x y := by
    simp only [Matrix.toBilin'_apply', Matrix.mulVecLin_apply]
    calc (C.J *ᵥ x) ⬝ᵥ (C.skewPart *ᵥ (C.J *ᵥ y))
        = (C.skewPart *ᵥ (C.J *ᵥ y)) ⬝ᵥ (C.J *ᵥ x) := dotProduct_comm _ _
      _ = ((C.skewPart *ᵥ (C.J *ᵥ y)) ᵥ* C.J) ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
      _ = (C.Jᵀ *ᵥ (C.skewPart *ᵥ (C.J *ᵥ y))) ⬝ᵥ x := by rw [← Matrix.mulVec_transpose]
      _ = ((C.J * C.skewPart * C.J) *ᵥ y) ⬝ᵥ x := by
          rw [C.J_symm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (-(C.skewPart *ᵥ y)) ⬝ᵥ x := by rw [C.skewPart_J_odd, Matrix.neg_mulVec]
      _ = -(x ⬝ᵥ (C.skewPart *ᵥ y)) := by rw [neg_dotProduct, dotProduct_comm]

/-- `[S3-14]` Compatibility of `toParityOnsagerSystem` with `totalGenerator` (`L`) and
`onsager_casimir_master_reciprocity`. -/
theorem toParityOnsagerSystem_totalGenerator {n : ℕ} (C : MatrixCasimirSystem n)
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (C.symPart *ᵥ x)) (x y : Fin n → ℝ) :
    (C.toParityOnsagerSystem hpsd).totalGenerator x y = dotProduct x (C.L *ᵥ y) ∧
    (C.toParityOnsagerSystem hpsd).totalGenerator (C.J *ᵥ x) (C.J *ᵥ y) =
      (C.toParityOnsagerSystem hpsd).totalGenerator y x := by
  constructor
  · change Matrix.toBilin' C.symPart x y + Matrix.toBilin' C.skewPart x y = dotProduct x (C.L *ᵥ y)
    simp only [Matrix.toBilin'_apply', ← dotProduct_add, ← Matrix.add_mulVec,
      C.L_eq_symPart_add_skewPart]
  · exact (C.toParityOnsagerSystem hpsd).onsager_casimir_master_reciprocity x y

end MatrixCasimirSystem

/-- `[S3-14]` `R3.1` Constructive T17 mixed-parity witness for `MatrixCasimirSystem 2`:
`J = diag(1, -1)` (one even sector, one odd sector) and `L = !![1, 2; -2, 3]` satisfying
`Lᵀ = J * L * J` while `J ≠ 1` and `Lᵀ ≠ L`. -/
def mixedParityCasimirWitness : MatrixCasimirSystem 2 where
  J := !![1, 0; 0, -1]
  L := !![1, 2; -2, 3]
  J_sq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  J_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  casimir_reciprocity := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `[S3-14]` `R3.1` Proof that `mixedParityCasimirWitness` preserves genuine odd-parity
antisymmetry `Lᵀ ≠ L` (`J ≠ 1`, avoiding `J = I` collapse). -/
theorem casimir_odd_sector_not_symmetric :
    mixedParityCasimirWitness.Lᵀ ≠ mixedParityCasimirWitness.L ∧
    mixedParityCasimirWitness.J ≠ 1 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    dsimp [mixedParityCasimirWitness] at h01
    norm_num at h01
  · intro h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
    dsimp [mixedParityCasimirWitness] at h11
    norm_num at h11

/-- `[S3-14]` Lift of `mixedParityCasimirWitness` to `OnsagerFormsBridge.ParityOnsagerFormPairing`
preserving alternating-form Casimir reciprocity. -/
theorem mixedParityCasimir_forms_reciprocity (n : ℕ)
    (v : Fin n → (Fin 2 → ℝ))
    (ω η : (Fin 2 → ℝ) [⋀^Fin n]→ₗ[ℝ] (Fin 2 → ℝ)) :
    let hpsd : ∀ x : Fin 2 → ℝ, 0 ≤ dotProduct x (mixedParityCasimirWitness.symPart *ᵥ x) :=
      fun x => by
        have hsym : mixedParityCasimirWitness.symPart = !![1, 0; 0, 3] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [MatrixCasimirSystem.symPart, mixedParityCasimirWitness] <;> norm_num
        rw [hsym]
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        change 0 ≤ x 0 * (1 * x 0 + 0 * x 1) + x 1 * (0 * x 0 + 3 * x 1)
        simp only [one_mul, zero_mul, add_zero, zero_add]
        refine add_nonneg (mul_self_nonneg (x 0)) ?_
        rw [← mul_assoc, mul_comm (x 1) 3, mul_assoc]
        exact mul_nonneg (by norm_num) (mul_self_nonneg (x 1))
    let PP := ParityOnsagerFormPairing.ofValueParity
      (mixedParityCasimirWitness.toParityOnsagerSystem hpsd) v
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω := by
  intro hpsd PP
  exact onsager_pairing_general_form_reciprocity PP ω η

/-! ## Section 3: Kubo (1957) & Bogoliubov (1961/1970) Duhamel Pairing & Cauchy–Schwarz (`S3-15`..`S3-16`) -/

/-- `[S3-15]` `[S3-16]` R. Kubo (1957) & N. N. Bogoliubov (1961/1970); OA sub: Carlen–Maas `§2`,
Tonchev `§V eq. (51)` & `§VI eqs. (94)–(95)`: Centered BKM real covariance satisfies the
Cauchy–Schwarz inequality `(Cov_BKM(A, B))² ≤ Cov_BKM(A, A) * Cov_BKM(B, B)`.
**`O-EXT` / `BUCKET 3` boundary**: Faithful `D.rpow` requires `ρ > 0` in finite dimensions;
infinite-dimensional Type III modular KMS pairings (`Δ_Ω`) and thermodynamic limits
`lim_{ν→0+} lim_{Λ↑∞}` remain `O-EXT`. -/
theorem centeredBKMRealCovariance_cauchy_schwarz
    {n : ℕ} (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    (centeredBKMRealCovariance D hpow A B) ^ 2 ≤
      centeredBKMRealCovariance D hpow A A * centeredBKMRealCovariance D hpow B B := by
  dsimp [centeredBKMRealCovariance, FaithfulDensityOperator.bkmRealBilinForm]
  exact D.kuboMoriPairing_real_cauchySchwarz_of_continuous_rpow hpow
    (centeredStatistic D A) (centeredStatistic D B)

/-- `[S3-16]` Bogoliubov (1961/1970) first-moment variance inequality:
`(E_D[A])² ≤ g_BKM(A, A)` for every finite operator observable `A` and faithful density `D`. -/
theorem expectationReal_sq_le_bkmRealBilinForm
    {n : ℕ} (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    (expectationReal D A) ^ 2 ≤ D.bkmRealBilinForm hpow A A := by
  have hcs := D.kuboMoriPairing_real_cauchySchwarz_of_continuous_rpow hpow A (1 : FiniteOperatorAlgebra n)
  have hA1 : D.bkmRealBilinForm hpow A 1 = (D.kuboMoriPairing A 1).re := rfl
  have hAA : D.bkmRealBilinForm hpow A A = (D.kuboMoriPairing A A).re := rfl
  have h11 : D.bkmRealBilinForm hpow 1 1 = (D.kuboMoriPairing 1 1).re := rfl
  rw [← hA1, ← hAA, ← h11, bkmRealBilinForm_one_right D hpow A,
    bkmRealBilinForm_one_one D hpow, mul_one] at hcs
  exact hcs

/-- `[S3-15]` `[S3-16]` Package `KuboMoriBogoliubov.FaithfulDensityState.bkmInnerProduct`
as a Mathlib `LinearMap.BilinForm ℝ (Matrix ι ι ℝ)`. -/
def bkmInnerProductBilinForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : KuboMoriBogoliubov.FaithfulDensityState ι) :
    LinearMap.BilinForm ℝ (Matrix ι ι ℝ) :=
  LinearMap.mk₂ ℝ rho.bkmInnerProduct
    (fun A B C => by
      change (∑ i : ι, ∑ j : ι, (A j i + B j i) * C j i * rho.bkmWeight i j) =
        (∑ i : ι, ∑ j : ι, A j i * C j i * rho.bkmWeight i j) +
          (∑ i : ι, ∑ j : ι, B j i * C j i * rho.bkmWeight i j)
      simp_rw [add_mul, Finset.sum_add_distrib])
    (fun r A B => by
      change (∑ i : ι, ∑ j : ι, (r * A j i) * B j i * rho.bkmWeight i j) =
        r * (∑ i : ι, ∑ j : ι, A j i * B j i * rho.bkmWeight i j)
      simp_rw [mul_assoc, ← Finset.mul_sum])
    (fun A B C => by
      change (∑ i : ι, ∑ j : ι, A j i * (B j i + C j i) * rho.bkmWeight i j) =
        (∑ i : ι, ∑ j : ι, A j i * B j i * rho.bkmWeight i j) +
          (∑ i : ι, ∑ j : ι, A j i * C j i * rho.bkmWeight i j)
      simp_rw [mul_add, add_mul, Finset.sum_add_distrib])
    (fun r A B => by
      change (∑ i : ι, ∑ j : ι, A j i * (r * B j i) * rho.bkmWeight i j) =
        r * (∑ i : ι, ∑ j : ι, A j i * B j i * rho.bkmWeight i j)
      have hmul : ∀ i j : ι, A j i * (r * B j i) * rho.bkmWeight i j =
          r * (A j i * B j i * rho.bkmWeight i j) := fun i j =>
        (congrArg (· * rho.bkmWeight i j) (mul_left_comm (A j i) r (B j i))).trans
          (mul_assoc r (A j i * B j i) (rho.bkmWeight i j))
      simp_rw [hmul, ← Finset.mul_sum])

/-- `[S3-16]` Spectral BKM Cauchy–Schwarz inequality on `KuboMoriBogoliubov.FaithfulDensityState`:
`⟨A, B⟩_{BKM}² ≤ ⟨A, A⟩_{BKM} * ⟨B, B⟩_{BKM}` via Mathlib's `LinearMap.BilinForm.apply_sq_le_of_symm`. -/
theorem bkmInnerProduct_cauchy_schwarz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : KuboMoriBogoliubov.FaithfulDensityState ι) (A B : Matrix ι ι ℝ) :
    (rho.bkmInnerProduct A B) ^ 2 ≤ rho.bkmInnerProduct A A * rho.bkmInnerProduct B B := by
  have hsym : LinearMap.IsSymm (bkmInnerProductBilinForm rho) := ⟨rho.bkm_metric_symmetry⟩
  have hnonneg : ∀ X : Matrix ι ι ℝ, 0 ≤ bkmInnerProductBilinForm rho X X :=
    rho.bkm_metric_pos_semidef
  exact LinearMap.BilinForm.apply_sq_le_of_symm (bkmInnerProductBilinForm rho) hnonneg hsym A B

/-- `[S3-16]` Strictness characterization: equality in `bkmInnerProduct_cauchy_schwarz`
forces `A` and `B` to be linearly dependent (`¬ LinearIndependent ℝ ![A, B]`). -/
theorem bkmInnerProduct_cauchy_schwarz_eq_not_linearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : KuboMoriBogoliubov.FaithfulDensityState ι) (A B : Matrix ι ι ℝ)
    (heq : rho.bkmInnerProduct A A * rho.bkmInnerProduct B B =
      rho.bkmInnerProduct A B * rho.bkmInnerProduct A B) :
    ¬ LinearIndependent ℝ ![A, B] := by
  have hnonneg : ∀ X : Matrix ι ι ℝ, 0 ≤ bkmInnerProductBilinForm rho X X :=
    rho.bkm_metric_pos_semidef
  have hposdef : ∀ X : Matrix ι ι ℝ, bkmInnerProductBilinForm rho X X = 0 → X = 0 :=
    fun X hX => (rho.bkm_metric_pos_def X).1 hX
  have hpos : ∀ X : Matrix ι ι ℝ, X ≠ 0 → 0 < bkmInnerProductBilinForm rho X X :=
    fun X hX => lt_of_le_of_ne (hnonneg X) (fun h0 => hX (hposdef X h0.symm))
  have heq' : bkmInnerProductBilinForm rho A B * bkmInnerProductBilinForm rho B A =
      bkmInnerProductBilinForm rho A A * bkmInnerProductBilinForm rho B B := by
    change rho.bkmInnerProduct A B * rho.bkmInnerProduct B A =
      rho.bkmInnerProduct A A * rho.bkmInnerProduct B B
    rw [rho.bkm_metric_symmetry B A]
    exact heq.symm
  exact LinearMap.BilinForm.not_linearIndependent_of_apply_mul_apply_eq
    (bkmInnerProductBilinForm rho) hpos A B heq'

/-- `[S3-15]` `[S3-16]` Compatibility linking `bkmOperator1Form`,
`BKMOnsagerMobilityBridge.matrixKuboMoriMobility`, and `FiniteBKMDiracMetricReadout.diracBKMMetricReadout`. -/
theorem bkm_readout_compatibility
    (D16 : FaithfulDensityOperator 16) (hpow16 : Continuous D16.rpow)
    (A16 : FiniteOperatorAlgebra 16) (M16 : Matrix (Fin 16) (Fin 16) ℂ)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (α : InfoGeometry.OperatorAlgebra.ExteriorAlgebra.Op1Form ℝ V (FiniteOperatorAlgebra 16))
    (u : V) :
    0 ≤ bkmOperator1Form D16 hpow16 α α u ∧
    0 ≤ (Matrix.trace (star M16 *
      InfoGeometry.Canonical.BKMOnsagerMobilityBridge.matrixKuboMoriMobility D16 hpow16 M16)).re ∧
    0 ≤ (InfoGeometry.Optics.FiniteBKMDiracMetricReadout.diracBKMMetricReadout D16 A16 A16).re :=
  ⟨bkmOperator1Form_nonneg D16 hpow16 α u,
   InfoGeometry.Canonical.BKMOnsagerMobilityBridge.matrixKuboMoriMobility_trace_nonneg D16 hpow16 M16,
   InfoGeometry.Optics.FiniteBKMDiracMetricReadout.diracBKMMetricReadout_re_nonnegative
     D16 hpow16 (fun X => D16.kuboMoriPairing_self_re_nonneg X hpow16) A16⟩

/-! ## Section 4: Mori (1965) Slow-Variable Orthogonal Projection (`S3-17`) -/

/-- `[S3-17]` H. Mori (1965); OA sub: te Vrugt–Wittkowski (2020) §II.B eqs. (3)–(5):
Rank-1 Mori slow-variable projection `P_A G = (B G A / B A A) • A` relative to a real
bilinear pairing `B` (`O-EXT` boundary: infinite-dimensional `e^{i Q L t}` Volterra memory kernel
convergence remains `O-EXT` / `BUCKET 3`). -/
def moriProjector1 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (A : V) : V →ₗ[ℝ] V where
  toFun G := (B G A / B A A) • A
  map_add' G₁ G₂ := by
    simp only [map_add, LinearMap.add_apply, add_div, add_smul]
  map_smul' r G := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc,
      smul_smul]

/-- `[S3-17]` te Vrugt–Wittkowski §II.B: `moriProjector1 B A A = A` when `B A A ≠ 0`. -/
theorem moriProjector1_self {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {A : V} (hAA : B A A ≠ 0) :
    moriProjector1 B A A = A := by
  change (B A A / B A A) • A = A
  rw [div_self hAA, one_smul]

/-- `[S3-17]` te Vrugt–Wittkowski §II.B eq. (5): Idempotence `P² = P` of `moriProjector1`. -/
theorem moriProjector1_idempotent {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {A : V} (hAA : B A A ≠ 0) (G : V) :
    moriProjector1 B A (moriProjector1 B A G) = moriProjector1 B A G := by
  change (B ((B G A / B A A) • A) A / B A A) • A = (B G A / B A A) • A
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hAA]

/-- `[S3-17]` te Vrugt–Wittkowski §II.B: `B`-self-adjointness `B (P G₁) G₂ = B G₁ (P G₂)`
when `B` is symmetric. -/
theorem moriProjector1_selfAdjoint {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hSymm : B.IsSymm) (A G₁ G₂ : V) :
    B (moriProjector1 B A G₁) G₂ = B G₁ (moriProjector1 B A G₂) := by
  change B ((B G₁ A / B A A) • A) G₂ = B G₁ ((B G₂ A / B A A) • A)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hSymm.eq A G₂, div_mul_eq_mul_div, mul_comm (B G₁ A) (B G₂ A), ← div_mul_eq_mul_div]

/-- `[S3-17]` te Vrugt–Wittkowski §II.B eq. (5): Orthogonality `B (G - P G) (P H) = 0`
between fast (`Q = I - P`) and slow (`P`) variables. -/
theorem moriProjector1_compl_ortho {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hSymm : B.IsSymm) {A : V} (hAA : B A A ≠ 0) (G H : V) :
    B (G - moriProjector1 B A G) (moriProjector1 B A H) = 0 := by
  rw [map_sub, LinearMap.sub_apply,
    moriProjector1_selfAdjoint hSymm A G (moriProjector1 B A H),
    moriProjector1_idempotent B hAA H]
  exact sub_self _

/-- `[S3-17]` Pythagorean decomposition and Bessel contraction for `moriProjector1`:
`B G G = B (P G) (P G) + B (G - P G) (G - P G)` and `B (P G) (P G) ≤ B G G`. -/
theorem moriProjector1_pythagorean_and_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hSymm : B.IsSymm) (hNonneg : ∀ X, 0 ≤ B X X)
    {A : V} (hAA : B A A ≠ 0) (G : V) :
    B G G = B (moriProjector1 B A G) (moriProjector1 B A G) +
      B (G - moriProjector1 B A G) (G - moriProjector1 B A G) ∧
    B (moriProjector1 B A G) (moriProjector1 B A G) ≤ B G G := by
  have hortho : B (G - moriProjector1 B A G) (moriProjector1 B A G) = 0 :=
    moriProjector1_compl_ortho hSymm hAA G G
  have hortho' : B (moriProjector1 B A G) (G - moriProjector1 B A G) = 0 := by
    rw [hSymm.eq]
    exact hortho
  have hdecomp : G = moriProjector1 B A G + (G - moriProjector1 B A G) := by
    abel
  have hpyth : B G G = B (moriProjector1 B A G) (moriProjector1 B A G) +
      B (G - moriProjector1 B A G) (G - moriProjector1 B A G) := by
    conv_lhs => rw [hdecomp]
    simp only [map_add, LinearMap.add_apply, hortho, hortho', add_zero, zero_add]
  refine ⟨hpyth, ?_⟩
  rw [hpyth]
  exact le_add_of_nonneg_right (hNonneg (G - moriProjector1 B A G))

/-- `[S3-17]` Specialization of `moriProjector1` to the genuine Kubo–Mori–Bogoliubov pairing
`D.bkmRealBilinForm hpow`, discharging `B A A ≠ 0` automatically from `A ≠ 0` via
`D.kuboMoriPairing_self_pos`. -/
def bkmMoriProjector1 {n : ℕ} (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n →ₗ[ℝ] FiniteOperatorAlgebra n :=
  moriProjector1 (D.bkmRealBilinForm hpow) A

/-- `[S3-17]` Idempotence and Bessel contraction of `bkmMoriProjector1` for any nonzero
observable `A ≠ 0` and faithful density `D`. -/
theorem bkmMoriProjector1_idempotent_and_le {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    {A : FiniteOperatorAlgebra n} (hA : A ≠ 0) (G : FiniteOperatorAlgebra n) :
    bkmMoriProjector1 D hpow A (bkmMoriProjector1 D hpow A G) = bkmMoriProjector1 D hpow A G ∧
    D.bkmRealBilinForm hpow (bkmMoriProjector1 D hpow A G) (bkmMoriProjector1 D hpow A G) ≤
      D.bkmRealBilinForm hpow G G := by
  have hAA : D.bkmRealBilinForm hpow A A ≠ 0 := by
    change (D.kuboMoriPairing A A).re ≠ 0
    exact ne_of_gt (D.kuboMoriPairing_self_pos A hpow hA)
  exact ⟨moriProjector1_idempotent (D.bkmRealBilinForm hpow) hAA G,
    (moriProjector1_pythagorean_and_le (D.bkmRealBilinForm_symm hpow)
      (fun X => D.kuboMoriPairing_self_re_nonneg X hpow) hAA G).2⟩

/-- `[S3-17]` H. Mori (1965); OA sub: te Vrugt–Wittkowski (2020) §II.B eqs. (16)–(17):
Multi-variable Mori slow-variable subspace packaged with a symmetric PSD bilinear form `B`,
slow modes `slow : Fin k → V`, and explicit inverse Gram matrix `gramInv` (`G * G⁻¹ = 1`). -/
structure MoriSlowVariables (V : Type*) [AddCommGroup V] [Module ℝ V] (k : ℕ) where
  B : LinearMap.BilinForm ℝ V
  B_symm : B.IsSymm
  B_nonneg : ∀ x, 0 ≤ B x x
  slow : Fin k → V
  gramInv : Matrix (Fin k) (Fin k) ℝ
  gram_mul_inv : (Matrix.of fun i j => B (slow i) (slow j)) * gramInv = 1
  inv_mul_gram : gramInv * (Matrix.of fun i j => B (slow i) (slow j)) = 1

namespace MoriSlowVariables

/-- `[S3-17]` The slow-variable Gram matrix `G_{ij} = B (slow i) (slow j)`. -/
def gram {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => M.B (M.slow i) (M.slow j)

/-- `[S3-17]` Symmetry of the Gram matrix `Gᵀ = G`. -/
theorem gram_transpose {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) : M.gramᵀ = M.gram := by
  ext i j
  simp only [gram, Matrix.transpose_apply, Matrix.of_apply]
  exact M.B_symm.eq (M.slow j) (M.slow i)

/-- `[S3-17]` Symmetry of the inverse Gram matrix `(G⁻¹)ᵀ = G⁻¹`. -/
theorem gramInv_transpose {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) : M.gramInvᵀ = M.gramInv := by
  have hT3 : (M.gramInv * M.gram)ᵀ = (1 : Matrix (Fin k) (Fin k) ℝ)ᵀ :=
    congrArg Matrix.transpose M.inv_mul_gram
  rw [Matrix.transpose_mul, Matrix.transpose_one, M.gram_transpose] at hT3
  calc M.gramInvᵀ = 1 * M.gramInvᵀ := by rw [Matrix.one_mul]
    _ = (M.gramInv * M.gram) * M.gramInvᵀ := by
        rw [show M.gramInv * M.gram = 1 from M.inv_mul_gram]
    _ = M.gramInv * (M.gram * M.gramInvᵀ) := by rw [Matrix.mul_assoc]
    _ = M.gramInv * 1 := by rw [hT3]
    _ = M.gramInv := by rw [Matrix.mul_one]

/-- `[S3-17]` te Vrugt–Wittkowski (2020) §II.B eq. (16): Multi-variable Mori orthogonal
projector `P G = ∑ i j, (B G (slow i) * gramInv i j) • slow j`. -/
def projector {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) : V →ₗ[ℝ] V where
  toFun G := ∑ i : Fin k, ∑ j : Fin k, (M.B G (M.slow i) * M.gramInv i j) • M.slow j
  map_add' G₁ G₂ := by
    simp only [map_add, LinearMap.add_apply, add_mul, add_smul, Finset.sum_add_distrib]
  map_smul' r G := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      ← smul_smul, ← Finset.smul_sum]

/-- `[S3-17]` Reproducing property on slow variables: `P (slow m) = slow m`. -/
theorem projector_slow {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) (m : Fin k) :
    M.projector (M.slow m) = M.slow m := by
  dsimp [projector]
  have hsum : ∀ j : Fin k, (∑ i : Fin k, M.B (M.slow m) (M.slow i) * M.gramInv i j) =
      if m = j then 1 else 0 := by
    intro j
    have hmul := congrArg (fun X : Matrix (Fin k) (Fin k) ℝ => X m j) M.gram_mul_inv
    simpa [Matrix.mul_apply, Matrix.one_apply] using hmul
  calc (∑ i : Fin k, ∑ j : Fin k, (M.B (M.slow m) (M.slow i) * M.gramInv i j) • M.slow j)
      = ∑ j : Fin k, ∑ i : Fin k, (M.B (M.slow m) (M.slow i) * M.gramInv i j) • M.slow j :=
        Finset.sum_comm
    _ = ∑ j : Fin k, (∑ i : Fin k, M.B (M.slow m) (M.slow i) * M.gramInv i j) • M.slow j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ j : Fin k, (if m = j then (1 : ℝ) else 0) • M.slow j := by
        refine Finset.sum_congr rfl fun j _ => by rw [hsum j]
    _ = M.slow m := by
        simp

/-- `[S3-17]` Idempotence `P (P G) = P G` of the multi-variable Mori projector. -/
theorem projector_idempotent {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) (G : V) :
    M.projector (M.projector G) = M.projector G := by
  conv_lhs => arg 2; dsimp [projector]
  simp only [map_sum, map_smul, M.projector_slow]
  rfl

/-- `[S3-17]` `B`-self-adjointness `B (P G₁) G₂ = B G₁ (P G₂)` of the multi-variable Mori
projector. -/
theorem projector_selfAdjoint {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) (G₁ G₂ : V) :
    M.B (M.projector G₁) G₂ = M.B G₁ (M.projector G₂) := by
  dsimp [projector]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  calc (∑ i : Fin k, ∑ j : Fin k,
        (M.B G₁ (M.slow i) * M.gramInv i j) * M.B (M.slow j) G₂)
      = ∑ i : Fin k, ∑ j : Fin k,
          M.B G₁ (M.slow i) * (M.gramInv j i * M.B G₂ (M.slow j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hginv : M.gramInv j i = M.gramInv i j := by
          have h := congrArg (fun X : Matrix (Fin k) (Fin k) ℝ => X j i) M.gramInv_transpose
          simpa [Matrix.transpose_apply] using h.symm
        rw [hginv, M.B_symm.eq (M.slow j) G₂, mul_assoc]
    _ = ∑ j : Fin k, ∑ i : Fin k,
          M.B G₁ (M.slow i) * (M.gramInv j i * M.B G₂ (M.slow j)) := Finset.sum_comm
    _ = ∑ j : Fin k, ∑ i : Fin k,
          (M.B G₂ (M.slow j) * M.gramInv j i) * M.B G₁ (M.slow i) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (M.gramInv j i) (M.B G₂ (M.slow j)), mul_comm (M.B G₁ (M.slow i)), mul_assoc]

/-- `[S3-17]` Orthogonality `B (G - P G) (P H) = 0` between the orthogonal subspace `Q = I - P`
and the slow subspace `im P`. -/
theorem projector_compl_ortho {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) (G H : V) :
    M.B (G - M.projector G) (M.projector H) = 0 := by
  rw [map_sub, LinearMap.sub_apply,
    M.projector_selfAdjoint G (M.projector H),
    M.projector_idempotent H]
  exact sub_self _

/-- `[S3-17]` Pythagorean variance identity `B G G = B (P G) (P G) + B (G - P G) (G - P G)`
and Bessel contraction `B (P G) (P G) ≤ B G G`. -/
theorem projector_pythagorean_and_le {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (M : MoriSlowVariables V k) (G : V) :
    M.B G G = M.B (M.projector G) (M.projector G) +
      M.B (G - M.projector G) (G - M.projector G) ∧
    M.B (M.projector G) (M.projector G) ≤ M.B G G := by
  have hortho : M.B (G - M.projector G) (M.projector G) = 0 := M.projector_compl_ortho G G
  have hortho' : M.B (M.projector G) (G - M.projector G) = 0 := by
    rw [M.B_symm.eq]
    exact hortho
  have hdecomp : G = M.projector G + (G - M.projector G) := by abel
  have hpyth : M.B G G = M.B (M.projector G) (M.projector G) +
      M.B (G - M.projector G) (G - M.projector G) := by
    conv_lhs => rw [hdecomp]
    simp only [map_add, LinearMap.add_apply, hortho, hortho', add_zero, zero_add]
  refine ⟨hpyth, ?_⟩
  rw [hpyth]
  exact le_add_of_nonneg_right (M.B_nonneg (G - M.projector G))

end MoriSlowVariables

/-- `[S3-17]` Uniform 2-mode faithful diagonal BKM state `ρ = diag(1/2, 1/2)` for T17
constructive witnessing of `MoriSlowVariables`. -/
def twoModeBKMState : KuboMoriBogoliubov.FaithfulDensityState (Fin 2) where
  eigenvalues := fun _ => (1 / 2 : ℝ)
  p_pos _ := by norm_num
  p_sum := by
    rw [Fin.sum_univ_two]
    norm_num

/-- `[S3-17]` Constructive T17 witness for `MoriSlowVariables` on `Matrix (Fin 2) (Fin 2) ℝ`
equipped with `twoModeBKMState.bkmInnerProduct` and slow observable `slow := ![1]`
(since `⟨1, 1⟩_{BKM} = 1/2 + 1/2 = 1`, `gramInv = 1`). -/
def twoModeMoriSlowVariables : MoriSlowVariables (Matrix (Fin 2) (Fin 2) ℝ) 1 where
  B := bkmInnerProductBilinForm twoModeBKMState
  B_symm := ⟨twoModeBKMState.bkm_metric_symmetry⟩
  B_nonneg := twoModeBKMState.bkm_metric_pos_semidef
  slow := ![1]
  gramInv := 1
  gram_mul_inv := by
    ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.mul_one, Matrix.of_apply, Matrix.one_apply_eq]
    dsimp [bkmInnerProductBilinForm, KuboMoriBogoliubov.FaithfulDensityState.bkmInnerProduct,
      KuboMoriBogoliubov.FaithfulDensityState.bkmWeight, twoModeBKMState]
    simp [Fin.sum_univ_two]
    norm_num
  inv_mul_gram := by
    ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.one_mul, Matrix.of_apply, Matrix.one_apply_eq]
    dsimp [bkmInnerProductBilinForm, KuboMoriBogoliubov.FaithfulDensityState.bkmInnerProduct,
      KuboMoriBogoliubov.FaithfulDensityState.bkmWeight, twoModeBKMState]
    simp [Fin.sum_univ_two]
    norm_num

end InfoGeometry.Thermo.OnsagerCasimirKBMPrimary
