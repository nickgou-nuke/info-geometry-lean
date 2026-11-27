/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering
import InfoGeometry.Twistor.WittenSpinorHelicity
import InfoGeometry.Nuclear.NuclearChiralPRMBridge

/-! Finite parity bridge for diagonal and off-diagonal Weyl operators,
spatial parity (`γ₀`) vs chirality (`γ₅`) segregation, spinor-helicity embedding,
and nuclear intrinsic `K`-doublet Peirce splitting. -/

noncomputable section
namespace InfoGeometry.Bridge.PolarAxialChiralParityBridge

open Matrix
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Twistor.WittenSpinorHelicity
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Nuclear.ChiralPRM

abbrev PauliBlock := QuaternionicPauliDiracSoldering.PauliBlock
abbrev DiracSpinor := QuaternionicPauliDiracSoldering.DiracSpinor

def diracChirality : Module.End ℂ DiracSpinor where
  toFun ψ := (ψ.1, -ψ.2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro c x; ext <;> simp <;> ring

def chiralEvenOperator (L R : PauliBlock) : Module.End ℂ DiracSpinor where
  toFun ψ := (L *ᵥ ψ.1, R *ᵥ ψ.2)
  map_add' := by
    intro x y
    change (L *ᵥ (x.1 + y.1), R *ᵥ (x.2 + y.2)) =
      (L *ᵥ x.1 + L *ᵥ y.1, R *ᵥ x.2 + R *ᵥ y.2)
    exact Prod.ext (Matrix.mulVec_add L x.1 y.1)
      (Matrix.mulVec_add R x.2 y.2)
  map_smul' := by
    intro c x
    change (L *ᵥ (c • x.1), R *ᵥ (c • x.2)) =
      (c • (L *ᵥ x.1), c • (R *ᵥ x.2))
    exact Prod.ext (Matrix.mulVec_smul L c x.1)
      (Matrix.mulVec_smul R c x.2)

theorem diracChirality_sq :
    diracChirality.comp diracChirality =
      (LinearMap.id : Module.End ℂ DiracSpinor) := by
  apply LinearMap.ext
  intro ψ
  rcases ψ with ⟨ψL, ψR⟩
  simp [diracChirality]

theorem chiralEvenOperator_commutes_chirality (L R : PauliBlock) :
    diracChirality.comp (chiralEvenOperator L R) =
      (chiralEvenOperator L R).comp diracChirality := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext
  · rfl
  · change -(R *ᵥ ψR) = R *ᵥ (-ψR)
    rw [Matrix.mulVec_neg]

theorem chiralWeylOperator_anticommutes_chirality (A B : PauliBlock) :
    diracChirality.comp (chiralWeylOperator A B) =
      -((chiralWeylOperator A B).comp diracChirality) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext
  · change A *ᵥ ψR = -(A *ᵥ (-ψR))
    rw [Matrix.mulVec_neg]
    simp
  · rfl

theorem chiralWeylOperator_sq_eq_even (A B : PauliBlock) :
    (chiralWeylOperator A B).comp (chiralWeylOperator A B) =
      chiralEvenOperator (A * B) (B * A) := by
  apply LinearMap.ext
  intro ψ
  rw [LinearMap.comp_apply, chiralWeylOperator_sq_apply]
  rfl

def polarAxialChiralOperator (A B : PauliParavector) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator (A.pauliMatrix + B.pauliMatrix)
    (coSolderingMap A - coSolderingMap B)

theorem polarAxialChiralOperator_anticommutes_chirality
    (A B : PauliParavector) :
    diracChirality.comp (polarAxialChiralOperator A B) =
      -((polarAxialChiralOperator A B).comp diracChirality) := by
  exact chiralWeylOperator_anticommutes_chirality _ _

theorem polarAxialChiralOperator_sq_eq_even
    (A B : PauliParavector) :
    (polarAxialChiralOperator A B).comp (polarAxialChiralOperator A B) =
      chiralEvenOperator
        ((A.pauliMatrix + B.pauliMatrix) *
          (coSolderingMap A - coSolderingMap B))
        ((coSolderingMap A - coSolderingMap B) *
          (A.pauliMatrix + B.pauliMatrix)) := by
  exact chiralWeylOperator_sq_eq_even _ _

/-! ## 1. Dirac spatial parity (`γ₀`) vs chirality (`γ₅`) segregation -/

/-- Genuine Dirac spatial parity (`γ₀ : (ψL, ψR) ↦ (ψR, ψL)`). -/
def diracSpatialParity : Module.End ℂ DiracSpinor where
  toFun ψ := (ψ.2, ψ.1)
  map_add' := by intro x y; ext <;> rfl
  map_smul' := by intro c x; ext <;> rfl

theorem diracSpatialParity_eq_chiralWeylOperator :
    diracSpatialParity = chiralWeylOperator 1 1 := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [diracSpatialParity, chiralWeylOperator]

theorem diracSpatialParity_sq :
    diracSpatialParity.comp diracSpatialParity =
      (LinearMap.id : Module.End ℂ DiracSpinor) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  rfl

theorem diracSpatialParity_mul_self :
    diracSpatialParity * diracSpatialParity = 1 :=
  diracSpatialParity_sq

theorem diracChirality_mul_self :
    diracChirality * diracChirality = 1 :=
  diracChirality_sq

/-- Spatial parity `γ₀` and chirality `γ₅` anticommute: `γ₀ γ₅ = - γ₅ γ₀`. -/
theorem diracSpatialParity_anticommutes_diracChirality :
    diracSpatialParity * diracChirality = -(diracChirality * diracSpatialParity) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [diracSpatialParity, diracChirality]

theorem diracSpatialParity_diracChirality_anticomm_zero :
    diracSpatialParity * diracChirality + diracChirality * diracSpatialParity = 0 := by
  rw [diracSpatialParity_anticommutes_diracChirality]
  simp

/-- Spatial parity `γ₀` and chirality `γ₅` are strictly distinct involutions. -/
theorem diracSpatialParity_ne_diracChirality :
    diracSpatialParity ≠ diracChirality := by
  intro h
  have h0 := congrArg (fun T : Module.End ℂ DiracSpinor => (T (![1, 0], 0)).1 0) h
  simp [diracSpatialParity, diracChirality] at h0

theorem diracSpatialParity_not_commute_diracChirality :
    diracSpatialParity * diracChirality ≠ diracChirality * diracSpatialParity := by
  intro h
  have h0 := congrArg (fun T : Module.End ℂ DiracSpinor => (T (![1, 0], 0)).2 0) h
  simp [diracSpatialParity, diracChirality] at h0
  norm_num at h0

/-- Pseudoscalar grade `γ₀ γ₅` generated by the noncommutativity of `γ₀` and `γ₅`. -/
def diracPseudoscalar : Module.End ℂ DiracSpinor :=
  diracSpatialParity * diracChirality

theorem diracPseudoscalar_sq :
    diracPseudoscalar * diracPseudoscalar = -1 := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [diracPseudoscalar, diracSpatialParity, diracChirality]

theorem diracPseudoscalar_ne_zero :
    diracPseudoscalar ≠ 0 := by
  intro h
  have hsq := diracPseudoscalar_sq
  rw [h, mul_zero] at hsq
  have h0 := congrArg (fun T : Module.End ℂ DiracSpinor => (T (![1, 0], 0)).1 0) hsq
  simp at h0

theorem diracPseudoscalar_anticommutes_spatialParity_and_chirality :
    diracSpatialParity * diracPseudoscalar = -(diracPseudoscalar * diracSpatialParity) ∧
      diracChirality * diracPseudoscalar = -(diracPseudoscalar * diracChirality) := by
  constructor <;>
    (apply LinearMap.ext; rintro ⟨ψL, ψR⟩;
     apply Prod.ext <;> simp [diracPseudoscalar, diracSpatialParity, diracChirality])

/-! ## 2. Polar vector vs axial vector Dirac operators -/

/-- Polar spatial-vector Dirac operator `chiralWeylOperator V (-V)` (odd under `γ₀`). -/
def polarVectorDiracOp (V : PauliBlock) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator V (-V)

/-- Axial spatial-vector Dirac operator `chiralWeylOperator A A` (even under `γ₀`). -/
def axialVectorDiracOp (A : PauliBlock) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator A A

theorem axialVectorDiracOp_eq_chirality_mul_polarVectorDiracOp (A : PauliBlock) :
    axialVectorDiracOp A = diracChirality * polarVectorDiracOp A := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [axialVectorDiracOp, polarVectorDiracOp, diracChirality,
    chiralWeylOperator, Matrix.neg_mulVec]

/-- Spatial parity `γ₀` flips the sign of a polar spatial-vector operator:
`γ₀ * polar(V) * γ₀ = -polar(V)`. -/
theorem diracSpatialParity_conj_polarVectorDiracOp (V : PauliBlock) :
    diracSpatialParity * polarVectorDiracOp V * diracSpatialParity =
      -polarVectorDiracOp V := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [diracSpatialParity, polarVectorDiracOp, chiralWeylOperator,
    Matrix.neg_mulVec]

/-- Spatial parity `γ₀` preserves an axial spatial-vector operator:
`γ₀ * axial(A) * γ₀ = +axial(A)`. -/
theorem diracSpatialParity_conj_axialVectorDiracOp (A : PauliBlock) :
    diracSpatialParity * axialVectorDiracOp A * diracSpatialParity =
      axialVectorDiracOp A := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [diracSpatialParity, axialVectorDiracOp, chiralWeylOperator]

/-- Both polar and axial vector Dirac operators anticommute with `γ₅` (`diracChirality`). -/
theorem polarVectorDiracOp_anticommutes_chirality (V : PauliBlock) :
    diracChirality * polarVectorDiracOp V + polarVectorDiracOp V * diracChirality = 0 := by
  have h := chiralWeylOperator_anticommutes_chirality V (-V)
  change diracChirality * polarVectorDiracOp V = -(polarVectorDiracOp V * diracChirality) at h
  rw [h, neg_add_cancel]

theorem axialVectorDiracOp_anticommutes_chirality (A : PauliBlock) :
    diracChirality * axialVectorDiracOp A + axialVectorDiracOp A * diracChirality = 0 := by
  have h := chiralWeylOperator_anticommutes_chirality A A
  change diracChirality * axialVectorDiracOp A = -(axialVectorDiracOp A * diracChirality) at h
  rw [h, neg_add_cancel]

/-- Spatial parity reflection on a 4-momentum/current paravector: `(E, p) ↦ (E, -p)`. -/
def spatialParityParavector (P : PauliParavector) : PauliParavector :=
  ⟨P.energy, -P.px, -P.py, -P.pz⟩

theorem spatialParityParavector_pauliMatrix (P : PauliParavector) :
    (spatialParityParavector P).pauliMatrix = coSolderingMap P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spatialParityParavector, PauliParavector.pauliMatrix, coSolderingMap] <;>
    ring

theorem spatialParityParavector_coSolderingMap (P : PauliParavector) :
    coSolderingMap (spatialParityParavector P) = P.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spatialParityParavector, PauliParavector.pauliMatrix, coSolderingMap] <;>
    ring

/-- Full 4-vector polar Dirac operator `V_μ γ^μ`. -/
def paravectorDiracPolarOp (V : PauliParavector) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator V.pauliMatrix (coSolderingMap V)

/-- Full 4-vector axial Dirac operator `γ₅ (A_μ γ^μ) = -A_μ γ^μ γ₅`. -/
def paravectorDiracAxialOp (A : PauliParavector) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator A.pauliMatrix (-coSolderingMap A)

theorem paravectorDiracPolarOp_spatial_eq (V : PauliParavector) (hE : V.energy = 0) :
    paravectorDiracPolarOp V = polarVectorDiracOp V.pauliMatrix := by
  have hco : coSolderingMap V = -V.pauliMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coSolderingMap, PauliParavector.pauliMatrix, hE] <;> ring
  simp [paravectorDiracPolarOp, polarVectorDiracOp, hco]

theorem paravectorDiracAxialOp_spatial_eq (A : PauliParavector) (hE : A.energy = 0) :
    paravectorDiracAxialOp A = axialVectorDiracOp A.pauliMatrix := by
  have hco : -coSolderingMap A = A.pauliMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coSolderingMap, PauliParavector.pauliMatrix, hE] <;> ring
  simp [paravectorDiracAxialOp, axialVectorDiracOp, hco]

theorem diracSpatialParity_conj_paravectorDiracPolarOp (V : PauliParavector) :
    diracSpatialParity * paravectorDiracPolarOp V * diracSpatialParity =
      paravectorDiracPolarOp (spatialParityParavector V) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;>
    simp [diracSpatialParity, paravectorDiracPolarOp, chiralWeylOperator,
      spatialParityParavector_pauliMatrix, spatialParityParavector_coSolderingMap]

theorem diracSpatialParity_conj_paravectorDiracAxialOp (A : PauliParavector) :
    diracSpatialParity * paravectorDiracAxialOp A * diracSpatialParity =
      -paravectorDiracAxialOp (spatialParityParavector A) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;>
    simp [diracSpatialParity, paravectorDiracAxialOp, chiralWeylOperator,
      spatialParityParavector_pauliMatrix, spatialParityParavector_coSolderingMap,
      Matrix.neg_mulVec]

/-- The existing `polarAxialChiralOperator A B` splits cleanly into polar part `A`
plus axial part `B`. -/
theorem polarAxialChiralOperator_eq_polar_add_axial (A B : PauliParavector) :
    polarAxialChiralOperator A B =
      paravectorDiracPolarOp A + paravectorDiracAxialOp B := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext
  · change (A.pauliMatrix + B.pauliMatrix) *ᵥ ψR =
      A.pauliMatrix *ᵥ ψR + B.pauliMatrix *ᵥ ψR
    exact Matrix.add_mulVec A.pauliMatrix B.pauliMatrix ψR
  · change (coSolderingMap A - coSolderingMap B) *ᵥ ψL =
      coSolderingMap A *ᵥ ψL + (-coSolderingMap B) *ᵥ ψL
    rw [Matrix.sub_mulVec, Matrix.neg_mulVec, sub_eq_add_neg]

theorem polarAxialChiralOperator_spatial_parity_conjugation (A B : PauliParavector) :
    diracSpatialParity * polarAxialChiralOperator A B * diracSpatialParity =
      paravectorDiracPolarOp (spatialParityParavector A) -
        paravectorDiracAxialOp (spatialParityParavector B) := by
  rw [polarAxialChiralOperator_eq_polar_add_axial, mul_add, add_mul,
    diracSpatialParity_conj_paravectorDiracPolarOp,
    diracSpatialParity_conj_paravectorDiracAxialOp, sub_eq_add_neg]

theorem polarAxialChiralOperator_purely_spatial_parity (A B : PauliParavector)
    (hA : A.energy = 0) (hB : B.energy = 0) :
    diracSpatialParity * polarAxialChiralOperator A B * diracSpatialParity =
      -polarVectorDiracOp A.pauliMatrix + axialVectorDiracOp B.pauliMatrix := by
  rw [polarAxialChiralOperator_eq_polar_add_axial,
    paravectorDiracPolarOp_spatial_eq A hA,
    paravectorDiracAxialOp_spatial_eq B hB,
    mul_add, add_mul,
    diracSpatialParity_conj_polarVectorDiracOp,
    diracSpatialParity_conj_axialVectorDiracOp]

/-! ## 3. Bridge `WittenSpinorHelicity` to `DiracSpinor` -/

/-- Embed a Weyl spinor-helicity pair `(λ, λ̃) : Spinor2 × Spinor2` into `DiracSpinor`. -/
def weylPairToDirac (lam lamTilde : Spinor2) : DiracSpinor :=
  (lam, lamTilde)

def leftHelicityEmbed (lam : Spinor2) : DiracSpinor :=
  (lam, 0)

def rightHelicityEmbed (lamTilde : Spinor2) : DiracSpinor :=
  (0, lamTilde)

/-- Left-chiral projector `P_+ = (1 + γ₅)/2`. -/
def diracChiralProjPlus : Module.End ℂ DiracSpinor :=
  (1 / 2 : ℂ) • (1 + diracChirality)

/-- Right-chiral projector `P_- = (1 - γ₅)/2`. -/
def diracChiralProjMinus : Module.End ℂ DiracSpinor :=
  (1 / 2 : ℂ) • (1 - diracChirality)

theorem diracChiralProj_algebra :
    diracChiralProjPlus * diracChiralProjPlus = diracChiralProjPlus ∧
    diracChiralProjMinus * diracChiralProjMinus = diracChiralProjMinus ∧
    diracChiralProjPlus * diracChiralProjMinus = 0 ∧
    diracChiralProjPlus + diracChiralProjMinus = 1 ∧
    diracChiralProjPlus - diracChiralProjMinus = diracChirality := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply LinearMap.ext; rintro ⟨ψL, ψR⟩; apply Prod.ext <;>
      ext i <;> simp [diracChiralProjPlus, diracChiralProjMinus, diracChirality] <;> ring)

theorem diracChiralProjPlus_weylPair (lam lamTilde : Spinor2) :
    diracChiralProjPlus (weylPairToDirac lam lamTilde) = leftHelicityEmbed lam := by
  apply Prod.ext <;> ext i <;>
    (simp [diracChiralProjPlus, weylPairToDirac, leftHelicityEmbed, diracChirality]; try ring)

theorem diracChiralProjMinus_weylPair (lam lamTilde : Spinor2) :
    diracChiralProjMinus (weylPairToDirac lam lamTilde) = rightHelicityEmbed lamTilde := by
  apply Prod.ext <;> ext i <;>
    (simp [diracChiralProjMinus, weylPairToDirac, rightHelicityEmbed, diracChirality]; try ring)

theorem diracChirality_leftHelicityEmbed (lam : Spinor2) :
    diracChirality (leftHelicityEmbed lam) = leftHelicityEmbed lam := by
  apply Prod.ext <;> simp [diracChirality, leftHelicityEmbed]

theorem diracChirality_rightHelicityEmbed (lamTilde : Spinor2) :
    diracChirality (rightHelicityEmbed lamTilde) = -rightHelicityEmbed lamTilde := by
  apply Prod.ext <;> simp [diracChirality, rightHelicityEmbed]

theorem diracSpatialParity_swaps_helicityEmbeddings (lam lamTilde : Spinor2) :
    diracSpatialParity (leftHelicityEmbed lam) = rightHelicityEmbed lam ∧
      diracSpatialParity (rightHelicityEmbed lamTilde) = leftHelicityEmbed lamTilde := by
  constructor <;> apply Prod.ext <;> simp [diracSpatialParity, leftHelicityEmbed, rightHelicityEmbed]

/-- Chiral little-group operator `diag(c, c⁻¹) = c P_+ + c⁻¹ P_-` on `DiracSpinor`. -/
def chiralLittleGroupOp (c : ℂ) : Module.End ℂ DiracSpinor :=
  chiralEvenOperator (c • (1 : PauliBlock)) (c⁻¹ • (1 : PauliBlock))

theorem chiralLittleGroupOp_apply (c : ℂ) (lam lamTilde : Spinor2) :
    chiralLittleGroupOp c (weylPairToDirac lam lamTilde) =
      weylPairToDirac (c • lam) (c⁻¹ • lamTilde) := by
  apply Prod.ext <;>
    simp [chiralLittleGroupOp, chiralEvenOperator, weylPairToDirac, Matrix.smul_mulVec]

theorem chiralLittleGroupOp_eq_proj_combo (c : ℂ) :
    chiralLittleGroupOp c = c • diracChiralProjPlus + c⁻¹ • diracChiralProjMinus := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> ext i <;>
    simp [chiralLittleGroupOp, chiralEvenOperator, diracChiralProjPlus,
      diracChiralProjMinus, diracChirality, Matrix.smul_mulVec] <;> ring

theorem chiralLittleGroupOp_preserves_spinorOuter (c : ℂ) (hc : c ≠ 0)
    (lam lamTilde : Spinor2) :
    let ψ' := chiralLittleGroupOp c (weylPairToDirac lam lamTilde)
    spinorOuter ψ'.1 ψ'.2 = spinorOuter lam lamTilde := by
  dsimp only
  rw [chiralLittleGroupOp_apply]
  exact spinorOuter_littleGroup c hc lam lamTilde

theorem chiralLittleGroupOp_u1_preserves_real_slice (c : ℂ) (hc : star c * c = 1)
    (r : ℝ) (lam : Spinor2) :
    let ψ' := chiralLittleGroupOp c (weylPairToDirac lam ((r : ℂ) • star lam))
    ψ'.2 = (r : ℂ) • star ψ'.1 := by
  dsimp only
  rw [chiralLittleGroupOp_apply]
  exact u1_littleGroup_preserves_reality c hc r lam

/-! ## 4. Bridge `NuclearChiralPRMBridge` (`K`-doublet Peirce basis) to `DiracSpinor` / `M2C` -/

/-- Lift a real `2 × 2` nuclear doublet matrix to `PauliBlock = M2C`. -/
def liftRealMat2 (M : M2R) : PauliBlock :=
  M.map Complex.ofReal

theorem liftRealMat2_mul (A B : M2R) :
    liftRealMat2 (A * B) = liftRealMat2 A * liftRealMat2 B := by
  ext i j
  simp [liftRealMat2, Matrix.mul_apply]

theorem liftRealMat2_one :
    liftRealMat2 (1 : M2R) = (1 : PauliBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftRealMat2]

/-- Orthogonal Hadamard/Cayley rotation `H = (1/√2) [[1, 1], [1, -1]]` on `PauliBlock`. -/
def hadamard2 : PauliBlock :=
  ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • !![(1 : ℂ), 1; 1, -1]

theorem hadamard2_sq : hadamard2 * hadamard2 = 1 := by
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [hadamard2, Matrix.mul_apply, Fin.sum_univ_two];
     try (field_simp [hne]; rw [hsq2]; ring))

theorem hadamard2_conjugates_chiralFlip_to_chirality :
    hadamard2 * liftRealMat2 chiralFlip * hadamard2 = chirality := by
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [hadamard2, liftRealMat2, chiralFlip, chirality, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two];
     try (field_simp [hne]; rw [hsq2]; ring))

theorem hadamard2_conjugates_peircePlus_to_chiralPlus :
    hadamard2 * liftRealMat2 peircePlus * hadamard2 = chiralPlus := by
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [hadamard2, liftRealMat2, peircePlus, chiralPlus, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two];
     try (field_simp [hne]; rw [hsq2]; ring))

theorem hadamard2_conjugates_peirceMinus_to_chiralMinus :
    hadamard2 * liftRealMat2 peirceMinus * hadamard2 = chiralMinus := by
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [hadamard2, liftRealMat2, peirceMinus, chiralMinus, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two];
     try (field_simp [hne]; rw [hsq2]; ring))

theorem peircePlus_sub_peirceMinus_eq_chiralFlip :
    peircePlus - peirceMinus = chiralFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peircePlus, peirceMinus, chiralFlip] <;> norm_num

theorem hadamard2_diagonalizes_prmMatrix (state : ChiralDoubletState) :
    hadamard2 * liftRealMat2 (prmMatrix state) * hadamard2 =
      !![(energyPlus state : ℂ), 0; 0, (energyMinus state : ℂ)] := by
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [hadamard2, liftRealMat2, prmMatrix, energyPlus, energyMinus,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two];
     try (field_simp [hne]; rw [hsq2]; ring))

/-- Lift a `2 × 2` real nuclear doublet operator `M : M2R` to `Module.End ℂ DiracSpinor`
acting on the `(ψL, ψR)` doublet blocks. -/
def doubletDiracLift (M : M2R) : Module.End ℂ DiracSpinor where
  toFun ψ :=
    ((M 0 0 : ℂ) • ψ.1 + (M 0 1 : ℂ) • ψ.2,
     (M 1 0 : ℂ) • ψ.1 + (M 1 1 : ℂ) • ψ.2)
  map_add' x y := by
    apply Prod.ext <;> ext i <;> simp <;> ring
  map_smul' c x := by
    apply Prod.ext <;> ext i <;> simp <;> ring

theorem doubletDiracLift_mul (A B : M2R) :
    doubletDiracLift (A * B) = doubletDiracLift A * doubletDiracLift B := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> ext i <;>
    simp [doubletDiracLift, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem doubletDiracLift_chiralFlip :
    doubletDiracLift chiralFlip = diracSpatialParity := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> ext i <;> simp [doubletDiracLift, chiralFlip, diracSpatialParity]

theorem doubletDiracLift_peircePlus :
    doubletDiracLift peircePlus = (1 / 2 : ℂ) • (1 + diracSpatialParity) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> ext i <;>
    (simp [doubletDiracLift, peircePlus, diracSpatialParity]; try ring)

theorem doubletDiracLift_peirceMinus :
    doubletDiracLift peirceMinus = (1 / 2 : ℂ) • (1 - diracSpatialParity) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> ext i <;>
    (simp [doubletDiracLift, peirceMinus, diracSpatialParity]; try ring)

theorem doubletDiracLift_peirce_diff :
    doubletDiracLift (peircePlus - peirceMinus) = diracSpatialParity := by
  rw [peircePlus_sub_peirceMinus_eq_chiralFlip, doubletDiracLift_chiralFlip]

/-- Embed a `ℂ²` nuclear doublet state `v : Vec2C` into `DiracSpinor` along a spinor fiber `u`. -/
def embedDoublet (u : Spinor2) (v : InfoGeometry.Algebra.FiniteSpin.Vec2C) : DiracSpinor :=
  (v 0 • u, v 1 • u)

theorem doubletDiracLift_intertwines_embedDoublet (M : M2R) (u : Spinor2)
    (v : InfoGeometry.Algebra.FiniteSpin.Vec2C) :
    doubletDiracLift M (embedDoublet u v) = embedDoublet u ((liftRealMat2 M) *ᵥ v) := by
  apply Prod.ext <;> ext i <;>
    (simp [doubletDiracLift, embedDoublet, liftRealMat2, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]; ring)

theorem chiralFlip_intertwines_diracSpatialParity (u : Spinor2)
    (v : InfoGeometry.Algebra.FiniteSpin.Vec2C) :
    diracSpatialParity (embedDoublet u v) =
      embedDoublet u ((liftRealMat2 chiralFlip) *ᵥ v) := by
  rw [← doubletDiracLift_chiralFlip]
  exact doubletDiracLift_intertwines_embedDoublet chiralFlip u v

/-- Hadamard/Cayley basis rotation on `DiracSpinor`:
`(ψL, ψR) ↦ (1/√2)(ψL + ψR, ψL - ψR)`. -/
def hadamardDirac : DiracSpinor ≃ₗ[ℂ] DiracSpinor where
  toFun ψ :=
    (((1 : ℂ) / (Real.sqrt 2 : ℂ)) • (ψ.1 + ψ.2),
     ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • (ψ.1 - ψ.2))
  invFun φ :=
    (((1 : ℂ) / (Real.sqrt 2 : ℂ)) • (φ.1 + φ.2),
     ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • (φ.1 - φ.2))
  left_inv ψ := by
    have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      rw [sq]
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    apply Prod.ext <;> ext i <;>
      (simp; field_simp [hne]; rw [hsq2]; ring)
  right_inv φ := by
    have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      rw [sq]
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    apply Prod.ext <;> ext i <;>
      (simp; field_simp [hne]; rw [hsq2]; ring)
  map_add' x y := by
    apply Prod.ext <;> ext i <;> simp <;> ring
  map_smul' c x := by
    apply Prod.ext <;> ext i <;> simp <;> ring

theorem hadamardDirac_sq :
    hadamardDirac.toLinearMap * hadamardDirac.toLinearMap = 1 := by
  apply LinearMap.ext
  intro ψ
  exact hadamardDirac.left_inv ψ

/-- Under the Hadamard/Cayley rotation, `diracSpatialParity` (`γ₀`) transforms into
`diracChirality` (`γ₅`). -/
theorem hadamardDirac_conjugates_spatialParity_to_chirality :
    hadamardDirac.toLinearMap * diracSpatialParity * hadamardDirac.toLinearMap =
      diracChirality := by
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext <;> ext i <;>
    (simp [hadamardDirac, diracSpatialParity, diracChirality];
     field_simp [hne]; rw [hsq2]; ring)

/-- Under the Hadamard/Cayley rotation, the nuclear Peirce splitting operator
`peircePlus - peirceMinus = chiralFlip` maps to the axial helicity operator `diracChirality`. -/
theorem hadamardDirac_conjugates_peirce_diff_to_chirality :
    hadamardDirac.toLinearMap * doubletDiracLift (peircePlus - peirceMinus) *
      hadamardDirac.toLinearMap = diracChirality := by
  rw [doubletDiracLift_peirce_diff]
  exact hadamardDirac_conjugates_spatialParity_to_chirality

theorem hadamardDirac_conjugates_peircePlus_to_chiralProjPlus :
    hadamardDirac.toLinearMap * doubletDiracLift peircePlus *
      hadamardDirac.toLinearMap = diracChiralProjPlus := by
  rw [doubletDiracLift_peircePlus]
  calc
    hadamardDirac.toLinearMap * ((1 / 2 : ℂ) • (1 + diracSpatialParity)) *
        hadamardDirac.toLinearMap
        = (1 / 2 : ℂ) • (hadamardDirac.toLinearMap * hadamardDirac.toLinearMap +
            hadamardDirac.toLinearMap * diracSpatialParity * hadamardDirac.toLinearMap) := by
          simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
    _ = diracChiralProjPlus := by
          rw [hadamardDirac_sq, hadamardDirac_conjugates_spatialParity_to_chirality]
          rfl

theorem hadamardDirac_conjugates_peirceMinus_to_chiralProjMinus :
    hadamardDirac.toLinearMap * doubletDiracLift peirceMinus *
      hadamardDirac.toLinearMap = diracChiralProjMinus := by
  rw [doubletDiracLift_peirceMinus]
  calc
    hadamardDirac.toLinearMap * ((1 / 2 : ℂ) • (1 - diracSpatialParity)) *
        hadamardDirac.toLinearMap
        = (1 / 2 : ℂ) • (hadamardDirac.toLinearMap * hadamardDirac.toLinearMap -
            hadamardDirac.toLinearMap * diracSpatialParity * hadamardDirac.toLinearMap) := by
          simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
    _ = diracChiralProjMinus := by
          rw [hadamardDirac_sq, hadamardDirac_conjugates_spatialParity_to_chirality]
          rfl

theorem hadamardDirac_diagonalizes_prmMatrix (state : ChiralDoubletState) :
    hadamardDirac.toLinearMap * doubletDiracLift (prmMatrix state) *
      hadamardDirac.toLinearMap =
      (energyPlus state : ℂ) • diracChiralProjPlus +
        (energyMinus state : ℂ) • diracChiralProjMinus := by
  have hprm : doubletDiracLift (prmMatrix state) =
      (energyPlus state : ℂ) • doubletDiracLift peircePlus +
        (energyMinus state : ℂ) • doubletDiracLift peirceMinus := by
    apply LinearMap.ext
    rintro ⟨ψL, ψR⟩
    apply Prod.ext <;> ext i <;>
      simp [doubletDiracLift, prmMatrix, energyPlus, energyMinus, peircePlus, peirceMinus] <;>
      ring
  rw [hprm]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    hadamardDirac_conjugates_peircePlus_to_chiralProjPlus,
    hadamardDirac_conjugates_peirceMinus_to_chiralProjMinus]

/-- R2 parity segregation summary: spatial parity (`γ₀`) and chirality (`γ₅`) are distinct
anticommuting involutions; nuclear `K`-doublet exchange `chiralFlip` lifts to `γ₀` in the
Weyl basis and rotates to `γ₅` (`σ₃`) only under the Hadamard/Cayley basis transformation. -/
theorem r2_parity_segregation_summary :
    diracSpatialParity ≠ diracChirality ∧
    diracSpatialParity * diracChirality + diracChirality * diracSpatialParity = 0 ∧
    doubletDiracLift chiralFlip = diracSpatialParity ∧
    hadamardDirac.toLinearMap * doubletDiracLift (peircePlus - peirceMinus) *
      hadamardDirac.toLinearMap = diracChirality ∧
    hadamard2 * liftRealMat2 chiralFlip * hadamard2 = chirality :=
  ⟨diracSpatialParity_ne_diracChirality,
   diracSpatialParity_diracChirality_anticomm_zero,
   doubletDiracLift_chiralFlip,
   hadamardDirac_conjugates_peirce_diff_to_chirality,
   hadamard2_conjugates_chiralFlip_to_chirality⟩

end InfoGeometry.Bridge.PolarAxialChiralParityBridge
