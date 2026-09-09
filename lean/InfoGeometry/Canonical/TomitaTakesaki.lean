import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.Grading
import InfoGeometry.Clifford.Lift
import InfoGeometry.Clifford.Relations
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.SplitQ11Equivariance
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Clifford.Tower
import InfoGeometry.Volume.ConnesCocycle
import Mathlib.Analysis.Normed.Algebra.Exponential

open scoped InnerProductSpace

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.TomitaTakesaki

open InfoGeometry.Clifford
open InfoGeometry.Krein

/-!
# Tomita-Takesaki Modular Atom (Split `Cl(1,1)`)

This module packages the modular pair (`J`, `ε`) on doubled real space and
connects it to the exact split Clifford algebra used in routing:
`SplitCliffordAlg = CliffordAlgebra splitQ11`.

This is an atom-level split-`Cl(1,1)` modular layer, not a full standard-form
Tomita-Takesaki development with `Δ`, cyclic/separating vectors, or a von
Neumann algebra action.
-/

section CliffordAtom

/-- The split Clifford algebra used by routing modules (`Cl(1,1)`). -/
noncomputable abbrev RoutingSplitCliffordAlg := CliffordAlgebra splitQ11

/-- Clifford generator corresponding to the modular conjugation direction. -/
noncomputable def cptJ : RoutingSplitCliffordAlg :=
  CliffordAlgebra.ι splitQ11 (1, 0)

/-- Clifford generator corresponding to `Jε` direction (complex structure axis). -/
noncomputable def cptJeps : RoutingSplitCliffordAlg :=
  CliffordAlgebra.ι splitQ11 (0, 1)

/-- Pseudoscalar `ε = J * (Jε)` in this sign convention. -/
noncomputable def cptEps : RoutingSplitCliffordAlg :=
  cptJ * cptJeps

/-- The four CPT atoms `{1, J, ε, Jε}` in split Clifford form. -/
def cptAtomSet : Set RoutingSplitCliffordAlg :=
  {1, cptJ, cptEps, cptJeps}

@[simp] lemma cptJ_sq :
    cptJ * cptJ = algebraMap ℝ RoutingSplitCliffordAlg 1 := by
  simp [cptJ, splitQ11_apply]

@[simp] lemma cptJeps_sq :
    cptJeps * cptJeps = algebraMap ℝ RoutingSplitCliffordAlg (-1) := by
  simp [cptJeps, splitQ11_apply]

/-- Lemma `cptJ_cptJeps_anticommute`. -/
lemma cptJ_cptJeps_anticommute :
    cptJ * cptJeps = -(cptJeps * cptJ) := by
  have hpolar : QuadraticMap.polar splitQ11 ((1 : ℝ), 0) ((0 : ℝ), 1) = 0 := by
    simp [QuadraticMap.polar, splitQ11_apply]
  rw [cptJ, cptJeps,
      CliffordAlgebra.ι_mul_ι_comm (Q := splitQ11) (a := ((1 : ℝ), 0)) (b := ((0 : ℝ), 1)),
      hpolar]
  simp

/-- Lemma `iota_mem_adjoin_cptAtomSet`. -/
lemma iota_mem_adjoin_cptAtomSet (v : ℝ × ℝ) :
    CliffordAlgebra.ι splitQ11 v ∈ Algebra.adjoin ℝ cptAtomSet := by
  have hJ : cptJ ∈ Algebra.adjoin ℝ cptAtomSet := by
    exact Algebra.subset_adjoin (by simp [cptAtomSet, cptJ])
  have hJeps : cptJeps ∈ Algebra.adjoin ℝ cptAtomSet := by
    exact Algebra.subset_adjoin (by simp [cptAtomSet, cptJeps])
  rcases v with ⟨a, b⟩
  have hdecomp :
      CliffordAlgebra.ι splitQ11 (a, b) = a • cptJ + b • cptJeps := by
    have hpair :
        ((a, b) : ℝ × ℝ)
          = a • (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)
            + b • (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) := by
      ext <;> simp
    calc
      CliffordAlgebra.ι splitQ11 (a, b)
          = CliffordAlgebra.ι splitQ11
              (a • (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)
                + b • (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)) := by
                rw [hpair]
      _ = a • CliffordAlgebra.ι splitQ11 (1, 0) + b • CliffordAlgebra.ι splitQ11 (0, 1) := by
            rw [(CliffordAlgebra.ι splitQ11).map_add,
                (CliffordAlgebra.ι splitQ11).map_smul,
                (CliffordAlgebra.ι splitQ11).map_smul]
      _ = a • cptJ + b • cptJeps := by simp [cptJ, cptJeps]
  have hsum : a • cptJ + b • cptJeps ∈ Algebra.adjoin ℝ cptAtomSet :=
    (Algebra.adjoin ℝ cptAtomSet).add_mem
      ((Algebra.adjoin ℝ cptAtomSet).smul_mem hJ a)
      ((Algebra.adjoin ℝ cptAtomSet).smul_mem hJeps b)
  simpa [hdecomp] using hsum

/-- Lemma `iota_range_subset_adjoin_cptAtomSet`. -/
lemma iota_range_subset_adjoin_cptAtomSet :
    Set.range (CliffordAlgebra.ι splitQ11) ⊆ Algebra.adjoin ℝ cptAtomSet := by
  intro x hx
  rcases hx with ⟨v, rfl⟩
  exact iota_mem_adjoin_cptAtomSet v

/--
Generator theorem: the CPT atom set `{1, J, ε, Jε}` generates the full split
Clifford algebra used in routing.
-/
theorem cptAtoms_generate_splitCliffordAlg :
    Algebra.adjoin ℝ cptAtomSet = ⊤ := by
  have hle :
      Algebra.adjoin ℝ (Set.range (CliffordAlgebra.ι splitQ11))
        ≤ Algebra.adjoin ℝ cptAtomSet := by
    refine Algebra.adjoin_le ?_
    intro x hx
    exact iota_range_subset_adjoin_cptAtomSet hx
  have htop :
      Algebra.adjoin ℝ (Set.range (CliffordAlgebra.ι splitQ11)) = ⊤ :=
    CliffordAlgebra.adjoin_range_ι (R := ℝ) (Q := splitQ11)
  apply top_unique
  simpa [htop] using hle

end CliffordAtom

section ModularRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Conjugation by an involution (`J² = 1`) as a ring endomorphism on doubled-space
endomorphisms.
-/
private noncomputable def involutiveConjugationRingHom
    (J : EndH)
    (hJ2 : J * J = (1 : EndH)) :
    EndH →+* EndH where
  toFun A := J * A * J
  map_zero' := by simp
  map_add' A B := by simp [mul_add, add_mul, mul_assoc]
  map_one' := by
    calc
      J * (1 : EndH) * J = J * J := by simp
      _ = (1 : EndH) := hJ2
  map_mul' A B := by
    calc
      J * (A * B) * J = J * A * B * J := by simp [mul_assoc]
      _ = J * A * (J * J) * B * J := by rw [hJ2]; simp [mul_assoc]
      _ = (J * A * J) * (J * B * J) := by simp [mul_assoc]

/--
Involutive conjugation transports exponentials:
`J exp(X) J = exp(J X J)` when `J² = 1`.
-/
private theorem involutiveConjugation_exp
    (J X : EndH)
    (hJ2 : J * J = (1 : EndH)) :
    J * NormedSpace.exp X * J = NormedSpace.exp (J * X * J) := by
  let φ : EndH →+* EndH := involutiveConjugationRingHom (E := E) J hJ2
  have hφcont : Continuous φ := by
    simpa [φ, involutiveConjugationRingHom] using
      ((continuous_const.mul continuous_id).mul continuous_const)
  simpa [φ] using (NormedSpace.map_exp φ hφcont X)

/--
Modular conjugation `J` (real-linear model of antilinear conjugation on complex space).
-/
noncomputable abbrev modularConjugationJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j (E := E)

@[simp] lemma modularConjugationJ_eq_modular_j :
    modularConjugationJ (E := E) = modular_j (E := E) := rfl

/-- Modular sign involution `ε = sgn(K)`. -/
noncomputable abbrev modularSignEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectral_epsilon (E := E)

@[simp] lemma modularSignEpsilon_eq_spectral_epsilon :
    modularSignEpsilon (E := E) = spectral_epsilon (E := E) := rfl

/-- Composite `Jε`, the real Hestenes rotation axis on doubled space. -/
noncomputable abbrev clockAxis : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))

/-- Canonical split identity: `clockAxis = J ∘ ε`. -/
lemma clockAxis_eq_modular_j_comp_spectral_epsilon :
    clockAxis (E := E)
      = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  rfl

/-- Canonical phase-axis name used on transport lanes. -/
noncomputable abbrev phaseAxisK : DoubledSpace E →L[ℝ] DoubledSpace E :=
  clockAxis (E := E)

lemma phaseAxisK_eq_clockAxis :
    phaseAxisK (E := E) = clockAxis (E := E) := rfl

/-- Legacy alias kept for API compatibility. -/
noncomputable abbrev modularComplexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  clockAxis (E := E)

lemma modularComplexI_eq_clockAxis :
    modularComplexI (E := E) = clockAxis (E := E) := rfl

@[simp] lemma modularComplexI_eq_complex_i :
    modularComplexI (E := E) = complex_i (E := E) := by
  ext u <;> simp [modularComplexI, clockAxis, modularConjugationJ, modularSignEpsilon,
    complex_i, modular_j, spectral_epsilon]

@[simp] lemma modularComplexI_apply_eq_complex_i (u : DoubledSpace E) :
    modularComplexI (E := E) u = complex_i (E := E) u := by
  simpa using congrArg (fun F : DoubledSpace E →L[ℝ] DoubledSpace E => F u)
    (modularComplexI_eq_complex_i (E := E))

lemma clockAxis_eq_complex_i :
    clockAxis (E := E) = complex_i (E := E) := by
  simpa [modularComplexI_eq_clockAxis] using
    (modularComplexI_eq_complex_i (E := E))

/--
Legacy/Clifford compatibility: the modular complex axis `Jε` coincides with the
dilation generator extracted from `[J, ε]`.
-/
lemma modularComplexI_eq_dilationOperator :
    modularComplexI (E := E) = dilationOperator (E := E) := by
  rw [modularComplexI]
  exact (dilationOperator_eq_complex_i (E := E)).symm

lemma clockAxis_eq_dilationOperator :
    clockAxis (E := E) = dilationOperator (E := E) := by
  simpa [modularComplexI_eq_clockAxis] using
    (modularComplexI_eq_dilationOperator (E := E))

@[simp] lemma modularConjugationJ_sq :
    (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  modular_j_involution (E := E)

@[simp] lemma modularSignEpsilon_sq :
    (modularSignEpsilon (E := E)).comp (modularSignEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  spectral_epsilon_involution (E := E)

/-- Lemma `modularConjugationJ_anticommutes_modularSign`. -/
lemma modularConjugationJ_anticommutes_modularSign :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      = -((modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))) :=
  modular_j_spectral_epsilon_anticommute (E := E)

@[simp] lemma clockAxis_sq :
    (clockAxis (E := E)).comp (clockAxis (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [clockAxis, modularConjugationJ, modularSignEpsilon,
    InvolutiveSelfDualCarrier.K, doubledCarrier] using
      (InvolutiveSelfDualCarrier.K_sq (X := doubledCarrier (E := E)))

@[simp] lemma modularComplexI_sq :
    (modularComplexI (E := E)).comp (modularComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [modularComplexI] using (clockAxis_sq (E := E))

/-- `J` anticommutes with the internal phase axis `Jε`. -/
lemma modularConjugationJ_anticommutes_modularComplexI :
    (modularConjugationJ (E := E)).comp (modularComplexI (E := E))
      = -((modularComplexI (E := E)).comp (modularConjugationJ (E := E))) := by
  simpa [modularConjugationJ, modularComplexI] using
    (InfoGeometry.Krein.modular_j_complex_i_anticommute (E := E))

omit [CompleteSpace E] in
/-- `J` is even for the doubled-space `Z₂` grading. -/
lemma modularConjugationJ_isEven :
    isEven (E := E) (modularConjugationJ (E := E)) := by
  unfold isEven modularConjugationJ
  rfl

/-- `ε = sgn(K)` is odd for the doubled-space `Z₂` grading. -/
lemma modularSignEpsilon_isOdd :
    isOdd (E := E) (modularSignEpsilon (E := E)) := by
  simpa [modularSignEpsilon] using (spectral_epsilon_isOdd (E := E))

/-- `Jε` is odd for the doubled-space `Z₂` grading. -/
lemma modularComplexI_isOdd :
    isOdd (E := E) (modularComplexI (E := E)) := by
  simpa [modularComplexI] using (complex_i_isOdd (E := E))

/-- The modular complex axis `K = Jε` is symmetric for the doubled Krein pairing. -/
lemma modularComplexI_kreinInner_swap
    (u v : DoubledSpace E) :
    KreinSpace.kreinInner (H := DoubledSpace E)
        ((modularComplexI (E := E)) u) v
      =
    KreinSpace.kreinInner (H := DoubledSpace E)
        u ((modularComplexI (E := E)) v) := by
  repeat rw [krein_inner_prod_l2]
  repeat rw [WithLp.ofLp_fst, WithLp.ofLp_snd]
  simp [modularComplexI, sub_eq_add_neg, real_inner_comm]
  abel

lemma clockAxis_kreinInner_swap
    (u v : DoubledSpace E) :
    KreinSpace.kreinInner (H := DoubledSpace E)
        ((clockAxis (E := E)) u) v
      =
    KreinSpace.kreinInner (H := DoubledSpace E)
        u ((clockAxis (E := E)) v) := by
  simpa [modularComplexI_eq_clockAxis] using
    modularComplexI_kreinInner_swap (E := E) u v

/-- The modular complex axis squares to `-1` inside the doubled Krein pairing. -/
lemma modularComplexI_kreinInner_comp
    (u v : DoubledSpace E) :
    KreinSpace.kreinInner (H := DoubledSpace E)
        ((modularComplexI (E := E)) u)
        ((modularComplexI (E := E)) v)
      =
    -KreinSpace.kreinInner (H := DoubledSpace E) u v := by
  have hK2 :
      (modularComplexI (E := E)) ((modularComplexI (E := E)) v) = -v := by
    have hSq := modularComplexI_sq (E := E)
    exact congrArg (fun F : DoubledSpace E →L[ℝ] DoubledSpace E => F v) hSq
  calc
    KreinSpace.kreinInner (H := DoubledSpace E)
        ((modularComplexI (E := E)) u)
        ((modularComplexI (E := E)) v)
      =
    KreinSpace.kreinInner (H := DoubledSpace E)
        u ((modularComplexI (E := E)) ((modularComplexI (E := E)) v)) := by
          rw [modularComplexI_kreinInner_swap]
    _ = KreinSpace.kreinInner (H := DoubledSpace E) u (-v) := by rw [hK2]
    _ = -KreinSpace.kreinInner (H := DoubledSpace E) u v := by
          simpa [neg_one_mul] using
            (KreinSpace.kreinInner_smul_right
              (H := DoubledSpace E) (-1) u v)

lemma clockAxis_kreinInner_comp
    (u v : DoubledSpace E) :
    KreinSpace.kreinInner (H := DoubledSpace E)
        ((clockAxis (E := E)) u)
        ((clockAxis (E := E)) v)
      =
    -KreinSpace.kreinInner (H := DoubledSpace E) u v := by
  simpa [modularComplexI_eq_clockAxis] using
    modularComplexI_kreinInner_comp (E := E) u v

/--
On the positive doubled-space Hilbert metric, the modular complex axis `K = Jε`
is skew:
`\langle Ku, v \rangle = - \langle u, Kv \rangle`.
-/
lemma modularComplexI_inner_skew
    (u v : DoubledSpace E) :
    ⟪modularComplexI (E := E) u, v⟫_ℝ
      =
    -⟪u, modularComplexI (E := E) v⟫_ℝ := by
  repeat rw [WithLp.prod_inner_apply]
  repeat rw [WithLp.ofLp_fst, WithLp.ofLp_snd]
  simp [modularComplexI, real_inner_comm]

lemma clockAxis_inner_skew
    (u v : DoubledSpace E) :
    ⟪clockAxis (E := E) u, v⟫_ℝ
      =
    -⟪u, clockAxis (E := E) v⟫_ℝ := by
  simpa [modularComplexI_eq_clockAxis] using
    modularComplexI_inner_skew (E := E) u v

lemma complex_i_inner_skew
    (u v : DoubledSpace E) :
    ⟪InfoGeometry.Krein.complex_i (E := E) u, v⟫_ℝ
      =
    -⟪u, InfoGeometry.Krein.complex_i (E := E) v⟫_ℝ := by
  simpa [modularComplexI] using modularComplexI_inner_skew (E := E) u v

/-- On the positive doubled-space Hilbert metric, `K = Jε` preserves the inner product. -/
lemma modularComplexI_inner_comp
    (u v : DoubledSpace E) :
    ⟪modularComplexI (E := E) u, modularComplexI (E := E) v⟫_ℝ
      =
    ⟪u, v⟫_ℝ := by
  have hK2 :
      (modularComplexI (E := E)) ((modularComplexI (E := E)) v) = -v := by
    have hSq := modularComplexI_sq (E := E)
    exact congrArg (fun F : DoubledSpace E →L[ℝ] DoubledSpace E => F v) hSq
  calc
    ⟪modularComplexI (E := E) u, modularComplexI (E := E) v⟫_ℝ
        =
      -⟪u, (modularComplexI (E := E)) ((modularComplexI (E := E)) v)⟫_ℝ := by
          rw [modularComplexI_inner_skew]
    _ = -⟪u, -v⟫_ℝ := by rw [hK2]
    _ = ⟪u, v⟫_ℝ := by simp

lemma clockAxis_inner_comp
    (u v : DoubledSpace E) :
    ⟪clockAxis (E := E) u, clockAxis (E := E) v⟫_ℝ
      =
    ⟪u, v⟫_ℝ := by
  simpa [modularComplexI_eq_clockAxis] using
    modularComplexI_inner_comp (E := E) u v

lemma complex_i_inner_comp
    (u v : DoubledSpace E) :
    ⟪InfoGeometry.Krein.complex_i (E := E) u, InfoGeometry.Krein.complex_i (E := E) v⟫_ℝ
      =
    ⟪u, v⟫_ℝ := by
  simpa [modularComplexI] using modularComplexI_inner_comp (E := E) u v

/--
Odd-odd channel for the modular CPT atom vanishes:
`Jε + εJ = 0`.
-/
lemma modularConjugationJ_anticommutator_modularSignEpsilon :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = 0 := by
  have hanti := modularConjugationJ_anticommutes_modularSign (E := E)
  calc
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
        + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = -((modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E)))
          + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E)) := by rw [hanti]
    _ = 0 := by abel

/--
Even-odd channel for the modular CPT atom:
`[J, ε] = 2(Jε)`.
-/
lemma modularConjugationJ_commutator_modularSignEpsilon :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      - (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = (2 : ℝ) • ((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) := by
  have hanti := modularConjugationJ_anticommutes_modularSign (E := E)
  let A := (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
  have htwo : (2 : ℝ) • A = A + A := by
    simpa using (two_smul ℝ A)
  calc
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
        - (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = A + A := by
          simp [A, sub_eq_add_neg, hanti]
    _ = (2 : ℝ) • A := by rw [htwo]
    _ = (2 : ℝ) • ((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) := by
          simp [A]

/--
Tomita inversion identity on the modular sign generator:
\[
J \exp(\tau\,\varepsilon) J = \exp(-\tau\,\varepsilon).
\]
-/
theorem modularConjugationJ_exp_modularSignEpsilon
    (τ : ℝ) :
    (modularConjugationJ (E := E)) *
        NormedSpace.exp (τ • (modularSignEpsilon (E := E))) *
        (modularConjugationJ (E := E))
      = NormedSpace.exp ((-τ) • (modularSignEpsilon (E := E))) := by
  have hJ2 : (modularConjugationJ (E := E)) * (modularConjugationJ (E := E))
      = (1 : EndH) := by
    change (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E)
    exact modularConjugationJ_sq (E := E)
  have hAnti :
      (modularConjugationJ (E := E)) * (modularSignEpsilon (E := E))
        = -((modularSignEpsilon (E := E)) * (modularConjugationJ (E := E))) := by
    simpa using (modularConjugationJ_anticommutes_modularSign (E := E))
  have hConjSign :
      (modularConjugationJ (E := E)) * (modularSignEpsilon (E := E))
          * (modularConjugationJ (E := E))
        = -(modularSignEpsilon (E := E)) := by
    calc
      (modularConjugationJ (E := E)) * (modularSignEpsilon (E := E))
          * (modularConjugationJ (E := E))
          = (-(modularSignEpsilon (E := E) * modularConjugationJ (E := E)))
              * modularConjugationJ (E := E) := by
                rw [hAnti]
      _ = -((modularSignEpsilon (E := E)) * (modularConjugationJ (E := E) *
            modularConjugationJ (E := E))) := by
              simp [mul_assoc]
      _ = -((modularSignEpsilon (E := E)) * (1 : EndH)) := by
            rw [hJ2]
      _ = -(modularSignEpsilon (E := E)) := by simp
  have hConjScaled :
      (modularConjugationJ (E := E)) * (τ • (modularSignEpsilon (E := E)))
          * (modularConjugationJ (E := E))
        = (-τ) • (modularSignEpsilon (E := E)) := by
    calc
      (modularConjugationJ (E := E)) * (τ • (modularSignEpsilon (E := E)))
          * (modularConjugationJ (E := E))
          = τ •
              ((modularConjugationJ (E := E)) * (modularSignEpsilon (E := E))
                * (modularConjugationJ (E := E))) := by
              simp [mul_assoc]
      _ = τ • (-(modularSignEpsilon (E := E))) := by rw [hConjSign]
      _ = (-τ) • (modularSignEpsilon (E := E)) := by simp [smul_neg, neg_smul]
  calc
    (modularConjugationJ (E := E)) *
        NormedSpace.exp (τ • (modularSignEpsilon (E := E))) *
        (modularConjugationJ (E := E))
        = NormedSpace.exp
            ((modularConjugationJ (E := E)) *
              (τ • (modularSignEpsilon (E := E))) *
              (modularConjugationJ (E := E))) := by
              simpa using involutiveConjugation_exp
                (E := E)
                (J := modularConjugationJ (E := E))
                (X := τ • (modularSignEpsilon (E := E)))
                hJ2
    _ = NormedSpace.exp ((-τ) • (modularSignEpsilon (E := E))) := by
          rw [hConjScaled]

/-- Tomita inversion identity on the internal phase axis `Jε`. -/
theorem modularConjugationJ_exp_modularComplexI
    (τ : ℝ) :
    (modularConjugationJ (E := E)) *
        NormedSpace.exp (τ • (modularComplexI (E := E))) *
        (modularConjugationJ (E := E))
      = NormedSpace.exp ((-τ) • (modularComplexI (E := E))) := by
  have hJ2 : (modularConjugationJ (E := E)) * (modularConjugationJ (E := E))
      = (1 : EndH) := by
    change (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E)
    exact modularConjugationJ_sq (E := E)
  have hAnti :
      (modularConjugationJ (E := E)) * (modularComplexI (E := E))
        = -((modularComplexI (E := E)) * (modularConjugationJ (E := E))) := by
    simpa using (modularConjugationJ_anticommutes_modularComplexI (E := E))
  have hConjAxis :
      (modularConjugationJ (E := E)) * (modularComplexI (E := E))
          * (modularConjugationJ (E := E))
        = -(modularComplexI (E := E)) := by
    calc
      (modularConjugationJ (E := E)) * (modularComplexI (E := E))
          * (modularConjugationJ (E := E))
          = (-(modularComplexI (E := E) * modularConjugationJ (E := E)))
              * modularConjugationJ (E := E) := by
                rw [hAnti]
      _ = -((modularComplexI (E := E)) * (modularConjugationJ (E := E) *
            modularConjugationJ (E := E))) := by
              simp [mul_assoc]
      _ = -((modularComplexI (E := E)) * (1 : EndH)) := by
            rw [hJ2]
      _ = -(modularComplexI (E := E)) := by simp
  have hConjScaled :
      (modularConjugationJ (E := E)) * (τ • (modularComplexI (E := E)))
          * (modularConjugationJ (E := E))
        = (-τ) • (modularComplexI (E := E)) := by
    calc
      (modularConjugationJ (E := E)) * (τ • (modularComplexI (E := E)))
          * (modularConjugationJ (E := E))
          = τ •
              ((modularConjugationJ (E := E)) * (modularComplexI (E := E))
                * (modularConjugationJ (E := E))) := by
              simp [mul_assoc]
      _ = τ • (-(modularComplexI (E := E))) := by rw [hConjAxis]
      _ = (-τ) • (modularComplexI (E := E)) := by simp [smul_neg, neg_smul]
  calc
    (modularConjugationJ (E := E)) *
        NormedSpace.exp (τ • (modularComplexI (E := E))) *
        (modularConjugationJ (E := E))
        = NormedSpace.exp
            ((modularConjugationJ (E := E)) *
              (τ • (modularComplexI (E := E))) *
              (modularConjugationJ (E := E))) := by
              simpa using involutiveConjugation_exp
                (E := E)
                (J := modularConjugationJ (E := E))
                (X := τ • (modularComplexI (E := E)))
                hJ2
    _ = NormedSpace.exp ((-τ) • (modularComplexI (E := E))) := by
          rw [hConjScaled]

/-- Right-intertwining form of Tomita inversion on the internal phase axis `Jε`. -/
theorem modularConjugationJ_exp_modularComplexI_right
    (τ : ℝ) :
    (modularConjugationJ (E := E)) * NormedSpace.exp (τ • (modularComplexI (E := E)))
      = NormedSpace.exp ((-τ) • (modularComplexI (E := E))) * (modularConjugationJ (E := E)) := by
  have hJ2 : (modularConjugationJ (E := E)) * (modularConjugationJ (E := E))
      = (1 : EndH) := by
    change (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E)
    exact modularConjugationJ_sq (E := E)
  calc
    (modularConjugationJ (E := E)) * NormedSpace.exp (τ • (modularComplexI (E := E)))
        = ((modularConjugationJ (E := E)) * NormedSpace.exp (τ • (modularComplexI (E := E)))) * (1 : EndH) := by
            simp
    _ = ((modularConjugationJ (E := E)) * NormedSpace.exp (τ • (modularComplexI (E := E)))) *
          ((modularConjugationJ (E := E)) * (modularConjugationJ (E := E))) := by
            rw [hJ2]
    _ = ((modularConjugationJ (E := E)) * NormedSpace.exp (τ • (modularComplexI (E := E))) *
          (modularConjugationJ (E := E))) * (modularConjugationJ (E := E)) := by
            simp [mul_assoc]
    _ = NormedSpace.exp ((-τ) • (modularComplexI (E := E))) * (modularConjugationJ (E := E)) := by
          rw [modularConjugationJ_exp_modularComplexI (E := E) τ]

/--
The **Modular Operator** Δ, identified as the exponential of the internal
phase/log-scale axis `K = Jε`.
In the Tomita-Takesaki theory, Δ represents the scaling or "density" of the
relational state space.
-/
noncomputable def modularOperatorDelta : EndH :=
  NormedSpace.exp (modularComplexI (E := E))

/--
**Scale Inversion Theorem**:
Reflecting the modular operator across the mirror `J` inverts the scale.
`J Δ J = exp(-K)`.
This is the formal realization of the "Infinity becomes Zero" (`X ↦ 1/X`)
conformal inversion at the holographic boundary.
-/
theorem modularOperator_inversion :
    (modularConjugationJ (E := E)) * (modularOperatorDelta (E := E)) *
        (modularConjugationJ (E := E))
      = NormedSpace.exp (-(modularComplexI (E := E))) := by
  unfold modularOperatorDelta
  simpa [one_smul, neg_one_smul] using
    (modularConjugationJ_exp_modularComplexI (E := E) (1 : ℝ))

/--
**Tomita Time Reversal**:
The modular transport flow `σ_t = exp(tK)` satisfies `J σ_t J = σ_{-t}`.
On the other side of the mirror (the anima/unconscious), modular time
flows backward relative to the ego.
-/
theorem modularFlow_reversal (t : ℝ) :
    (modularConjugationJ (E := E)) * NormedSpace.exp (t • (modularComplexI (E := E))) *
        (modularConjugationJ (E := E))
      = NormedSpace.exp ((-t) • (modularComplexI (E := E))) :=
  modularConjugationJ_exp_modularComplexI (E := E) t

/--
Concrete additive-time automorphism group generated by the modular sign
operator `ε` on doubled-space endomorphisms.
-/
noncomputable def modularSignAdditiveModularFlow :
    InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := E) :=
  InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator
    (H := E) (modularSignEpsilon (E := E))

@[simp] theorem modularSignAdditiveModularFlow_apply
    (τ : ℝ) (A : EndH) :
    modularSignAdditiveModularFlow (E := E) τ A =
      InfoGeometry.Krein.modular_shift
        (E := E) (modularSignEpsilon (E := E)) τ A := rfl

/--
Thermal KMS-like relation for the modular-sign generator, restated directly in
the additive modular-flow language used by the Tomita carrier.
-/
theorem modularSignAdditiveModularFlow_kms_of_satisfies_kms_like
    (ω : EndH →L[ℝ] ℝ)
    (β : ℝ)
    (hKMS :
      InfoGeometry.Krein.satisfies_kms_like
        (E := E)
        (modularSignEpsilon (E := E))
        ω β) :
    ∀ A B : EndH,
      ω (A * modularSignAdditiveModularFlow (E := E) β B) = ω (B * A) := by
  intro A B
  simpa [modularSignAdditiveModularFlow_apply] using hKMS A B

/--
Canonical supergraded package for the modular CPT atom `⟨1, ε, J, Jε⟩`.
-/
theorem modularCPT_supergraded_lie_package :
    isEven (E := E) (modularConjugationJ (E := E)) ∧
      isOdd (E := E) (modularSignEpsilon (E := E)) ∧
      isOdd (E := E) (modularComplexI (E := E)) ∧
      (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
        + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E)) = 0 := by
  exact ⟨modularConjugationJ_isEven (E := E), modularSignEpsilon_isOdd (E := E),
    modularComplexI_isOdd (E := E),
    modularConjugationJ_anticommutator_modularSignEpsilon (E := E)⟩

/-- Canonical modular CPT supercharge, `Q := Jε`. -/
noncomputable def modularCPTSupercharge : Supercharge (E := E) where
  Q := modularComplexI (E := E)
  odd := modularComplexI_isOdd (E := E)

/-- The modular CPT supercharge squares to `-Id`. -/
lemma modularCPTSupercharge_hamiltonian :
    superHamiltonian (modularCPTSupercharge (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [modularCPTSupercharge, modularComplexI] using
    (complex_iSupercharge_hamiltonian (E := E))

/-- `Q = Jε` maps grade-plus states to grade-minus states. -/
lemma modularCPTSupercharge_maps_plus_to_minus
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) ((modularCPTSupercharge (E := E)).Q v) := by
  exact supercharge_maps_plus_to_minus (S := modularCPTSupercharge (E := E)) hv

/-- The modular CPT supercharge agrees with the legacy dilation generator. -/
lemma modularCPTSupercharge_Q_eq_dilationOperator :
    (modularCPTSupercharge (E := E)).Q = dilationOperator (E := E) := by
  change modularComplexI (E := E) = dilationOperator (E := E)
  exact modularComplexI_eq_dilationOperator (E := E)

/-- `Q = Jε` maps grade-minus states to grade-plus states. -/
lemma modularCPTSupercharge_maps_minus_to_plus
    {v : DoubledSpace E} (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) ((modularCPTSupercharge (E := E)).Q v) := by
  exact supercharge_maps_minus_to_plus (S := modularCPTSupercharge (E := E)) hv

/--
Canonical positive-time subspace in doubled form:
vectors with matched components `(x, x)`.
-/
def DiagonalPositiveTimeVector (Ω : DoubledSpace E) : Prop :=
  ∃ x : E, Ω = to_doubled x x

/-- Compatibility alias for the diagonal positive-time subspace. -/
abbrev PositiveTimeVector (Ω : DoubledSpace E) : Prop :=
  DiagonalPositiveTimeVector (E := E) Ω

omit [CompleteSpace E] in
/--
On the diagonal positive-time subspace, modular conjugation `J` fixes vectors.
-/
lemma modularConjugationJ_fixed_of_diagonalPositiveTimeVector
    (Ω : DoubledSpace E)
    (hΩ : DiagonalPositiveTimeVector (E := E) Ω) :
    modularConjugationJ (E := E) Ω = Ω := by
  rcases hΩ with ⟨x, rfl⟩
  apply DoubledSpace.ext <;> simp [modularConjugationJ, modular_j]

omit [CompleteSpace E] in
/-- Compatibility wrapper for `modularConjugationJ_fixed_of_diagonalPositiveTimeVector`. -/
lemma modularConjugationJ_fixed_of_positiveTimeVector
    (Ω : DoubledSpace E)
    (hΩ : PositiveTimeVector (E := E) Ω) :
    modularConjugationJ (E := E) Ω = Ω :=
  modularConjugationJ_fixed_of_diagonalPositiveTimeVector (E := E) Ω hΩ

omit [CompleteSpace E] in
/--
Reflection quadratic form is nonnegative on the diagonal positive-time subspace.
-/
theorem reflectionQuadratic_nonneg_of_diagonalPositiveTimeVector
    (Ω : DoubledSpace E)
    (hΩ : DiagonalPositiveTimeVector (E := E) Ω) :
    0 ≤ inner ℝ ((modularConjugationJ (E := E)) Ω) Ω := by
  rw [modularConjugationJ_fixed_of_diagonalPositiveTimeVector (E := E) Ω hΩ]
  exact real_inner_self_nonneg

/--
Compatibility wrapper for
`reflectionQuadratic_nonneg_of_diagonalPositiveTimeVector`.
-/
theorem reflectionQuadratic_nonneg_of_positiveTimeVector
    (Ω : DoubledSpace E)
    (hΩ : PositiveTimeVector (E := E) Ω) :
    0 ≤ inner ℝ ((modularConjugationJ (E := E)) Ω) Ω :=
  reflectionQuadratic_nonneg_of_diagonalPositiveTimeVector (E := E) Ω hΩ

/--
Canonical split-Clifford representation realized by the modular atom on doubled
space.
-/
noncomputable abbrev modularAtomRepresentation :
    RoutingSplitCliffordAlg →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  cl11Rep (E := E)

/-- Compatibility alias for the modular atom representation. -/
noncomputable abbrev tomitaRepresentation :
    RoutingSplitCliffordAlg →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  modularAtomRepresentation (E := E)

@[simp] lemma modularAtomRepresentation_cptJ :
    modularAtomRepresentation (E := E) cptJ = modularConjugationJ (E := E) := by
  simpa [modularAtomRepresentation, cptJ, modularConjugationJ] using
    (cl11Rep_ι_one_zero (E := E))

@[simp] lemma tomitaRepresentation_cptJ :
    tomitaRepresentation (E := E) cptJ = modularConjugationJ (E := E) := by
  simpa [tomitaRepresentation] using modularAtomRepresentation_cptJ (E := E)

@[simp] lemma modularAtomRepresentation_cptJeps :
    modularAtomRepresentation (E := E) cptJeps = modularComplexI (E := E) := by
  simpa [modularAtomRepresentation, cptJeps, modularComplexI] using
    (cl11Rep_ι_zero_one (E := E))

@[simp] lemma tomitaRepresentation_cptJeps :
    tomitaRepresentation (E := E) cptJeps = modularComplexI (E := E) := by
  simpa [tomitaRepresentation] using modularAtomRepresentation_cptJeps (E := E)

@[simp] lemma modularAtomRepresentation_cptEps :
    modularAtomRepresentation (E := E) cptEps = modularSignEpsilon (E := E) := by
  simpa [modularAtomRepresentation, cptEps, cptJ, cptJeps, modularSignEpsilon] using
    (cl11Rep_pseudoscalar (E := E))

@[simp] lemma tomitaRepresentation_cptEps :
    tomitaRepresentation (E := E) cptEps = modularSignEpsilon (E := E) := by
  simpa [tomitaRepresentation] using modularAtomRepresentation_cptEps (E := E)

end ModularRealization

end InfoGeometry.Canonical.TomitaTakesaki

namespace TomitaTakesaki

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable abbrev modularConjugationJ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :=
  InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)

noncomputable abbrev modularSignEpsilon (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :=
  InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := E)

noncomputable abbrev clockAxis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :=
  InfoGeometry.Canonical.TomitaTakesaki.clockAxis (E := E)

noncomputable abbrev phaseAxisK (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :=
  InfoGeometry.Canonical.TomitaTakesaki.phaseAxisK (E := E)

noncomputable abbrev modularComplexI (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :=
  InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)

@[simp] theorem modularConjugationJ_eq_modular_j :
    modularConjugationJ (E := E) = modular_j (E := E) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_eq_modular_j

@[simp] theorem modularSignEpsilon_eq_spectral_epsilon :
    modularSignEpsilon (E := E) = spectral_epsilon (E := E) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon

@[simp] theorem modularComplexI_eq_complex_i :
    modularComplexI (E := E) = complex_i (E := E) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i

@[simp] theorem modularComplexI_sq :
    (modularComplexI (E := E)).comp (modularComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_sq (E := E)

@[simp] theorem modularConjugationJ_sq :
    (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_sq (E := E)

@[simp] theorem modularSignEpsilon_sq :
    (modularSignEpsilon (E := E)).comp (modularSignEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_sq (E := E)

theorem modularComplexI_kreinInner_swap
    (u v : DoubledSpace E) :
    InfoGeometry.Krein.KreinSpace.kreinInner
        ((modularComplexI (E := E)) u) v
      =
    InfoGeometry.Krein.KreinSpace.kreinInner
        u ((modularComplexI (E := E)) v) :=
  InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_kreinInner_swap (E := E) u v

theorem modularComplexI_kreinInner_comp
    (u v : DoubledSpace E) :
    InfoGeometry.Krein.KreinSpace.kreinInner
        ((modularComplexI (E := E)) u)
        ((modularComplexI (E := E)) v)
      =
    -InfoGeometry.Krein.KreinSpace.kreinInner u v :=
  InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_kreinInner_comp (E := E) u v

end TomitaTakesaki
