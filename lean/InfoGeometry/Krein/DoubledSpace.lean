import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.Cartan.Involution
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# InfoGeometry.Krein.DoubledSpace

Direct canonical doubled states `WithLp 2 (E × E)` acting as an `L²` doubled model.
We equip this product with the $L^2$ sum norm and Krein symmetries.

Provides:
- `DoubledSpace E`: the canonical doubled space
- `modular_j`: swap isometry (modular swap)
- `spectral_epsilon`: fundamental symmetry (sign flip)
- `complex_i`: canonical complex structure $J \circ \epsilon$
-/

namespace InfoGeometry.Krein

open InfoGeometry.Cartan

section Compatibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Alias for the canonical doubled Hilbert space `WithLp 2 (E × E)`. -/
abbrev DoubledSpace (E : Type*) : Type _ := WithLp (2 : ENNReal) (E × E)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Extensionality lemma for `DoubledSpace`. -/
@[ext] lemma DoubledSpace.ext {u v : DoubledSpace E}
    (hfst : WithLp.fst u = WithLp.fst v)
    (hsnd : WithLp.snd u = WithLp.snd v) : u = v := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  exact Prod.ext hfst hsnd

/-- Create a doubled state from a physical and a ghost component. -/
abbrev to_doubled (x ξ : E) : DoubledSpace E := WithLp.toLp (2 : ENNReal) (x, ξ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] lemma fst_to_doubled (x ξ : E) :
    WithLp.fst (to_doubled x ξ : DoubledSpace E) = x := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] lemma snd_to_doubled (x ξ : E) :
    WithLp.snd (to_doubled x ξ : DoubledSpace E) = ξ := rfl

/-- Physical coordinate projection as a continuous linear map. -/
noncomputable abbrev fst_L : DoubledSpace E →L[ℝ] E :=
  WithLp.fstL (p := (2 : ENNReal)) ℝ E E

/-- Ghost coordinate projection as a continuous linear map. -/
noncomputable abbrev snd_L : DoubledSpace E →L[ℝ] E :=
  WithLp.sndL (p := (2 : ENNReal)) ℝ E E

/-- The modular swap $J(x, \xi) = (\xi, x)$ as a continuous linear map. -/
noncomputable def modular_j : DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u := WithLp.toLp (2 : ENNReal) (WithLp.snd u, WithLp.fst u)
  map_add' u v := by
    simpa [WithLp.add_snd, WithLp.add_fst] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := (WithLp.snd u, WithLp.fst u))
        (y := (WithLp.snd v, WithLp.fst v)))
  map_smul' c u := by
    simpa [WithLp.smul_snd, WithLp.smul_fst] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
        (x := (WithLp.snd u, WithLp.fst u)))
  cont := by
    simpa using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
        ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E)).prodMk
         (WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)))

/-- The fundamental symmetry $\epsilon(x, \xi) = (x, -\xi)$ as a continuous linear map. -/
noncomputable def spectral_epsilon : DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u := WithLp.toLp (2 : ENNReal) (WithLp.fst u, -WithLp.snd u)
  map_add' u v := by
    simpa [WithLp.add_fst, WithLp.add_snd, neg_add, add_comm] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := (WithLp.fst u, -WithLp.snd u))
        (y := (WithLp.fst v, -WithLp.snd v)))
  map_smul' c u := by
    simpa [WithLp.smul_fst, WithLp.smul_snd, smul_neg] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
        (x := (WithLp.fst u, -WithLp.snd u)))
  cont := by
    simpa using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
        ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)).prodMk
         (continuous_neg.comp (WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E))))

/-- Canonical complex-like generator $I = J \circ \epsilon$. -/
noncomputable def complex_i : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j.comp spectral_epsilon

/-- Canonical split rotation axis `K = J ∘ ε` on the doubled real carrier. -/
noncomputable def clockAxis : DoubledSpace E →L[ℝ] DoubledSpace E :=
  complex_i

theorem complex_i_adjoint_eq_neg :
    ContinuousLinearMap.adjoint (complex_i (E := E)) = -(complex_i (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [complex_i, modular_j, spectral_epsilon, WithLp.prod_inner_apply,
    real_inner_comm]

omit [CompleteSpace E] in
@[simp] lemma clockAxis_eq_complex_i :
    clockAxis (E := E) = complex_i (E := E) := rfl

omit [CompleteSpace E] in
lemma complex_i_eq_clockAxis :
    complex_i (E := E) = clockAxis (E := E) := rfl

/-- The ambient Hilbert inner product packaged as a bilinear form. -/
noncomputable def doubledHilbertBilin : LinearMap.BilinForm ℝ (DoubledSpace E) :=
  LinearMap.mk₂ ℝ
    (fun u v => inner ℝ u v)
    (by
      intro u₁ u₂ v
      simp [inner_add_left])
    (by
      intro c u v
      simp [real_inner_smul_left]
      ring)
    (by
      intro u v₁ v₂
      simp [inner_add_right])
    (by
      intro c u v
      simp [real_inner_smul_right]
      ring)

/--
Canonical substrate packaging of the doubled lane as an involutive self-dual carrier.
This is used to rebase doubled identities onto owner-level root lemmas.
-/
noncomputable def doubledCarrier : InvolutiveSelfDualCarrier where
  H := DoubledSpace E
  kreinPairing := doubledHilbertBilin (E := E)
  J := modular_j (E := E)
  ε := spectral_epsilon (E := E)
  J_sq := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [modular_j]
  ε_sq := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [spectral_epsilon]
  J_ε_anticomm := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [modular_j, spectral_epsilon]
  pairing_symm := by
    intro u v
    simp [doubledHilbertBilin, real_inner_comm]
  pairing_J_invariant := by
    intro u v
    simp [doubledHilbertBilin, modular_j, WithLp.prod_inner_apply, add_comm]
  pairing_ε_invariant := by
    intro u v
    simp [doubledHilbertBilin, spectral_epsilon, WithLp.prod_inner_apply]
  pairing_nondegenerate := by
    intro u v h
    apply ext_inner_right ℝ
    intro w
    exact congrArg (fun φ : Module.Dual ℝ (DoubledSpace E) => φ w) h

/-- $Cl(1,1)$ compatibility relation package on doubled-space endomorphisms. -/
def cl11_relations (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
  ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
  J.comp ε = -(ε.comp J)

/-- Typeclass alias for the Clifford structure. -/
abbrev cl11_algebra (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  cl11_relations J ε

omit [CompleteSpace E] in
@[simp] lemma modular_j_apply (u : DoubledSpace E) :
    modular_j u = WithLp.toLp (2 : ENNReal) (WithLp.snd u, WithLp.fst u) := rfl

omit [CompleteSpace E] in
@[simp] lemma modular_j_to_doubled (x ξ : E) :
    modular_j (to_doubled x ξ : DoubledSpace E) = to_doubled ξ x := by
  apply DoubledSpace.ext <;> simp [modular_j]

omit [CompleteSpace E] in
@[simp] lemma spectral_epsilon_apply (u : DoubledSpace E) :
    spectral_epsilon u = WithLp.toLp (2 : ENNReal) (WithLp.fst u, -WithLp.snd u) := rfl

omit [CompleteSpace E] in
@[simp] lemma spectral_epsilon_to_doubled (x ξ : E) :
    spectral_epsilon (to_doubled x ξ : DoubledSpace E) = to_doubled x (-ξ) := by
  apply DoubledSpace.ext <;> simp [spectral_epsilon]

omit [CompleteSpace E] in
@[simp] lemma complex_i_apply (u : DoubledSpace E) :
    complex_i u = WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) := by
  apply DoubledSpace.ext <;> simp [complex_i]

omit [CompleteSpace E] in
@[simp] lemma clockAxis_apply (u : DoubledSpace E) :
    clockAxis u = WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) := by
  rw [clockAxis]
  exact complex_i_apply (E := E) u

omit [CompleteSpace E] in
@[simp] lemma complex_i_to_doubled (x ξ : E) :
    complex_i (to_doubled x ξ : DoubledSpace E) = to_doubled (-ξ) x := by
  apply DoubledSpace.ext <;> simp [complex_i]

omit [CompleteSpace E] in
@[simp] lemma clockAxis_to_doubled (x ξ : E) :
    clockAxis (to_doubled x ξ : DoubledSpace E) = to_doubled (-ξ) x := by
  rw [clockAxis]
  exact complex_i_to_doubled (E := E) x ξ

lemma modular_j_involution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (modular_j (E := E)).comp modular_j = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp

lemma spectral_epsilon_involution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (spectral_epsilon (E := E)).comp spectral_epsilon = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp

lemma modular_j_spectral_epsilon_anticommute (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (modular_j (E := E)).comp spectral_epsilon = -(spectral_epsilon.comp modular_j) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp [modular_j_apply, spectral_epsilon_apply]

/-- Exact product identity `J I = ε` for the doubled-space split generators. -/
lemma modular_j_comp_complex_i (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (modular_j (E := E)).comp (complex_i (E := E)) = spectral_epsilon := by
  simpa [complex_i, doubledCarrier]
    using (InvolutiveSelfDualCarrier.J_comp_K (X := doubledCarrier (E := E)))

/-- Exact product identity `I J = -ε` for the doubled-space split generators. -/
lemma complex_i_comp_modular_j (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (complex_i (E := E)).comp (modular_j (E := E)) = -spectral_epsilon := by
  simpa [complex_i, doubledCarrier]
    using (InvolutiveSelfDualCarrier.K_comp_J (X := doubledCarrier (E := E)))

/-- Exact product identity `I ε = J` for the doubled-space split generators. -/
lemma complex_i_comp_spectral_epsilon (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (complex_i (E := E)).comp spectral_epsilon = modular_j := by
  simpa [complex_i, doubledCarrier]
    using (InvolutiveSelfDualCarrier.K_comp_ε (X := doubledCarrier (E := E)))

/-- Exact product identity `ε I = -J` for the doubled-space split generators. -/
lemma spectral_epsilon_comp_complex_i (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    spectral_epsilon.comp (complex_i (E := E)) = -modular_j := by
  simpa [complex_i, doubledCarrier]
    using (InvolutiveSelfDualCarrier.ε_comp_K (X := doubledCarrier (E := E)))

/-- Exact product identity `ε J = -I` for the doubled-space split generators. -/
lemma spectral_epsilon_comp_modular_j (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    spectral_epsilon.comp (modular_j (E := E)) = -(complex_i (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [complex_i, modular_j, spectral_epsilon]

lemma complex_i_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (complex_i (E := E)).comp complex_i = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [complex_i, doubledCarrier]
    using (InvolutiveSelfDualCarrier.K_sq (X := doubledCarrier (E := E)))

/-- The real elliptic Hestenes axis as a linear equivalence, with inverse `-I`. -/
noncomputable def complex_iLE (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗ[ℝ] DoubledSpace E :=
  { (complex_i (E := E)).toLinearMap with
    invFun := fun x => -(complex_i (E := E) x)
    left_inv := by
      intro x
      apply DoubledSpace.ext <;> simp [complex_i]
    right_inv := by
      intro x
      apply DoubledSpace.ext <;> simp [complex_i] }

@[simp]
lemma complex_iLE_apply (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (x : DoubledSpace E) :
    complex_iLE E x = complex_i (E := E) x := by
  rfl

@[simp]
lemma complex_iLE_symm_apply (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (x : DoubledSpace E) :
    (complex_iLE E).symm x = -(complex_i (E := E) x) := by
  rfl

lemma clockAxis_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (clockAxis (E := E)).comp clockAxis = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [clockAxis] using complex_i_sq (E := E)

/-! ### Real Hestenes pion atom

The doubled carrier has two anticommuting involutions `J` and `ε`, with
`K = J ε` a square-minus-one axis.  The nilpotent channels therefore use the
`J/K` pair, not the two involutions `J/ε` directly.  This is the real
Hestenes presentation of the finite chiral atom.
-/

noncomputable def hestenesPionPlus : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (modular_j (E := E) - clockAxis (E := E))

noncomputable def hestenesPionMinus : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (modular_j (E := E) + clockAxis (E := E))

noncomputable def hestenesPionZero : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • spectral_epsilon (E := E)

lemma hestenesPionPlus_sq :
    (hestenesPionPlus (E := E)).comp hestenesPionPlus = 0 := by
  have hJK :
      (modular_j (E := E)).comp (complex_i (E := E)) = spectral_epsilon (E := E) :=
    modular_j_comp_complex_i (E := E)
  have hKJ :
      (complex_i (E := E)).comp (modular_j (E := E)) = -(spectral_epsilon (E := E)) :=
    complex_i_comp_modular_j (E := E)
  simp [hestenesPionPlus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub]
  rw [modular_j_involution, complex_i_sq, hJK, hKJ]
  module

lemma hestenesPionMinus_sq :
    (hestenesPionMinus (E := E)).comp hestenesPionMinus = 0 := by
  have hJK :
      (modular_j (E := E)).comp (complex_i (E := E)) = spectral_epsilon (E := E) :=
    modular_j_comp_complex_i (E := E)
  have hKJ :
      (complex_i (E := E)).comp (modular_j (E := E)) = -(spectral_epsilon (E := E)) :=
    complex_i_comp_modular_j (E := E)
  simp [hestenesPionMinus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add]
  rw [modular_j_involution, complex_i_sq, hJK, hKJ]
  module

lemma hestenesPionPlus_mul_minus :
    (hestenesPionPlus (E := E)).comp hestenesPionMinus =
      ((1 / 2 : ℝ) •
        (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectral_epsilon (E := E))) := by
  have hJK :
      (modular_j (E := E)).comp (complex_i (E := E)) = spectral_epsilon (E := E) :=
    modular_j_comp_complex_i (E := E)
  have hKJ :
      (complex_i (E := E)).comp (modular_j (E := E)) = -(spectral_epsilon (E := E)) :=
    complex_i_comp_modular_j (E := E)
  simp [hestenesPionPlus, hestenesPionMinus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_add]
  rw [modular_j_involution, complex_i_sq, hJK, hKJ]
  module

lemma hestenesPionMinus_mul_plus :
    (hestenesPionMinus (E := E)).comp hestenesPionPlus =
      ((1 / 2 : ℝ) •
        (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectral_epsilon (E := E))) := by
  have hJK :
      (modular_j (E := E)).comp (complex_i (E := E)) = spectral_epsilon (E := E) :=
    modular_j_comp_complex_i (E := E)
  have hKJ :
      (complex_i (E := E)).comp (modular_j (E := E)) = -(spectral_epsilon (E := E)) :=
    complex_i_comp_modular_j (E := E)
  simp [hestenesPionPlus, hestenesPionMinus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_sub]
  rw [modular_j_involution, complex_i_sq, hJK, hKJ]
  module

lemma hestenesPion_car :
    (hestenesPionPlus (E := E)).comp hestenesPionMinus +
        (hestenesPionMinus (E := E)).comp hestenesPionPlus =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  rw [hestenesPionPlus_mul_minus, hestenesPionMinus_mul_plus]
  module

lemma hestenesPion_commutator :
    (hestenesPionPlus (E := E)).comp hestenesPionMinus -
        (hestenesPionMinus (E := E)).comp hestenesPionPlus =
      spectral_epsilon (E := E) := by
  rw [hestenesPionPlus_mul_minus, hestenesPionMinus_mul_plus]
  module

lemma hestenesPion_zero_plus :
    (hestenesPionZero (E := E)).comp hestenesPionPlus -
        (hestenesPionPlus (E := E)).comp hestenesPionZero =
      hestenesPionPlus (E := E) := by
  simp only [hestenesPionZero, hestenesPionPlus,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [show (spectral_epsilon (E := E)).comp (modular_j (E := E)) =
      -(clockAxis (E := E)) by
        simpa [clockAxis] using spectral_epsilon_comp_modular_j (E := E),
    show (spectral_epsilon (E := E)).comp clockAxis =
      -(modular_j (E := E)) by
        simpa [clockAxis] using spectral_epsilon_comp_complex_i (E := E),
    show (modular_j (E := E)).comp (spectral_epsilon (E := E)) =
      clockAxis (E := E) by rfl,
    show (clockAxis (E := E)).comp (spectral_epsilon (E := E)) =
      modular_j (E := E) by
        simpa [clockAxis] using complex_i_comp_spectral_epsilon (E := E)]
  module

lemma hestenesPion_zero_minus :
    (hestenesPionZero (E := E)).comp hestenesPionMinus -
        (hestenesPionMinus (E := E)).comp hestenesPionZero =
      -hestenesPionMinus (E := E) := by
  simp only [hestenesPionZero, hestenesPionMinus,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    smul_smul]
  rw [show (spectral_epsilon (E := E)).comp (modular_j (E := E)) =
      -(clockAxis (E := E)) by
        simpa [clockAxis] using spectral_epsilon_comp_modular_j (E := E),
    show (spectral_epsilon (E := E)).comp clockAxis =
      -(modular_j (E := E)) by
        simpa [clockAxis] using spectral_epsilon_comp_complex_i (E := E),
    show (modular_j (E := E)).comp (spectral_epsilon (E := E)) =
      clockAxis (E := E) by rfl,
    show (clockAxis (E := E)).comp (spectral_epsilon (E := E)) =
      modular_j (E := E) by
        simpa [clockAxis] using complex_i_comp_spectral_epsilon (E := E)]
  module

/-! ### Inverse basis change for the real nilpotent atom -/

omit [CompleteSpace E] in
theorem hestenesPionPlus_add_hestenesPionMinus :
    hestenesPionPlus (E := E) + hestenesPionMinus (E := E) =
      modular_j (E := E) := by
  simp [hestenesPionPlus, hestenesPionMinus]
  module

omit [CompleteSpace E] in
theorem hestenesPionMinus_sub_hestenesPionPlus :
    hestenesPionMinus (E := E) - hestenesPionPlus (E := E) =
      clockAxis (E := E) := by
  simp [hestenesPionPlus, hestenesPionMinus, sub_eq_add_neg]
  module

omit [CompleteSpace E] in
theorem two_smul_hestenesPionZero :
    (2 : ℝ) • hestenesPionZero (E := E) =
      spectral_epsilon (E := E) := by
  simp [hestenesPionZero]

theorem modular_j_spectral_epsilon_has_cl11_relations (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    cl11_relations (modular_j (E := E)) spectral_epsilon :=
  ⟨modular_j_involution E, spectral_epsilon_involution E, modular_j_spectral_epsilon_anticommute E⟩

theorem modular_j_spectral_epsilon_is_cl11 (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    cl11_algebra (modular_j (E := E)) spectral_epsilon :=
  modular_j_spectral_epsilon_has_cl11_relations E

/-- Modular J as a linear equivalence. -/
noncomputable def modular_jLE (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗ[ℝ] DoubledSpace E :=
  { modular_j (E := E).toLinearMap with
    invFun := modular_j (E := E)
    left_inv := fun x => by
      have h := congrArg (fun f => f x) (modular_j_involution E)
      simpa using h
    right_inv := fun x => by
      have h := congrArg (fun f => f x) (modular_j_involution E)
      simpa using h }

/-- Spectral epsilon as a linear equivalence. -/
noncomputable def spectral_epsilonLE (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗ[ℝ] DoubledSpace E :=
  { spectral_epsilon (E := E).toLinearMap with
    invFun := spectral_epsilon (E := E)
    left_inv := fun x => by
      have h := congrArg (fun f => f x) (spectral_epsilon_involution E)
      simpa using h
    right_inv := fun x => by
      have h := congrArg (fun f => f x) (spectral_epsilon_involution E)
      simpa using h }

lemma modular_j_is_cartan (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCartanInvolution (modular_jLE E).toLinearMap := by
  have h := modular_j_involution E
  exact congrArg ContinuousLinearMap.toLinearMap h

lemma spectral_epsilon_is_cartan (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCartanInvolution (spectral_epsilonLE E).toLinearMap := by
  have h := spectral_epsilon_involution E
  exact congrArg ContinuousLinearMap.toLinearMap h

end Compatibility

/-! ### Cayley fiber identification -/

open Complex

/-- The real Cayley identification of the doubled scalar fiber with `ℂ`.

This is a fiber-level statement only.  It does not identify an `Lp` space with
an unweighted `lp` space, nor does it make a claim about a GNS representation.
-/
noncomputable def cayleyDoubledRealFiber : DoubledSpace ℝ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv :=
    (WithLp.linearEquiv (2 : ENNReal) ℝ (ℝ × ℝ)).trans
      Complex.equivRealProdCLM.symm.toLinearEquiv
  norm_map' u := by
    change ‖Complex.equivRealProdCLM.symm (WithLp.ofLp u)‖ = ‖u‖
    have hsq :
        ‖Complex.equivRealProdCLM.symm (WithLp.ofLp u)‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [Complex.equivRealProdCLM_symm_apply, Complex.sq_norm,
        Complex.normSq_add_mul_I, WithLp.prod_norm_sq_eq_of_L2]
      simp [Real.norm_eq_abs, sq_abs]
    nlinarith [norm_nonneg (Complex.equivRealProdCLM.symm (WithLp.ofLp u)),
      norm_nonneg u]

@[simp] theorem cayleyDoubledRealFiber_apply (u : DoubledSpace ℝ) :
    cayleyDoubledRealFiber u =
      (WithLp.ofLp u).1 + (WithLp.ofLp u).2 * Complex.I := by
  change Complex.equivRealProdCLM.symm (WithLp.ofLp u) = _
  rw [Complex.equivRealProdCLM_symm_apply]

theorem cayleyDoubledRealFiber_complex_i (u : DoubledSpace ℝ) :
    cayleyDoubledRealFiber (complex_i u) =
      Complex.I * cayleyDoubledRealFiber u := by
  rw [cayleyDoubledRealFiber_apply, complex_i_apply,
    cayleyDoubledRealFiber_apply]
  have hcoord :
      WithLp.ofLp
          (WithLp.toLp (2 : ENNReal)
            (-WithLp.snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ) u,
              WithLp.fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ) u)) =
        (-WithLp.snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ) u,
          WithLp.fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ) u) := rfl
  rw [hcoord]
  have hu :
      WithLp.ofLp u =
        (WithLp.fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ) u,
          WithLp.snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ) u) := rfl
  rw [hu]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

section KreinAnalytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => WithLp (2 : ENNReal) (E × E)

/-- The Hessian indefinite form on DoubledSpace. -/
noncomputable def hessian_indefinite_form (u v : H₂) : ℝ :=
  KreinSpace.kreinInner (H := H₂) u v

/-- Characterization of Krein skew-adjointness. -/
def is_krein_skew_adjoint (A : H₂ →L[ℝ] H₂) : Prop :=
  KreinSpace.IsKreinSkewAdjoint (H := H₂) A

theorem is_krein_skew_adjoint_hessian_infinitesimal
    {A : H₂ →L[ℝ] H₂}
    (hA : is_krein_skew_adjoint A)
    (x y : H₂) :
    hessian_indefinite_form (A x) y + hessian_indefinite_form x (A y) = 0 :=
  (KreinSpace.isKreinSkewAdjoint_iff (H := H₂) A).mp hA x y

/-- The Lie algebra of the information state space. -/
noncomputable def information_lie_algebra :
    LieSubalgebra ℝ (H₂ →L[ℝ] H₂) where
  carrier := {A | is_krein_skew_adjoint A}
  zero_mem' := by
    simp [is_krein_skew_adjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := H₂)]
  add_mem' hA hB := by
    simp [is_krein_skew_adjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := H₂)] at hA hB ⊢
    rw [hA, hB]
    simp [add_comm]
  smul_mem' c A hA := by
    simp [is_krein_skew_adjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := H₂)] at hA ⊢
    rw [hA, smul_neg]
  lie_mem' hA hB := by
    simpa [is_krein_skew_adjoint] using
      (KreinSpace.isKreinSkewAdjoint_lie (H := H₂) (hA := hA) (hB := hB))

end KreinAnalytic

lemma hestenesPionPlus_sq_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : DoubledSpace E) :
    hestenesPionPlus (E := E) (hestenesPionPlus (E := E) x) = 0 := by
  have h := congrArg
    (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x)
    (hestenesPionPlus_sq (E := E))
  simpa [ContinuousLinearMap.comp_apply] using h

lemma hestenesPionMinus_sq_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : DoubledSpace E) :
    hestenesPionMinus (E := E) (hestenesPionMinus (E := E) x) = 0 := by
  have h := congrArg
    (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x)
    (hestenesPionMinus_sq (E := E))
  simpa [ContinuousLinearMap.comp_apply] using h

lemma hestenesPion_car_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : DoubledSpace E) :
    hestenesPionPlus (E := E) (hestenesPionMinus (E := E) x) +
        hestenesPionMinus (E := E) (hestenesPionPlus (E := E) x) = x := by
  have h := congrArg
    (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x)
    (hestenesPion_car (E := E))
  simpa [ContinuousLinearMap.comp_apply] using h

lemma hestenesPion_commutator_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : DoubledSpace E) :
    hestenesPionPlus (E := E) (hestenesPionMinus (E := E) x) -
        hestenesPionMinus (E := E) (hestenesPionPlus (E := E) x) =
      spectral_epsilon (E := E) x := by
  have h := congrArg
    (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x)
    (hestenesPion_commutator (E := E))
  simpa [ContinuousLinearMap.comp_apply] using h

lemma hestenesPion_zero_plus_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : DoubledSpace E) :
    hestenesPionZero (E := E) (hestenesPionPlus (E := E) x) -
        hestenesPionPlus (E := E) (hestenesPionZero (E := E) x) =
      hestenesPionPlus (E := E) x := by
  have h := congrArg
    (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x)
    (hestenesPion_zero_plus (E := E))
  simpa [ContinuousLinearMap.comp_apply] using h

lemma hestenesPion_zero_minus_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (x : DoubledSpace E) :
    hestenesPionZero (E := E) (hestenesPionMinus (E := E) x) -
        hestenesPionMinus (E := E) (hestenesPionZero (E := E) x) =
      -hestenesPionMinus (E := E) x := by
  have h := congrArg
    (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x)
    (hestenesPion_zero_minus (E := E))
  simpa [ContinuousLinearMap.comp_apply] using h

end InfoGeometry.Krein
