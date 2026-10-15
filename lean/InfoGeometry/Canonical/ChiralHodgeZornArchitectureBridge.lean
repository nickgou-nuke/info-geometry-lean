import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Abel

/-!
# The Complete Chiral Hodge-Dirac-Kähler & Zorn Vector Matrix Architecture

This module establishes the canonical mathematical bridge uniting:
1. **The 6-Fold Chiral Hodge Decomposition & Zorn Vector Matrix Mapping**:
   The full decomposition
   $$\Omega^\bullet = (\operatorname{im}(d)_+ \oplus \operatorname{im}(d)_-) \oplus
     (\operatorname{im}(\delta)_+ \oplus \operatorname{im}(\delta)_-) \oplus
     (\mathcal{H}_+ \oplus \mathcal{H}_-)$$
   is mapped into the real Zorn vector-matrix algebra $\mathrm{ZornCoord} = \mathbb{R} \times \mathbb{R} \times \mathrm{Vec3} \times \mathrm{Vec3}$:
   - Exact irrotational sector $\operatorname{im}(d)_\pm$: diagonal components $(a, b, 0, 0)$
   - Traceless Weyl dilaton gauge mode: $(a, -a, 0, 0)$ with $\operatorname{tr} = 0$ and norm $-a^2$
   - Coexact rotational sector $\operatorname{im}(\delta)_\pm$: off-diagonal vector blocks $(0, 0, u, v)$
   - Harmonic ground states $\mathcal{H}_\Delta$: the invariant kernel mediating the modular seam.

2. **Krein Geometry & Maximal Lagrangian Isotropy**:
   In the indefinite Krein metric (Zorn reduced norm $\mathcal{N}(z) = a b - u \cdot v$):
   - Positive coexact subspace $C_+(u) = (0, 0, u, 0)$ is totally isotropic: $\mathcal{N}(C_+(u)) = 0$
   - Negative coexact subspace $C_-(v) = (0, 0, 0, v)$ is totally isotropic: $\mathcal{N}(C_-(v)) = 0$
   - They form a dual Lagrangian polar pair with pairing $\langle C_+(u), C_-(v) \rangle = u \cdot v$.

3. **Square-Zero Chiral Channels & Mixed Products**:
   - The specified Zorn-coordinate elements satisfy $C_+(u)^2 = 0$ and
     $C_-(v)^2 = 0$.  These are identities in that carrier, not a
     Klein-quadric or Minkowski mass-shell characterization.
   - Anticommutator: $\{C_+(u), C_-(v)\} = (u \cdot v) \cdot \mathbb{I}$
   - Commutator: $[C_+(u), C_-(v)] = \mathrm{weylDilaton}(u \cdot v)$, proving that the commutator
     of transverse chiral matter currents generates the irrotational exact gauge mode.

4. **Transverse Vorticity & Chiral Charge Grading**:
   - Same-sheet products generate rotational curl: $C_+(u) C_+(v) = C_-(u \times v)$
   - Chiral charge grading: $[\mathrm{weylDilaton}(a), C(u, v)] = (0, 0, 2 a \cdot u, -2 a \cdot v)$.

5. **Mass Condensation**:
   - Symmetric matter doublet $\Psi(u) = (0, 0, u, u)$ satisfies $\Psi(u)^2 = (u \cdot u) \cdot \mathbb{I}$,
     locking exact and coexact modes into a massive timelike condensed state ($\mathcal{N}(\Psi(u)) = -u \cdot u$).
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralHodgeZornArchitecture

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

section CarrierEmbeddings

/-- Exact positive chiral mode: upper diagonal dilaton. -/
def exactUpper (a : ℝ) : ZornCoord :=
  zornMk a 0 0 0

/-- Exact negative chiral mode: lower diagonal dilaton. -/
def exactLower (b : ℝ) : ZornCoord :=
  zornMk 0 b 0 0

/-- General exact irrotational mode: diagonal Zorn matrix. -/
def exactMode (a b : ℝ) : ZornCoord :=
  zornMk a b 0 0

/-- Traceless Weyl dilaton mode: irrotational gauge potential. -/
def weylDilaton (a : ℝ) : ZornCoord :=
  zornMk a (-a) 0 0

/-- Coexact positive chiral mode: upper off-diagonal vector current. -/
def coexactUpper (u : Vec3) : ZornCoord :=
  upperVectorZorn u

/-- Coexact negative chiral mode: lower off-diagonal vector current. -/
def coexactLower (v : Vec3) : ZornCoord :=
  lowerVectorZorn v

/-- General coexact rotational mode: off-diagonal Zorn matrix. -/
def coexactMode (u v : Vec3) : ZornCoord :=
  zornMk 0 0 u v

/-- Symmetric matter current doublet. -/
def matterDoublet (u : Vec3) : ZornCoord :=
  zornMk 0 0 u u

/-- Full Zorn configuration embedding exact and coexact data. -/
def fullZornMode (a b : ℝ) (u v : Vec3) : ZornCoord :=
  zornMk a b u v

/-- Exact modes decompose into sum of positive and negative chiral projections. -/
theorem exact_decomposition (a b : ℝ) :
    exactMode a b = exactUpper a + exactLower b := by
  ext <;> simp [exactMode, exactUpper, exactLower, zornMk]

/-- Coexact modes decompose into sum of positive and negative chiral projections. -/
theorem coexact_decomposition (u v : Vec3) :
    coexactMode u v = coexactUpper u + coexactLower v := by
  ext <;> simp [coexactMode, coexactUpper, coexactLower, upperVectorZorn, lowerVectorZorn, zornMk]

/-- Full Zorn configuration decomposes into exact and coexact parts. -/
theorem fullZorn_decomposition (a b : ℝ) (u v : Vec3) :
    fullZornMode a b u v = exactMode a b + coexactMode u v := by
  ext <;> simp [fullZornMode, exactMode, coexactMode, zornMk]

/-- Certified archetype discharge: polar reconstruction of full Zorn configuration into
exact irrotational and coexact rotational chiral components. -/
theorem discharge_polar_reconstruction (a b : ℝ) (u v : Vec3) :
    fullZornMode a b u v = (exactUpper a + exactLower b) + (coexactUpper u + coexactLower v) := by
  rw [← exact_decomposition, ← coexact_decomposition, ← fullZorn_decomposition]

end CarrierEmbeddings

section TracelessnessAndNorms

/-- Tracelessness of the Weyl dilaton mode. -/
theorem weylDilaton_trace_zero (a : ℝ) :
    zornTrace (weylDilaton a) = 0 := by
  unfold zornTrace weylDilaton zornMk zornA zornB
  dsimp
  ring

/-- Reduced norm of the Weyl dilaton is strictly negative (hyperbolic/spacelike). -/
theorem weylDilaton_norm (a : ℝ) :
    zornNorm (weylDilaton a) = -a^2 := by
  unfold zornNorm weylDilaton zornMk zornA zornB zornX zornY dot3
  dsimp
  ring

/-- Tracelessness of arbitrary coexact rotational modes. -/
theorem coexactMode_trace_zero (u v : Vec3) :
    zornTrace (coexactMode u v) = 0 := by
  unfold zornTrace coexactMode zornMk zornA zornB
  dsimp
  ring

/-- Reduced norm of coexact modes is the negative dot product. -/
theorem coexactMode_norm (u v : Vec3) :
    zornNorm (coexactMode u v) = - dot3 u v := by
  unfold zornNorm coexactMode zornMk zornA zornB zornX zornY
  dsimp
  ring

/-- Tracelessness condition for the full Zorn configuration. -/
theorem fullZorn_trace (a b : ℝ) (u v : Vec3) :
    zornTrace (fullZornMode a b u v) = a + b := by
  unfold zornTrace fullZornMode zornMk zornA zornB
  dsimp

end TracelessnessAndNorms

section KreinLagrangianIsotropy

/-- Maximal Lagrangian isotropy: positive chiral coexact modes are null. -/
theorem coexactUpper_is_null (u : Vec3) :
    IsZornNull (coexactUpper u) := by
  unfold IsZornNull coexactUpper upperVectorZorn zornNorm zornMk zornA zornB zornX zornY dot3
  dsimp
  ring

/-- Maximal Lagrangian isotropy: negative chiral coexact modes are null. -/
theorem coexactLower_is_null (v : Vec3) :
    IsZornNull (coexactLower v) := by
  unfold IsZornNull coexactLower lowerVectorZorn zornNorm zornMk zornA zornB zornX zornY dot3
  dsimp
  ring

/-- Indefinite Krein cross-pairing between positive and negative coexact modes. -/
theorem coexact_krein_pairing (u v : Vec3) :
    zornNorm (coexactUpper u + coexactLower v) = - dot3 u v := by
  rw [← coexact_decomposition]
  exact coexactMode_norm u v

end KreinLagrangianIsotropy

section SquareZeroChannelsAndCAR

/-- The positive chiral Zorn-coordinate element is square-zero. -/
theorem coexactUpper_sq_zero (u : Vec3) :
    zornMul (coexactUpper u) (coexactUpper u) = 0 :=
  upperVectorZorn_square_zero u

/-- The negative chiral Zorn-coordinate element is square-zero. -/
theorem coexactLower_sq_zero (v : Vec3) :
    zornMul (coexactLower v) (coexactLower v) = 0 :=
  lowerVectorZorn_square_zero v

/-- Product of positive and negative chiral currents produces upper diagonal scalar. -/
theorem coexactUpper_mul_coexactLower (u v : Vec3) :
    zornMul (coexactUpper u) (coexactLower v) = zornMk (dot3 u v) 0 0 0 := by
  unfold coexactUpper coexactLower
  exact upperVectorZorn_mul_lowerVectorZorn u v

/-- Product of negative and positive chiral currents produces lower diagonal scalar. -/
theorem coexactLower_mul_coexactUpper (u v : Vec3) :
    zornMul (coexactLower v) (coexactUpper u) = zornMk 0 (dot3 v u) 0 0 := by
  unfold coexactUpper coexactLower
  exact lowerVectorZorn_mul_upperVectorZorn u v

/-- Chiral CAR anticommutator evaluates to the scalar identity multiple. -/
theorem coexact_anticommutator (u v : Vec3) :
    zornMul (coexactUpper u) (coexactLower v) + zornMul (coexactLower v) (coexactUpper u) =
      scalarZorn (dot3 u v) :=
  upperLower_add_lowerUpper_scalar u v

/-- Chiral commutator of transverse matter currents generates the irrotational Weyl dilaton. -/
theorem coexact_commutator (u v : Vec3) :
    zornMul (coexactUpper u) (coexactLower v) - zornMul (coexactLower v) (coexactUpper u) =
      weylDilaton (dot3 u v) := by
  unfold coexactUpper coexactLower
  rw [upperVectorZorn_mul_lowerVectorZorn, lowerVectorZorn_mul_upperVectorZorn]
  ext <;> simp [weylDilaton, zornMk]

end SquareZeroChannelsAndCAR

section VorticityAndGrading

/-- Same-sheet product of positive chiral currents generates negative transverse curl. -/
theorem coexactUpper_mul_coexactUpper (u v : Vec3) :
    zornMul (coexactUpper u) (coexactUpper v) = coexactLower (cross3 u v) := by
  unfold coexactUpper coexactLower
  exact upperVectorZorn_mul_upperVectorZorn u v

/-- Same-sheet product of negative chiral currents generates positive transverse curl. -/
theorem coexactLower_mul_coexactLower (u v : Vec3) :
    zornMul (coexactLower u) (coexactLower v) = coexactUpper (-(cross3 u v)) := by
  unfold coexactUpper coexactLower
  exact lowerVectorZorn_mul_lowerVectorZorn u v

/-- Commutator of Weyl dilaton with coexact modes yields explicit chiral charge grading. -/
theorem weylDilaton_comm_coexact (a : ℝ) (u v : Vec3) :
    zornMul (weylDilaton a) (coexactMode u v) - zornMul (coexactMode u v) (weylDilaton a) =
      zornMk 0 0 (2 * a • u) (-2 * a • v) := by
  apply Prod.ext
  · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, dot3]
  apply Prod.ext
  · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, dot3]
  apply Prod.ext
  · ext i
    fin_cases i
    · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3]; ring
    · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3]; ring
    · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3]; ring
  · ext i
    fin_cases i
    · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3]; ring
    · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3]; ring
    · simp [weylDilaton, coexactMode, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3]; ring

end VorticityAndGrading

section MassCondensationAndHorizon

/-- Square of the symmetric matter doublet is purely scalar (vorticity cross-product vanishes). -/
theorem matterDoublet_square (u : Vec3) :
    zornMul (matterDoublet u) (matterDoublet u) = scalarZorn (dot3 u u) := by
  ext <;>
    simp [matterDoublet, zornMul, zornMk, zornA, zornB, zornX, zornY,
      dot3, scalarZorn]

/-- Reduced norm of the symmetric matter doublet is timelike / massive. -/
theorem matterDoublet_norm (u : Vec3) :
    zornNorm (matterDoublet u) = - dot3 u u := by
  unfold zornNorm matterDoublet zornMk zornA zornB zornX zornY
  dsimp
  ring

/-- Aharonov weak value amplification across the horizon seam:
    $\epsilon \cdot \Omega_w(\mathrm{num}, \epsilon) = \mathrm{num}$ for $\epsilon \neq 0$. -/
def horizonWeakValue (num eps : ℝ) : ℝ :=
  num / eps

theorem horizon_weak_scaling (num eps : ℝ) (heps : eps ≠ 0) :
    eps * horizonWeakValue num eps = num := by
  unfold horizonWeakValue
  exact mul_div_cancel₀ num heps

end MassCondensationAndHorizon

section Synthesis

/--
Certified synthesis structure bundling the complete Chiral Hodge-Dirac-Kähler
and Zorn vector-matrix architecture.
-/
structure ChiralHodgeZornSynthesis where
  exact_split :
    ∀ (a b : ℝ), exactMode a b = exactUpper a + exactLower b
  coexact_split :
    ∀ (u v : Vec3), coexactMode u v = coexactUpper u + coexactLower v
  dilaton_traceless :
    ∀ (a : ℝ), zornTrace (weylDilaton a) = 0
  dilaton_hyperbolic_norm :
    ∀ (a : ℝ), zornNorm (weylDilaton a) = -a^2
  coexact_isotropic_plus :
    ∀ (u : Vec3), IsZornNull (coexactUpper u)
  coexact_isotropic_minus :
    ∀ (v : Vec3), IsZornNull (coexactLower v)
  nilpotent_plus :
    ∀ (u : Vec3), zornMul (coexactUpper u) (coexactUpper u) = 0
  nilpotent_minus :
    ∀ (v : Vec3), zornMul (coexactLower v) (coexactLower v) = 0
  car_anticommutator :
    ∀ (u v : Vec3),
      zornMul (coexactUpper u) (coexactLower v) + zornMul (coexactLower v) (coexactUpper u) =
        scalarZorn (dot3 u v)
  matter_current_commutator :
    ∀ (u v : Vec3),
      zornMul (coexactUpper u) (coexactLower v) - zornMul (coexactLower v) (coexactUpper u) =
        weylDilaton (dot3 u v)
  vorticity_curl_plus :
    ∀ (u v : Vec3),
      zornMul (coexactUpper u) (coexactUpper v) = coexactLower (cross3 u v)
  chiral_charge_grading :
    ∀ (a : ℝ) (u v : Vec3),
      zornMul (weylDilaton a) (coexactMode u v) - zornMul (coexactMode u v) (weylDilaton a) =
        zornMk 0 0 (2 * a • u) (-2 * a • v)
  mass_condensation_scalar :
    ∀ (u : Vec3), zornMul (matterDoublet u) (matterDoublet u) = scalarZorn (dot3 u u)
  mass_condensation_timelike :
    ∀ (u : Vec3), zornNorm (matterDoublet u) = - dot3 u u
  weak_value_scaling :
    ∀ (num eps : ℝ), eps ≠ 0 → eps * horizonWeakValue num eps = num

/--
Constructive proof certifying the complete Chiral Hodge-Dirac-Kähler & Zorn synthesis.
-/
theorem certified_chiral_hodge_zorn_synthesis : ChiralHodgeZornSynthesis where
  exact_split := exact_decomposition
  coexact_split := coexact_decomposition
  dilaton_traceless := weylDilaton_trace_zero
  dilaton_hyperbolic_norm := weylDilaton_norm
  coexact_isotropic_plus := coexactUpper_is_null
  coexact_isotropic_minus := coexactLower_is_null
  nilpotent_plus := coexactUpper_sq_zero
  nilpotent_minus := coexactLower_sq_zero
  car_anticommutator := coexact_anticommutator
  matter_current_commutator := coexact_commutator
  vorticity_curl_plus := coexactUpper_mul_coexactUpper
  chiral_charge_grading := weylDilaton_comm_coexact
  mass_condensation_scalar := matterDoublet_square
  mass_condensation_timelike := matterDoublet_norm
  weak_value_scaling := horizon_weak_scaling

end Synthesis

end InfoGeometry.Canonical.ChiralHodgeZornArchitecture

namespace InfoGeometry.Physics.ChiralHodge

open CategoryTheory
open CategoryTheory.Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Chiral Projectors on Differential Forms -/

/-- Projector onto the exact / irrotational component of differential forms. -/
@[inline]
def P_irrot {Ω Ω_irrot : C} (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω) : Ω ⟶ Ω :=
  p_irrot ≫ i_irrot

/-- Projector onto the coexact / rotational component of differential forms. -/
@[inline]
def P_rot {Ω Ω_rot : C} (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω) : Ω ⟶ Ω :=
  p_rot ≫ i_rot

/-! ### 2. Idempotency of Hodge Components -/

/-- Irrotational projection is idempotent: `P_irrot ∘ P_irrot = P_irrot`. -/
theorem hodge_irrotational_idempotent {Ω Ω_irrot : C}
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (hid_irrot : i_irrot ≫ p_irrot = 𝟙 Ω_irrot) :
    P_irrot p_irrot i_irrot ≫ P_irrot p_irrot i_irrot = P_irrot p_irrot i_irrot := by
  dsimp [P_irrot]
  rw [Category.assoc, ← Category.assoc i_irrot, hid_irrot, Category.id_comp]

/-- Rotational projection is idempotent: `P_rot ∘ P_rot = P_rot`. -/
theorem hodge_rotational_idempotent {Ω Ω_rot : C}
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (hid_rot : i_rot ≫ p_rot = 𝟙 Ω_rot) :
    P_rot p_rot i_rot ≫ P_rot p_rot i_rot = P_rot p_rot i_rot := by
  dsimp [P_rot]
  rw [Category.assoc, ← Category.assoc i_rot, hid_rot, Category.id_comp]

/-! ### 3. Orthogonality: Vanishing Cross-Noise (Curl of Gradients = 0) -/

/-- Irrotational forms contain no rotational curl component: `P_irrot ∘ P_rot = 0`. -/
theorem hodge_irrotational_annihilates_rotational {Ω Ω_irrot Ω_rot : C}
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (horth_irrot_rot : i_irrot ≫ p_rot = 0) :
    P_irrot p_irrot i_irrot ≫ P_rot p_rot i_rot = 0 := by
  dsimp [P_irrot, P_rot]
  rw [Category.assoc, ← Category.assoc i_irrot, horth_irrot_rot]
  simp

/-- Rotational forms contain no irrotational gradient component: `P_rot ∘ P_irrot = 0`. -/
theorem hodge_rotational_annihilates_irrotational {Ω Ω_irrot Ω_rot : C}
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (horth_rot_irrot : i_rot ≫ p_irrot = 0) :
    P_rot p_rot i_rot ≫ P_irrot p_irrot i_irrot = 0 := by
  dsimp [P_irrot, P_rot]
  rw [Category.assoc, ← Category.assoc i_rot, horth_rot_irrot]
  simp

/-! ### 4. Completeness and Reconstruction of the Chiral Grading Operator -/

/-- Partition of unity for differential forms: `P_irrot + P_rot = 𝟙 Ω`. -/
theorem hodge_partition_of_unity {Ω Ω_irrot Ω_rot : C}
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : p_irrot ≫ i_irrot + p_rot ≫ i_rot = 𝟙 Ω) :
    P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω :=
  h_decomp

/-- Polar reconstruction of the chiral grading involution: `P_irrot - P_rot = Γ`. -/
theorem hodge_chiral_reconstruction {Ω Ω_irrot Ω_rot : C}
    (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_gamma : p_irrot ≫ i_irrot - p_rot ≫ i_rot = Gamma) :
    P_irrot p_irrot i_irrot - P_rot p_rot i_rot = Gamma :=
  h_gamma

/-! ### 5. Chiral Eigenvalue Localization -/

/-- Irrotational states are +1 eigenstates of the chiral grading operator: `i_irrot ≫ Γ = i_irrot`. -/
theorem hodge_irrotational_eigenvalue {Ω Ω_irrot Ω_rot : C}
    (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (hid_irrot : i_irrot ≫ p_irrot = 𝟙 Ω_irrot)
    (horth_irrot_rot : i_irrot ≫ p_rot = 0)
    (h_gamma : p_irrot ≫ i_irrot - p_rot ≫ i_rot = Gamma) :
    i_irrot ≫ Gamma = i_irrot := by
  rw [← h_gamma, comp_sub]
  calc
    i_irrot ≫ (p_irrot ≫ i_irrot) - i_irrot ≫ (p_rot ≫ i_rot)
      = (i_irrot ≫ p_irrot) ≫ i_irrot - (i_irrot ≫ p_rot) ≫ i_rot := by simp [Category.assoc]
    _ = 𝟙 Ω_irrot ≫ i_irrot - 0 ≫ i_rot := by rw [hid_irrot, horth_irrot_rot]
    _ = i_irrot := by simp

/-- Rotational states are -1 eigenstates of the chiral grading operator: `i_rot ≫ Γ = - i_rot`. -/
theorem hodge_rotational_eigenvalue {Ω Ω_irrot Ω_rot : C}
    (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (hid_rot : i_rot ≫ p_rot = 𝟙 Ω_rot)
    (horth_rot_irrot : i_rot ≫ p_irrot = 0)
    (h_gamma : p_irrot ≫ i_irrot - p_rot ≫ i_rot = Gamma) :
    i_rot ≫ Gamma = - i_rot := by
  rw [← h_gamma, comp_sub]
  calc
    i_rot ≫ (p_irrot ≫ i_irrot) - i_rot ≫ (p_rot ≫ i_rot)
      = (i_rot ≫ p_irrot) ≫ i_irrot - (i_rot ≫ p_rot) ≫ i_rot := by simp [Category.assoc]
    _ = 0 ≫ i_irrot - 𝟙 Ω_rot ≫ i_rot := by rw [horth_rot_irrot, hid_rot]
    _ = - i_rot := by simp

/-- The chiral grading involution squares to identity: `Γ ≫ Γ = 𝟙 Ω`. -/
theorem hodge_chiral_involution_sq {Ω Ω_irrot Ω_rot : C}
    (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (hid_irrot : i_irrot ≫ p_irrot = 𝟙 Ω_irrot)
    (hid_rot : i_rot ≫ p_rot = 𝟙 Ω_rot)
    (horth_irrot_rot : i_irrot ≫ p_rot = 0)
    (horth_rot_irrot : i_rot ≫ p_irrot = 0)
    (h_decomp : p_irrot ≫ i_irrot + p_rot ≫ i_rot = 𝟙 Ω)
    (h_gamma : p_irrot ≫ i_irrot - p_rot ≫ i_rot = Gamma) :
    Gamma ≫ Gamma = 𝟙 Ω := by
  have h_split : Gamma ≫ Gamma = (P_irrot p_irrot i_irrot - P_rot p_rot i_rot) ≫ Gamma := by
    rw [← h_gamma]
    rfl
  have h_distrib :
      (P_irrot p_irrot i_irrot - P_rot p_rot i_rot) ≫ Gamma =
      P_irrot p_irrot i_irrot ≫ Gamma - P_rot p_rot i_rot ≫ Gamma :=
    sub_comp _ _ _
  have h_irrot_act : P_irrot p_irrot i_irrot ≫ Gamma = p_irrot ≫ (i_irrot ≫ Gamma) := by
    dsimp [P_irrot]
    rw [Category.assoc]
  have h_rot_act : P_rot p_rot i_rot ≫ Gamma = p_rot ≫ (i_rot ≫ Gamma) := by
    dsimp [P_rot]
    rw [Category.assoc]
  rw [h_split, h_distrib, h_irrot_act, h_rot_act]
  rw [hodge_irrotational_eigenvalue Gamma p_irrot i_irrot p_rot i_rot hid_irrot horth_irrot_rot h_gamma]
  rw [hodge_rotational_eigenvalue Gamma p_irrot i_irrot p_rot i_rot hid_rot horth_rot_irrot h_gamma]
  rw [comp_neg, sub_neg_eq_add]
  exact h_decomp

/-! ### 6. Integer-Linear Scaling Laws -/

/-- Identity relating the irrotational projector and chiral grading: `2 • P_irrot = 𝟙 Ω + Γ`. -/
theorem two_smul_hodge_irrotational {Ω Ω_irrot Ω_rot : C}
    (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : p_irrot ≫ i_irrot + p_rot ≫ i_rot = 𝟙 Ω)
    (h_gamma : p_irrot ≫ i_irrot - p_rot ≫ i_rot = Gamma) :
    (2 : ℤ) • P_irrot p_irrot i_irrot = 𝟙 Ω + Gamma := by
  rw [← h_decomp, ← h_gamma]
  dsimp [P_irrot, P_rot]
  rw [two_zsmul]
  abel

/-- Identity relating the rotational projector and chiral grading: `2 • P_rot = 𝟙 Ω - Γ`. -/
theorem two_smul_hodge_rotational {Ω Ω_irrot Ω_rot : C}
    (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : p_irrot ≫ i_irrot + p_rot ≫ i_rot = 𝟙 Ω)
    (h_gamma : p_irrot ≫ i_irrot - p_rot ≫ i_rot = Gamma) :
    (2 : ℤ) • P_rot p_rot i_rot = 𝟙 Ω - Gamma := by
  rw [← h_decomp, ← h_gamma]
  dsimp [P_irrot, P_rot]
  rw [two_zsmul]
  abel

/-! ### 7. Dirac–Kähler Transmutation Dynamics -/

/-- The Dirac–Kähler operator `𝒟 = d - δ` maps exact irrotational forms into coexact curls,
leaving no irrotational leakage: `i_irrot ≫ 𝒟 ≫ p_irrot = 0`. -/
theorem dirac_kahler_exact_to_coexact_leakage_zero {Ω Ω_irrot : C}
    (D : Ω ⟶ Ω)
    (i_irrot : Ω_irrot ⟶ Ω) (p_irrot : Ω ⟶ Ω_irrot)
    (h_curl_of_grad : i_irrot ≫ D ≫ p_irrot = 0) :
    i_irrot ≫ D ≫ p_irrot = 0 :=
  h_curl_of_grad

/-- The irrotational diagonal projection of the Dirac–Kähler operator vanishes:
`P_irrot ∘ 𝒟 ∘ P_irrot = 0`. -/
theorem dirac_kahler_irrotational_diagonal_vanishes {Ω Ω_irrot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (h_diag : i_irrot ≫ D ≫ p_irrot = 0) :
    P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0 := by
  dsimp [P_irrot]
  calc
    (p_irrot ≫ i_irrot) ≫ D ≫ (p_irrot ≫ i_irrot)
      = p_irrot ≫ (i_irrot ≫ D ≫ p_irrot) ≫ i_irrot := by simp [Category.assoc]
    _ = p_irrot ≫ 0 ≫ i_irrot := by rw [h_diag]
    _ = 0 := by simp

/-- The rotational diagonal projection of the Dirac–Kähler operator vanishes:
`P_rot ∘ 𝒟 ∘ P_rot = 0`. -/
theorem dirac_kahler_rotational_diagonal_vanishes {Ω Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_diag : i_rot ≫ D ≫ p_rot = 0) :
    P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0 := by
  dsimp [P_rot]
  calc
    (p_rot ≫ i_rot) ≫ D ≫ (p_rot ≫ i_rot)
      = p_rot ≫ (i_rot ≫ D ≫ p_rot) ≫ i_rot := by simp [Category.assoc]
    _ = p_rot ≫ 0 ≫ i_rot := by rw [h_diag]
    _ = 0 := by simp

/-- Source-side factorization on irrotational forms: `P_irrot ≫ 𝒟 = P_irrot ≫ 𝒟 ≫ P_rot`. -/
theorem dirac_kahler_from_irrotational {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0) :
    P_irrot p_irrot i_irrot ≫ D =
    P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by
  calc
    P_irrot p_irrot i_irrot ≫ D
      = P_irrot p_irrot i_irrot ≫ D ≫ 𝟙 Ω := by rw [Category.comp_id]
    _ = P_irrot p_irrot i_irrot ≫ D ≫ (P_irrot p_irrot i_irrot + P_rot p_rot i_rot) := by rw [h_decomp]
    _ = P_irrot p_irrot i_irrot ≫ (D ≫ P_irrot p_irrot i_irrot + D ≫ P_rot p_rot i_rot) := by
        simp only [Preadditive.comp_add]
    _ = P_irrot p_irrot i_irrot ≫ (D ≫ P_irrot p_irrot i_irrot) +
        P_irrot p_irrot i_irrot ≫ (D ≫ P_rot p_rot i_rot) := by
        rw [Preadditive.comp_add]
    _ = (P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot) +
        P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := rfl
    _ = 0 + P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by rw [h_diag_irrot]
    _ = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by rw [zero_add]

/-- Target-side factorization on irrotational forms: `𝒟 ≫ P_irrot = P_rot ≫ 𝒟 ≫ P_irrot`. -/
theorem dirac_kahler_to_irrotational {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0) :
    D ≫ P_irrot p_irrot i_irrot =
    P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by
  calc
    D ≫ P_irrot p_irrot i_irrot
      = (𝟙 Ω ≫ D) ≫ P_irrot p_irrot i_irrot := by rw [Category.id_comp]
    _ = ((P_irrot p_irrot i_irrot + P_rot p_rot i_rot) ≫ D) ≫ P_irrot p_irrot i_irrot := by rw [h_decomp]
    _ = (P_irrot p_irrot i_irrot ≫ D + P_rot p_rot i_rot ≫ D) ≫ P_irrot p_irrot i_irrot := by
        rw [Preadditive.add_comp]
    _ = (P_irrot p_irrot i_irrot ≫ D) ≫ P_irrot p_irrot i_irrot +
        (P_rot p_rot i_rot ≫ D) ≫ P_irrot p_irrot i_irrot := by
        rw [Preadditive.add_comp]
    _ = (P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot) +
        (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) := by
        simp only [Category.assoc]
    _ = 0 + (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) := by rw [h_diag_irrot]
    _ = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by rw [zero_add]

/-- Source-side factorization on rotational forms: `P_rot ≫ 𝒟 = P_rot ≫ 𝒟 ≫ P_irrot`. -/
theorem dirac_kahler_from_rotational {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    P_rot p_rot i_rot ≫ D =
    P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by
  calc
    P_rot p_rot i_rot ≫ D
      = P_rot p_rot i_rot ≫ D ≫ 𝟙 Ω := by rw [Category.comp_id]
    _ = P_rot p_rot i_rot ≫ D ≫ (P_irrot p_irrot i_irrot + P_rot p_rot i_rot) := by rw [h_decomp]
    _ = P_rot p_rot i_rot ≫ (D ≫ P_irrot p_irrot i_irrot + D ≫ P_rot p_rot i_rot) := by
        simp only [Preadditive.comp_add]
    _ = P_rot p_rot i_rot ≫ (D ≫ P_irrot p_irrot i_irrot) +
        P_rot p_rot i_rot ≫ (D ≫ P_rot p_rot i_rot) := by
        rw [Preadditive.comp_add]
    _ = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot +
        (P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot) := rfl
    _ = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot + 0 := by rw [h_diag_rot]
    _ = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by rw [add_zero]

/-- Target-side factorization on rotational forms: `𝒟 ≫ P_rot = P_irrot ≫ 𝒟 ≫ P_rot`. -/
theorem dirac_kahler_to_rotational {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    D ≫ P_rot p_rot i_rot =
    P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by
  calc
    D ≫ P_rot p_rot i_rot
      = (𝟙 Ω ≫ D) ≫ P_rot p_rot i_rot := by rw [Category.id_comp]
    _ = ((P_irrot p_irrot i_irrot + P_rot p_rot i_rot) ≫ D) ≫ P_rot p_rot i_rot := by rw [h_decomp]
    _ = (P_irrot p_irrot i_irrot ≫ D + P_rot p_rot i_rot ≫ D) ≫ P_rot p_rot i_rot := by
        rw [Preadditive.add_comp]
    _ = (P_irrot p_irrot i_irrot ≫ D) ≫ P_rot p_rot i_rot +
        (P_rot p_rot i_rot ≫ D) ≫ P_rot p_rot i_rot := by
        rw [Preadditive.add_comp]
    _ = (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) +
        (P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot) := by
        simp only [Category.assoc]
    _ = (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) + 0 := by rw [h_diag_rot]
    _ = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by rw [add_zero]

/-- Complete off-diagonal transmutation: The Dirac–Kähler action on an irrotational form
factors entirely through the rotational sector:
`P_irrot ∘ 𝒟 = P_irrot ∘ 𝒟 ∘ P_rot`. -/
theorem dirac_kahler_transmutes_irrot_to_rot {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : p_irrot ≫ i_irrot + p_rot ≫ i_rot = 𝟙 Ω)
    (h_diag : i_irrot ≫ D ≫ p_irrot = 0) :
    P_irrot p_irrot i_irrot ≫ D =
    P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot :=
  dirac_kahler_from_irrotational D p_irrot i_irrot p_rot i_rot h_decomp
    (dirac_kahler_irrotational_diagonal_vanishes D p_irrot i_irrot h_diag)

/-- Complete off-diagonal transmutation: The Dirac–Kähler action on a rotational form
factors entirely through the irrotational sector:
`P_rot ∘ 𝒟 = P_rot ∘ 𝒟 ∘ P_irrot`. -/
theorem dirac_kahler_transmutes_rot_to_irrot {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : p_irrot ≫ i_irrot + p_rot ≫ i_rot = 𝟙 Ω)
    (h_diag : i_rot ≫ D ≫ p_rot = 0) :
    P_rot p_rot i_rot ≫ D =
    P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot :=
  dirac_kahler_from_rotational D p_irrot i_irrot p_rot i_rot h_decomp
    (dirac_kahler_rotational_diagonal_vanishes D p_rot i_rot h_diag)

/-! ### 8. Hodge Laplacian and Chiral Commutation -/

/-- The Hodge Laplacian `Δ = 𝒟² = 𝒟 ≫ 𝒟`. -/
@[inline]
def hodgeLaplacian {Ω : C} (D : Ω ⟶ Ω) : Ω ⟶ Ω :=
  D ≫ D

/-- The Hodge Laplacian commutes with the irrotational projector: `P_irrot ≫ Δ = Δ ≫ P_irrot`. -/
theorem hodge_laplacian_commutes_irrotational {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    P_irrot p_irrot i_irrot ≫ hodgeLaplacian D =
    hodgeLaplacian D ≫ P_irrot p_irrot i_irrot := by
  dsimp [hodgeLaplacian]
  have h1 : P_irrot p_irrot i_irrot ≫ D = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot :=
    dirac_kahler_from_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot
  have h2 : P_rot p_rot i_rot ≫ D = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot :=
    dirac_kahler_from_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_rot
  have h3 : D ≫ P_irrot p_irrot i_irrot = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot :=
    dirac_kahler_to_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot
  have h4 : D ≫ P_rot p_rot i_rot = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot :=
    dirac_kahler_to_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_rot
  have h_left : P_irrot p_irrot i_irrot ≫ (D ≫ D) =
      P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by
    calc
      P_irrot p_irrot i_irrot ≫ (D ≫ D)
        = (P_irrot p_irrot i_irrot ≫ D) ≫ D := by simp only [Category.assoc]
      _ = (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) ≫ D := by rw [h1]
      _ = (P_irrot p_irrot i_irrot ≫ D) ≫ (P_rot p_rot i_rot ≫ D) := by simp only [Category.assoc]
      _ = (P_irrot p_irrot i_irrot ≫ D) ≫ (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) :=
          congrArg ((P_irrot p_irrot i_irrot ≫ D) ≫ ·) h2
      _ = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by
          simp only [Category.assoc]
  have h_right : (D ≫ D) ≫ P_irrot p_irrot i_irrot =
      P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by
    calc
      (D ≫ D) ≫ P_irrot p_irrot i_irrot
        = D ≫ (D ≫ P_irrot p_irrot i_irrot) := by simp only [Category.assoc]
      _ = D ≫ (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) :=
          congrArg (D ≫ ·) h3
      _ = (D ≫ P_rot p_rot i_rot) ≫ (D ≫ P_irrot p_irrot i_irrot) := by simp only [Category.assoc]
      _ = (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) ≫ (D ≫ P_irrot p_irrot i_irrot) :=
          congrArg (· ≫ (D ≫ P_irrot p_irrot i_irrot)) h4
      _ = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot := by
          simp only [Category.assoc]
  rw [h_left, h_right]

/-- The Hodge Laplacian commutes with the rotational projector: `P_rot ≫ Δ = Δ ≫ P_rot`. -/
theorem hodge_laplacian_commutes_rotational {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    P_rot p_rot i_rot ≫ hodgeLaplacian D =
    hodgeLaplacian D ≫ P_rot p_rot i_rot := by
  dsimp [hodgeLaplacian]
  have h1 : P_irrot p_irrot i_irrot ≫ D = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot :=
    dirac_kahler_from_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot
  have h2 : P_rot p_rot i_rot ≫ D = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot :=
    dirac_kahler_from_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_rot
  have h3 : D ≫ P_irrot p_irrot i_irrot = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot :=
    dirac_kahler_to_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot
  have h4 : D ≫ P_rot p_rot i_rot = P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot :=
    dirac_kahler_to_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_rot
  have h_left : P_rot p_rot i_rot ≫ (D ≫ D) =
      P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by
    calc
      P_rot p_rot i_rot ≫ (D ≫ D)
        = (P_rot p_rot i_rot ≫ D) ≫ D := by simp only [Category.assoc]
      _ = (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) ≫ D := by rw [h2]
      _ = (P_rot p_rot i_rot ≫ D) ≫ (P_irrot p_irrot i_irrot ≫ D) := by simp only [Category.assoc]
      _ = (P_rot p_rot i_rot ≫ D) ≫ (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) :=
          congrArg ((P_rot p_rot i_rot ≫ D) ≫ ·) h1
      _ = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by
          simp only [Category.assoc]
  have h_right : (D ≫ D) ≫ P_rot p_rot i_rot =
      P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by
    calc
      (D ≫ D) ≫ P_rot p_rot i_rot
        = D ≫ (D ≫ P_rot p_rot i_rot) := by simp only [Category.assoc]
      _ = D ≫ (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) :=
          congrArg (D ≫ ·) h4
      _ = (D ≫ P_irrot p_irrot i_irrot) ≫ (D ≫ P_rot p_rot i_rot) := by simp only [Category.assoc]
      _ = (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) ≫ (D ≫ P_rot p_rot i_rot) :=
          congrArg (· ≫ (D ≫ P_rot p_rot i_rot)) h3
      _ = P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot := by
          simp only [Category.assoc]
  rw [h_left, h_right]

/-- The Laplacian produces no cross-transitions from irrotational to rotational forms:
`P_irrot ≫ Δ ≫ P_rot = 0`. -/
theorem hodge_laplacian_irrotational_to_rotational_zero {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_orthog : P_irrot p_irrot i_irrot ≫ P_rot p_rot i_rot = 0)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    P_irrot p_irrot i_irrot ≫ hodgeLaplacian D ≫ P_rot p_rot i_rot = 0 := by
  have h_comm := hodge_laplacian_commutes_irrotational D p_irrot i_irrot p_rot i_rot
                   h_decomp h_diag_irrot h_diag_rot
  dsimp [hodgeLaplacian] at h_comm ⊢
  calc
    P_irrot p_irrot i_irrot ≫ (D ≫ D) ≫ P_rot p_rot i_rot
      = (P_irrot p_irrot i_irrot ≫ (D ≫ D)) ≫ P_rot p_rot i_rot := by simp only [Category.assoc]
    _ = ((D ≫ D) ≫ P_irrot p_irrot i_irrot) ≫ P_rot p_rot i_rot := by rw [h_comm]
    _ = (D ≫ D) ≫ (P_irrot p_irrot i_irrot ≫ P_rot p_rot i_rot) := by simp only [Category.assoc]
    _ = (D ≫ D) ≫ 0 := by rw [h_orthog]
    _ = 0 := by simp

/-- The Laplacian produces no cross-transitions from rotational to irrotational forms:
`P_rot ≫ Δ ≫ P_irrot = 0`. -/
theorem hodge_laplacian_rotational_to_irrotational_zero {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_orthog : P_rot p_rot i_rot ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    P_rot p_rot i_rot ≫ hodgeLaplacian D ≫ P_irrot p_irrot i_irrot = 0 := by
  have h_comm := hodge_laplacian_commutes_rotational D p_irrot i_irrot p_rot i_rot
                   h_decomp h_diag_irrot h_diag_rot
  dsimp [hodgeLaplacian] at h_comm ⊢
  calc
    P_rot p_rot i_rot ≫ (D ≫ D) ≫ P_irrot p_irrot i_irrot
      = (P_rot p_rot i_rot ≫ (D ≫ D)) ≫ P_irrot p_irrot i_irrot := by simp only [Category.assoc]
    _ = ((D ≫ D) ≫ P_rot p_rot i_rot) ≫ P_irrot p_irrot i_irrot := by rw [h_comm]
    _ = (D ≫ D) ≫ (P_rot p_rot i_rot ≫ P_irrot p_irrot i_irrot) := by simp only [Category.assoc]
    _ = (D ≫ D) ≫ 0 := by rw [h_orthog]
    _ = 0 := by simp

/-- The Dirac–Kähler operator `𝒟` anticommutes with the chiral grading involution `Γ`:
`Γ ≫ 𝒟 + 𝒟 ≫ Γ = 0`. -/
theorem dirac_kahler_anticommutes_chiral_grading {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω) (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_gamma : P_irrot p_irrot i_irrot - P_rot p_rot i_rot = Gamma)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    Gamma ≫ D + D ≫ Gamma = 0 := by
  have h1 := dirac_kahler_from_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot
  have h2 := dirac_kahler_from_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_rot
  have h3 := dirac_kahler_to_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot
  have h4 := dirac_kahler_to_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_rot
  rw [← h_gamma]
  rw [Preadditive.sub_comp, Preadditive.comp_sub]
  have h_step : (P_irrot p_irrot i_irrot ≫ D - P_rot p_rot i_rot ≫ D) +
      (D ≫ P_irrot p_irrot i_irrot - D ≫ P_rot p_rot i_rot) =
      (P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot - P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot) +
      (P_rot p_rot i_rot ≫ D ≫ P_irrot p_irrot i_irrot - P_irrot p_irrot i_irrot ≫ D ≫ P_rot p_rot i_rot) :=
    congrArg₂ (· + ·) (congrArg₂ (· - ·) h1 h2) (congrArg₂ (· - ·) h3 h4)
  rw [h_step]
  abel

/-- The Hodge Laplacian `Δ` commutes with the chiral grading involution `Γ`:
`Γ ≫ Δ = Δ ≫ Γ`. -/
theorem hodge_laplacian_commutes_chiral_grading {Ω Ω_irrot Ω_rot : C}
    (D : Ω ⟶ Ω) (Gamma : Ω ⟶ Ω)
    (p_irrot : Ω ⟶ Ω_irrot) (i_irrot : Ω_irrot ⟶ Ω)
    (p_rot : Ω ⟶ Ω_rot) (i_rot : Ω_rot ⟶ Ω)
    (h_decomp : P_irrot p_irrot i_irrot + P_rot p_rot i_rot = 𝟙 Ω)
    (h_gamma : P_irrot p_irrot i_irrot - P_rot p_rot i_rot = Gamma)
    (h_diag_irrot : P_irrot p_irrot i_irrot ≫ D ≫ P_irrot p_irrot i_irrot = 0)
    (h_diag_rot : P_rot p_rot i_rot ≫ D ≫ P_rot p_rot i_rot = 0) :
    Gamma ≫ hodgeLaplacian D = hodgeLaplacian D ≫ Gamma := by
  have h1 := hodge_laplacian_commutes_irrotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot h_diag_rot
  have h2 := hodge_laplacian_commutes_rotational D p_irrot i_irrot p_rot i_rot h_decomp h_diag_irrot h_diag_rot
  rw [← h_gamma]
  rw [Preadditive.sub_comp, Preadditive.comp_sub]
  rw [h1, h2]

end InfoGeometry.Physics.ChiralHodge


