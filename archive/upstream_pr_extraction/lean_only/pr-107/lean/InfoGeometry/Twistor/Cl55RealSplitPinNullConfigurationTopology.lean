import InfoGeometry.Twistor.Cl55RealSplitPinNullConfiguration
import InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

/-!
# Topological split-Pin symmetry of `Q55` null configurations

The concrete real split-Pin action on `V55` is linear and therefore
continuous by finite dimensionality.  Instantiating the existing native
projectivization/configuration topology theorems shows that each split-Pin
element acts by homeomorphisms on the projective `Q55` null boundary and on
its ordered and unordered marked-configuration carriers.

This remains an action by global homeomorphisms of the carrier spaces.  It is
not an exchange path, a fundamental-group computation, or monodromy.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationTopology

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullArtinBraid
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

/-- Constant generator family exposing one native split-Pin transformation to
the generic configuration-topology API. -/
private def splitPinLinearFamily (g : realSplitPin55) :
    ℕ → (V55 ≃ₗ[ℝ] V55) :=
  fun _ => (realSplitPinNativeOrthogonalAction g).toLinearEquiv

private theorem splitPinLinearFamily_preserves_Q55 (g : realSplitPin55) :
    ∀ i v, Q55 (splitPinLinearFamily g i v) = Q55 v := by
  intro i v
  exact (realSplitPinNativeOrthogonalAction g).map_app v

private theorem splitPinLinearFamily_continuous (g : realSplitPin55) :
    Continuous ((splitPinLinearFamily g 0 : V55 → V55)) := by
  exact LinearMap.continuous_of_finiteDimensional
    (splitPinLinearFamily g 0).toLinearMap

private theorem splitPinLinearFamily_symm_continuous (g : realSplitPin55) :
    Continuous (((splitPinLinearFamily g 0).symm : V55 → V55)) := by
  exact LinearMap.continuous_of_finiteDimensional
    (splitPinLinearFamily g 0).symm.toLinearMap

/-- The concrete split-Pin null action is the generic projectivized quadratic
isometry action used by the topology owner. -/
theorem realSplitPinNullAction_eq_nullProjectiveGenerator
    (g : realSplitPin55) (p : TwistorSpace Q55) :
    realSplitPinNullAction g p =
      nullProjectiveGenerator Q55 (splitPinLinearFamily g)
        (splitPinLinearFamily_preserves_Q55 g) 0 p := by
  apply Subtype.ext
  rfl

/-- Every real split-Pin element acts homeomorphically on the projective
`Q55` null boundary. -/
theorem realSplitPinNullAction_isHomeomorph (g : realSplitPin55) :
    @IsHomeomorph (TwistorSpace Q55) (TwistorSpace Q55)
      (nullBoundaryTopology Q55) (nullBoundaryTopology Q55)
      (realSplitPinNullAction g) := by
  have h := nullProjectiveGenerator_isHomeomorph Q55
    (splitPinLinearFamily g) (splitPinLinearFamily_preserves_Q55 g) 0
    (splitPinLinearFamily_continuous g)
    (splitPinLinearFamily_symm_continuous g)
  convert h using 1

/-- Actual homeomorphism representing one real split-Pin element on the
projective `Q55` null boundary. -/
def realSplitPinNullActionHomeomorph
    (g : realSplitPin55) :
    let _ := nullBoundaryTopology Q55
    TwistorSpace Q55 ≃ₜ TwistorSpace Q55 := by
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  exact (realSplitPinNullAction_isHomeomorph g).homeomorph _

@[simp] theorem realSplitPinNullActionHomeomorph_apply
    (g : realSplitPin55) (p : TwistorSpace Q55) :
    let _ := nullBoundaryTopology Q55
    realSplitPinNullActionHomeomorph g p = realSplitPinNullAction g p := by
  rfl

/-- The concrete componentwise split-Pin action agrees with the existing
generic ordered-configuration map. -/
theorem realSplitPinOrderedNullAction_eq_mapOrderedConfiguration
    (g : realSplitPin55) (n : ℕ) (p : Ordered Q55 n) :
    realSplitPinOrderedNullAction n g p =
      mapOrderedConfiguration Q55 (splitPinLinearFamily g)
        (splitPinLinearFamily_preserves_Q55 g) 0 n p := by
  apply Subtype.ext
  funext i
  apply realSplitPinNullAction_eq_nullProjectiveGenerator

/-- Every real split-Pin element acts homeomorphically on ordered distinct
projective-null configurations. -/
theorem realSplitPinOrderedNullAction_isHomeomorph
    (g : realSplitPin55) (n : ℕ) :
    @IsHomeomorph (Ordered Q55 n) (Ordered Q55 n)
      (orderedConfigurationTopology Q55 n)
      (orderedConfigurationTopology Q55 n)
      (realSplitPinOrderedNullAction n g) := by
  have h := mapOrderedConfiguration_isHomeomorph Q55
    (splitPinLinearFamily g) (splitPinLinearFamily_preserves_Q55 g) 0 n
    (splitPinLinearFamily_continuous g)
    (splitPinLinearFamily_symm_continuous g)
  convert h using 1

/-- Actual homeomorphism representing one real split-Pin element on ordered
distinct projective-null configurations. -/
def realSplitPinOrderedNullActionHomeomorph
    (g : realSplitPin55) (n : ℕ) :
    let _ := orderedConfigurationTopology Q55 n
    Ordered Q55 n ≃ₜ Ordered Q55 n := by
  letI : TopologicalSpace (Ordered Q55 n) :=
    orderedConfigurationTopology Q55 n
  exact (realSplitPinOrderedNullAction_isHomeomorph g n).homeomorph _

@[simp] theorem realSplitPinOrderedNullActionHomeomorph_apply
    (g : realSplitPin55) (n : ℕ) (p : Ordered Q55 n) :
    let _ := orderedConfigurationTopology Q55 n
    realSplitPinOrderedNullActionHomeomorph g n p =
      realSplitPinOrderedNullAction n g p := by
  rfl

instance realSplitPinNullMulAction :
    MulAction (↥realSplitPin55) (TwistorSpace Q55) where
  smul g p := realSplitPinNullAction g p
  one_smul p := by
    exact congrArg (fun e : Equiv.Perm (TwistorSpace Q55) => e p)
      (map_one (realSplitPinNullAction))
  mul_smul g h p := by
    change realSplitPinNullAction (g * h) p =
      realSplitPinNullAction g (realSplitPinNullAction h p)
    exact congrArg (fun e : Equiv.Perm (TwistorSpace Q55) => e p)
      (map_mul (realSplitPinNullAction) g h)

instance realSplitPinOrderedNullMulAction (n : ℕ) :
    MulAction (↥realSplitPin55) (Ordered Q55 n) where
  smul g p := realSplitPinOrderedNullAction n g p
  one_smul p := by
    exact congrArg (fun e : Equiv.Perm (Ordered Q55 n) => e p)
      (map_one (realSplitPinOrderedNullAction n))
  mul_smul g h p := by
    change realSplitPinOrderedNullAction n (g * h) p =
      realSplitPinOrderedNullAction n g
        (realSplitPinOrderedNullAction n h p)
    exact congrArg (fun e : Equiv.Perm (Ordered Q55 n) => e p)
      (map_mul (realSplitPinOrderedNullAction n) g h)

@[simp] theorem realSplitPinNullActionHomeomorph_smul
    (g : realSplitPin55) (p : TwistorSpace Q55) :
    let _ := nullBoundaryTopology Q55
    realSplitPinNullActionHomeomorph g p = g • p := by
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  rw [realSplitPinNullActionHomeomorph_apply]
  rfl

@[simp] theorem realSplitPinOrderedNullActionHomeomorph_smul
    (g : realSplitPin55) (n : ℕ) (p : Ordered Q55 n) :
    let _ := orderedConfigurationTopology Q55 n
    realSplitPinOrderedNullActionHomeomorph g n p = g • p := by
  letI : TopologicalSpace (Ordered Q55 n) :=
    orderedConfigurationTopology Q55 n
  rw [realSplitPinOrderedNullActionHomeomorph_apply]
  rfl

/-- The descended split-Pin action agrees with the existing generic
unordered-configuration quotient map. -/
theorem realSplitPinUnorderedNullAction_eq_mapUnorderedConfiguration
    (g : realSplitPin55) (n : ℕ) (p : Unordered Q55 n) :
    realSplitPinUnorderedNullAction n g p =
      mapUnorderedConfiguration Q55 (splitPinLinearFamily g)
        (splitPinLinearFamily_preserves_Q55 g) 0 n p := by
  refine Quotient.inductionOn p ?_
  intro p
  exact congrArg Quotient.mk'
    (realSplitPinOrderedNullAction_eq_mapOrderedConfiguration g n p)

/-- Every real split-Pin element acts homeomorphically on the unordered
marked-null configuration quotient. -/
theorem realSplitPinUnorderedNullAction_isHomeomorph
    (g : realSplitPin55) (n : ℕ) :
    @IsHomeomorph (Unordered Q55 n) (Unordered Q55 n)
      (unorderedConfigurationTopology Q55 n)
      (unorderedConfigurationTopology Q55 n)
      (realSplitPinUnorderedNullAction n g) := by
  have h := mapUnorderedConfiguration_isHomeomorph Q55
    (splitPinLinearFamily g) (splitPinLinearFamily_preserves_Q55 g) 0 n
    (splitPinLinearFamily_continuous g)
    (splitPinLinearFamily_symm_continuous g)
  convert h using 1

/-- Actual homeomorphism representing one real split-Pin element on the
unordered marked-null configuration carrier. -/
def realSplitPinUnorderedNullHomeomorph
    (g : realSplitPin55) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    Unordered Q55 n ≃ₜ Unordered Q55 n := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact (realSplitPinUnorderedNullAction_isHomeomorph g n).homeomorph _

@[simp] theorem realSplitPinUnorderedNullHomeomorph_apply
    (g : realSplitPin55) (n : ℕ) (p : Unordered Q55 n) :
    let _ := unorderedConfigurationTopology Q55 n
    realSplitPinUnorderedNullHomeomorph g n p =
      realSplitPinUnorderedNullAction n g p := by
  rfl

@[simp] theorem realSplitPinUnorderedNullHomeomorph_one (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    realSplitPinUnorderedNullHomeomorph 1 n = Homeomorph.refl _ := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  apply Homeomorph.ext
  intro p
  rw [realSplitPinUnorderedNullHomeomorph_apply]
  exact congrArg (fun e : Equiv.Perm (Unordered Q55 n) => e p)
    (map_one (realSplitPinUnorderedNullAction n))

@[simp] theorem realSplitPinUnorderedNullHomeomorph_inv
    (g : realSplitPin55) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    realSplitPinUnorderedNullHomeomorph g⁻¹ n =
      (realSplitPinUnorderedNullHomeomorph g n).symm := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  apply Homeomorph.ext
  intro p
  apply (realSplitPinUnorderedNullHomeomorph g n).injective
  rw [Homeomorph.apply_symm_apply,
    realSplitPinUnorderedNullHomeomorph_apply,
    realSplitPinUnorderedNullHomeomorph_apply]
  exact (realSplitPinUnorderedNullAction n g).apply_symm_apply p

/-- Composition of the concrete split-Pin configuration homeomorphisms
matches multiplication in the native split-Pin group. -/
@[simp] theorem realSplitPinUnorderedNullHomeomorph_mul
    (g h : realSplitPin55) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    realSplitPinUnorderedNullHomeomorph (g * h) n =
      (realSplitPinUnorderedNullHomeomorph h n).trans
        (realSplitPinUnorderedNullHomeomorph g n) := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  apply Homeomorph.ext
  intro p
  change realSplitPinUnorderedNullAction n (g * h) p =
    realSplitPinUnorderedNullAction n g
      (realSplitPinUnorderedNullAction n h p)
  exact congrArg (fun e : Equiv.Perm (Unordered Q55 n) => e p)
    (map_mul (realSplitPinUnorderedNullAction n) g h)

/-! The native Mathlib action target is `MulAction` on the carrier.  A
`Homeomorph` has no canonical monoid structure, so the homeomorphisms are
recorded separately by `realSplitPinUnorderedNullHomeomorph`. -/

instance realSplitPinUnorderedNullMulAction (n : ℕ) :
    MulAction (↥realSplitPin55) (Unordered Q55 n) where
  smul g p := realSplitPinUnorderedNullAction n g p
  one_smul p := by
    exact congrArg (fun e : Equiv.Perm (Unordered Q55 n) => e p)
      (map_one (realSplitPinUnorderedNullAction n))
  mul_smul g h p := by
    change realSplitPinUnorderedNullAction n (g * h) p =
      realSplitPinUnorderedNullAction n g
        (realSplitPinUnorderedNullAction n h p)
    simpa only [Equiv.Perm.mul_apply] using
      congrArg (fun e : Equiv.Perm (Unordered Q55 n) => e p)
        (map_mul (realSplitPinUnorderedNullAction n) g h)

@[simp] theorem realSplitPinUnorderedNullHomeomorph_smul
    (g : realSplitPin55) (n : ℕ) (p : Unordered Q55 n) :
    let _ := unorderedConfigurationTopology Q55 n
    realSplitPinUnorderedNullHomeomorph g n p = g • p := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  rw [realSplitPinUnorderedNullHomeomorph_apply]
  rfl

end InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationTopology
