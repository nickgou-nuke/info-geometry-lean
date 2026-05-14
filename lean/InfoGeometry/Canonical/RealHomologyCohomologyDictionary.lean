import InfoGeometry.Canonical.BogoliubovCartanEigenOperator
import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.HestenesPhaseSemilinear
import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.RealHomologyCohomologyDictionary

Dictionary layer for real Hestenes--Krein homology/cohomology language.

This file does not construct quotient homology groups or a full cohomology
complex. It records theorem-safe predicates and readbacks:

* cycles are vectors killed by a real boundary/operator;
* boundaries are vectors in the image of that operator;
* homology equivalence means difference by a generated boundary;
* cocycles/coboundaries are the dual predicate-level analogues;
* Drazin-null cycles are generalized-kernel vectors `A^k x = 0`;
* pairings and Bogoliubov transport of pairings are supplied as sockets;
* Cartan eigen-operator weights are reused from the existing owner module.

The owner language is real doubled/Hestenes--Krein. No scalar-complex
coefficient lane is introduced here.
-/

namespace InfoGeometry.Canonical.RealHomologyCohomologyDictionary

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovCartanEigenOperator
open InfoGeometry.Canonical.Drazin

/-! ## Generic real boundary algebra -/

/--
A real boundary operator.

This is the minimal chain-complex socket: `d² = 0`, without committing to a
normed carrier or a quotient construction.
-/
@[rep_depth operator]
structure RealBoundaryOperator (C : Type*) [AddCommGroup C] [Module ℝ C] where
  d : C →ₗ[ℝ] C
  d_sq_zero : d.comp d = 0

namespace RealBoundaryOperator

variable {C : Type*}
variable [AddCommGroup C] [Module ℝ C]
variable (B : RealBoundaryOperator C)

/-- Real cycles: elements killed by the boundary operator. -/
@[rep_depth operator]
def IsCycle (x : C) : Prop :=
  B.d x = 0

/-- Real boundaries: elements in the image of the boundary operator. -/
@[rep_depth operator]
def IsBoundary (x : C) : Prop :=
  ∃ y : C, B.d y = x

/-- Boundaries are cycles when `d² = 0`. -/
@[rep_depth operator]
theorem boundary_is_cycle
    {x : C}
    (hx : B.IsBoundary x) :
    B.IsCycle x := by
  rcases hx with ⟨y, rfl⟩
  unfold IsCycle
  have h := congrArg (fun F : C →ₗ[ℝ] C => F y) B.d_sq_zero
  simpa [LinearMap.comp_apply] using h

/-- Homology equivalence: two representatives differ by a boundary. -/
@[rep_depth operator]
def HomologyEquivalent (x y : C) : Prop :=
  B.IsBoundary (x - y)

/-- Reflexivity of homology equivalence. -/
@[rep_depth operator]
theorem homologyEquivalent_refl
    (x : C) :
    B.HomologyEquivalent x x := by
  unfold HomologyEquivalent IsBoundary
  refine ⟨0, ?_⟩
  simp

/-- Symmetry of homology equivalence. -/
@[rep_depth operator]
theorem homologyEquivalent_symm
    {x y : C}
    (hxy : B.HomologyEquivalent x y) :
    B.HomologyEquivalent y x := by
  unfold HomologyEquivalent IsBoundary at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    B.d (-z) = -B.d z := by simp
    _ = -(x - y) := by rw [hz]
    _ = y - x := by abel

/-- Transitivity of homology equivalence. -/
@[rep_depth operator]
theorem homologyEquivalent_trans
    {x y z : C}
    (hxy : B.HomologyEquivalent x y)
    (hyz : B.HomologyEquivalent y z) :
    B.HomologyEquivalent x z := by
  unfold HomologyEquivalent IsBoundary at hxy hyz ⊢
  rcases hxy with ⟨a, ha⟩
  rcases hyz with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  calc
    B.d (a + b) = B.d a + B.d b := by simp
    _ = (x - y) + (y - z) := by rw [ha, hb]
    _ = x - z := by abel

/-- Homology equivalence is an equivalence relation. -/
@[rep_depth operator]
theorem homologyEquivalent_equivalence :
    Equivalence B.HomologyEquivalent := by
  refine ⟨?refl, ?symm, ?trans⟩
  · intro x
    exact B.homologyEquivalent_refl x
  · intro x y hxy
    exact B.homologyEquivalent_symm hxy
  · intro x y z hxy hyz
    exact B.homologyEquivalent_trans hxy hyz

/--
A real homology witness/readout. It descends to homology if it vanishes on
boundaries.
-/
@[rep_depth operator]
structure BoundaryVanishingWitness where
  eval : C →ₗ[ℝ] ℝ
  vanishes_on_boundaries :
    ∀ y : C, eval (B.d y) = 0

namespace BoundaryVanishingWitness

variable {B}
variable (ω : BoundaryVanishingWitness B)

/-- Boundary-vanishing witnesses are constant on homology classes. -/
@[rep_depth operator]
theorem descends_to_homology_equivalence
    {x y : C}
    (hxy : B.HomologyEquivalent x y) :
    ω.eval x = ω.eval y := by
  unfold HomologyEquivalent IsBoundary at hxy
  rcases hxy with ⟨b, hb⟩
  have hzero : ω.eval (x - y) = 0 := by
    rw [← hb]
    exact ω.vanishes_on_boundaries b
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end BoundaryVanishingWitness

end RealBoundaryOperator

/-! ## Generic real cohomology witnesses and frame readouts -/

/--
A real pairing between chains and cochains/witnesses.

The only algebraic law needed for homology descent is compatibility with
subtraction in the chain argument.
-/
@[rep_depth operator]
structure RealPairing
    (Chain Cochain : Type*) [AddCommGroup Chain] where
  pairing : Chain → Cochain → ℝ
  sub_left :
    ∀ (x y : Chain) (φ : Cochain),
      pairing (x - y) φ = pairing x φ - pairing y φ

namespace RealPairing

variable {Chain Cochain : Type*}
variable [AddCommGroup Chain] [Module ℝ Chain]
variable (P : RealPairing Chain Cochain)

/-- A witness/cochain vanishes on boundaries. -/
@[rep_depth operator]
def VanishesOnBoundaries
    (B : RealBoundaryOperator Chain)
    (φ : Cochain) : Prop :=
  ∀ y : Chain, P.pairing (B.d y) φ = 0

/--
Witnesses that vanish on boundaries descend to homology-equivalence classes.
-/
@[rep_depth operator]
theorem pairing_descends_to_homology_equiv
    (B : RealBoundaryOperator Chain)
    {x y : Chain} {φ : Cochain}
    (hxy : B.HomologyEquivalent x y)
    (hφ : P.VanishesOnBoundaries B φ) :
    P.pairing x φ = P.pairing y φ := by
  unfold RealBoundaryOperator.HomologyEquivalent RealBoundaryOperator.IsBoundary at hxy
  rcases hxy with ⟨b, hb⟩
  have hzero : P.pairing (x - y) φ = 0 := by
    rw [← hb]
    exact hφ b
  rw [P.sub_left x y φ] at hzero
  exact sub_eq_zero.mp hzero

end RealPairing

/--
A frame transport preserving the real homology/cohomology pairing.

This is the abstract real form of Bogoliubov/Krein/Hestenes frame invariance.
-/
@[rep_depth krein]
structure PairingFrameTransport
    (Chain Cochain : Type*) [AddCommGroup Chain] where
  transportChain : Chain → Chain
  transportCochain : Cochain → Cochain
  pairing : RealPairing Chain Cochain
  preserves_pairing :
    ∀ x φ,
      pairing.pairing (transportChain x) (transportCochain φ) =
        pairing.pairing x φ

namespace PairingFrameTransport

variable {Chain Cochain : Type*}
variable [AddCommGroup Chain]
variable (T : PairingFrameTransport Chain Cochain)

/-- Pairing-preserving frame maps preserve the pairing readout. -/
@[rep_depth krein]
theorem preserves_pairing_readout
    (x : Chain) (φ : Cochain) :
    T.pairing.pairing (T.transportChain x) (T.transportCochain φ) =
      T.pairing.pairing x φ :=
  T.preserves_pairing x φ

end PairingFrameTransport

section Doubled

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- A real cycle for an operator/differential `D` is killed by `D`. -/
@[rep_depth transport]
def IsRealCycle (D : EndH) (x : H₂) : Prop :=
  D x = 0

/-- A real boundary for `D` is generated by applying `D` to a higher representative. -/
@[rep_depth transport]
def IsRealBoundary (D : EndH) (x : H₂) : Prop :=
  ∃ y : H₂, D y = x

/-- Homology equivalence: representatives differ by a generated boundary. -/
@[rep_depth transport]
def HomologyEquivalent (D : EndH) (x y : H₂) : Prop :=
  IsRealBoundary (E := E) D (x - y)

/-- If `D² = 0`, every real boundary is a real cycle. -/
@[rep_depth transport]
theorem realBoundary_is_realCycle_of_sq_zero
    {D : EndH}
    (hD : D.comp D = 0)
    {x : H₂}
    (hx : IsRealBoundary (E := E) D x) :
    IsRealCycle (E := E) D x := by
  rcases hx with ⟨y, rfl⟩
  unfold IsRealCycle
  simpa [ContinuousLinearMap.comp_apply] using congrArg (fun F : EndH => F y) hD

/-- Homology equivalence is reflexive. -/
@[rep_depth transport]
theorem homologyEquivalent_refl
    (D : EndH) (x : H₂) :
    HomologyEquivalent (E := E) D x x := by
  unfold HomologyEquivalent IsRealBoundary
  refine ⟨0, ?_⟩
  simp

/-- Homology equivalence is symmetric. -/
@[rep_depth transport]
theorem homologyEquivalent_symm
    {D : EndH} {x y : H₂}
    (hxy : HomologyEquivalent (E := E) D x y) :
    HomologyEquivalent (E := E) D y x := by
  unfold HomologyEquivalent IsRealBoundary at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    D (-z) = -D z := by simp
    _ = -(x - y) := by rw [hz]
    _ = y - x := by abel

/-- Homology equivalence is transitive. -/
@[rep_depth transport]
theorem homologyEquivalent_trans
    {D : EndH} {x y z : H₂}
    (hxy : HomologyEquivalent (E := E) D x y)
    (hyz : HomologyEquivalent (E := E) D y z) :
    HomologyEquivalent (E := E) D x z := by
  unfold HomologyEquivalent IsRealBoundary at hxy hyz ⊢
  rcases hxy with ⟨a, ha⟩
  rcases hyz with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  calc
    D (a + b) = D a + D b := by simp
    _ = (x - y) + (y - z) := by rw [ha, hb]
    _ = x - z := by abel

/-- Homology equivalence is an equivalence relation. -/
@[rep_depth transport]
theorem homologyEquivalent_equivalence
    (D : EndH) :
    Equivalence (HomologyEquivalent (E := E) D) := by
  refine ⟨?refl, ?symm, ?trans⟩
  · intro x
    exact homologyEquivalent_refl (E := E) D x
  · intro x y hxy
    exact homologyEquivalent_symm (E := E) hxy
  · intro x y z hxy hyz
    exact homologyEquivalent_trans (E := E) hxy hyz

/-- Drazin/generalized-null cycle predicate: `A^k x = 0`. -/
@[rep_depth operator]
def IsDrazinNullCycle (A : EndH) (k : ℕ) (x : H₂) : Prop :=
  (A ^ k) x = 0

/--
Drazin-regular state: selected by the regular/core projector.

This is the resolved sector, not the generalized-null homology-like residue.
-/
@[rep_depth operator]
def IsDrazinRegularState (P : EndH) (x : H₂) : Prop :=
  P x = x

/--
Drazin-defect state: selected by the complementary/null projector.

This is the projector-facing predicate for the Drazin homology-like residue.
-/
@[rep_depth operator]
def IsDrazinDefectState (Q : EndH) (x : H₂) : Prop :=
  Q x = x

/-- Socket predicate: a transport preserves the generalized null sector of `A^k`. -/
@[rep_depth operator]
def PreservesDrazinNullCycles (A U : EndH) (k : ℕ) : Prop :=
  ∀ x, IsDrazinNullCycle (E := E) A k x →
    IsDrazinNullCycle (E := E) A k (U x)

/-- Readback for supplied Drazin-null stability. -/
@[rep_depth operator]
theorem drazinNullCycle_transport
    {A U : EndH} {k : ℕ}
    (hU : PreservesDrazinNullCycles (E := E) A U k)
    {x : H₂}
    (hx : IsDrazinNullCycle (E := E) A k x) :
    IsDrazinNullCycle (E := E) A k (U x) :=
  hU x hx

/-! ## Real linear witnesses -/

/--
A real linear witness pairs trivially with generated boundaries.

This is the safe cohomology-facing condition: arbitrary nonlinear pairings do
not descend to homology classes.
-/
@[rep_depth transport]
def PairsTriviallyOnBoundaries
    (D : EndH) (φ : H₂ →L[ℝ] ℝ) : Prop :=
  ∀ y : H₂, φ (D y) = 0

/-!
A real linear witness that vanishes on boundaries descends to
homology-equivalence classes.
-/
@[rep_depth transport]
theorem witness_descends_to_homologyEquivalent
    {D : EndH} {φ : H₂ →L[ℝ] ℝ}
    (hφ : PairsTriviallyOnBoundaries (E := E) D φ)
    {x y : H₂}
    (hxy : HomologyEquivalent (E := E) D x y) :
    φ x = φ y := by
  unfold HomologyEquivalent IsRealBoundary at hxy
  rcases hxy with ⟨z, hz⟩
  have hsub : φ (x - y) = 0 := by
    rw [← hz]
    exact hφ z
  rw [map_sub] at hsub
  exact sub_eq_zero.mp hsub

section ModuleEndDrazinResidue

variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
Module-endomorphism Drazin-null cycle predicate.

This is the same generalized-kernel condition as `IsDrazinNullCycle`, stated
for the `Module.End` API used by `DrazinCoreFlow`.
-/
@[rep_depth operator]
def IsModuleEndDrazinNullCycle (A : Module.End K V) (k : ℕ) (x : V) : Prop :=
  (A ^ k) x = 0

/--
Readback: the module-endomorphism Drazin-null predicate is membership in the
owner `drazinCore A k = ker(A^k)`.
-/
@[rep_depth operator]
theorem isModuleEndDrazinNullCycle_iff_mem_drazinCore
    (A : Module.End K V) (k : ℕ) (x : V) :
    IsModuleEndDrazinNullCycle A k x ↔
      x ∈ IsDrazinInverse.drazinCore A k := by
  rfl

/--
Readback alias: the module-endomorphism Drazin-null predicate is membership in
the owner `drazinCore A k = ker(A^k)`.
-/
@[rep_depth operator]
theorem isDrazinNullCycle_iff_mem_drazinCore
    (A : Module.End K V) (k : ℕ) (x : V) :
    IsModuleEndDrazinNullCycle A k x ↔
      x ∈ IsDrazinInverse.drazinCore A k :=
  isModuleEndDrazinNullCycle_iff_mem_drazinCore A k x

/--
The complementary Drazin projector selects generalized-kernel/null states.
-/
@[rep_depth operator]
theorem complementaryProjection_selects_moduleEndDrazinNullCycle
    {A D : Module.End K V} {k : ℕ}
    (h : IsDrazinInverse A D k) (x : V) :
    IsModuleEndDrazinNullCycle A k (IsDrazinInverse.complementaryProjection A D x) := by
  exact IsDrazinInverse.complementaryProjection_mapsTo_drazinCore (h := h) x

/--
The range of the complementary Drazin projector is exactly the Drazin-null
predicate, using the owner generalized-kernel theorem.
-/
@[rep_depth operator]
theorem complementaryProjection_range_eq_moduleEndDrazinNullCycles
    {A D : Module.End K V} {k : ℕ}
    (h : IsDrazinInverse A D k) (x : V) :
    x ∈ LinearMap.range (IsDrazinInverse.complementaryProjection A D)
      ↔ IsModuleEndDrazinNullCycle A k x := by
  rw [IsDrazinInverse.complementaryProjection_range_eq_drazinCore (h := h)]
  rfl

/--
Drazin-null cycles are exactly the range of the complementary Drazin projector,
using the existing owner generalized-kernel theorem.
-/
@[rep_depth operator]
theorem isDrazinNullCycle_iff_mem_range_complementaryProjection
    {A D : Module.End K V} {k : ℕ}
    (h : IsDrazinInverse A D k) (x : V) :
    IsModuleEndDrazinNullCycle A k x
      ↔ x ∈ LinearMap.range (IsDrazinInverse.complementaryProjection A D) := by
  exact (complementaryProjection_range_eq_moduleEndDrazinNullCycles
    (K := K) (V := V) (h := h) x).symm

/--
Any Drazin-null vector is fixed by the complementary Drazin projector.

This is the projector-selection form of the generalized-kernel theorem.
-/
@[rep_depth operator]
theorem complementaryProjection_fixed_of_moduleEndDrazinNullCycle
    {A D : Module.End K V} {k : ℕ}
    (h : IsDrazinInverse A D k)
    {x : V}
    (hx : IsModuleEndDrazinNullCycle A k x) :
    IsDrazinInverse.complementaryProjection A D x = x := by
  have hxRange :
      x ∈ LinearMap.range (IsDrazinInverse.complementaryProjection A D) := by
    exact (complementaryProjection_range_eq_moduleEndDrazinNullCycles
      (K := K) (V := V) (h := h) x).2 hx
  rcases hxRange with ⟨y, hy⟩
  rw [← hy]
  have hIdem :
      IsDrazinInverse.complementaryProjection A D *
          IsDrazinInverse.complementaryProjection A D =
        IsDrazinInverse.complementaryProjection A D :=
    IsDrazinInverse.complementaryProjection_is_idempotent h
  simpa using congrArg (fun F : Module.End K V => F y) hIdem

/-- Alias: the complementary Drazin projector fixes Drazin-null cycles. -/
@[rep_depth operator]
theorem complementaryProjection_fixes_drazinNullCycle
    {A D : Module.End K V} {k : ℕ}
    (h : IsDrazinInverse A D k)
    {x : V}
    (hx : IsModuleEndDrazinNullCycle A k x) :
    IsDrazinInverse.complementaryProjection A D x = x :=
  complementaryProjection_fixed_of_moduleEndDrazinNullCycle
    (K := K) (V := V) (h := h) hx

end ModuleEndDrazinResidue

/-- A real pairing between homology-side vectors and cohomology witnesses. -/
@[rep_depth transport]
structure RealPairingSocket (Cochain : Type u) where
  pairing : H₂ → Cochain → ℝ
  pairing_sub_left :
    ∀ x y φ, pairing (x - y) φ = pairing x φ - pairing y φ

namespace RealPairingSocket

variable {Cochain : Type u}
variable (P : RealPairingSocket (E := E) Cochain)

/-- A witness pairs trivially with all generated boundaries. -/
@[rep_depth transport]
def PairsTriviallyOnBoundaries (D : EndH) (φ : Cochain) : Prop :=
  ∀ y : H₂, P.pairing (D y) φ = 0

/-- A representative cohomology witness detects a homology representative. -/
@[rep_depth transport]
def Detects (x : H₂) (φ : Cochain) : Prop :=
  P.pairing x φ ≠ 0

/--
A chain/cochain transport preserves the real pairing readout.

This is the abstract socket used by K/Bogoliubov/Krein-preserving frame maps:
the concrete proof that a frame preserves `K`, Drazin sectors, and the Krein
form can be supplied upstream, while this dictionary records the readout law.
-/
@[rep_depth transport]
def PreservesPairingTransport
    (transportChain : H₂ → H₂)
    (transportCochain : Cochain → Cochain) : Prop :=
  ∀ x φ, P.pairing (transportChain x) (transportCochain φ) = P.pairing x φ

/-- Readback: a pairing-preserving transport leaves the numerical readout invariant. -/
@[rep_depth transport]
theorem pairing_readout_invariant_of_preservesPairingTransport
    {transportChain : H₂ → H₂}
    {transportCochain : Cochain → Cochain}
    (hT : P.PreservesPairingTransport transportChain transportCochain)
    (x : H₂) (φ : Cochain) :
    P.pairing (transportChain x) (transportCochain φ) = P.pairing x φ :=
  hT x φ

/-- A detecting witness remains detecting under a pairing-preserving transport. -/
@[rep_depth transport]
theorem detects_transport_of_preservesPairingTransport
    {transportChain : H₂ → H₂}
    {transportCochain : Cochain → Cochain}
    (hT : P.PreservesPairingTransport transportChain transportCochain)
    {x : H₂} {φ : Cochain}
    (hDetects : P.Detects x φ) :
    P.Detects (transportChain x) (transportCochain φ) := by
  unfold Detects at hDetects ⊢
  rw [hT x φ]
  exact hDetects

/--
If a witness kills boundaries, it has the same pairing value on homologous
representatives.
-/
@[rep_depth transport]
theorem pairing_eq_of_homologyEquivalent
    {D : EndH} {x y : H₂} {φ : Cochain}
    (hφ : P.PairsTriviallyOnBoundaries D φ)
    (hxy : HomologyEquivalent (E := E) D x y) :
    P.pairing x φ = P.pairing y φ := by
  unfold HomologyEquivalent IsRealBoundary at hxy
  rcases hxy with ⟨z, hz⟩
  have hboundary : P.pairing (x - y) φ = 0 := by
    rw [← hz]
    exact hφ z
  have hsub : P.pairing (x - y) φ = P.pairing x φ - P.pairing y φ :=
    P.pairing_sub_left x y φ
  rw [hboundary] at hsub
  exact sub_eq_zero.mp hsub.symm

end RealPairingSocket

/-! ## Frame transport of witnesses and pairings -/

/-- Transport a real witness by a supplied inverse-frame map. -/
@[rep_depth transport]
noncomputable def transportWitness
    (Uinv : EndH) (φ : H₂ →L[ℝ] ℝ) : H₂ →L[ℝ] ℝ :=
  φ.comp Uinv

/--
If `Uinv` is a left inverse for `U`, the transported witness has the same
readout on the transported state.
-/
@[rep_depth transport]
theorem transportedWitness_readout_eq
    {U Uinv : EndH}
    (hLeft : Uinv.comp U = ContinuousLinearMap.id ℝ H₂)
    (φ : H₂ →L[ℝ] ℝ)
    (x : H₂) :
    transportWitness (E := E) Uinv φ (U x) = φ x := by
  unfold transportWitness
  have hx : Uinv (U x) = x := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndH => F x) hLeft
  simp [hx]

/-- A real doubled frame preserves the Krein pairing. -/
@[rep_depth krein]
def PreservesKreinPairing (U : EndH) : Prop :=
  ∀ x y : H₂,
    KreinSpace.kreinInner (H := H₂) (U x) (U y) =
      KreinSpace.kreinInner (H := H₂) x y

/--
A frame also preserves the internal phase axis `K`.

This is the real replacement for a complex-linear frame condition.
-/
@[rep_depth krein]
def PreservesPhaseAxis (U : EndH) : Prop :=
  U.comp (InfoGeometry.Krein.clockAxis (E := E)) =
    (InfoGeometry.Krein.clockAxis (E := E)).comp U

/--
A Hestenes--Krein frame map: preserves both the real Krein pairing and the
internal phase axis.
-/
@[rep_depth krein]
structure HestenesKreinFrameMap where
  U : EndH
  preservesKrein : PreservesKreinPairing (E := E) U
  preservesPhaseAxis : PreservesPhaseAxis (E := E) U

/-- A Hestenes--Krein frame map preserves the real pairing readout. -/
@[rep_depth krein]
theorem hestenesKreinFrameMap_preserves_pairing_readout
    (F : HestenesKreinFrameMap (E := E))
    (x y : H₂) :
    KreinSpace.kreinInner (H := H₂) (F.U x) (F.U y) =
      KreinSpace.kreinInner (H := H₂) x y :=
  F.preservesKrein x y

end Doubled

section AbstractCohomology

variable {Cochain : Type u}

/-- A real cocycle is killed by a supplied coboundary operator. -/
@[rep_depth transport]
def IsRealCocycle [Zero Cochain] (δ : Cochain → Cochain) (φ : Cochain) : Prop :=
  δ φ = 0

/-- A real coboundary is generated by a supplied coboundary operator. -/
@[rep_depth transport]
def IsRealCoboundary (δ : Cochain → Cochain) (φ : Cochain) : Prop :=
  ∃ ψ : Cochain, δ ψ = φ

end AbstractCohomology

section LinearCohomologyWitnesses

variable {W : Type u}
variable [AddCommGroup W] [Module ℝ W]

/-- Linear real cocycle: a witness killed by a real linear coboundary operator. -/
@[rep_depth transport]
def IsLinearRealCocycle (δ : W →ₗ[ℝ] W) (φ : W) : Prop :=
  δ φ = 0

/-- Linear real coboundary: a witness generated by a real linear coboundary operator. -/
@[rep_depth transport]
def IsLinearRealCoboundary (δ : W →ₗ[ℝ] W) (φ : W) : Prop :=
  ∃ ψ : W, δ ψ = φ

/-- Linear coboundaries are cocycles when the supplied coboundary squares to zero. -/
@[rep_depth transport]
theorem linearRealCoboundary_is_linearRealCocycle
    {δ : W →ₗ[ℝ] W}
    (hδ₂ : δ.comp δ = 0)
    {φ : W}
    (hφ : IsLinearRealCoboundary δ φ) :
    IsLinearRealCocycle δ φ := by
  rcases hφ with ⟨ψ, rfl⟩
  unfold IsLinearRealCocycle
  exact congrArg (fun F : W →ₗ[ℝ] W => F ψ) hδ₂

end LinearCohomologyWitnesses

end InfoGeometry.Canonical.RealHomologyCohomologyDictionary
