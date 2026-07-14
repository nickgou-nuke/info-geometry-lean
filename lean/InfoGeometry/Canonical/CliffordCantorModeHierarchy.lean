import InfoGeometry.Clifford.Cl11Quaternion
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SplitQ11CausalCone
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Canonical.CantorCylinderLattice
import InfoGeometry.Canonical.SectorLattice
import InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.FockSpaceSugawara
import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.External.Virasoro.VirasoroAlgebra

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CliffordCantorModeHierarchy

Verified theorem-owner packet for the corrected chain:

`Cl(1,1) -> finite split Clifford tower -> Cantor idempotent refinement ->
direct limit -> mode/central-extension layer`.

The finite split seed, fixed matrix-facing causal-cone closure, Cantor
refinement, and split-tower direct-limit facts are proved inside the repository.
The Heisenberg, affine Kac-Moody, and Virasoro laws are imported directly from
their theorem-owner modules; they are not derived from the finite matrix tower
alone.
-/

namespace CliffordCantorModeHierarchy

open InfoGeometry.Canonical.CantorCylinderLattice
open InfoGeometry.Canonical.KreinProjectorLattice
open InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
open InfoGeometry.Canonical.SectorLattice
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Krein
open VirasoroProject

section LocalSeed

/-- Prose-facing square-minus split-quaternion unit. -/
@[rep_depth krein]
noncomputable def splitQuaternionI : Alg :=
  InfoGeometry.Clifford.SplitQ11CausalCone.splitQuaternionI

/-- Prose-facing first square-plus split-quaternion unit. -/
@[rep_depth krein]
noncomputable def splitQuaternionJ : Alg :=
  InfoGeometry.Clifford.SplitQ11CausalCone.splitQuaternionJ

/-- Prose-facing second square-plus split-quaternion unit. -/
@[rep_depth krein]
noncomputable def splitQuaternionK : Alg :=
  InfoGeometry.Clifford.SplitQ11CausalCone.splitQuaternionK

/--
The exact split-quaternion presentation from the prose, expressed through the
repo's local `Cl(1,1)` names.
-/
@[rep_depth krein]
theorem split_quaternion_basis_laws :
    splitQuaternionI * splitQuaternionI = -(1 : Alg)
      ∧ splitQuaternionJ * splitQuaternionJ = (1 : Alg)
      ∧ splitQuaternionK * splitQuaternionK = (1 : Alg)
      ∧ splitQuaternionI * splitQuaternionJ = splitQuaternionK
      ∧ splitQuaternionJ * splitQuaternionI = -splitQuaternionK := by
  simpa [splitQuaternionI, splitQuaternionJ, splitQuaternionK] using
    InfoGeometry.Clifford.SplitQ11CausalCone.split_quaternion_basis_laws

/-- The split-null commutator in the local `Cl(1,1)` seed is the `ε` axis. -/
@[rep_depth krein]
theorem splitNull_commutator_eq_eps :
    nullPlus * nullMinus - nullMinus * nullPlus = epsGen := by
  change epsPlusProjector - epsMinusProjector = epsGen
  rw [epsPlusProjector_eq_half_one_add_eps, epsMinusProjector_eq_half_one_sub_eps]
  module

/--
Finite local seed for the split-quaternion/`Cl(1,1)` block:

* one generator squares to `+1`, the phase generator squares to `-1`;
* the pseudoscalar `ε` squares to `1`;
* the split-null elements are nilpotent;
* their anticommutator is `1`;
* their commutator is the Krein sector axis;
* the two `ε`-sector projectors are complementary idempotents.
-/
@[rep_depth krein]
theorem local_split_quaternion_seed_laws :
    jGen * jGen = (1 : Alg)
      ∧ kGen * kGen = -(1 : Alg)
      ∧ epsGen * epsGen = (1 : Alg)
      ∧ nullPlus * nullPlus = 0
      ∧ nullMinus * nullMinus = 0
      ∧ nullMinus * nullPlus + nullPlus * nullMinus = (1 : Alg)
      ∧ nullPlus * nullMinus - nullMinus * nullPlus = epsGen
      ∧ epsMinusProjector * epsMinusProjector = epsMinusProjector
      ∧ epsPlusProjector * epsPlusProjector = epsPlusProjector := by
  exact ⟨jGen_sq, kGen_sq, epsGen_sq, nullPlus_sq, nullMinus_sq,
    nullMinus_mul_nullPlus_add_swap, splitNull_commutator_eq_eps,
    epsMinusProjector_idempotent, epsPlusProjector_idempotent⟩

/-- Null products and the `p± = (1 ± ε) / 2` projector formulas. -/
@[rep_depth krein]
theorem local_null_projector_formula_laws :
    nullPlus * nullMinus = epsPlusProjector
      ∧ nullMinus * nullPlus = epsMinusProjector
      ∧ epsPlusProjector = (1 / 2 : ℝ) • ((1 : Alg) + epsGen)
      ∧ epsMinusProjector = (1 / 2 : ℝ) • ((1 : Alg) - epsGen)
      ∧ nullPlus * nullMinus + nullMinus * nullPlus = (1 : Alg)
      ∧ nullPlus * nullMinus - nullMinus * nullPlus = epsGen := by
  exact ⟨rfl, rfl, epsPlusProjector_eq_half_one_add_eps,
    epsMinusProjector_eq_half_one_sub_eps,
    by simpa [add_comm] using nullMinus_mul_nullPlus_add_swap,
    splitNull_commutator_eq_eps⟩

end LocalSeed

section LocalLieReadout

/-- The Krein axis acts with weight `+1` on the positive null generator. -/
@[rep_depth krein]
theorem epsGen_mul_nullPlus :
    epsGen * nullPlus = nullPlus := by
  rw [nullPlus_eq_half_jGen_sub_kGen]
  simp [mul_sub]
  module

/-- Right multiplication by the Krein axis gives the opposite weight on `u₊`. -/
@[rep_depth krein]
theorem nullPlus_mul_epsGen :
    nullPlus * epsGen = -nullPlus := by
  rw [nullPlus_eq_half_jGen_sub_kGen]
  simp [sub_mul]
  module

/-- Local `sl₂`-style weight relation `[ε, u₊] = 2u₊`. -/
@[rep_depth krein]
theorem epsGen_commutator_nullPlus :
    epsGen * nullPlus - nullPlus * epsGen = (2 : ℝ) • nullPlus := by
  rw [epsGen_mul_nullPlus, nullPlus_mul_epsGen]
  module

/-- The Krein axis acts with weight `-1` on the negative null generator. -/
@[rep_depth krein]
theorem epsGen_mul_nullMinus :
    epsGen * nullMinus = -nullMinus := by
  rw [nullMinus_eq_half_jGen_add_kGen]
  simp [mul_add]

/-- Right multiplication by the Krein axis gives the opposite weight on `u₋`. -/
@[rep_depth krein]
theorem nullMinus_mul_epsGen :
    nullMinus * epsGen = nullMinus := by
  rw [nullMinus_eq_half_jGen_add_kGen]
  simp [add_mul]
  module

/-- Local `sl₂`-style weight relation `[ε, u₋] = -2u₋`. -/
@[rep_depth krein]
theorem epsGen_commutator_nullMinus :
    epsGen * nullMinus - nullMinus * epsGen = (-2 : ℝ) • nullMinus := by
  rw [epsGen_mul_nullMinus, nullMinus_mul_epsGen]
  module

end LocalLieReadout

section MatrixBaseCase

/--
The split-quaternion leg of the base case:
`Cl(1,1) ≃ ℍ[ℝ, 1, 0, -1]` in the convention used by
`InfoGeometry.Clifford.Cl11Quaternion`.
-/
@[rep_depth krein]
theorem cl11_split_quaternion_base_case :
    Nonempty
      (InfoGeometry.Clifford.Cl11Quaternion.Cl11
        ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Quaternion.Hsplit) :=
  ⟨CliffordAlgebraQuaternion.equiv
    (R := ℝ) (c₁ := (1 : ℝ)) (c₂ := (-1 : ℝ))⟩

/-- The split-quaternion algebra has the proved concrete `2 × 2` real matrix model. -/
@[rep_depth krein]
theorem split_quaternion_matrix_base_case :
    Nonempty
      (InfoGeometry.Clifford.Cl11Quaternion.Hsplit
        ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Quaternion.Mat₂ ℝ) :=
  ⟨InfoGeometry.Clifford.Cl11Quaternion.quatEquivMat⟩

/-- The finite base case has the proved real Pauli matrix model `Cl(1,1) ≃ M₂(ℝ)`. -/
@[rep_depth krein]
theorem cl11_matrix_base_case :
    Nonempty
      (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11
        ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Matrix.Mat2) :=
  ⟨InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat⟩

end MatrixBaseCase

section RecursiveTower

/--
Each finite recursive step is the finite-spine owner split Bott factorization.
-/
@[rep_depth krein]
theorem finite_split_clifford_recursive_step (n : ℕ) :
    splitBottStep n = InfoGeometry.CliffordTower.clsplit_succ_equiv n :=
  splitBottStep_eq_owner n

/-- The split Clifford direct limit has arbitrarily deep finite representatives. -/
@[rep_depth krein]
theorem split_direct_limit_has_arbitrarily_deep_representatives
    (z : SplitCliffordInfinity) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ x,
      DirectLimit.Module.of ℝ ℕ _
        (fun m n h => splitCliffordMap m n h) n x = z :=
  splitCliffordInfinity_unbounded_representatives z

end RecursiveTower

section CantorRefinement

/-- Ring-valued characteristic idempotents implement binary Cantor refinement. -/
@[rep_depth krein]
theorem cantor_cylinder_indicator_refinement
    {n : ℕ} (w : BinaryWord n) :
    setIndicator ℝ ({v : BinaryWord (n + 1) | truncateWord v = w}) =
      cylinderIndicator ℝ (leftChild w) + cylinderIndicator ℝ (rightChild w) :=
  cylinderIndicator_refinement (R := ℝ) w

/-- Singleton Cantor cylinder indicators are idempotents in the finite function algebra. -/
@[rep_depth krein]
theorem cantor_cylinder_indicator_idempotent
    {n : ℕ} (w : BinaryWord n) :
    IsIdempotentElem (cylinderIndicator ℝ w) :=
  cylinderIndicator_idempotent (R := ℝ) w

end CantorRefinement

section CombinedSectorProjectors

/--
The local Krein projector lattice recovers the involutive sector axis.
This is the finite idempotent-to-involution correspondence used by the sector tree.
-/
@[rep_depth krein]
theorem local_krein_lattice_involution_sq :
    KreinSector.kreinInvolution * KreinSector.kreinInvolution = (1 : Alg) :=
  KreinSector.kreinInvolution_sq

/-- Elementary combined Cantor-Krein sector assignments evaluate to idempotents. -/
@[rep_depth krein]
theorem elementary_cantor_krein_sector_idempotent
    {n : ℕ} (w : BinaryWord n) (k : KreinSector) :
    IsIdempotentElem (projectionAssignmentToAlg (elementaryProjectionAssignment w k)) :=
  elementaryProjectionAssignment_idempotent w k

/--
The combined sector projector refines by splitting the Cantor cell into its two
children while keeping the same local Krein sector.
-/
@[rep_depth krein]
theorem elementary_cantor_krein_sector_refinement
    {n : ℕ} (w : BinaryWord n) (k : KreinSector) :
    refineProjectionAssignment (elementaryProjectionAssignment w k) =
      elementaryProjectionAssignment (leftChild w) k ⊔
        elementaryProjectionAssignment (rightChild w) k :=
  refineProjectionAssignment_elementary w k

end CombinedSectorProjectors

section TheoremPacket

/--
The corrected hierarchy as a single theorem-level packet.

The first fields are finite/local or direct-limit facts.  The last fields cite
the imported theorem-owner definitions and laws for Heisenberg, affine
Kac-Moody, Virasoro, and Sugawara.
-/
structure CliffordCantorModeHierarchyPacket (n : ℕ) (m q : ℤ) : Prop where
  split_quaternion_basis :
    splitQuaternionI * splitQuaternionI = -(1 : Alg)
      ∧ splitQuaternionJ * splitQuaternionJ = (1 : Alg)
      ∧ splitQuaternionK * splitQuaternionK = (1 : Alg)
      ∧ splitQuaternionI * splitQuaternionJ = splitQuaternionK
      ∧ splitQuaternionJ * splitQuaternionI = -splitQuaternionK
  local_seed :
    jGen * jGen = (1 : Alg)
      ∧ kGen * kGen = -(1 : Alg)
      ∧ epsGen * epsGen = (1 : Alg)
      ∧ nullPlus * nullPlus = 0
      ∧ nullMinus * nullMinus = 0
      ∧ nullMinus * nullPlus + nullPlus * nullMinus = (1 : Alg)
      ∧ nullPlus * nullMinus - nullMinus * nullPlus = epsGen
      ∧ epsMinusProjector * epsMinusProjector = epsMinusProjector
      ∧ epsPlusProjector * epsPlusProjector = epsPlusProjector
  local_null_projectors :
    nullPlus * nullMinus = epsPlusProjector
      ∧ nullMinus * nullPlus = epsMinusProjector
      ∧ epsPlusProjector = (1 / 2 : ℝ) • ((1 : Alg) + epsGen)
      ∧ epsMinusProjector = (1 / 2 : ℝ) • ((1 : Alg) - epsGen)
      ∧ nullPlus * nullMinus + nullMinus * nullPlus = (1 : Alg)
      ∧ nullPlus * nullMinus - nullMinus * nullPlus = epsGen
  local_lie_readout :
    epsGen * nullPlus - nullPlus * epsGen = (2 : ℝ) • nullPlus
      ∧ epsGen * nullMinus - nullMinus * epsGen = (-2 : ℝ) • nullMinus
  fixed_local_causal_cone :
    InfoGeometry.Clifford.SplitQ11CausalCone.LocalCausalConeClosure
  matrix_base_case :
    Nonempty
      (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11
        ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Matrix.Mat2)
  split_quaternion_base_case :
    Nonempty
      (InfoGeometry.Clifford.Cl11Quaternion.Cl11
        ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Quaternion.Hsplit)
  split_quaternion_matrix_case :
    Nonempty
      (InfoGeometry.Clifford.Cl11Quaternion.Hsplit
        ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Quaternion.Mat₂ ℝ)
  finite_tower_step :
    splitBottStep n = InfoGeometry.CliffordTower.clsplit_succ_equiv n
  direct_limit_representatives :
    ∀ z : SplitCliffordInfinity, ∀ N : ℕ, ∃ n ≥ N, ∃ x,
      DirectLimit.Module.of ℝ ℕ _
        (fun m n h => splitCliffordMap m n h) n x = z
  cantor_refinement :
    ∀ w : BinaryWord n,
      setIndicator ℝ ({v : BinaryWord (n + 1) | truncateWord v = w}) =
        cylinderIndicator ℝ (leftChild w) + cylinderIndicator ℝ (rightChild w)
  combined_sector_refinement :
    ∀ (w : BinaryWord n) (k : KreinSector),
      refineProjectionAssignment (elementaryProjectionAssignment w k) =
        elementaryProjectionAssignment (leftChild w) k ⊔
          elementaryProjectionAssignment (rightChild w) k
  combined_sector_idempotent :
    ∀ (w : BinaryWord n) (k : KreinSector),
      IsIdempotentElem (projectionAssignmentToAlg (elementaryProjectionAssignment w k))
  local_krein_involution :
    KreinSector.kreinInvolution * KreinSector.kreinInvolution = (1 : Alg)
  heisenberg_central_extension_definition :
    HeisenbergAlgebra ℝ =
      LieTwoCocycle.CentralExtension (AbelianLieAlgebraOn.heisenbergCocycle ℝ)
  heisenberg_mode_eq :
    ⁅HeisenbergAlgebra.jgen ℝ m, HeisenbergAlgebra.jgen ℝ q⁆
      = if m + q = 0 then (m : ℝ) • HeisenbergAlgebra.kgen ℝ else 0
  heisenberg_cocycle_nontrivial :
    AbelianLieAlgebraOn.heisenbergCocycle ℝ ≠ 0
      ∧ (AbelianLieAlgebraOn.heisenbergCocycle ℝ).cohomologyClass ≠ 0
  kac_moody_central_extension_definition :
    ∀ (𝓰 : Type) [LieRing 𝓰] [LieAlgebra ℝ 𝓰]
      (Φ : LinearMap.BilinForm ℝ 𝓰)
      (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm),
        AffineKacMoody ℝ 𝓰 Φ hΦ hΦs =
          LieTwoCocycle.CentralExtension (affineKacMoodyCocycle ℝ 𝓰 Φ hΦ hΦs)
  virasoro_central_extension_definition :
    VirasoroAlgebra ℝ =
      LieTwoCocycle.CentralExtension (WittAlgebra.virasoroCocycle ℝ)
  virasoro_mode_eq :
    ⁅VirasoroAlgebra.lgen ℝ m, VirasoroAlgebra.lgen ℝ q⁆
      = (m - q : ℝ) • VirasoroAlgebra.lgen ℝ (m + q)
        + if m + q = 0 then ((m ^ 3 - m : ℝ) / 12) • VirasoroAlgebra.cgen ℝ else 0
  virasoro_cocycle_nontrivial :
    (WittAlgebra.virasoroCocycle ℝ).cohomologyClass ≠ 0
  sugawara_central_charge_one :
    ∀ (α : ℝ) (v : ChargedFockSpace ℝ α),
      ChargedFockSpace.sugawaraRepresentation ℝ α (VirasoroAlgebra.cgen ℝ) v = v

/--
Proof-backed construction of the corrected finite-to-mode hierarchy packet.
-/
@[rep_depth transport]
theorem cliffordCantorModeHierarchyPacket
    (n : ℕ) (m q : ℤ) :
    CliffordCantorModeHierarchyPacket n m q := by
  refine
    { split_quaternion_basis := split_quaternion_basis_laws
      local_seed := local_split_quaternion_seed_laws
      local_null_projectors := local_null_projector_formula_laws
      local_lie_readout := ⟨epsGen_commutator_nullPlus, epsGen_commutator_nullMinus⟩
      fixed_local_causal_cone :=
        InfoGeometry.Clifford.SplitQ11CausalCone.localCausalConeClosure
      matrix_base_case := cl11_matrix_base_case
      split_quaternion_base_case := cl11_split_quaternion_base_case
      split_quaternion_matrix_case := split_quaternion_matrix_base_case
      finite_tower_step := finite_split_clifford_recursive_step n
      direct_limit_representatives := split_direct_limit_has_arbitrarily_deep_representatives
      cantor_refinement := ?_
      combined_sector_refinement := ?_
      combined_sector_idempotent := ?_
      local_krein_involution := local_krein_lattice_involution_sq
      heisenberg_central_extension_definition := rfl
      heisenberg_mode_eq := HeisenbergAlgebra.lie_jgen ℝ m q
      heisenberg_cocycle_nontrivial :=
        AbelianLieAlgebraOn.heisenbergCocycle_nontriviality ℝ
      kac_moody_central_extension_definition := ?_
      virasoro_central_extension_definition := rfl
      virasoro_mode_eq := VirasoroAlgebra.lgen_bracket ℝ m q
      virasoro_cocycle_nontrivial :=
        WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero ℝ
      sugawara_central_charge_one :=
        ChargedFockSpace.sugawaraRepresentation_cgen_apply ℝ }
  · intro w
    exact cantor_cylinder_indicator_refinement w
  · intro w k
    exact elementary_cantor_krein_sector_refinement w k
  · intro w k
    exact elementary_cantor_krein_sector_idempotent w k
  · intro 𝓰 _ _ Φ hΦ hΦs
    rfl

end TheoremPacket

end CliffordCantorModeHierarchy
