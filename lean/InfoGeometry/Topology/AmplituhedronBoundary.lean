import Mathlib.Tactic
import InfoGeometry.Projective.ArnoldRelations

/-!
# Three-Point Amplituhedron Boundary Operators

This file records the finite algebraic surface behind the requested
three-channel boundary calculation.

Closed here:

* a three-point boundary packet has three nilpotent on-shell edge operators and
  three logarithmic channel forms;
* the advertised "super-amplitude volume" is exactly the three-term mixed
  expression;
* left multiplication by an on-shell nilpotent edge removes its own channel;
* if a separate owner supplies that the mixed expression vanishes, an arbitrary
  BCFW-style readout follows through the supplied comparison implication.

Not closed here:

* no amplituhedron or positive Grassmannian is constructed;
* no theorem identifies this algebraic packet with `F_Q(C^4,3)` de Rham
  cohomology;
* no BCFW recursion theorem is derived;
* no `N = 4` SYM state-count theorem or rank-32 cohomology theorem is proved.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

open InfoGeometry.Projective.ArnoldRelations

/--
Three-channel algebraic boundary data.

The `omega_*` fields are abstract logarithmic channel forms.  The `e_*` fields
are abstract on-shell edge operators.  Nilpotency is finite algebraic data, not
a derived theorem about concrete light-cone geometry.
-/
structure Amplituhedron3Point (Op : Type*) [Ring Op] where
  omega12 : Op
  omega23 : Op
  omega31 : Op
  e12 : Op
  e23 : Op
  e31 : Op
  e12_sq : e12 * e12 = 0
  e23_sq : e23 * e23 = 0
  e31_sq : e31 * e31 = 0
  e12_comm_omega23 : e12 * omega23 = omega23 * e12

variable {Op : Type*} [Ring Op]

/--
The three-term mixed boundary expression.

This is the algebraic carrier that a future geometric owner may compare with an
Arnold mixed relation or a BCFW residue balance.
-/
def superAmplitudeVolume (amp : Amplituhedron3Point Op) : Op :=
  amp.e12 * amp.omega23 + amp.e23 * amp.omega31 + amp.e31 * amp.omega12

/-- The boundary expression is definitionally the three mixed channels. -/
theorem superAmplitudeVolume_eq
    (amp : Amplituhedron3Point Op) :
    superAmplitudeVolume amp =
      amp.e12 * amp.omega23 + amp.e23 * amp.omega31 +
        amp.e31 * amp.omega12 :=
  rfl

/--
Left on-shell factorization at the `12` channel.

The first channel drops out because `e12 * e12 = 0`.  No commutativity or
amplituhedron geometry is used.
-/
theorem left_on_shell_factorization_12
    (amp : Amplituhedron3Point Op) :
    amp.e12 * superAmplitudeVolume amp =
      amp.e12 * amp.e23 * amp.omega31 +
        amp.e12 * amp.e31 * amp.omega12 := by
  calc
    amp.e12 * superAmplitudeVolume amp
        = amp.e12 *
            (amp.e12 * amp.omega23 +
              (amp.e23 * amp.omega31 + amp.e31 * amp.omega12)) := by
          simp [superAmplitudeVolume, add_assoc]
    _ = amp.e12 * (amp.e12 * amp.omega23) +
          amp.e12 * (amp.e23 * amp.omega31 + amp.e31 * amp.omega12) := by
          rw [mul_add]
    _ = amp.e12 * (amp.e12 * amp.omega23) +
          (amp.e12 * (amp.e23 * amp.omega31) +
            amp.e12 * (amp.e31 * amp.omega12)) := by
          rw [mul_add]
    _ = (amp.e12 * amp.e12) * amp.omega23 +
          (amp.e12 * (amp.e23 * amp.omega31) +
            amp.e12 * (amp.e31 * amp.omega12)) := by
          rw [mul_assoc]
    _ = 0 * amp.omega23 +
          (amp.e12 * (amp.e23 * amp.omega31) +
            amp.e12 * (amp.e31 * amp.omega12)) := by
          rw [amp.e12_sq]
    _ = amp.e12 * (amp.e23 * amp.omega31) +
          amp.e12 * (amp.e31 * amp.omega12) := by
          simp
    _ = amp.e12 * amp.e23 * amp.omega31 +
          amp.e12 * amp.e31 * amp.omega12 := by
          rw [← mul_assoc, ← mul_assoc]

/-- The `12` on-shell channel kills its own mixed term. -/
theorem left_self_channel_vanishes_12
    (amp : Amplituhedron3Point Op) :
    amp.e12 * (amp.e12 * amp.omega23) = 0 := by
  rw [← mul_assoc, amp.e12_sq, zero_mul]

/--
Left on-shell factorization at the `23` channel.

The second channel drops out because `e23 * e23 = 0`.
-/
theorem left_on_shell_factorization_23
    (amp : Amplituhedron3Point Op) :
    amp.e23 * superAmplitudeVolume amp =
      amp.e23 * amp.e12 * amp.omega23 +
        amp.e23 * amp.e31 * amp.omega12 := by
  calc
    amp.e23 * superAmplitudeVolume amp
        = amp.e23 *
            (amp.e12 * amp.omega23 +
              (amp.e23 * amp.omega31 + amp.e31 * amp.omega12)) := by
          simp [superAmplitudeVolume, add_assoc]
    _ = amp.e23 * (amp.e12 * amp.omega23) +
          amp.e23 * (amp.e23 * amp.omega31 + amp.e31 * amp.omega12) := by
          rw [mul_add]
    _ = amp.e23 * (amp.e12 * amp.omega23) +
          (amp.e23 * (amp.e23 * amp.omega31) +
            amp.e23 * (amp.e31 * amp.omega12)) := by
          rw [mul_add]
    _ = amp.e23 * (amp.e12 * amp.omega23) +
          ((amp.e23 * amp.e23) * amp.omega31 +
            amp.e23 * (amp.e31 * amp.omega12)) := by
          rw [mul_assoc]
    _ = amp.e23 * (amp.e12 * amp.omega23) +
          (0 * amp.omega31 +
            amp.e23 * (amp.e31 * amp.omega12)) := by
          rw [amp.e23_sq]
    _ = amp.e23 * (amp.e12 * amp.omega23) +
          amp.e23 * (amp.e31 * amp.omega12) := by
          simp
    _ = amp.e23 * amp.e12 * amp.omega23 +
          amp.e23 * amp.e31 * amp.omega12 := by
          rw [← mul_assoc, ← mul_assoc]

/-- The `23` on-shell channel kills its own mixed term. -/
theorem left_self_channel_vanishes_23
    (amp : Amplituhedron3Point Op) :
    amp.e23 * (amp.e23 * amp.omega31) = 0 := by
  rw [← mul_assoc, amp.e23_sq, zero_mul]

/--
Left on-shell factorization at the `31` channel.

The third channel drops out because `e31 * e31 = 0`.
-/
theorem left_on_shell_factorization_31
    (amp : Amplituhedron3Point Op) :
    amp.e31 * superAmplitudeVolume amp =
      amp.e31 * amp.e12 * amp.omega23 +
        amp.e31 * amp.e23 * amp.omega31 := by
  calc
    amp.e31 * superAmplitudeVolume amp
        = amp.e31 *
            (amp.e12 * amp.omega23 +
              (amp.e23 * amp.omega31 + amp.e31 * amp.omega12)) := by
          simp [superAmplitudeVolume, add_assoc]
    _ = amp.e31 * (amp.e12 * amp.omega23) +
          amp.e31 * (amp.e23 * amp.omega31 + amp.e31 * amp.omega12) := by
          rw [mul_add]
    _ = amp.e31 * (amp.e12 * amp.omega23) +
          (amp.e31 * (amp.e23 * amp.omega31) +
            amp.e31 * (amp.e31 * amp.omega12)) := by
          rw [mul_add]
    _ = amp.e31 * (amp.e12 * amp.omega23) +
          (amp.e31 * (amp.e23 * amp.omega31) +
            (amp.e31 * amp.e31) * amp.omega12) := by
          rw [mul_assoc]
    _ = amp.e31 * (amp.e12 * amp.omega23) +
          (amp.e31 * (amp.e23 * amp.omega31) +
            0 * amp.omega12) := by
          rw [amp.e31_sq]
    _ = amp.e31 * (amp.e12 * amp.omega23) +
          amp.e31 * (amp.e23 * amp.omega31) := by
          simp
    _ = amp.e31 * amp.e12 * amp.omega23 +
          amp.e31 * amp.e23 * amp.omega31 := by
          rw [← mul_assoc, ← mul_assoc]

/-- The `31` on-shell channel kills its own mixed term. -/
theorem left_self_channel_vanishes_31
    (amp : Amplituhedron3Point Op) :
    amp.e31 * (amp.e31 * amp.omega12) = 0 := by
  rw [← mul_assoc, amp.e31_sq, zero_mul]

/-- Compact packet of the three nilpotence-driven left factorizations. -/
theorem left_on_shell_factorization_packet
    (amp : Amplituhedron3Point Op) :
    amp.e12 * superAmplitudeVolume amp =
        amp.e12 * amp.e23 * amp.omega31 +
          amp.e12 * amp.e31 * amp.omega12 ∧
      amp.e23 * superAmplitudeVolume amp =
        amp.e23 * amp.e12 * amp.omega23 +
          amp.e23 * amp.e31 * amp.omega12 ∧
      amp.e31 * superAmplitudeVolume amp =
        amp.e31 * amp.e12 * amp.omega23 +
          amp.e31 * amp.e23 * amp.omega31 :=
  ⟨left_on_shell_factorization_12 amp,
    left_on_shell_factorization_23 amp,
    left_on_shell_factorization_31 amp⟩

/-! ## Arnold relation comparison interface -/

/--
Concrete comparison from an abstract Arnold mixed relation into a boundary ring.

The field `hKernel` says the target map kills the abstract Arnold relation.  The
field `hCompare` is the separate comparison obligation identifying that mapped
relation with this boundary packet's `superAmplitudeVolume`.
-/
structure ArnoldBoundaryRealization
    (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (Op : Type*) [Ring Op]
    (amp : Amplituhedron3Point Op) where
  w12 : ArnoldExterior R M
  w23 : ArnoldExterior R M
  w31 : ArnoldExterior R M
  toBoundary : ArnoldExterior R M →+* Op
  hKernel : arnoldMixedRelation R M w12 w23 w31 ∈ RingHom.ker toBoundary
  hCompare :
    toBoundary (arnoldMixedRelation R M w12 w23 w31) =
      superAmplitudeVolume amp

namespace ArnoldBoundaryRealization

/--
The abstract Arnold relation evaluates to zero in the selected boundary target.
-/
theorem arnold_relation_maps_to_zero
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {Op : Type*} [Ring Op]
    {amp : Amplituhedron3Point Op}
    (D : ArnoldBoundaryRealization R M Op amp) :
    D.toBoundary (arnoldMixedRelation R M D.w12 D.w23 D.w31) = 0 :=
  arnold_mixed_relation_vanishes_under_kernel_membership
    R M D.w12 D.w23 D.w31 D.toBoundary D.hKernel

/--
If the selected comparison identifies the mapped Arnold relation with the
boundary volume, then the boundary volume vanishes.

This is still only an algebraic comparison theorem.  It does not construct
concrete `d log Q` forms or prove BCFW recursion.
-/
theorem superAmplitudeVolume_zero_of_arnold
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {Op : Type*} [Ring Op]
    {amp : Amplituhedron3Point Op}
    (D : ArnoldBoundaryRealization R M Op amp) :
    superAmplitudeVolume amp = 0 := by
  rw [← D.hCompare]
  exact D.arnold_relation_maps_to_zero

end ArnoldBoundaryRealization

/--
Interface from algebraic Arnold-style closure to a BCFW-style readout.

The implication is data.  This file does not prove the analytic or physical
BCFW theorem.
-/
structure BCFWArnoldBoundaryComparison (Op : Type*) [Ring Op]
    (amp : Amplituhedron3Point Op) where
  bcfwReadout : Prop
  arnoldClosure_to_bcfw : superAmplitudeVolume amp = 0 → bcfwReadout

/-- A supplied Arnold-closure comparison yields the supplied BCFW readout. -/
theorem bcfw_of_superAmplitudeVolume_zero
    (amp : Amplituhedron3Point Op)
    (C : BCFWArnoldBoundaryComparison Op amp)
    (hClosure : superAmplitudeVolume amp = 0) :
    C.bcfwReadout :=
  C.arnoldClosure_to_bcfw hClosure

/--
A supplied Arnold-boundary comparison plus a supplied BCFW implication gives
the selected BCFW readout.

The analytic/physical comparison remains explicit data in `C`; this theorem
only composes the algebraic Arnold kernel readout with that supplied implication.
-/
theorem bcfw_of_arnold_boundary_realization
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (amp : Amplituhedron3Point Op)
    (D : ArnoldBoundaryRealization R M Op amp)
    (C : BCFWArnoldBoundaryComparison Op amp) :
    C.bcfwReadout :=
  C.arnoldClosure_to_bcfw D.superAmplitudeVolume_zero_of_arnold

/-! ## Finite `16 + 16 = 32` boundary carrier -/

/-- The two chiral halves used by the finite boundary carrier. -/
inductive BoundaryChirality where
  | chiral
  | antiChiral
  deriving DecidableEq, Fintype, Repr

/-- Sixteen labels for one chiral half of the finite readout carrier. -/
abbrev ChiralBoundaryState16 : Type :=
  Fin 16

/--
The finite `16 + 16` carrier.

This is only a carrier.  A theorem identifying it with de Rham cohomology of
`F_Q(C^4,3)` must be supplied by a separate cohomology owner.
-/
abbrev SuperBoundaryState32 : Type :=
  BoundaryChirality × ChiralBoundaryState16

/-- The chirality set has two elements. -/
theorem boundaryChirality_card :
    Fintype.card BoundaryChirality = 2 := by
  native_decide

/-- One chiral half has sixteen labels. -/
theorem chiralBoundaryState16_card :
    Fintype.card ChiralBoundaryState16 = 16 := by
  simp [ChiralBoundaryState16]

/-- The finite boundary carrier has `2 * 16 = 32` labels. -/
theorem superBoundaryState32_card :
    Fintype.card SuperBoundaryState32 = 32 := by
  rw [Fintype.card_prod, boundaryChirality_card, chiralBoundaryState16_card]

/-- Split the carrier as an explicit chiral/anti-chiral sum. -/
def superBoundaryState32EquivSum :
    SuperBoundaryState32 ≃ (ChiralBoundaryState16 ⊕ ChiralBoundaryState16) where
  toFun
    | (BoundaryChirality.chiral, i) => Sum.inl i
    | (BoundaryChirality.antiChiral, i) => Sum.inr i
  invFun
    | Sum.inl i => (BoundaryChirality.chiral, i)
    | Sum.inr i => (BoundaryChirality.antiChiral, i)
  left_inv := by
    intro x
    rcases x with ⟨c, i⟩
    cases c <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

/-- The sum presentation also has cardinality `32`. -/
theorem superBoundaryState32_sum_card :
    Fintype.card (ChiralBoundaryState16 ⊕ ChiralBoundaryState16) = 32 := by
  rw [Fintype.card_sum]
  norm_num [ChiralBoundaryState16]

/-- The three mixed channel terms of a boundary packet. -/
def channelTerm (amp : Amplituhedron3Point Op) (c : Fin 3) : Op :=
  if c = 0 then
    amp.e12 * amp.omega23
  else if c = 1 then
    amp.e23 * amp.omega31
  else
    amp.e31 * amp.omega12

/--
An explicit 32-entry boundary basis interface.

The entries are indexed by the finite `16 + 16` carrier and are assigned to one
of the three algebraic mixed channels.  This structure does not assert linear
independence or cohomological completeness.
-/
structure BoundaryBasis32 (Op : Type*) [Ring Op]
    (amp : Amplituhedron3Point Op) where
  basis : SuperBoundaryState32 → Op
  channel : SuperBoundaryState32 → Fin 3
  basis_eq_channelTerm : ∀ s, basis s = channelTerm amp (channel s)

namespace BoundaryBasis32

/-- The basis interface has exactly thirty-two labels. -/
theorem label_card
    (amp : Amplituhedron3Point Op)
    (_B : BoundaryBasis32 Op amp) :
    Fintype.card SuperBoundaryState32 = 32 :=
  superBoundaryState32_card

/-- Read back that every basis entry is one of the declared channel terms. -/
theorem basis_entry_readout
    (amp : Amplituhedron3Point Op)
    (B : BoundaryBasis32 Op amp)
    (s : SuperBoundaryState32) :
    B.basis s = channelTerm amp (B.channel s) :=
  B.basis_eq_channelTerm s

/-- Column matrix form of the 32-entry boundary basis interface. -/
def basisMatrix
    (amp : Amplituhedron3Point Op)
    (B : BoundaryBasis32 Op amp) :
    Matrix SuperBoundaryState32 (Fin 1) Op :=
  fun s _ => B.basis s

/-- Matrix entries are the declared channel terms. -/
theorem basisMatrix_entry
    (amp : Amplituhedron3Point Op)
    (B : BoundaryBasis32 Op amp)
    (s : SuperBoundaryState32)
    (j : Fin 1) :
    B.basisMatrix amp s j = channelTerm amp (B.channel s) :=
  B.basis_eq_channelTerm s

end BoundaryBasis32

/-- Canonical 32-state index used by downstream transport layers. -/
abbrev SuperBoundaryState32Index : Type := Fin 32

/-- Canonical equivalence between the abstract 32-element boundary carrier and `Fin 32`. -/
noncomputable def superBoundaryState32IndexEquiv (Op : Type*) [Ring Op] :
    SuperBoundaryState32 ≃ Fin 32 :=
  Fintype.equivFinOfCardEq superBoundaryState32_card

/-- 32-way re-indexed boundary matrix over `Fin 32`. -/
noncomputable def boundaryBasis32Matrix
    (Op : Type*) [Ring Op]
    (amp : Amplituhedron3Point Op)
    (B : BoundaryBasis32 Op amp) :
    Matrix (Fin 32) (Fin 1) Op :=
  fun i _ =>
    B.basis ((superBoundaryState32IndexEquiv (Op := Op)).symm i)

namespace BoundaryBasis32

/-- Every row in the `Fin 32` re-indexed basis matrix is still a declared channel term. -/
theorem basis32_entry_channel
    (Op : Type*) [Ring Op]
    (amp : Amplituhedron3Point Op)
    (B : BoundaryBasis32 Op amp)
    (s : Fin 32)
    (_j : Fin 1) :
    boundaryBasis32Matrix Op amp B s _j =
      channelTerm amp (B.channel ((superBoundaryState32IndexEquiv (Op := Op)).symm s) ) := by
  simp [boundaryBasis32Matrix, B.basis_eq_channelTerm]

end BoundaryBasis32

end InfoGeometry.Topology.AmplituhedronBoundary
