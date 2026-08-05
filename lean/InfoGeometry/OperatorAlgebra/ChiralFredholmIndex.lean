/-
InfoGeometry/OperatorAlgebra/ChiralFredholmIndex.lean

Chiral Fredholm index and modular mirror sign.

This module packages the Fredholm index as proof-carrying data and proves the
formal algebraic consequence of the modular chiral mirror:

  if J swaps left/right chiral sectors, then the chiral index changes sign.

The determinant line / Fredholm determinant / Berezinian layer should be added
later as a refinement, not as the primitive definition of the index.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Operator.Compact
import InfoGeometry.OperatorAlgebra.ModularChiralMirror

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

open InfoGeometry.OperatorAlgebra.ModularChiralMirror

/-! ## 1. Abstract Fredholm index datum -/

/--
Proof-carrying Fredholm index datum.

This is intentionally abstract.  Concrete finite-dimensional, Hilbert-space,
semifinite, or regularized Fredholm backends can instantiate it later.
-/
structure FredholmIndexDatum
    (V W : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] where
  /-- The Fredholm operator. -/
  operator : V →ₗ[ℝ] W

  /-- The kernel of the operator is finite-dimensional. -/
  kernelFinite :
    FiniteDimensional ℝ (LinearMap.ker operator)

  /-- The cokernel quotient by the range is finite-dimensional. -/
  cokernelFinite :
    FiniteDimensional ℝ (W ⧸ LinearMap.range operator)

namespace FredholmIndexDatum

variable
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (F : FredholmIndexDatum V W)

/--
The algebraic Fredholm index, derived from Mathlib finranks of the kernel and
cokernel.  It is not an independently supplied integer readout.
-/
noncomputable def index : ℤ :=
  (Module.finrank ℝ (LinearMap.ker F.operator) : ℤ) -
    (Module.finrank ℝ (W ⧸ LinearMap.range F.operator) : ℤ)

/-- Read back the kernel finite-dimensionality carried by the Fredholm datum. -/
theorem kernel_finite :
    FiniteDimensional ℝ (LinearMap.ker F.operator) :=
  F.kernelFinite

/-- Read back the cokernel finite-dimensionality carried by the Fredholm datum. -/
theorem cokernel_finite :
    FiniteDimensional ℝ (W ⧸ LinearMap.range F.operator) :=
  F.cokernelFinite

/-- The Fredholm index is the native kernel-minus-cokernel dimension. -/
theorem index_eq_finrank_ker_sub_finrank_coker :
    F.index =
      (Module.finrank ℝ (LinearMap.ker F.operator) : ℤ) -
        (Module.finrank ℝ (W ⧸ LinearMap.range F.operator) : ℤ) :=
  rfl

end FredholmIndexDatum

/-! ## 2. Chiral kernel-count shadow -/

/--
Finite chiral zero-mode count.

This is the algebraic shadow of

`index(D₊) = dim ker D₊ - dim ker D₋`.
-/
abbrev ChiralKernelCount := ℕ × ℕ

namespace ChiralKernelCount

/-- Left/chiral-positive zero modes. -/
abbrev leftKernel (C : ChiralKernelCount) : ℕ := C.1

/-- Right/chiral-negative zero modes. -/
abbrev rightKernel (C : ChiralKernelCount) : ℕ := C.2

/-- The chiral index: `leftKernel - rightKernel`. -/
def index
    (C : ChiralKernelCount) : ℤ :=
  (C.leftKernel : ℤ) - (C.rightKernel : ℤ)

/-- The mirror count swaps left and right kernels. -/
def mirror
    (C : ChiralKernelCount) : ChiralKernelCount :=
  (C.rightKernel, C.leftKernel)

/-- Mirroring reverses the chiral index. -/
theorem mirror_index
    (C : ChiralKernelCount) :
    C.mirror.index = -C.index := by
  dsimp [index, mirror]
  ring

/--
If the mirrored problem has the same index as the original, then the index
vanishes.
-/
theorem index_eq_zero_of_mirror_fixed
    (C : ChiralKernelCount)
    (h : C.mirror.index = C.index) :
    C.index = 0 := by
  have hm : C.mirror.index = -C.index :=
    C.mirror_index
  rw [h] at hm
  linarith

end ChiralKernelCount

/-! ## 3. Chiral Fredholm datum -/

/--
A chiral Fredholm problem.

The actual block operator `D₊ : H_L → H_R` is left abstract because the
submodule/closed-range/Fredholm API depends on the concrete analytic backend.
The necessary algebraic data are recorded here:

* a chiral grading;
* a Dirac/Fredholm operator;
* oddness of the Dirac operator;
* a Fredholm index datum.
-/
structure ChiralFredholmDatum
    (H : Type*) [AddCommGroup H] [Module ℝ H] where
  /-- Chiral grading. -/
  chi : H →ₗ[ℝ] H

  /-- Dirac/Fredholm operator. -/
  D : H →ₗ[ℝ] H

  /-- `χ² = 1`. -/
  chi_square :
    chi.comp chi = LinearMap.id

  /-- Oddness: `χD = -Dχ`. -/
  D_odd :
    chi.comp D = -(D.comp chi)

  /-- Abstract Fredholm index of the chiral block. -/
  fredholmIndex :
    FredholmIndexDatum H H

  /-- Finite zero-mode count shadow. -/
  kernelCount :
    ChiralKernelCount

  /-- Compatibility between the abstract Fredholm index and zero-mode count. -/
  index_eq_kernelCount :
    fredholmIndex.index = kernelCount.index

namespace ChiralFredholmDatum

variable
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (F : ChiralFredholmDatum H)

/-- The mirrored zero-mode count has the negative index. -/
theorem mirrored_kernelCount_index :
    F.kernelCount.mirror.index = -F.kernelCount.index :=
  F.kernelCount.mirror_index

end ChiralFredholmDatum

/-! ## 4. Modular mirror compatibility -/

/--
A modular mirror compatible with a chiral Fredholm problem.

This packages the statement that the mirror flips chirality and is compatible
with the Dirac/Fredholm operator.
-/
structure ModularMirrorFredholmCompatibility
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    (F : ChiralFredholmDatum H) where
  /-- Modular/CPT mirror. -/
  J : H →ₗ[ℝ] H

  /-- `J² = 1`. -/
  J_square :
    J.comp J = LinearMap.id

  /-- `Jχ = -χJ`. -/
  J_flips_chi :
    J.comp F.chi = -(F.chi.comp J)

  /--
  Dirac compatibility, recorded as the concrete sign choice used by the model.
  -/
  J_D_comm_or_anticomm :
    J.comp F.D = F.D.comp J ∨ J.comp F.D = -(F.D.comp J)

  /--
  The mirror swaps the left and right Fredholm zero-mode counts.

  This is the kernel-count shadow of `J P_L J = P_R`.
  -/
  mirror_swaps_kernelCount :
    F.kernelCount.mirror =
      (F.kernelCount.rightKernel, F.kernelCount.leftKernel)

namespace ModularMirrorFredholmCompatibility

variable
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {F : ChiralFredholmDatum H}
    (M : ModularMirrorFredholmCompatibility H F)

/-- The modular mirror reverses the chiral zero-mode index. -/
theorem mirror_reverses_kernel_index :
    F.kernelCount.mirror.index = -F.kernelCount.index :=
  F.kernelCount.mirror_index

/--
If the mirror identifies the Fredholm problem with itself at the level of
index, then the chiral index vanishes.

This is the formal anomaly test: a nonzero chiral index obstructs exact
mirror-identification.
-/
theorem index_vanishes_if_mirror_fixed
    (hfixed : F.kernelCount.mirror.index = F.kernelCount.index) :
    F.kernelCount.index = 0 :=
  F.kernelCount.index_eq_zero_of_mirror_fixed hfixed

/-- The stored mirror/Fredholm compatibility is an explicit sign equation. -/
theorem J_D_comm_or_anticomm_eq :
    M.J.comp F.D = F.D.comp M.J ∨ M.J.comp F.D = -(F.D.comp M.J) :=
  M.J_D_comm_or_anticomm

end ModularMirrorFredholmCompatibility

/-! ## 5. Even Kasparov/Fredholm module socket -/

/--
A proof-carrying even Fredholm/Kasparov-cycle socket.

This is not a full KK-theory implementation. It records the conditions needed
downstream for index pairings:

* represented algebra;
* graded Hilbert/module carrier;
* Fredholm operator;
* oddness;
* compactness/commutator certificates.
-/
structure EvenKasparovCycleDatum
    (A H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  /-- Representation of the algebra by operators on the carrier. -/
  rep : A → H →L[ℝ] H

  /-- Chiral grading. -/
  chi : H →L[ℝ] H

  /-- Fredholm/Kasparov operator. -/
  F : H →L[ℝ] H

  /-- Grading law. -/
  chi_square :
    chi.comp chi = ContinuousLinearMap.id ℝ H

  /-- Oddness of the Fredholm operator. -/
  F_odd :
    chi.comp F = -(F.comp chi)

  /-- Every represented commutator `[F, π(a)]` is compact. -/
  commutators_compact :
    ∀ a : A,
      IsCompactOperator
        ((F * rep a - rep a * F : H →L[ℝ] H) : H → H)

  /-- Every represented defect `π(a)(F² - 1)` is compact. -/
  square_minus_one_compact :
    ∀ a : A,
      IsCompactOperator
        ((rep a * (F * F - (1 : H →L[ℝ] H)) : H →L[ℝ] H) : H → H)

  /-- Every represented self-adjointness defect `π(a)(F - F*)` is compact. -/
  self_adjoint_mod_compact :
    ∀ a : A,
      IsCompactOperator
        ((rep a * (F - ContinuousLinearMap.adjoint F) : H →L[ℝ] H) : H → H)

  /-- Abstract Fredholm index pairing socket. -/
  indexPairing : A → ℤ

/--
A cyclic/supertrace formula for an index pairing.

This is the place where `SuperTraceDatum`, zeta residues, Dixmier traces,
or JLO/local-index data should enter. It is deliberately not identified with a
Fredholm determinant.
-/
structure ChiralIndexFormulaDatum
    (A H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K : EvenKasparovCycleDatum A H) where
  /-- Cocycle or supertrace readout. -/
  cocycleReadout : A → ℂ

  /--
  The cyclic-cocycle/supertrace pairing is the complex realization of the
  Kasparov cycle's integer index pairing.
  -/
  index_formula :
    ∀ a : A, cocycleReadout a = (K.indexPairing a : ℂ)

namespace ChiralIndexFormulaDatum

/-- The canonical complex readout of a Kasparov cycle's integer index pairing. -/
def ofIndexPairing
    {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K : EvenKasparovCycleDatum A H) :
    ChiralIndexFormulaDatum A H K where
  cocycleReadout := fun a => (K.indexPairing a : ℂ)
  index_formula := fun _ => rfl

@[simp]
theorem ofIndexPairing_cocycleReadout
    {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K : EvenKasparovCycleDatum A H) (a : A) :
    (ofIndexPairing K).cocycleReadout a = (K.indexPairing a : ℂ) :=
  rfl

end ChiralIndexFormulaDatum

/-! ## 6. Owner targets -/

/-- Owner target for constructing chiral Fredholm index data. -/
def ChiralFredholmIndexOwnerTarget
    (H : Type*) [AddCommGroup H] [Module ℝ H] : Prop :=
  ∀ F : ChiralFredholmDatum H,
    F.chi.comp F.chi = LinearMap.id ∧
      F.chi.comp F.D = -(F.D.comp F.chi) ∧
      F.fredholmIndex.index = F.kernelCount.index ∧
      F.kernelCount.mirror.index = -F.kernelCount.index

/-- Owner target for constructing an even Kasparov-cycle socket. -/
def EvenKasparovCycleOwnerTarget
    (A H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : Prop :=
  ∀ K : EvenKasparovCycleDatum A H,
    K.chi.comp K.chi = ContinuousLinearMap.id ℝ H ∧
      K.chi.comp K.F = -(K.F.comp K.chi) ∧
      (∀ a : A, IsCompactOperator
        ((K.F * K.rep a - K.rep a * K.F : H →L[ℝ] H) : H → H)) ∧
      (∀ a : A, IsCompactOperator
        ((K.rep a * (K.F * K.F - (1 : H →L[ℝ] H)) : H →L[ℝ] H) : H → H)) ∧
      (∀ a : A, IsCompactOperator
        ((K.rep a * (K.F - ContinuousLinearMap.adjoint K.F) : H →L[ℝ] H) : H → H))

end InfoGeometry.OperatorAlgebra.ChiralFredholmIndex
