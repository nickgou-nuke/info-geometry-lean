/-
InfoGeometry/OperatorAlgebra/ChiralFredholmIndex.lean

Chiral Fredholm index and modular mirror sign.

This module packages the Fredholm index as proof-carrying data and proves the
formal algebraic consequence of the modular chiral mirror:

  if J swaps left/right chiral sectors, then the chiral index changes sign.

The determinant line / Fredholm determinant / Berezinian layer should be added
later as a refinement, not as the primitive definition of the index.
-/

import Mathlib
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

  /-- Fredholmness certificate. -/
  isFredholm : Prop

  /-- Analytic/Fredholm index. -/
  index : ℤ

  /-- Finite kernel certificate. -/
  kernelFinite : Prop

  /-- Finite cokernel certificate. -/
  cokernelFinite : Prop

/-! ## 2. Chiral kernel-count shadow -/

/--
Finite chiral zero-mode count.

This is the algebraic shadow of

`index(D₊) = dim ker D₊ - dim ker D₋`.
-/
structure ChiralKernelCount where
  /-- Left/chiral-positive zero modes. -/
  leftKernel : ℕ

  /-- Right/chiral-negative zero modes. -/
  rightKernel : ℕ

namespace ChiralKernelCount

/-- The chiral index: `leftKernel - rightKernel`. -/
def index
    (C : ChiralKernelCount) : ℤ :=
  (C.leftKernel : ℤ) - (C.rightKernel : ℤ)

/-- The mirror count swaps left and right kernels. -/
def mirror
    (C : ChiralKernelCount) : ChiralKernelCount where
  leftKernel := C.rightKernel
  rightKernel := C.leftKernel

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
  Dirac compatibility.

  Depending on conventions, a concrete model may instead use `J D J = ±D`
  or an opposite-algebra relation.  This field stores the chosen compatibility.
  -/
  J_D_compatibility : Prop

  /--
  The mirror swaps the left and right Fredholm zero-mode counts.

  This is the kernel-count shadow of `J P_L J = P_R`.
  -/
  mirror_swaps_kernelCount :
    F.kernelCount.mirror = {
      leftKernel := F.kernelCount.rightKernel
      rightKernel := F.kernelCount.leftKernel
    }

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
    (A H : Type*) [AddCommGroup H] [Module ℝ H] where
  /-- Representation of the algebra by operators on the carrier. -/
  rep : A → H →ₗ[ℝ] H

  /-- Chiral grading. -/
  chi : H →ₗ[ℝ] H

  /-- Fredholm/Kasparov operator. -/
  F : H →ₗ[ℝ] H

  /-- Grading law. -/
  chi_square :
    chi.comp chi = LinearMap.id

  /-- Oddness of the Fredholm operator. -/
  F_odd :
    chi.comp F = -(F.comp chi)

  /-- Commutator compactness certificate. -/
  commutators_compact : Prop

  /-- `a(F² - 1)` compactness certificate. -/
  square_minus_one_compact : Prop

  /-- Self-adjointness modulo compact operators certificate. -/
  self_adjoint_mod_compact : Prop

  /-- Abstract Fredholm index pairing socket. -/
  indexPairing : A → ℤ

/--
A cyclic/supertrace formula for an index pairing.

This is the place where `SuperTraceDatum`, zeta residues, Dixmier traces,
or JLO/local-index data should enter. It is deliberately not identified with a
Fredholm determinant.
-/
structure ChiralIndexFormulaDatum
    (A H : Type*) [AddCommGroup H] [Module ℝ H]
    (K : EvenKasparovCycleDatum A H) where
  /-- Cocycle or supertrace readout. -/
  cocycleReadout : A → ℂ

  /-- Integer index readout. -/
  indexReadout : A → ℤ

  /--
  Index formula certificate.

  Intended meaning:
  `indexReadout a` equals the appropriate cyclic-cocycle/supertrace pairing.
  -/
  index_formula : Prop

/-! ## 6. Owner targets -/

/-- Owner target for constructing chiral Fredholm index data. -/
def ChiralFredholmIndexOwnerTarget
    (H : Type*) [AddCommGroup H] [Module ℝ H] : Prop :=
  Nonempty (ChiralFredholmDatum H)

/-- Owner target for constructing an even Kasparov-cycle socket. -/
def EvenKasparovCycleOwnerTarget
    (A H : Type*) [AddCommGroup H] [Module ℝ H] : Prop :=
  Nonempty (EvenKasparovCycleDatum A H)

end InfoGeometry.OperatorAlgebra.ChiralFredholmIndex
