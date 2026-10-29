/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SymmetricDissipator
import InfoGeometry.Algebra.PrimonSuperalgebra

/-! # Dissipator invariance of the actual full-matrix colimit parity sectors

The carrier is the existing real Boolean-word matrix ring direct limit, with
its already constructed involutive `globalParity`. We use the canonical
integer-linear structure of that ring; its elements remain full real matrices
modulo the existing bonding relation. No diagonal subalgebra is substituted.
-/

namespace InfoGeometry.Canonical.SymmetricDissipatorParity

open InfoGeometry.OperatorAlgebra.SymmetricDissipator
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.PrimonSuperalgebra

/-- The actual involutive parity commutes with the action of two odd charges. -/
theorem globalParity_dissipator (u v x : PrimonUHFAlgebra)
    (hu : isFermionic u) (hv : isFermionic v) :
    globalParity (dissipator (R := ℤ) u v x) =
      dissipator (R := ℤ) u v (globalParity x) :=
  parity_equivariant globalParityEquiv u v x hu hv

theorem dissipator_preserves_bosonic (u v x : PrimonUHFAlgebra)
    (hu : isFermionic u) (hv : isFermionic v) (hx : isBosonic x) :
    isBosonic (dissipator (R := ℤ) u v x) := by
  change globalParity (dissipator (R := ℤ) u v x) = _
  rw [globalParity_dissipator u v x hu hv, hx]

theorem dissipator_preserves_fermionic (u v x : PrimonUHFAlgebra)
    (hu : isFermionic u) (hv : isFermionic v) (hx : isFermionic x) :
    isFermionic (dissipator (R := ℤ) u v x) := by
  change globalParity (dissipator (R := ℤ) u v x) = _
  rw [globalParity_dissipator u v x hu hv, hx, map_neg]

/-- The symmetrized component is genuinely fixed by the existing involution. -/
theorem symmetrized_isBosonic (x : PrimonUHFAlgebra) :
    isBosonic (x + globalParity x) := by
  change globalParity (x + globalParity x) = _
  rw [map_add, globalParity_involutive, add_comm]

/-- The antisymmetrized component is genuinely sign-reversed. -/
theorem antisymmetrized_isFermionic (x : PrimonUHFAlgebra) :
    isFermionic (x - globalParity x) := by
  change globalParity (x - globalParity x) = _
  rw [map_sub, globalParity_involutive, neg_sub]

/-- Explicit descent from every full real matrix stage to this parity carrier. -/
theorem toColimit_dissipator (n : ℕ) (u v x : MatrixStage n) :
    toColimit n (Core.SquareZeroSandwich.symmDissipator u v x) =
      dissipator (R := ℤ) (toColimit n u) (toColimit n v) (toColimit n x) := by
  rw [← map_dissipator (R := ℤ)]
  congr 1
  simp only [dissipator_apply, Core.SquareZeroSandwich.symmDissipator_apply,
    Core.SquareZeroSandwich.symmSandwich_apply, two_smul]

end InfoGeometry.Canonical.SymmetricDissipatorParity
