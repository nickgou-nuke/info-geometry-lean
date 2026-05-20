import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.Trace
import InfoGeometry.Algebraic.SplitCliffordCarrier
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean

Native Clifford-language chiral carrier.

The old chiral carrier is folded into the Clifford grade involution:
* parity is Mathlib's grade involution;
* chiral sectors are the even/odd eigenspaces;
* modular flow is the underlying linear action of parity;
* all legacy names are compatibility shadows only.
-/

noncomputable section

namespace InfoGeometry.Algebraic

open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Algebraic.SplitSuperGeometry

/--
Native Clifford chiral algebra on the split Clifford carrier.

This is the new canonical surface. The only primitive datum is the Clifford
grade involution; everything else is derived from it.
-/
structure ChiralOperatorAlgebra (n : ℕ) where
  /-- Clifford grade involution, the parity operator. -/
  parity : ParityInvolution (Cl_nn n)

  /-- Modular boost as the underlying linear parity action. -/
  modularBoost : Module.End ℝ (Cl_nn n) := parity.toLinearMap

  /-- Left chiral sector, i.e. the `+1` eigenspace. -/
  leftChiralCharge : Submodule ℝ (Cl_nn n) := parity.evenPart

  /-- Right chiral sector, i.e. the `-1` eigenspace. -/
  rightChiralCharge : Submodule ℝ (Cl_nn n) := parity.oddPart

  /-- Modular Hamiltonian readout, identified with the modular boost. -/
  modularHamiltonian : Module.End ℝ (Cl_nn n) := modularBoost

namespace ChiralOperatorAlgebra

variable {n : ℕ}

/-- The Clifford grade involution read out as the chiral parity. -/
def chiralParity (C : ChiralOperatorAlgebra n) : ParityInvolution (Cl_nn n) :=
  C.parity

/-- Compatibility shadow for the old boost name. -/
def boost (C : ChiralOperatorAlgebra n) : Module.End ℝ (Cl_nn n) :=
  C.modularBoost

/-- Compatibility shadow for the old `uPlus` name. -/
def uPlus (C : ChiralOperatorAlgebra n) : Submodule ℝ (Cl_nn n) :=
  C.leftChiralCharge

/-- Compatibility shadow for the old `uMinus` name. -/
def uMinus (C : ChiralOperatorAlgebra n) : Submodule ℝ (Cl_nn n) :=
  C.rightChiralCharge

/-- Compatibility shadow for the old conformal operator name. -/
def conformalOperator (C : ChiralOperatorAlgebra n) : Module.End ℝ (Cl_nn n) :=
  C.modularHamiltonian

/-- The canonical Clifford chiral algebra. -/
def canonical (n : ℕ) : ChiralOperatorAlgebra n where
  parity := splitCliffordParityInvolution n

@[simp]
theorem canonical_chiralParity
    (n : ℕ) :
    (canonical n).chiralParity = splitCliffordParityInvolution n :=
  rfl

@[simp]
theorem canonical_modularBoost
    (n : ℕ) :
    (canonical n).modularBoost =
      (splitCliffordParityInvolution n).toLinearMap :=
  rfl

@[simp]
theorem canonical_leftChiralCharge
    (n : ℕ) :
    (canonical n).leftChiralCharge =
      (splitCliffordParityInvolution n).evenPart :=
  rfl

@[simp]
theorem canonical_rightChiralCharge
    (n : ℕ) :
    (canonical n).rightChiralCharge =
      (splitCliffordParityInvolution n).oddPart :=
  rfl

@[simp]
theorem canonical_modularHamiltonian
    (n : ℕ) :
    (canonical n).modularHamiltonian =
      (canonical n).modularBoost :=
  rfl

/-- The old carrier name now points at the native Clifford chiral algebra. -/
abbrev asCarrier (n : ℕ) := ChiralOperatorAlgebra n

/--
The Clifford root-law vector rule in the new canonical language.
-/
theorem canonical_root_laws
    {n : ℕ} (v : SplitModule n) :
    (canonical n).parity.toAlgEquiv (splitCliffordVector n v) =
      - splitCliffordVector n v :=
  splitCliffordParityInvolution_vector (n := n) v

/--
The positive split generator in `Cl(1,1)` is odd under the canonical parity.

This is the smallest explicit split Clifford super-grading in the native
carrier language.
-/
@[simp]
theorem canonical_cl11_pos_generator_odd :
    (canonical 1).parity.toAlgEquiv
        (splitCliffordVector 1 (splitBasisVector (Sum.inl (0 : Fin 1)))) =
      - splitCliffordVector 1 (splitBasisVector (Sum.inl (0 : Fin 1))) := by
  simpa using
    (canonical_root_laws (n := 1)
      (v := splitBasisVector (Sum.inl (0 : Fin 1))))

/--
The negative split generator in `Cl(1,1)` is odd under the canonical parity.

Together with `canonical_cl11_pos_generator_odd`, this gives the symmetric
`Cl(1,1)` super-graded atom.
-/
@[simp]
theorem canonical_cl11_neg_generator_odd :
    (canonical 1).parity.toAlgEquiv
        (splitCliffordVector 1 (splitBasisVector (Sum.inr (0 : Fin 1)))) =
      - splitCliffordVector 1 (splitBasisVector (Sum.inr (0 : Fin 1))) := by
  simpa using
    (canonical_root_laws (n := 1)
      (v := splitBasisVector (Sum.inr (0 : Fin 1))))

end ChiralOperatorAlgebra

end InfoGeometry.Algebraic
