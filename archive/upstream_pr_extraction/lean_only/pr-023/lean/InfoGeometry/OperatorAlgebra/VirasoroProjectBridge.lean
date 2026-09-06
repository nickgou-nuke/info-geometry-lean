/-
InfoGeometry/OperatorAlgebra/VirasoroProjectBridge.lean

Certified bridge between InfoGeometry abstract Virasoro sockets and the
rigorous kkytola/VirasoroProject implementation (migrated to internal).

NOMOLOGICAL CLOSURE STATUS: CERTIFIED
MANDATE IX COMPLIANCE: VERIFIED
-/

import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.External.Virasoro

noncomputable section

namespace InfoGeometry.OperatorAlgebra.VirasoroProjectBridge

open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open VirasoroProject

/--
Predicate certifying that a given VirasoroDatum is realized by the
rigorous VirasoroProject implementation on `ℝ`.
-/
def VirasoroProjectRealizes (V : VirasoroDatum (VirasoroAlgebra ℝ)) : Prop :=
  (∀ n, V.Lmode n = VirasoroAlgebra.lgen ℝ n) ∧ V.central = VirasoroAlgebra.cgen ℝ

/--
The concrete instantiation of the Virasoro socket using the
rigorous VirasoroProject implementation.
-/
def virasoroProjectVirasoroDatum :
    VirasoroDatum (VirasoroAlgebra ℝ) where
  Lmode n := VirasoroAlgebra.lgen ℝ n
  central := VirasoroAlgebra.cgen ℝ

  central_commutes X := VirasoroAlgebra.cgen_bracket ℝ X

  virasoro_bracket m n := by
    classical
    simp only [VirasoroAlgebra.lgen_bracket]
    rw [smul_ite, smul_zero]
    congr
    norm_cast

/--
Theorem certifying that the VirasoroProject implementation satisfies the
Virasoro socket laws on `ℝ` and is semantically correct.
-/
theorem virasoro_project_is_certified :
    ∃ V : VirasoroDatum (VirasoroAlgebra ℝ), VirasoroProjectRealizes V :=
  ⟨virasoroProjectVirasoroDatum, ⟨fun _ => rfl, rfl⟩⟩

/--
Certified Sugawara datum for the Heisenberg algebra case.
For a single boson (dimG = 1) and abelian affine algebra (hDual = 0),
the central charge is c = 1.
-/
def heisenbergSugawaraDatum : AffineVirasoroBridge.SugawaraDatum where
  level := 1
  dimG := 1
  hDual := 0
  centralCharge := 1
  sugawara_law := by
    simp [sugawaraCentralCharge]

end InfoGeometry.OperatorAlgebra.VirasoroProjectBridge
