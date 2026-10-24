/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracPeircePerfectPairing
import InfoGeometry.SuperMetriplectic.WittDiracPeircePairing

/-! The neutral Witt support carries the real Dirac perfect pairing on its
off-diagonal matrix corner. Every covector has a unique trace representative.
-/
namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
open Matrix InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.Core.PeirceDecomposition

theorem witt_diracCornerTracePairing_isPerfPair (n : ℕ) :
    ((neutralKreinData n).diracCornerTracePairing
      (wittAnnihilator n * wittCreator n)
      (witt_support_idempotent n) (witt_support_diracAdjoint n)).IsPerfPair :=
  (neutralKreinData n).diracCornerTracePairing_isPerfPair _
    (witt_support_idempotent n) (witt_support_diracAdjoint n)

theorem witt_existsUnique_dirac_trace_representative (n : ℕ)
    (f : Module.Dual ℝ (LinearMap.range
      (component10Linear (wittAnnihilator n * wittCreator n)))) :
    ∃! X : LinearMap.range (component10Linear (wittAnnihilator n * wittCreator n)),
      ∀ Y : LinearMap.range (component10Linear (wittAnnihilator n * wittCreator n)),
        trace (X.val * (neutralKreinData n).diracAdjoint Y.val) = f Y :=
  (neutralKreinData n).existsUnique_dirac_trace_representative _
    (witt_support_idempotent n) (witt_support_diracAdjoint n) f

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
