/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.ColorCARStandardModel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic


namespace InfoGeometry.Physics.SignedThreeModeCAR

open InfoGeometry.Physics.ColorCARStandardModel

/-!
# Signed (Jordan-Wigner) three-mode CAR operators

Define sign-corrected creation/annihilation operators on CAR3 to satisfy
fermionic cross-mode anticommutation relations for distinct modes.
-/

noncomputable section

def Nparity0 : CAR3 := N_plus ⊗ₜ[ℂ] 1 ⊗ₜ[ℂ] 1
def Nparity1 : CAR3 := 1 ⊗ₜ[ℂ] N_plus ⊗ₜ[ℂ] 1
def Nparity2 : CAR3 := 1 ⊗ₜ[ℂ] 1 ⊗ₜ[ℂ] N_plus

def gamma0 : CAR3 := Nparity0


end

end InfoGeometry.Physics.SignedThreeModeCAR
