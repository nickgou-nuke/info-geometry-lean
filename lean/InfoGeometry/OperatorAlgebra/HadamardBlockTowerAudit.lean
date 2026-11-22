/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.HadamardBlockTower

/-!
# Kernel axiom audit for the finite Walsh and bent-sign theorems.
-/

open InfoGeometry.OperatorAlgebra.HadamardBlockTower

#print axioms walsh_orth
#print axioms walshCharacterTransform_exact
#print axioms walshCharacterTransform_transports_spike
#print axioms semiBentSign8_walsh_spectrum
#print axioms semiBentSign8_walsh_bound_and_attainment
#print axioms signMaskWalshTransform8_lower_bound
#print axioms signedWalsh_orth
#print axioms bentSign16_sq
#print axioms bentWalshMatrix16_orth
#print axioms bentSign16_walsh_flat
