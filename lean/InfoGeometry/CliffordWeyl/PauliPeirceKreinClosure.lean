/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge

namespace InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge

open InfoGeometry.CliffordWeyl
open InfoGeometry.Clifford.Cl11Matrix

/- The complementary Peirce swap for the concrete Krein modular involution. -/
theorem J1_swap_corners_right :
    pauliChiral.Pright * J1 = J1 * pauliChiral.Pleft :=
  Pright_mul_swap pauliChiral J1 (J1_anticommutes_chi)

end InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
