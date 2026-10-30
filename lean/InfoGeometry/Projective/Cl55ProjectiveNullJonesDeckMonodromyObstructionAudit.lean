/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstruction

/-!
# Source audit: conditional Q55 exchange monodromy obstruction

Given actual ordered exchange paths satisfying the stated Artin homotopy,
their covering permutation monodromy is the native B₃-to-S₃ shadow. The
Jones representation therefore cannot factor through that finite deck
monodromy. The path and homotopy premises remain explicit.
-/

#print axioms InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstruction.q55ExchangePermutationMonodromy_eq_braidPermutation
#print axioms InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstruction.q55FirstExchangeSquare_mem_pureConfigurationLoop
#print axioms InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstruction.q55JonesRepresentation_not_factor_through_exchangeDeckMonodromy
