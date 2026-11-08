/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner

/-!
# Canonical CAR current owner

The source-backed finite-cutoff stabilization and Heisenberg commutator
theorems live in `FermionicCurrentChargedFockIntertwiner`. This historical
module remains as an import-stable endpoint for umbrella files, but it does
not introduce a second carrier or a source-independent constructor.

A theorem claiming stabilization for an arbitrary raw CAR source must include
an actual representation and its cutoff-to-completion proof. The canonical
owner supplies that data for the exterior-Fock realization, so no vacuous
identity or witness wrapper is exported here.
-/

namespace InfoGeometry.Canonical.CARStabilizedCurrentHeisenbergRep

end InfoGeometry.Canonical.CARStabilizedCurrentHeisenbergRep
