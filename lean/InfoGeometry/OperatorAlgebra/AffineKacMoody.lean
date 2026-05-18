import Mathlib
import InfoGeometry.External.Virasoro.AffineKacMoody

/-!
# InfoGeometry.OperatorAlgebra.AffineKacMoody

Native pull-and-export surface for the vendored affine Kac-Moody module.

This file does not reprove the upstream results. It imports the vendored
`VirasoroProject` affine Kac-Moody file and re-exports its main symbols into
the operator-algebra namespace.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

export VirasoroProject (affineKacMoodyCocycle AffineKacMoody)

end InfoGeometry.OperatorAlgebra
