/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.DikinOrbitCore
import InfoGeometry.Quantum.DikinBlahutOrbits
import InfoGeometry.Canonical.CartanDicksonColimitRH
import InfoGeometry.Canonical.DikinInstancesPart3

/-!
# Exact source unification for the two inverse-square orbit Dikin lanes

The two owners retain their domain-specific APIs and confinement theorems,
while their coefficient and ellipsoid are definitionally the same canonical
objects. The equivalences below expose that shared owner as an explicit bridge.
-/

namespace InfoGeometry.Canonical.DikinOrbitUnification

theorem blahut_metric_eq_core (x : ℝ) :
    InfoGeometry.Quantum.DikinBlahutOrbits.dikinMetric x =
      InfoGeometry.Geometry.DikinOrbitCore.coefficient x := rfl

theorem cartan_metric_eq_core (x : ℝ) :
    InfoGeometry.Canonical.CartanDicksonColimitRH.dikinMetric x =
      InfoGeometry.Geometry.DikinOrbitCore.coefficient x := rfl

theorem orbitDikinMetric_eq_core_quadratic (x v : ℝ) :
    orbitDikinMetric x v =
      InfoGeometry.Geometry.DikinOrbitCore.quadratic x v := rfl

theorem blahut_ellipsoid_iff_core (x y r : ℝ) :
    InfoGeometry.Quantum.DikinBlahutOrbits.InDikinEllipsoid x y r ↔
      InfoGeometry.Geometry.DikinOrbitCore.ellipsoid x y r := Iff.rfl

theorem cartan_ellipsoid_iff_core (x y r : ℝ) :
    InfoGeometry.Canonical.CartanDicksonColimitRH.InDikinEllipsoid x y r ↔
      InfoGeometry.Geometry.DikinOrbitCore.ellipsoid x y r := Iff.rfl

theorem blahut_ellipsoid_iff_cartan (x y r : ℝ) :
    InfoGeometry.Quantum.DikinBlahutOrbits.InDikinEllipsoid x y r ↔
      InfoGeometry.Canonical.CartanDicksonColimitRH.InDikinEllipsoid x y r := Iff.rfl

end InfoGeometry.Canonical.DikinOrbitUnification
