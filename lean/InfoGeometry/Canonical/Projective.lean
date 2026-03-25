/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/


import InfoGeometry.Projective.Dynamics
import InfoGeometry.Projective.FaithfulKL
import InfoGeometry.Projective.ConeKL
import InfoGeometry.Projective.Bridge
import InfoGeometry.Projective.GaugeQuotient
import InfoGeometry.Projective.GaugeReduction
import InfoGeometry.Projective.LogSum
import InfoGeometry.Projective.LogSumIneq
import InfoGeometry.Projective.Normalize
import InfoGeometry.Projective.Null
import InfoGeometry.Projective.PhysicalKinematics
import InfoGeometry.Projective.Projective
import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Projective.Rays

/-!
# InfoGeometry.Canonical.Projective

Canonical projective-layer umbrella (publication surface).
The zero-null twistor bridge is quarantined and must be imported explicitly from
`InfoGeometry.Unstable.Quarantine` while it remains proof-vacuous.
-/
