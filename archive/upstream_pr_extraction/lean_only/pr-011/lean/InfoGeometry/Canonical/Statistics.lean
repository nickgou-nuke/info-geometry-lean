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


import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.ExponentialFamily.Finite
import InfoGeometry.ExponentialFamily.Bernoulli
import InfoGeometry.ExponentialFamily.Gaussian
import InfoGeometry.KL
import InfoGeometry.MaxEnt
import InfoGeometry.MaxEnt.DualBridge
import InfoGeometry.MaxEnt.Finite
import InfoGeometry.MaxEnt.Jaynes
import InfoGeometry.MaxEnt.IProjection
import InfoGeometry.MaxEnt.JaynesInfoStatMech
import InfoGeometry.MaxEnt.JaynesInfoStatMechTest
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.MaxEnt.Lagrange
import InfoGeometry.MaxEnt.Optimality
import InfoGeometry.OptimalTransport
import InfoGeometry.PositiveMeasure
import InfoGeometry.RegularizedKL
import InfoGeometry.KL.RegularizedKLTest
import InfoGeometry.Renyi
import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.ExponentialFamily.Finite

/-!
# InfoGeometry.Canonical.Statistics

Canonical KL/MaxEnt/exponential-family/statistical umbrella for publication.

Integrated canonical exponential-family modules:
- Bernoulli Hessian geometry
- Gaussian Hessian geometry
- Optimal-transport / KL / Bregman bridge aliases
-/
