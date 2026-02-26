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

import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Krein.CartanDecomposition
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.Metric
import InfoGeometry.Krein.Modular
import InfoGeometry.Krein.Prelude
import InfoGeometry.Krein.Thermal

/-!
# InfoGeometry.Canonical.Krein

Canonical Krein-layer umbrella (publication surface).

This file re‑exports the various Krein submodules so that
`import InfoGeometry.Canonical.Krein` brings in the full Krein
infrastructure.  Legacy compatibility modules like
`InfoGeometry.Krein` simply import this file.
-/
