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

import InfoGeometry.Canonical.All

namespace InfoGeometry

/-!
# InfoGeometry.Library

Compatibility umbrella for the current `InfoGeometry.Canonical.All` import surface.

This is not the whole-project entrypoint.  The intended full project surface is
`InfoGeometry.All` / root `InfoGeometry`, and every repo-owned Lean module should
be buildable and provided through that surface.  The theorem owner modules and
Lean/Lake checks remain the authority for what is closed, conditional, or still
carrying proof debt.
-/

end InfoGeometry
