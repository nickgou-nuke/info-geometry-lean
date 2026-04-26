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

import InfoGeometry.Canonical.OpenProblemFormalization
import InfoGeometry.Canonical.WeylCharacterEquivalence

namespace InfoGeometry.Canonical.PrimeGasWeylCharacterBridge

set_option linter.dupNamespace false

open InfoGeometry.Canonical.OpenProblemFormalization
open InfoGeometry.Canonical.WeylCharacterEquivalence
open InfoGeometry.Canonical.SouriauThermodynamics

/--
Prime-gas bridge into the conservative Souriau/Weyl character surface.

The prime gas remains an explicit hypothesis packet.  The actual partition
function/character and Weyl-denominator/Möbius readouts are delegated to the
already-owned `WeylCharacterEquivalence` packet.
-/
structure PrimeGasWeylCharacterBridge (𝔤 : Type*) where
  primeGas : PrimeGasMaxEntPacket
  souriauWeyl : SouriauWeylPartitionPacket 𝔤
  primeOccupationLogEnergy : primeGas.data.primeOccupationLogEnergy
  eulerProductPartition : primeGas.data.eulerProductPartition

namespace PrimeGasWeylCharacterBridge

variable {𝔤 : Type*} (B : PrimeGasWeylCharacterBridge 𝔤)

/-- The partition function is the Souriau character readout. -/
theorem partitionFunction_is_souriau_character :
    B.souriauWeyl.representation.partitionFunction B.souriauWeyl.beta =
      B.souriauWeyl.representation.character
        (B.souriauWeyl.representation.thermalElement B.souriauWeyl.beta) :=
  B.souriauWeyl.partitionFunction_is_souriau_character

/-- The Weyl denominator equals the supplied prime Euler product bridge. -/
theorem denominator_is_prime_euler_product :
    B.souriauWeyl.denominatorBridge.weylDenominator =
      B.souriauWeyl.denominatorBridge.primeEulerProduct :=
  B.souriauWeyl.denominator_is_prime_euler_product

/-- The parity trace witness is routed unchanged through the bridge. -/
theorem parity_trace_witness
    (n : ℕ) (h : B.souriauWeyl.parityWitness.squareFree n) :
    B.souriauWeyl.parityWitness.signature
        (B.souriauWeyl.parityWitness.squareFreeToWeyl n h) =
      mobiusCoefficient n :=
  B.souriauWeyl.parity_trace_witness n h

end PrimeGasWeylCharacterBridge

set_option linter.dupNamespace true

end InfoGeometry.Canonical.PrimeGasWeylCharacterBridge
