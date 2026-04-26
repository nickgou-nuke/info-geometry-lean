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
import InfoGeometry.Canonical.SuperKMS_Equilibrium

namespace InfoGeometry.Canonical.PrimeGasSuperKMSBridge

open InfoGeometry.Canonical.ChiralRadiationCones
open InfoGeometry.Canonical.SuperKMS_Equilibrium
open InfoGeometry.Canonical.SuperSouriauFermionGasBridge
open InfoGeometry.Canonical.OpenProblemFormalization
open InfoGeometry.Canonical.OpenProblemFormalization.PrimeGasOnsagerFierzBridge

/--
Prime-gas to Super-KMS blackbody bridge.

This keeps the prime-gas Jaynes packet explicit, routes its KMS target into the
supergraded even/odd temperature lane, and packages the chiral equilibrium
backbone as a theorem-facing owner object.
-/
structure PrimeGasSuperKMSBlackbodyBridge where
  primeGas : InfoGeometry.Canonical.OpenProblemFormalization.PrimeGasMaxEntPacket
  jaynesRNBridge :
    InfoGeometry.Canonical.OpenProblemFormalization.PrimeGasJaynesRNBridge primeGas
  kmsTarget :
    InfoGeometry.Canonical.OpenProblemFormalization.PrimeGasOnsagerFierzBridge.PrimeGasKMSTargetBridge
  superAlgebra : SupergradedAlgebra
  equilibrium : SuperKMSChiralEquilibrium superAlgebra
  superTemperature : InfoGeometry.Canonical.SuperSouriauFermionGasBridge.SuperGeometricTemperature
  superTemperature_eq : by
    letI : Fintype kmsTarget.bridge.ι := kmsTarget.bridge.instFintype
    exact
      superTemperature =
        InfoGeometry.Canonical.OpenProblemFormalization.PrimeGasOnsagerFierzBridge.toSuperGeometricTemperature
          kmsTarget
  evenTemperature_matches :
    equilibrium.state.beta = superTemperature.betaEven

namespace PrimeGasSuperKMSBlackbodyBridge

/--
The odd KMS branch is explicitly zero on the prime-gas routed temperature.
-/
theorem superTemperature_zero_odd
    (B : PrimeGasSuperKMSBlackbodyBridge) :
    B.superTemperature.betaOdd = 0 := by
  rw [B.superTemperature_eq]
  exact
    InfoGeometry.Canonical.OpenProblemFormalization.PrimeGasOnsagerFierzBridge.toSuperGeometricTemperature_zero_odd
      B.kmsTarget

/--
The chiral Dirac mass term remains an equilibrium constant on the Super-KMS
blackbody bridge.
-/
theorem diracMassTerm_is_equilibrium_constant
    (B : PrimeGasSuperKMSBlackbodyBridge) (ψL ψR : ℝ) :
    diracMassTerm B.equilibrium.massDynamics.massParameter ψL ψR =
      diracMassTerm B.equilibrium.massDynamics.flipRate ψL ψR := by
  simpa using
    dirac_mass_term_is_equilibrium_constant B.equilibrium ψL ψR

/--
The bridge exposes the chiral equilibrium packet explicitly.
-/
def chiralEquilibrium (B : PrimeGasSuperKMSBlackbodyBridge) :
    SuperKMSChiralEquilibrium B.superAlgebra :=
  B.equilibrium

end PrimeGasSuperKMSBlackbodyBridge

end InfoGeometry.Canonical.PrimeGasSuperKMSBridge
