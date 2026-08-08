theory NuclearPhononGenerators
  imports Complex_Main
begin

definition sBosonCount :: nat where "sBosonCount = 1"
definition dBosonCount :: nat where "dBosonCount = 5"
definition ibmModeCount :: nat where "ibmModeCount = sBosonCount + dBosonCount"
definition uNGeneratorCount :: "nat => nat" where "uNGeneratorCount n = n*n"
definition ibmU6GeneratorCount :: nat where "ibmU6GeneratorCount = uNGeneratorCount ibmModeCount"
definition ibmBilinearPartition :: nat where "ibmBilinearPartition = 1 + dBosonCount + dBosonCount + dBosonCount*dBosonCount"
definition symmetricPairCount :: "nat => nat" where "symmetricPairCount n = n*(n+1) div 2"
definition antisymmetricPairCount :: "nat => nat" where "antisymmetricPairCount n = n*(n-1) div 2"
definition sp6GeneratorCount :: nat where "sp6GeneratorCount = symmetricPairCount 3 + symmetricPairCount 3 + 3*3"
definition collectiveTensorCertificate :: nat where "collectiveTensorCertificate = antisymmetricPairCount 3 + symmetricPairCount 3 + symmetricPairCount 3 + symmetricPairCount 3"

datatype raise = Raise rat rat rat nat
fun Qcoeff :: "raise => rat" where "Qcoeff (Raise q k t w) = q"
fun Kcoeff :: "raise => rat" where "Kcoeff (Raise q k t w) = k"
fun Tcoeff :: "raise => rat" where "Tcoeff (Raise q k t w) = t"
definition sp6PhononRaising :: raise where "sp6PhononRaising = Raise (1/2) (-1/2) (1/2) 2"
definition sp6PhononLowering :: raise where "sp6PhononLowering = Raise (1/2) (-1/2) (-1/2) 2"
definition raisingPlusQ :: "raise => raise => rat" where "raisingPlusQ A B = Qcoeff A + Qcoeff B"
definition raisingPlusK :: "raise => raise => rat" where "raisingPlusK A B = Kcoeff A + Kcoeff B"
definition raisingPlusT :: "raise => raise => rat" where "raisingPlusT A B = Tcoeff A + Tcoeff B"
definition raisingMinusT :: "raise => raise => rat" where "raisingMinusT A B = Tcoeff A - Tcoeff B"
definition poincareC1 :: "rat => rat" where "poincareC1 m = -m*m"
definition springStiffnessFromC1 :: "rat => rat" where "springStiffnessFromC1 C1 = -C1"
definition springPotential :: "rat => rat => rat" where "springPotential m lam = m*m*lam*lam/2"
definition dilationBracketCoeff :: "rat => rat" where "dilationBracketCoeff C1 = 2*C1"
definition phononEnergy :: "rat => rat => rat" where "phononEnergy omega n = (n+1/2)*omega"
definition uDimension :: "nat => nat" where "uDimension n = n*n"
definition suDimension :: "nat => nat" where "suDimension n = n*n - 1"
definition soDimension :: "nat => nat" where "soDimension n = n*(n-1) div 2"
definition spRealDimensionFromHalfRank :: "nat => nat" where "spRealDimensionFromHalfRank n = n*(2*n+1)"
definition deltaNat :: "nat => nat => int" where "deltaNat i j = (if i = j then 1 else 0)"
definition matrixUnitFirstCoeff :: "nat => nat => nat => nat => int" where "matrixUnitFirstCoeff i j k l = deltaNat j k"
definition matrixUnitSecondCoeff :: "nat => nat => nat => nat => int" where "matrixUnitSecondCoeff i j k l = - deltaNat l i"

theorem nuclear_phonon_generators_kernel:
  "ibmModeCount = 6 \<and> ibmU6GeneratorCount = 36 \<and> ibmBilinearPartition = 36 \<and>
   symmetricPairCount 3 = 6 \<and> antisymmetricPairCount 3 = 3 \<and> sp6GeneratorCount = 21 \<and> collectiveTensorCertificate = 21 \<and>
   Qcoeff sp6PhononRaising = 1/2 \<and> Kcoeff sp6PhononRaising = -1/2 \<and> Tcoeff sp6PhononRaising = 1/2 \<and>
   raisingPlusQ sp6PhononRaising sp6PhononLowering = 1 \<and>
   raisingPlusK sp6PhononRaising sp6PhononLowering = -1 \<and>
   raisingPlusT sp6PhononRaising sp6PhononLowering = 0 \<and>
   raisingMinusT sp6PhononRaising sp6PhononLowering = 1 \<and>
   springStiffnessFromC1 (poincareC1 3) = 9 \<and>
   springStiffnessFromC1 (poincareC1 0) = 0 \<and> springPotential 3 2 = 18 \<and>
   dilationBracketCoeff (poincareC1 3) = -18 \<and> phononEnergy 5 1 = 15/2"
  by (simp add: sBosonCount_def dBosonCount_def ibmModeCount_def uNGeneratorCount_def
      ibmU6GeneratorCount_def ibmBilinearPartition_def symmetricPairCount_def
      antisymmetricPairCount_def sp6GeneratorCount_def collectiveTensorCertificate_def
      sp6PhononRaising_def sp6PhononLowering_def raisingPlusQ_def raisingPlusK_def
      raisingPlusT_def raisingMinusT_def poincareC1_def springStiffnessFromC1_def
      springPotential_def dilationBracketCoeff_def phononEnergy_def)

theorem symmetry_group_kernel:
  "uDimension 6 = 36 \<and> suDimension 3 = 8 \<and>
   soDimension 6 = 15 \<and> soDimension 5 = 10 \<and> soDimension 3 = 3 \<and>
   spRealDimensionFromHalfRank 3 = 21 \<and>
   matrixUnitFirstCoeff 1 2 2 3 = 1 \<and>
   matrixUnitSecondCoeff 1 2 2 3 = 0 \<and>
   matrixUnitFirstCoeff 1 2 2 1 = 1 \<and>
   matrixUnitSecondCoeff 1 2 2 1 = -1"
  by (simp add: uDimension_def suDimension_def soDimension_def
      spRealDimensionFromHalfRank_def matrixUnitFirstCoeff_def matrixUnitSecondCoeff_def
      deltaNat_def)

datatype concept = Nuclear_Phonon | IBM_U6_Bilinear_Generator | Quadrupole_d_dagger_s | Sp6R_Raising_Generator | Noncompact_Dilation_Shear | Casimir_Dilation_Spring
datatype edge = represented_by | counted_by | decomposes_into | raises_by | quantizes
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Nuclear_Phonon represented_by IBM_U6_Bilinear_Generator = True" |
  "edgeHolds IBM_U6_Bilinear_Generator counted_by Quadrupole_d_dagger_s = True" |
  "edgeHolds Nuclear_Phonon raises_by Sp6R_Raising_Generator = True" |
  "edgeHolds Sp6R_Raising_Generator decomposes_into Noncompact_Dilation_Shear = True" |
  "edgeHolds Noncompact_Dilation_Shear quantizes Casimir_Dilation_Spring = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Nuclear_Phonon represented_by IBM_U6_Bilinear_Generator = True \<and>
   edgeHolds IBM_U6_Bilinear_Generator counted_by Quadrupole_d_dagger_s = True \<and>
   edgeHolds Nuclear_Phonon raises_by Sp6R_Raising_Generator = True \<and>
   edgeHolds Sp6R_Raising_Generator decomposes_into Noncompact_Dilation_Shear = True \<and>
   edgeHolds Noncompact_Dilation_Shear quantizes Casimir_Dilation_Spring = True"
  by simp

end
