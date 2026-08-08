theory FusOctonionKKS
  imports Complex_Main
begin

definition octonionDim :: nat where "octonionDim = 8"
definition imaginaryOctonionDim :: nat where "imaginaryOctonionDim = 7"
definition octonionOrbitDim :: nat where "octonionOrbitDim = 6"
definition g2Dim :: nat where "g2Dim = 14"
definition su3StabilizerDim :: nat where "su3StabilizerDim = 8"
definition g2OrbitDim :: nat where "g2OrbitDim = g2Dim - su3StabilizerDim"
definition fanoLineCount :: nat where "fanoLineCount = 7"
definition fanoDirectedProducts :: nat where "fanoDirectedProducts = 21"
definition associatorObstruction :: rat where "associatorObstruction = 2"
definition kksFormSample :: "rat => rat => rat" where "kksFormSample mu bracketXY = -mu*bracketXY"
definition signatureTotal :: "nat*nat => nat" where "signatureTotal s = fst s + snd s"
definition sphereS6Signature :: "nat*nat" where "sphereS6Signature = (6,0)"
definition splitSignature33 :: "nat*nat" where "splitSignature33 = (3,3)"
definition splitSignature24 :: "nat*nat" where "splitSignature24 = (2,4)"
definition so55su5Partition :: nat where "so55su5Partition = 24+1+10+10"
definition spinEven16 :: nat where "spinEven16 = 1+10+5"
definition spinOdd16 :: nat where "spinOdd16 = 5+10+1"
definition mobiusInv :: "rat => rat => rat*rat" where "mobiusInv epart opart = ((epart+opart)/2,(epart-opart)/2)"
definition mobiusRec :: "rat => rat => rat*rat" where "mobiusRec x y = (x+y,x-y)"
definition kleinAverage4 :: "rat => rat => rat => rat => rat" where "kleinAverage4 a b c d = (a+b+c+d)/4"
definition tripotentPolynomial :: "rat => rat" where "tripotentPolynomial d = d*(d-1)*(d+1)"
definition poincareCasimir :: "rat => rat" where "poincareCasimir m = -m*m"
definition spectralSpringStiffness :: "rat => rat" where "spectralSpringStiffness C1 = -C1"
definition kksClosedObstruction :: "rat => rat" where "kksClosedObstruction a = a"

theorem fus_octonion_kks_kernel:
  "octonionDim = 8 \<and> imaginaryOctonionDim = 7 \<and> octonionOrbitDim = 6 \<and> g2OrbitDim = 6 \<and>
   fanoLineCount = 7 \<and> fanoDirectedProducts = 21 \<and> associatorObstruction = 2 \<and>
   kksFormSample 3 5 = -15 \<and> kksClosedObstruction associatorObstruction = 2 \<and>
   signatureTotal sphereS6Signature = 6 \<and> signatureTotal splitSignature33 = 6 \<and> signatureTotal splitSignature24 = 6 \<and>
   so55su5Partition = 45 \<and> spinEven16 = 16 \<and> spinOdd16 = 16 \<and>
   fst (mobiusRec (fst (mobiusInv 7 3)) (snd (mobiusInv 7 3))) = 7 \<and>
   snd (mobiusRec (fst (mobiusInv 7 3)) (snd (mobiusInv 7 3))) = 3 \<and>
   kleinAverage4 1 2 3 4 = 5/2 \<and>
   tripotentPolynomial (-1) = 0 \<and> tripotentPolynomial 0 = 0 \<and> tripotentPolynomial 1 = 0 \<and>
   spectralSpringStiffness (poincareCasimir 3) = 9"
  by (simp add: octonionDim_def imaginaryOctonionDim_def octonionOrbitDim_def g2Dim_def su3StabilizerDim_def g2OrbitDim_def fanoLineCount_def fanoDirectedProducts_def associatorObstruction_def kksFormSample_def kksClosedObstruction_def signatureTotal_def sphereS6Signature_def splitSignature33_def splitSignature24_def so55su5Partition_def spinEven16_def spinOdd16_def mobiusInv_def mobiusRec_def kleinAverage4_def tripotentPolynomial_def poincareCasimir_def spectralSpringStiffness_def)

datatype concept = Fus_Octonion_KKS | Moufang_Loop | Octonion_Associator_Obstruction | Nearly_Kahler_S6_Orbit | Split_Hyperboloid_Orbit | SO55_SU5_Klein_Spectral
datatype edge = generalizes_to | obstructed_by | induces | split_induces | bridges_to
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Fus_Octonion_KKS generalizes_to Moufang_Loop = True" |
  "edgeHolds Fus_Octonion_KKS obstructed_by Octonion_Associator_Obstruction = True" |
  "edgeHolds Fus_Octonion_KKS induces Nearly_Kahler_S6_Orbit = True" |
  "edgeHolds Fus_Octonion_KKS split_induces Split_Hyperboloid_Orbit = True" |
  "edgeHolds Fus_Octonion_KKS bridges_to SO55_SU5_Klein_Spectral = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Fus_Octonion_KKS generalizes_to Moufang_Loop = True \<and>
   edgeHolds Fus_Octonion_KKS obstructed_by Octonion_Associator_Obstruction = True \<and>
   edgeHolds Fus_Octonion_KKS induces Nearly_Kahler_S6_Orbit = True \<and>
   edgeHolds Fus_Octonion_KKS split_induces Split_Hyperboloid_Orbit = True \<and>
   edgeHolds Fus_Octonion_KKS bridges_to SO55_SU5_Klein_Spectral = True"
  by simp

end
