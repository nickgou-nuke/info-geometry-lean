theory LECM2022ElectroweakRadiiISB
  imports Complex_Main
begin

definition V2 :: "rat => rat" where "V2 x = x*x"
definition ckmFirstRowSum :: "rat => rat => rat => rat" where "ckmFirstRowSum Vud Vus Vub = V2 Vud + V2 Vus + V2 Vub"
definition ckmUnitarityDefect :: "rat => rat => rat => rat" where "ckmUnitarityDefect Vud Vus Vub = ckmFirstRowSum Vud Vus Vub - 1"
definition T_superallowed :: rat where "T_superallowed = 1"
definition J_superallowed :: rat where "J_superallowed = 0"
definition bareFermiMatrixSquared :: rat where "bareFermiMatrixSquared = 2"
definition permyriadToPercent :: "rat => rat" where "permyriadToPercent x = x/100"
definition correctedFermiSquared :: "rat => rat" where "correctedFermiSquared deltaC = bareFermiMatrixSquared*(1-deltaC)"
definition FtCorrected :: "rat => rat => rat => rat" where "FtCorrected ft deltaR deltaC = ft*(1+deltaR)*(1-deltaC)"
definition combinedISBObservable :: "rat => rat => rat" where "combinedISBObservable beta radius = beta+radius"
definition exactIsospinRadiusConstraint :: "rat => rat*rat" where "exactIsospinRadiusConstraint x = (x,-x)"
definition isbDeviationFromExact :: "rat => rat => rat" where "isbDeviationFromExact beta radius = combinedISBObservable beta radius"
definition isovectorMonopoleScale :: "rat => rat => rat" where "isovectorMonopoleScale NminusZ A = NminusZ/A"
definition uniformSphereCoulombScale :: "rat => rat => rat" where "uniformSphereCoulombScale Z R = Z/R"

theorem lecm2022_electroweak_radii_isb_kernel:
  "ckmFirstRowSum (3/5) (4/5) 0 = 1 \<and>
   ckmUnitarityDefect (3/5) (4/5) 0 = 0 \<and>
   T_superallowed = 1 \<and> J_superallowed = 0 \<and>
   permyriadToPercent 10 = 1/10 \<and> permyriadToPercent 100 = 1 \<and>
   correctedFermiSquared 0 = bareFermiMatrixSquared \<and>
   correctedFermiSquared (1/100) = 99/50 \<and>
   (\<forall>x. combinedISBObservable (fst (exactIsospinRadiusConstraint x)) (snd (exactIsospinRadiusConstraint x)) = 0) \<and>
   combinedISBObservable (3/10) (-1/5) = 1/10 \<and>
   isbDeviationFromExact (3/10) (-1/5) = 1/10 \<and>
   isovectorMonopoleScale 2 40 = 1/20 \<and>
   uniformSphereCoulombScale 20 4 = 5"
  by (simp add: V2_def ckmFirstRowSum_def ckmUnitarityDefect_def T_superallowed_def J_superallowed_def bareFermiMatrixSquared_def permyriadToPercent_def correctedFermiSquared_def combinedISBObservable_def exactIsospinRadiusConstraint_def isbDeviationFromExact_def isovectorMonopoleScale_def uniformSphereCoulombScale_def)

datatype concept = CKM_First_Row_Unitarity | Superallowed_Beta_Decay | ISB_Correction_deltaC | Electroweak_Nuclear_Radii | Isovector_Monopole_Operator | Combined_ISB_Observable
datatype edge = E_constrains | E_measures | E_corrects | E_probes | E_cancels_under_exact_isospin
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Superallowed_Beta_Decay E_constrains CKM_First_Row_Unitarity = True" |
  "edgeHolds ISB_Correction_deltaC E_corrects Superallowed_Beta_Decay = True" |
  "edgeHolds Electroweak_Nuclear_Radii E_probes ISB_Correction_deltaC = True" |
  "edgeHolds Isovector_Monopole_Operator E_measures Electroweak_Nuclear_Radii = True" |
  "edgeHolds Combined_ISB_Observable E_cancels_under_exact_isospin Isovector_Monopole_Operator = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Superallowed_Beta_Decay E_constrains CKM_First_Row_Unitarity = True \<and>
   edgeHolds ISB_Correction_deltaC E_corrects Superallowed_Beta_Decay = True \<and>
   edgeHolds Electroweak_Nuclear_Radii E_probes ISB_Correction_deltaC = True \<and>
   edgeHolds Isovector_Monopole_Operator E_measures Electroweak_Nuclear_Radii = True \<and>
   edgeHolds Combined_ISB_Observable E_cancels_under_exact_isospin Isovector_Monopole_Operator = True"
  by simp

end
