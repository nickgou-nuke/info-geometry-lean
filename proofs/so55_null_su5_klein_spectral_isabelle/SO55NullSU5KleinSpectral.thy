theory SO55NullSU5KleinSpectral
  imports Complex_Main
begin

definition n5 :: nat where "n5 = 5"
definition nullVectorDim :: nat where "nullVectorDim = 2*n5"
definition soDim :: "nat => nat" where "soDim n = n*(n-1) div 2"
definition matrixDim :: "nat => nat" where "matrixDim n = n*n"
definition slDim :: "nat => nat" where "slDim n = matrixDim n - 1"
definition skewDim :: "nat => nat" where "skewDim n = n*(n-1) div 2"
definition so55NullBlockDim :: nat where "so55NullBlockDim = matrixDim n5 + skewDim n5 + skewDim n5"
definition su5PartitionDim :: nat where "su5PartitionDim = slDim n5 + 1 + skewDim n5 + skewDim n5"
definition spinEven16Dim :: nat where "spinEven16Dim = 1 + 10 + 5"
definition spinOdd16Dim :: nat where "spinOdd16Dim = 5 + 10 + 1"
definition varlamovModePartitionDim :: nat where "varlamovModePartitionDim = spinEven16Dim + spinOdd16Dim"
definition involutionParity :: "rat => rat => rat*rat" where "involutionParity diag off = (diag, -off)"
definition mobiusInversionZ2 :: "rat => rat => rat*rat" where "mobiusInversionZ2 epart opart = ((epart+opart)/2, (epart-opart)/2)"
definition mobiusReconstructZ2 :: "rat => rat => rat*rat" where "mobiusReconstructZ2 x y = (x+y, x-y)"
definition kleinBottleQuotientAverage :: "rat => rat => rat => rat => rat" where "kleinBottleQuotientAverage a b c d = (a+b+c+d)/4"
definition tripotentDetPolynomial :: "rat => rat" where "tripotentDetPolynomial d = d*(d-1)*(d+1)"
definition poincareCasimir :: "rat => rat" where "poincareCasimir m = -m*m"
definition spectralSpringStiffness :: "rat => rat" where "spectralSpringStiffness C1 = -C1"
definition brillouinPairing :: "rat => rat*rat" where "brillouinPairing k = (k,-k)"
definition kleinBottleModeInvariant :: "rat => rat" where "kleinBottleModeInvariant k = fst (brillouinPairing k) + snd (brillouinPairing k)"

theorem so55_null_su5_klein_spectral_kernel:
  "nullVectorDim = 10 \<and> soDim nullVectorDim = 45 \<and> slDim n5 = 24 \<and> skewDim n5 = 10 \<and>
   so55NullBlockDim = 45 \<and> su5PartitionDim = 45 \<and> su5PartitionDim = so55NullBlockDim \<and>
   spinEven16Dim = 16 \<and> spinOdd16Dim = 16 \<and> varlamovModePartitionDim = 32 \<and>
   involutionParity (fst (involutionParity (7/3) (5/2))) (snd (involutionParity (7/3) (5/2))) = (7/3,5/2) \<and>
   mobiusReconstructZ2 (fst (mobiusInversionZ2 7 3)) (snd (mobiusInversionZ2 7 3)) = (7,3) \<and>
   kleinBottleQuotientAverage 1 2 3 4 = 5/2 \<and>
   tripotentDetPolynomial (-1) = 0 \<and> tripotentDetPolynomial 0 = 0 \<and> tripotentDetPolynomial 1 = 0 \<and>
   spectralSpringStiffness (poincareCasimir 3) = 9 \<and> kleinBottleModeInvariant (11/7) = 0"
  by (simp add: n5_def nullVectorDim_def soDim_def matrixDim_def slDim_def skewDim_def so55NullBlockDim_def su5PartitionDim_def spinEven16Dim_def spinOdd16Dim_def varlamovModePartitionDim_def involutionParity_def mobiusInversionZ2_def mobiusReconstructZ2_def kleinBottleQuotientAverage_def tripotentDetPolynomial_def poincareCasimir_def spectralSpringStiffness_def brillouinPairing_def kleinBottleModeInvariant_def)

datatype concept = SO55_Null_Basis | SU5_Adjoint_24 | Dilaton_Line_1 | Fermion_Ten_B | Fermion_TenBar_C | Spinor_Exterior_16 | Klein_Mobius_Spectral_Quotient
datatype edge = decomposes_to | trace_splits_to | skew_splits_to | classifies_spin_modes | quotients_modes
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds SO55_Null_Basis decomposes_to SU5_Adjoint_24 = True" |
  "edgeHolds SO55_Null_Basis trace_splits_to Dilaton_Line_1 = True" |
  "edgeHolds SO55_Null_Basis skew_splits_to Fermion_Ten_B = True" |
  "edgeHolds SO55_Null_Basis skew_splits_to Fermion_TenBar_C = True" |
  "edgeHolds Spinor_Exterior_16 quotients_modes Klein_Mobius_Spectral_Quotient = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds SO55_Null_Basis decomposes_to SU5_Adjoint_24 = True \<and>
   edgeHolds SO55_Null_Basis trace_splits_to Dilaton_Line_1 = True \<and>
   edgeHolds SO55_Null_Basis skew_splits_to Fermion_Ten_B = True \<and>
   edgeHolds SO55_Null_Basis skew_splits_to Fermion_TenBar_C = True \<and>
   edgeHolds Spinor_Exterior_16 quotients_modes Klein_Mobius_Spectral_Quotient = True"
  by simp

end
