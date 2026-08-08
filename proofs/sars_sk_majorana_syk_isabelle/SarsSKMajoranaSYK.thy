theory SarsSKMajoranaSYK
  imports Main
begin

definition dlaDimSYK :: "nat => nat" where "dlaDimSYK n = 2^(2*n - 1) - 2"
definition dlaDimSK :: "nat => nat" where "dlaDimSK L = 2*(4^(L-1)-1)"
definition poolSizeSK :: "nat => nat" where "poolSizeSK L = L*(L-1)"
definition poolSizeSYK :: "nat => nat" where "poolSizeSYK n = n + 3*n*(n-1) div 2"
definition majoranaCount :: "nat => nat" where "majoranaCount n = 2*n"
definition hilbertDim :: "nat => nat" where "hilbertDim n = 2^n"
definition matrixAlgDim :: "nat => nat" where "matrixAlgDim n = (hilbertDim n)^2"
definition clBalancedDim :: "nat => nat" where "clBalancedDim n = 2^(2*n)"
definition cl55MatrixDim :: nat where "cl55MatrixDim = 32*32"

datatype concept = Quantum_SK_Model | SYK_Majorana_Model | Symmetry_Adapted_Operator_Pool | Jordan_Wigner_Clifford_Embedding | Pin55_Spinor_Block | Dense_Dynamical_Lie_Algebra
datatype edge = has_pool_size | has_dla_dimension | embeds_by | realizes_cl55_block | scales_as
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Quantum_SK_Model has_pool_size Symmetry_Adapted_Operator_Pool = True" |
  "edgeHolds SYK_Majorana_Model has_pool_size Symmetry_Adapted_Operator_Pool = True" |
  "edgeHolds SYK_Majorana_Model embeds_by Jordan_Wigner_Clifford_Embedding = True" |
  "edgeHolds Jordan_Wigner_Clifford_Embedding realizes_cl55_block Pin55_Spinor_Block = True" |
  "edgeHolds SYK_Majorana_Model has_dla_dimension Dense_Dynamical_Lie_Algebra = True" |
  "edgeHolds Dense_Dynamical_Lie_Algebra scales_as SYK_Majorana_Model = True" |
  "edgeHolds _ _ _ = False"

theorem sk_syk_kernel:
  "dlaDimSYK 4 = 126 \<and> dlaDimSK 8 = 32766 \<and> poolSizeSK 8 = 56 \<and>
   poolSizeSYK 4 = 22 \<and> majoranaCount 4 = 8 \<and> hilbertDim 10 = 1024 \<and>
   matrixAlgDim 5 = 1024 \<and> clBalancedDim 5 = 1024 \<and> cl55MatrixDim = 1024 \<and>
   dlaDimSYK 4 < dlaDimSK 8"
  by (simp add: dlaDimSYK_def dlaDimSK_def poolSizeSK_def poolSizeSYK_def majoranaCount_def hilbertDim_def matrixAlgDim_def clBalancedDim_def cl55MatrixDim_def)

theorem graph_kernel:
  "edgeHolds Quantum_SK_Model has_pool_size Symmetry_Adapted_Operator_Pool = True \<and>
   edgeHolds SYK_Majorana_Model has_pool_size Symmetry_Adapted_Operator_Pool = True \<and>
   edgeHolds SYK_Majorana_Model embeds_by Jordan_Wigner_Clifford_Embedding = True \<and>
   edgeHolds Jordan_Wigner_Clifford_Embedding realizes_cl55_block Pin55_Spinor_Block = True \<and>
   edgeHolds SYK_Majorana_Model has_dla_dimension Dense_Dynamical_Lie_Algebra = True \<and>
   edgeHolds Dense_Dynamical_Lie_Algebra scales_as SYK_Majorana_Model = True"
  by simp

end
