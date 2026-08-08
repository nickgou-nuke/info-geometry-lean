theory SarsWeylColimit
  imports Main
begin

datatype phase_point = P int int

fun sigma :: "phase_point => phase_point => int" where
  "sigma (P q p) (P r s) = q * s - p * r"

fun pad_sigma :: "phase_point => phase_point => int" where
  "pad_sigma (P q p) (P r s) = q * s + 0 - p * r - 0"

definition block_dim :: "nat => int" where "block_dim n = 32 ^ n"
definition cl55_dim :: int where "cl55_dim = 2 ^ 10"

datatype parity = Even | Odd
fun super_target :: "parity => parity => parity" where
  "super_target Odd Odd = Even" |
  "super_target Even Even = Even" |
  "super_target _ _ = Odd"

theorem sigma_pad_preserved: "pad_sigma u v = sigma u v"
  by (cases u; cases v; simp)

theorem sigma_skew: "sigma v u = - sigma u v"
  by (cases u; cases v; simp)

theorem weyl_colimit_kernel:
  "(\<forall>u v. pad_sigma u v = sigma u v) \<and>
   block_dim 0 = 1 \<and>
   block_dim 1 = 32 \<and>
   block_dim 2 = 1024 \<and>
   cl55_dim = block_dim 2 \<and>
   super_target Odd Odd = Even"
  by (simp add: sigma_pad_preserved block_dim_def cl55_dim_def)

end
