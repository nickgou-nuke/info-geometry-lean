theory SarsRoadblock
  imports Main
begin

definition a4_roots :: int where "a4_roots = 5 * 4"
definition sm_roots :: int where "sm_roots = 3 * 2 + 2 * 1"
definition broken_roots :: int where "broken_roots = a4_roots - sm_roots"
definition su5_adjoint :: int where "su5_adjoint = 4 + a4_roots"
definition sm_adjoint :: int where "sm_adjoint = 4 + sm_roots"
definition fundamental_scalar :: int where "fundamental_scalar = 5 * 5"
definition exterior_c5 :: int where "exterior_c5 = 1 + 5 + 10 + 10 + 5 + 1"
definition so10_adjoint :: int where "so10_adjoint = 10 * (10 - 1) div 2"
definition cl55_dim :: int where "cl55_dim = 2 ^ 10"
definition m32_dim :: int where "m32_dim = 32 * 32"
definition trace_gamma32 :: int where "trace_gamma32 = 16 - 16"
definition trace_identity32 :: int where "trace_identity32 = 16 + 16"

datatype parity = Even | Odd
fun super_bracket_target :: "parity => parity => parity" where
  "super_bracket_target Odd Odd = Even" |
  "super_bracket_target Even Even = Even" |
  "super_bracket_target _ _ = Odd"

theorem sars_roadblock_kernel:
  "a4_roots = 20 \<and> sm_roots = 8 \<and> broken_roots = 12 \<and>
   su5_adjoint = 24 \<and> sm_adjoint = 12 \<and> fundamental_scalar = 25 \<and>
   fundamental_scalar ~= su5_adjoint \<and> fundamental_scalar - su5_adjoint = 1 \<and>
   exterior_c5 = 32 \<and> so10_adjoint = 45 \<and> cl55_dim = m32_dim \<and>
   m32_dim = 1024 \<and> trace_gamma32 = 0 \<and> trace_identity32 = 32 \<and>
   super_bracket_target Odd Odd = Even"
  by (simp add: a4_roots_def sm_roots_def broken_roots_def su5_adjoint_def sm_adjoint_def fundamental_scalar_def exterior_c5_def so10_adjoint_def cl55_dim_def m32_dim_def trace_gamma32_def trace_identity32_def)

end
