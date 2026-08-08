theory SarsSU5Cl55Supertrace
  imports Main
begin

definition omega_square_55 :: int where "omega_square_55 = (-1)^45 * (-1)^5"
definition su5_lambda2 :: int where "su5_lambda2 = 5 * 4 div 2"
definition su5_adjoint :: int where "su5_adjoint = 5 * 5 - 1"
definition so10_adjoint :: int where "so10_adjoint = 10 * (10 - 1) div 2"
definition sm_adjoint :: int where "sm_adjoint = (3 * 3 - 1) + (2 * 2 - 1) + 1"
definition xy_bosons :: int where "xy_bosons = su5_adjoint - sm_adjoint"
definition supertrace_identity_32 :: int where "supertrace_identity_32 = 16 - 16"
definition trace_identity_32 :: int where "trace_identity_32 = 16 + 16"
definition exterior_C5_dimension :: int where "exterior_C5_dimension = 1 + 5 + 10 + 10 + 5 + 1"
definition sars_scalar_5fund_dimension :: int where "sars_scalar_5fund_dimension = 5 * 5"
definition sars_dimension_gap :: int where "sars_dimension_gap = sars_scalar_5fund_dimension - su5_adjoint"
definition cl55_matrix_dimension :: int where "cl55_matrix_dimension = 32 * 32"
datatype parity = Even | Odd
fun super_bracket_target :: "parity => parity => parity" where
  "super_bracket_target Odd Odd = Even" |
  "super_bracket_target Even Even = Even" |
  "super_bracket_target _ _ = Odd"

theorem omega_square_55_eq_1: "omega_square_55 = 1"
  by (simp add: omega_square_55_def)

theorem su5_lambda2_eq_10: "su5_lambda2 = 10"
  by (simp add: su5_lambda2_def)

theorem su5_adjoint_eq_24: "su5_adjoint = 24"
  by (simp add: su5_adjoint_def)

theorem so10_adjoint_eq_45: "so10_adjoint = 45"
  by (simp add: so10_adjoint_def)

theorem sm_adjoint_eq_12: "sm_adjoint = 12"
  by (simp add: sm_adjoint_def)

theorem xy_bosons_eq_12: "xy_bosons = 12"
  by (simp add: xy_bosons_def su5_adjoint_def sm_adjoint_def)

theorem supertrace_identity_32_eq_0: "supertrace_identity_32 = 0"
  by (simp add: supertrace_identity_32_def)

theorem trace_identity_32_eq_32: "trace_identity_32 = 32"
  by (simp add: trace_identity_32_def)

theorem exterior_C5_dimension_eq_32: "exterior_C5_dimension = 32"
  by (simp add: exterior_C5_dimension_def)

theorem sars_scalar_5fund_dimension_eq_25: "sars_scalar_5fund_dimension = 25"
  by (simp add: sars_scalar_5fund_dimension_def)

theorem sars_scalar_not_adjoint: "sars_scalar_5fund_dimension ~= su5_adjoint"
  by (simp add: sars_scalar_5fund_dimension_def su5_adjoint_def)

theorem sars_dimension_gap_eq_1: "sars_dimension_gap = 1"
  by (simp add: sars_dimension_gap_def sars_scalar_5fund_dimension_def su5_adjoint_def)

theorem cl55_matrix_dimension_eq_1024: "cl55_matrix_dimension = 1024"
  by (simp add: cl55_matrix_dimension_def)

theorem odd_odd_superbracket_target_even: "super_bracket_target Odd Odd = Even"
  by simp

theorem sars_su5_cl55_kernel:
  "omega_square_55 = 1 \<and>
   su5_lambda2 = 10 \<and>
   su5_adjoint = 24 \<and>
   so10_adjoint = 45 \<and>
   sm_adjoint = 12 \<and>
   xy_bosons = 12 \<and>
   supertrace_identity_32 = 0 \<and>
   trace_identity_32 = 32 \<and>
   exterior_C5_dimension = 32 \<and>
   sars_scalar_5fund_dimension = 25 \<and>
   sars_scalar_5fund_dimension ~= su5_adjoint \<and>
   sars_dimension_gap = 1 \<and>
   cl55_matrix_dimension = 1024 \<and>
   super_bracket_target Odd Odd = Even"
  by (simp add: omega_square_55_eq_1 su5_lambda2_eq_10 su5_adjoint_eq_24 so10_adjoint_eq_45 sm_adjoint_eq_12 xy_bosons_eq_12 supertrace_identity_32_eq_0 trace_identity_32_eq_32 exterior_C5_dimension_eq_32 sars_scalar_5fund_dimension_eq_25 sars_scalar_not_adjoint sars_dimension_gap_eq_1 cl55_matrix_dimension_eq_1024 odd_odd_superbracket_target_even)

end
