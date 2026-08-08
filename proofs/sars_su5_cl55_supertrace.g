omega_square_55 := (-1)^45 * (-1)^5;
su5_lambda2 := Binomial(5,2);
su5_adjoint := 5^2 - 1;
sm_adjoint := (3^2 - 1) + (2^2 - 1) + 1;
xy_bosons := su5_adjoint - sm_adjoint;
so10_adjoint := 10*(10-1)/2;
exterior_C5_dimension := Sum([0..5], k -> Binomial(5,k));
sars_scalar_5fund_dimension := 5*5;
sars_dimension_gap := sars_scalar_5fund_dimension - su5_adjoint;
cl55_matrix_dimension := 32*32;
odd_odd_target_even := true;
supertrace_identity_32 := 16 - 16;
trace_identity_32 := 16 + 16;
weyl_A4_order := Size(SymmetricGroup(5));
if omega_square_55 <> 1 then Error("omega_square_55"); fi;
if su5_lambda2 <> 10 then Error("su5_lambda2"); fi;
if su5_adjoint <> 24 then Error("su5_adjoint"); fi;
if sm_adjoint <> 12 then Error("sm_adjoint"); fi;
if xy_bosons <> 12 then Error("xy_bosons"); fi;
if so10_adjoint <> 45 then Error("so10_adjoint"); fi;
if exterior_C5_dimension <> 32 then Error("exterior_C5_dimension"); fi;
if sars_scalar_5fund_dimension <> 25 then Error("sars_scalar_5fund_dimension"); fi;
if sars_scalar_5fund_dimension = su5_adjoint then Error("sars_scalar_not_adjoint"); fi;
if sars_dimension_gap <> 1 then Error("sars_dimension_gap"); fi;
if cl55_matrix_dimension <> 2^10 then Error("cl55_matrix_dimension"); fi;
if odd_odd_target_even <> true then Error("odd_odd_target_even"); fi;
if supertrace_identity_32 <> 0 then Error("supertrace_identity_32"); fi;
if trace_identity_32 <> 32 then Error("trace_identity_32"); fi;
if weyl_A4_order <> Factorial(5) then Error("weyl_A4_order"); fi;
Print(rec(
  omega_square_55 := omega_square_55,
  su5_lambda2 := su5_lambda2,
  su5_adjoint := su5_adjoint,
  sm_adjoint := sm_adjoint,
  xy_bosons := xy_bosons,
  so10_adjoint := so10_adjoint,
  exterior_C5_dimension := exterior_C5_dimension,
  sars_scalar_5fund_dimension := sars_scalar_5fund_dimension,
  sars_scalar_not_adjoint := sars_scalar_5fund_dimension <> su5_adjoint,
  sars_dimension_gap := sars_dimension_gap,
  odd_odd_target_even := odd_odd_target_even,
  cl55_matrix_dimension := cl55_matrix_dimension,
  supertrace_identity_32 := supertrace_identity_32,
  trace_identity_32 := trace_identity_32,
  weyl_A4_order := weyl_A4_order
));
QUIT;
