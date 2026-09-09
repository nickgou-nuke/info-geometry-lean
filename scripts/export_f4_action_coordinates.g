#!/usr/bin/env gap
#############################################################################
# Exact rational action-coordinate evaluator and certificate exporter for F4.
# Evaluates the 52 x 729 matrix of inner derivations [L_A, L_B] on H3(Os).
#############################################################################

SetPrintFormattingStatus("*stdout*", false);

dot3 := function(u, v)
  return u[1]*v[1] + u[2]*v[2] + u[3]*v[3];
end;

cross3 := function(u, v)
  return [
    u[2]*v[3] - u[3]*v[2],
    u[3]*v[1] - u[1]*v[3],
    u[1]*v[2] - u[2]*v[1]
  ];
end;

ZornVM := function(a, v, w, b)
  return rec(a := Rat(a), v := List(v, Rat), w := List(w, Rat), b := Rat(b));
end;

zvm_zero := ZornVM(0, [0,0,0], [0,0,0], 0);

zvm_add := function(X, Y)
  return ZornVM(X.a + Y.a, X.v + Y.v, X.w + Y.w, X.b + Y.b);
end;

zvm_sub := function(X, Y)
  return ZornVM(X.a - Y.a, X.v - Y.v, X.w - Y.w, X.b - Y.b);
end;

zvm_smul := function(r, X)
  return ZornVM(r * X.a, r * X.v, r * X.w, r * X.b);
end;

zvm_conj := function(X)
  return ZornVM(X.b, -X.v, -X.w, X.a);
end;

zvm_trace := function(X)
  return X.a + X.b;
end;

zvm_norm := function(X)
  return X.a * X.b - dot3(X.v, X.w);
end;

zvm_mul := function(X, Y)
  local a_new, v_new, w_new, b_new;
  a_new := X.a * Y.a + dot3(X.v, Y.w);
  v_new := X.a * Y.v + Y.b * X.v - cross3(X.w, Y.w);
  w_new := Y.a * X.w + X.b * Y.w + cross3(X.v, Y.v);
  b_new := dot3(X.w, Y.v) + X.b * Y.b;
  return ZornVM(a_new, v_new, w_new, b_new);
end;

H3Zorn := function(a1, a2, a3, a, b, c)
  return rec(
    a1 := Rat(a1), a2 := Rat(a2), a3 := Rat(a3),
    a := a, b := b, c := c
  );
end;

h3_zero := H3Zorn(0, 0, 0, zvm_zero, zvm_zero, zvm_zero);
h3_one := H3Zorn(1, 1, 1, zvm_zero, zvm_zero, zvm_zero);

h3_add := function(X, Y)
  return H3Zorn(
    X.a1 + Y.a1, X.a2 + Y.a2, X.a3 + Y.a3,
    zvm_add(X.a, Y.a), zvm_add(X.b, Y.b), zvm_add(X.c, Y.c)
  );
end;

h3_sub := function(X, Y)
  return H3Zorn(
    X.a1 - Y.a1, X.a2 - Y.a2, X.a3 - Y.a3,
    zvm_sub(X.a, Y.a), zvm_sub(X.b, Y.b), zvm_sub(X.c, Y.c)
  );
end;

h3_smul := function(r, X)
  return H3Zorn(
    r * X.a1, r * X.a2, r * X.a3,
    zvm_smul(r, X.a), zvm_smul(r, X.b), zvm_smul(r, X.c)
  );
end;

trace_bilin := function(X, Y)
  return X.a1 * Y.a1 + X.a2 * Y.a2 + X.a3 * Y.a3 +
    zvm_trace(zvm_mul(X.a, zvm_conj(Y.a))) +
    zvm_trace(zvm_mul(X.b, zvm_conj(Y.b))) +
    zvm_trace(zvm_mul(X.c, zvm_conj(Y.c)));
end;

adjoint_quad := function(X)
  local a1_new, a2_new, a3_new, a_new, b_new, c_new;
  a1_new := X.a2 * X.a3 - zvm_norm(X.b);
  a2_new := X.a1 * X.a3 - zvm_norm(X.c);
  a3_new := X.a1 * X.a2 - zvm_norm(X.a);
  a_new := zvm_sub(zvm_mul(zvm_conj(X.c), zvm_conj(X.b)), zvm_smul(X.a3, X.a));
  b_new := zvm_sub(zvm_mul(zvm_conj(X.a), zvm_conj(X.c)), zvm_smul(X.a1, X.b));
  c_new := zvm_sub(zvm_mul(zvm_conj(X.b), zvm_conj(X.a)), zvm_smul(X.a2, X.c));
  return H3Zorn(a1_new, a2_new, a3_new, a_new, b_new, c_new);
end;

cross_product := function(X, Y)
  return h3_sub(h3_sub(adjoint_quad(h3_add(X, Y)), adjoint_quad(X)), adjoint_quad(Y));
end;

U_op := function(X, Y)
  return h3_sub(h3_smul(trace_bilin(X, Y), X), cross_product(adjoint_quad(X), Y));
end;

T_op := function(X, Y, Z)
  return h3_sub(h3_sub(U_op(h3_add(X, Z), Y), U_op(X, Y)), U_op(Z, Y));
end;

jordan_mul := function(X, Y)
  return h3_smul(1/2, T_op(X, h3_one, Y));
end;

inner_action := function(A, B, X)
  return h3_sub(jordan_mul(A, jordan_mul(B, X)), jordan_mul(B, jordan_mul(A, X)));
end;

h3_coord := function(X)
  return [
    X.a1, X.a2, X.a3,
    X.a.a, X.a.v[1], X.a.v[2], X.a.v[3], X.a.w[1], X.a.w[2], X.a.w[3], X.a.b,
    X.b.a, X.b.v[1], X.b.v[2], X.b.v[3], X.b.w[1], X.b.w[2], X.b.w[3], X.b.b,
    X.c.a, X.c.v[1], X.c.v[2], X.c.v[3], X.c.w[1], X.c.w[2], X.c.w[3], X.c.b
  ];
end;

zorn_basis := function(i)
  if i = 0 then return ZornVM(1, [0,0,0], [0,0,0], 0);
  elif i = 1 then return ZornVM(0, [1,0,0], [0,0,0], 0);
  elif i = 2 then return ZornVM(0, [0,1,0], [0,0,0], 0);
  elif i = 3 then return ZornVM(0, [0,0,1], [0,0,0], 0);
  elif i = 4 then return ZornVM(0, [0,0,0], [1,0,0], 0);
  elif i = 5 then return ZornVM(0, [0,0,0], [0,1,0], 0);
  elif i = 6 then return ZornVM(0, [0,0,0], [0,0,1], 0);
  elif i = 7 then return ZornVM(0, [0,0,0], [0,0,0], 1);
  fi;
end;

h3_diag1 := H3Zorn(1, 0, 0, zvm_zero, zvm_zero, zvm_zero);
h3_diag2 := H3Zorn(0, 1, 0, zvm_zero, zvm_zero, zvm_zero);
h3_diag3 := H3Zorn(0, 0, 1, zvm_zero, zvm_zero, zvm_zero);

h3_off12 := function(i) return H3Zorn(0, 0, 0, zorn_basis(i), zvm_zero, zvm_zero); end;
h3_off23 := function(i) return H3Zorn(0, 0, 0, zvm_zero, zorn_basis(i), zvm_zero); end;
h3_off31 := function(i) return H3Zorn(0, 0, 0, zvm_zero, zvm_zero, zorn_basis(i)); end;

probes := [h3_diag1, h3_diag2, h3_diag3];
for i in [0..7] do Add(probes, h3_off12(i)); od;
for i in [0..7] do Add(probes, h3_off23(i)); od;
for i in [0..7] do Add(probes, h3_off31(i)); od;

generator_pairs := [];
for i in [0..7] do Add(generator_pairs, [h3_diag1, h3_off12(i)]); od;
for i in [0..7] do Add(generator_pairs, [h3_diag1, h3_off31(i)]); od;
for i in [0..7] do Add(generator_pairs, [h3_diag2, h3_off23(i)]); od;
for i in [0..7] do
  for j in [i+1..7] do
    Add(generator_pairs, [h3_off12(i), h3_off12(j)]);
  od;
od;

if Length(generator_pairs) <> 52 then
  Error("expected 52 generator pairs");
fi;
if Length(probes) <> 27 then
  Error("expected 27 probes");
fi;

M := [];
for pair in generator_pairs do
  row := [];
  for probe in probes do
    Append(row, h3_coord(inner_action(pair[1], pair[2], probe)));
  od;
  Add(M, row);
od;

rank := RankMat(M);
if rank <> 52 then
  Error(Concatenation("action matrix rank is ", String(rank), ", expected 52"));
fi;

# Find 52 separating column pivots: for each row i, a column col where M[i, col] != 0 and M[j, col] = 0 for j != i
pivots := [];
pivotValues := [];
for i in [1..52] do
  foundCol := fail;
  for col in [1..729] do
    if M[i][col] <> 0 then
      isSeparating := true;
      for j in [1..52] do
        if j <> i and M[j][col] <> 0 then
          isSeparating := false;
          break;
        fi;
      od;
      if isSeparating then
        foundCol := col;
        break;
      fi;
    fi;
  od;
  if foundCol = fail then
    Error(Concatenation("no separating pivot found for row ", String(i)));
  fi;
  Add(pivots, foundCol);
  Add(pivotValues, M[i][foundCol]);
od;

Print("# INFO_GEOMETRY_F4_ACTION_CERTIFICATE v1\n");
Print("# carrier=H3Zorn\n");
Print("# action_basis_dimension=27\n");
Print("# derivation_count=52\n");
Print("# flattened_action_coordinates=729\n");
Print("# coefficient_field=Rationals\n");
Print("# index_base=0\n");
Print("F4_ACTION_COORDINATE_ROWS=52\n");
Print("F4_ACTION_COORDINATE_COLS=729\n");
Print("F4_ACTION_COORDINATE_RANK=52\n");
Print("F4_ACTION_PIVOT_COUNT=52\n");
for i in [1..52] do
  Print("F4_ACTION_PIVOT ", i - 1, ": ", pivots[i] - 1, "\n");
od;
for i in [1..52] do
  Print("F4_ACTION_PIVOT_VALUE ", i - 1, ": ", pivotValues[i], "\n");
od;
Print("F4_ACTION_LINEAR_INDEPENDENCE_CERTIFICATE_BEGIN\n");
for i in [1..52] do
  Print("F4ACTIONROW ", i - 1, ": ", M[i], "\n");
od;
Print("F4_ACTION_LINEAR_INDEPENDENCE_CERTIFICATE_END\n");
QUIT_GAP(0);
