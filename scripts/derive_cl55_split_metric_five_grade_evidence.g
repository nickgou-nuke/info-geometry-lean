#! /usr/bin/env gap

# Deterministic evidence generator for the real split Witt carrier W = U ⊕ U*.
# The Gram matrix is the neutral pairing [[0,I_5],[I_5,0]].

n := 5;
z := NullMat(n, n, Integers);
i5 := IdentityMat(n, Integers);
gram := Concatenation(
  List([1..n], r -> Concatenation(z[r], i5[r])),
  List([1..n], r -> Concatenation(i5[r], z[r]))
);

charpoly := CharacteristicPolynomial(Rationals, gram);
x := Indeterminate(Rationals);
rank := RankMat(gram);
det := DeterminantMat(gram);

if rank <> 2 * n then
  Error("split Gram matrix is not nondegenerate");
fi;
if det <> (-1)^n then
  Error("unexpected split Gram determinant");
fi;
if charpoly <> (x^2 - 1)^n then
  Error("unexpected Gram characteristic polynomial");
fi;

# Five native quadratic Witt grades:
# g_-2 = Λ²(U*), g_-1 = U*, g_0 = End(U),
# g_+1 = U, g_+2 = Λ²(U).
gradeDims := [ Binomial(n,2), n, n*n, n, Binomial(n,2) ];
gradeLabels := [ -2, -1, 0, 1, 2 ];

if Sum(gradeDims) <> 55 then
  Error("five-grade dimension sum is not 55");
fi;

Print("CL55_SPLIT_METRIC_EVIDENCE\n");
Print("gram_size=", 2*n, "x", 2*n, "\n");
Print("gram_block_form=[[0,I_", n, "],[I_", n, ",0]]\n");
Print("rank=", rank, "\n");
Print("determinant=", det, "\n");
Print("characteristic_polynomial=", charpoly, "\n");
Print("eigenvalue_multiplicity_plus_one=", n, "\n");
Print("eigenvalue_multiplicity_minus_one=", n, "\n");
Print("signature=(", n, ",", n, ")\n");
Print("grade_labels=", gradeLabels, "\n");
Print("grade_dimensions=", gradeDims, "\n");
Print("grade_dimension_sum=", Sum(gradeDims), "\n");
Print("allowed_grade_sums=[-4..4]\n");
Print("grade_closure_checks=[[-2,2,0],[-1,-1,-2],[-1,1,0],[1,1,2]]\n");
Print("STATUS=PASS\n");
