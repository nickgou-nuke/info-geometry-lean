# Determinant Reference
## Key Properties
- Geometric: |det(A)| = n-volume scaling; sign = orientation preservation
- Leibniz: det(A) = Σ_{σ∈S_n} sgn(σ) Π_i a_{i,σ(i)}
- Multilinear, alternating, det(I)=1 characterizes determinant uniquely
- det(cA) = c^n·det(A); det(A^T) = det(A); det(AB) = det(A)det(B)
- Laplace: det(A) = Σ_j (-1)^{i+j} a_{ij} M_{ij}
- Sylvester: det(I_m + AB) = det(I_n + BA)
- det(A) = Π λ_i (product of eigenvalues)
- det(exp(A)) = exp(tr(A))

## Pfaffian
- Pf(M)² = det(M) for skew-symmetric M
- Berezin integral: ∫ exp[-½θ^T A θ] dθ = Pf A

## Berezinian (superdeterminant)
- Ber(M) = det(A - B D^{-1} C) / det(D) for supermatrix [[A,B],[C,D]]
- Preserves supertrace: STr(log M) = log(Ber(M))
