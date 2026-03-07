# Determinant Homomorphisms, Tensor Products, and Entropic Splitting

This note records the algebraic route from noncommutative operator composition
to additive modular-entropy observables.

## 1. Determinant as Group-Homomorphic Projection

For finite-dimensional linear dynamics, determinant is the multiplicative scalar
shadow of operator composition:

- `det(AB) = det(A) det(B)`.
- In canonical determinant/Jacobian lemmas, composition in operator space is
  projected to multiplicative volume transport.

This is the same multiplicative pattern that appears in Radon-Nikodym chain
composition and cocycle transport laws.

## 2. Log Deformation and Additive Hamiltonians

Applying `log |det(·)|` converts multiplicative transport into additive charges:

- `log|det(AB)| = log|det(A)| + log|det(B)|`.

So even when microscopic operator updates are noncommutative and order-sensitive,
the projected scalar entropy/Hamiltonian channel is additive after logarithmic
deformation.

## 3. Tensor Products and Extensivity

For composite systems (`A ⊗ B`), determinant multiplicativity with dimension
weights gives:

- `det(A ⊗ B) = det(A)^(dim B) det(B)^(dim A)`.
- Hence
  `log|det(A ⊗ B)| = (dim B) log|det(A)| + (dim A) log|det(B)|`.

This is the extensivity law: composite entropic load splits as a weighted sum
of subsystem contributions.

## 4. Unified Interpretation

The additive modular-Hamiltonian behavior is not ad hoc. It is the logarithmic
image of determinant homomorphism on noncommutative dynamics:

1. operator composition,
2. determinant volume projection,
3. logarithmic additive thermodynamic splitting.

That chain explains why local additive entropy bookkeeping coexists with
noncommutative microscopic update geometry.
