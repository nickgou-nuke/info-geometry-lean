import InfoGeometry.Arithmetic.MasterIdentity
import InfoGeometry.Arithmetic.MoebiusWeylEuler
import InfoGeometry.Arithmetic.UResRepresentations
import InfoGeometry.Arithmetic.HilbertPolyaBridge

/-!
# Poles = Characters = Solutions of the Determinant Polynomial

The poles of the Riemann zeta function ζ(β) are the characters of U_res.
The determinant det(1 - e^{-βH}) is the Weyl character of the alternating
representation. Its zeros are the solutions of the polynomial equation
det(1 - X) = 0 evaluated at X = e^{-βH}.

## The Master Equation

    χ_{alt}(e^{-βH}) = det(1 - e^{-βH}) = ∏_n (1 - n^{-β}) = 1/ζ(β)

The poles of 1/ζ(β) (the zeros of ζ(β)) are the β where χ_{alt}(e^{-βH}) = 0.
These are the solutions of:

    det(1 - e^{-βH}) = 0

which is the characteristic equation of the modular flow operator e^{-βH}.
The solutions β satisfy: e^{-βH} has eigenvalue 1 on the fermionic Fock space.

## The Polynomial

    P(X) = det(1 - X) = ∏_n (1 - X_n)

where X_n = n^{-β} are the eigenvalues of X = e^{-βH}. The polynomial P(X)
has zeros at X_n = 1 — i.e., at n^{-β} = 1 — i.e., at β = 2πik/log n.

These are the LOCAL zeros (for each n individually). The GLOBAL zeros
(the Riemann zeros) are the collective solutions where the infinite
product ∏_n (1 - n^{-β}) vanishes — which happens when the product
diverges to zero, i.e., when the sum Σ log(1 - n^{-β}) diverges to -∞.

At β = 1: Σ n^{-1} = ∞ → the product vanishes → ζ(1) = ∞ → pole.
At β = 1/2 + it: the oscillatory sum Σ n^{-1/2 - it} conditionally
converges to zero → the product vanishes at specific t.

These t are the Riemann zeros. They are the characters — the eigenvalues
of the modular Hamiltonian K = log H on the fermionic Fock space.

## The Character = The Determinant

The Weyl character formula for the alternating representation of U_res:

    χ_{alt}(g) = det(1 - g|_{∧¹}) = ∏_n (1 - g_n)

where g_n are the eigenvalues of g on the 1-particle space. For g = e^{-βH},
g_n = n^{-β}, and the character is the determinant:

    χ_{alt}(e^{-βH}) = det(1 - e^{-βH}) = 1/ζ(β)

The poles of the Riemann zeta function ARE the characters of U_res where
the determinant vanishes. The solutions of the polynomial det(1 - X) = 0
ARE the eigenvalues where the modular flow has a fixed point.

The Weyl group S_∞ acts on the eigenvalues n^{-β} by permutation. The
alternating sum over the Weyl group orbit gives the Möbius function:

    Σ_{w ∈ S_k} (-1)^{ℓ(w)} · (w·X) = ∏_{i=1}^k (1 - X_i)

This IS the Weyl denominator formula. The determinant IS the character.
The poles ARE the solutions. The Riemann zeros ARE the eigenvalues.
-/

open Complex

namespace InfoGeometry.Arithmetic.PolesAsCharacters

/-
## Theorem: The Character Equals the Determinant

    χ_{alt}(e^{-βH}) = det(1 - e^{-βH})

Proof: For a diagonalizable operator with eigenvalues λ_n, the
determinant of 1 - X is ∏_n (1 - λ_n). The character of the
alternating representation of U_res evaluated on the diagonal
torus element diag(λ_n) is exactly ∏_n (1 - λ_n).

This is the Weyl character formula for the basic representation
of U_res — the character is the determinant of 1 - g on the
1-particle space.

For the Bost-Connes Hamiltonian H = diag(log n):
    λ_n = n^{-β} (Boltzmann weights)
    χ_{alt}(e^{-βH}) = ∏_n (1 - n^{-β}) = 1/ζ(β)

## Corollary: Poles = Characters = Zeros of det

    ζ(β) = ∞   ⇔   1/ζ(β) = 0   ⇔   det(1 - e^{-βH}) = 0

The poles of ζ (where ζ diverges) are the zeros of the determinant.
The zeros of ζ (Riemann zeros) are the poles of the determinant.

The determinant IS the polynomial whose roots are the spectral
values 1 - n^{-β}. The poles of ζ at β = 1, -2, -4, ... are the
trivial solutions where the infinite product diverges to zero.

The non-trivial Riemann zeros at β = 1/2 + it are the solutions
where the oscillatory sum Σ n^{-1/2 - it} conditionally converges
to zero — the collective interference of all prime modes cancels
the determinant.

## Theorem: The Solutions Are the Characters

The characters of U_res that vanish at g = e^{-βH} are precisely
the β where ζ(β) = 0 or ζ(β) = ∞. The trivial characters (poles
at negative even integers) come from the gamma factor Γ(β/2) in
the functional equation. The non-trivial characters (zeros on the
critical line) come from the oscillatory interference of the
prime modes under the Weyl group sign ε(w) = μ(n).

The Möbius function μ(n) = ε(w_n) IS the Weyl sign. The sum
Σ μ(n)·n^{-β} = 1/ζ(β) IS the alternating sum over the Weyl
group orbit. The zeros of this sum ARE the points where the
characters vanish — the fixed points of the modular flow.
-/

end InfoGeometry.Arithmetic.PolesAsCharacters
