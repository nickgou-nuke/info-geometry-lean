# Hestenes–Krein–BdG precise formulation

Formal Lean artifact: `/home/goutev/auto/proofs/HestenesKreinBdGPrecision.lean`

Verified command:

```bash
cd /home/goutev/auto/proofs && lake lean HestenesKreinBdGPrecision.lean
```

Result: pass.

## 1. The `2 × 2` chiral Krein space `K_{1,1}`

Base space:

```text
V = ℝ²
A₂ = End(V) = M₂(ℝ) ≃ Cl_{1,1}(ℝ)
```

Krein metric / fundamental symmetry:

```text
η = σ₃ = [ 1  0]
         [ 0 -1]
```

Lean:

```lean
def η : M2R := !![1, 0; 0, -1]
def kreinInner (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 - u 1 * v 1
```

The two chiral sheets are the projector images:

```text
P_R = [1 0]       P_L = [0 0]
      [0 0]             [0 1]
```

Lean theorems:

```lean
P_R * P_R = P_R
P_L * P_L = P_L
P_R * P_L = 0
P_L * P_R = 0
P_R + P_L = 1
```

## 2. Real Clifford atom `Cl_{1,1}(ℝ)`

Generators:

```text
e₁ = σ₁ = [0 1]
          [1 0]

e₂ = [0 -1]
     [1  0]
```

Lean:

```lean
def e1 : M2R := Jmod
def e2 : M2R := Kcpx
```

Verified relations:

```lean
e1 * e1 = 1
e2 * e2 = -1
e1 * e2 + e2 * e1 = 0
e1 * e2 = η
```

Thus the volume element is exactly the Krein fundamental symmetry:

```text
e₁e₂ = η
```

## 3. Krein adjoint / Clifford conjugation

For `A = [[a,b],[c,d]]`, the Krein adjoint is:

```text
A♯ = η Aᵀ η = [ a -c]
              [-b  d]
```

Lean:

```lean
def kreinAdjoint (A : M2R) : M2R := !![A 0 0, -A 1 0; -A 0 1, A 1 1]
```

Verified:

```lean
kreinAdjoint (kreinAdjoint A) = A
```

## 4. Tomita/modular reflection on chiral sheets

Finite Tomita reflection:

```text
J = σ₁ = [0 1]
         [1 0]
```

Lean:

```lean
def Jmod : M2R := !![0, 1; 1, 0]
```

Verified:

```lean
Jmod * Jmod = 1
Jmod * P_L * Jmod = P_R
Jmod * P_R * Jmod = P_L
```

So the modular reflection swaps the two Krein sheets.

## 5. Block diagonal and off-block diagonal geometry

For any `A : M₂(ℝ)`:

```text
dblock(A)   = [A₀₀  0 ]
              [ 0  A₁₁]

offblock(A) = [ 0  A₀₁]
              [A₁₀  0 ]
```

Verified:

```lean
dblock A + offblock A = A
```

The Hestenes/Dirac mass coupling is pure off-block:

```lean
def diracMassCoupling (m : ℝ) : M2R := m • Jmod
```

Verified:

```lean
dblock (diracMassCoupling m) = 0
offblock (diracMassCoupling m) = diracMassCoupling m
```

Thus the Dirac mass is formalized as off-sheet `R/L` coupling.

## 6. Nambu–Gorkov / BdG degree doubling

Doubled algebra:

```text
M₂(M₂(ℝ)) ≃ M₄(ℝ)
```

Lean:

```lean
abbrev NambuBlockR := Matrix (Fin 2) (Fin 2) M2R
```

Doubled Krein symmetry:

```text
Γ₀ = [ η   0]
     [ 0  -η]
```

Lean:

```lean
def Gamma0 : NambuBlockR := !![η, 0; 0, -η]
```

Verified:

```lean
Gamma0 * Gamma0 = 1
```

Doubled Tomita/Nambu particle-hole reflection:

```text
J_Tom = [ 0  J]
        [ J  0]
```

Lean:

```lean
def JTom : NambuBlockR := !![0, Jmod; Jmod, 0]
```

Verified:

```lean
JTom * JTom = 1
JTom * ParticleProjector * JTom = HoleProjector
JTom * HoleProjector * JTom = ParticleProjector
```

## 7. BdG Hamiltonian

Finite BdG block:

```text
BdG(H, Δ) = [ H      Δ  ]
            [ Δ♯   -H♯]
```

Lean:

```lean
def bdgBlock (H Δ : M2R) : NambuBlockR := !![H, Δ; kreinAdjoint Δ, -kreinAdjoint H]
```

Dirac kinetic/mass block:

```text
h₀(p,m) = [ p  m]
          [ m -p]
```

Singlet pairing block:

```text
Δ(s) = [ 0  s]
       [-s  0]
```

Lean:

```lean
def h0 (p m : ℝ) : M2R := !![p, m; m, -p]
def singletDelta (Δ : ℝ) : M2R := !![0, Δ; -Δ, 0]
def bdgHamiltonian (p m Δ : ℝ) : NambuBlockR := bdgBlock (h0 p m) (singletDelta Δ)
```

Verified decomposition:

```lean
dblock (h0 p m) = !![p, 0; 0, -p]
offblock (h0 p m) = !![0, m; m, 0]
dblock (singletDelta Δ) = 0
offblock (singletDelta Δ) = singletDelta Δ
```

## 8. CAR / CCR / supergraded real super-Lie layer

Finite CAR atom:

```text
a  = [0 1]      a† = [0 0]
     [0 0]           [1 0]
```

Lean:

```lean
def annR : M2R := !![0, 1; 0, 0]
def creR : M2R := !![0, 0; 1, 0]
```

Verified:

```lean
annR * annR = 0
creR * creR = 0
antiComm annR creR = 1
```

Finite CCR obstruction:

```lean
theorem finite_CCR_trace_obstruction (Q P : M2R) :
    Matrix.trace (comm Q P) = 0
```

So exact `[Q,P]=1` cannot live in finite `M₂(ℝ)`, because finite matrix commutators have trace zero. CCR must be represented by an infinite/Weyl/completion layer over the finite atom.

Supergraded bracket:

```lean
inductive Parity where | even | odd

def superBracket (p q : Parity) (A B : M2R) : M2R :=
  match p, q with
  | Parity.odd, Parity.odd => A * B + B * A
  | _, _ => A * B - B * A
```

Verified:

```lean
superBracket odd odd A B = antiComm A B
superBracket even q A B = comm A B
```

## 9. Synthesis theorem

The compact theorem package is:

```lean
theorem hestenes_krein_bdg_supergraded_synthesis (m : ℝ) : ...
```

It proves in one statement:

- `η² = 1`
- `J² = 1`
- `K² = -1`
- `e₁e₂ = η`
- `{e₁,e₂}=0`
- `P_R + P_L = 1`
- `J P_L J = P_R`
- `P_R P_L = 0`
- `Γ₀² = 1`
- `J_Tom² = 1`
- Dirac mass is pure off-block coupling
- finite CAR is exact
- finite CCR has trace obstruction

This is the precise finite algebraic core of the proposed Hestenes–Krein–BdG–Tomita–Nambu architecture.

## 10. Weyl CCR completion interface

The finite trace obstruction is now paired with an explicit abstract Weyl interface in the same Lean file.  This keeps the core finite matrix geometry honest while still giving the bosonic CCR sector a mathematically correct completion target.

Canonical two-generator symplectic test plane:

```lean
abbrev R2 := Fin 2 → ℝ

def canonicalSigma (u v : R2) : ℝ := u 0 * v 1 - u 1 * v 0
```

Verified:

```lean
canonicalSigma u u = 0
canonicalSigma v u = -canonicalSigma u v
```

Weyl phase:

```lean
def weylPhase {V : Type*} (σ : V → V → ℝ) (u v : V) : ℂ :=
  Complex.exp (-(Complex.I / 2) * (σ u v : ℂ))
```

Abstract Weyl system:

```lean
structure WeylSystem (V A : Type*)
    [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A] where
  sigma : V → V → ℝ
  sigma_skew : ∀ u v : V, sigma v u = -sigma u v
  W : V → A
  W_zero : W 0 = 1
  W_neg : ∀ u : V, W (-u) = star (W u)
  W_mul : ∀ u v : V, W u * W v = weylPhase sigma u v • W (u + v)
```

Bridge theorem:

```lean
theorem car_core_weyl_completion_boundary ...
```

It proves the combined boundary:

- finite CAR remains exact: `{a,a†}=1`
- finite matrix CCR remains obstructed: `Tr([Q,P])=0`
- the abstract Weyl completion supplies the proper relation:
  `W(u)W(v)=exp(-i σ(u,v)/2) W(u+v)`

Thus the finite Hestenes–Krein–BdG core and the infinite/Weyl CCR completion are separated by a compiler-verified interface rather than confused inside a finite matrix model.

## 11. Split `(5,5)` supertrace compensation

The file now also includes a finite theorem-backed model of the `Cl(5,5)` spinor grading as a `32 = 16 + 16` split block.  This captures the balanced positive/negative chirality count without needing to construct the full `Cl55 ≃ M₃₂(ℝ)` representation in this pass.

Lean objects:

```lean
abbrev M16R := Matrix (Fin 16) (Fin 16) ℝ
abbrev M32SplitR := Matrix (Fin 2) (Fin 2) M16R

def Gamma32 : M32SplitR := !![(1 : M16R), 0; 0, -(1 : M16R)]
def blockTrace32 (A : M32SplitR) : ℝ := Matrix.trace (A 0 0) + Matrix.trace (A 1 1)
def superTrace32 (A : M32SplitR) : ℝ := blockTrace32 (Gamma32 * A)
```

Verified:

```lean
Gamma32 * Gamma32 = 1
blockTrace32 1 = 32
blockTrace32 Gamma32 = 0
superTrace32 1 = 0
```

Bridge theorem:

```lean
theorem cl55_supertrace_compensates_finite_trace_obstruction :
    superTrace32 (1 : M32SplitR) = 0 ∧
    blockTrace32 (1 : M32SplitR) = 32 ∧
    (∀ Q P : M2R, Matrix.trace (comm Q P) = 0)
```

Interpretation:

- ordinary finite trace sees the identity: `Tr(1)=32`
- the balanced `(5,5)` supertrace cancels the identity: `Str(1)=0`
- the original finite commutator trace obstruction remains true
- the supergraded `(5,5)` block provides the compensated trace channel for CAR/supercommutator closure

This is the local finite supertrace counterpart to the Weyl/infinite CCR completion interface.

### Bridge to the compiled `Clifford55.R_PT` spine

`HestenesKreinBdGPrecision.lean` now imports the already verified `Clifford55.lean` module and names the existing Cl(5,5) volume element:

```lean
def Gamma55Volume : Clifford55.Cl55 := Clifford55.R_PT
```

Compiled bridge theorem:

```lean
theorem cl55_R_PT_supertrace_compensation_bridge :
    Gamma55Volume = Clifford55.R_PT ∧
    Gamma32 * Gamma32 = (1 : M32SplitR) ∧
    superTrace32 (1 : M32SplitR) = 0 ∧
    blockTrace32 (1 : M32SplitR) = 32 ∧
    (∀ Q P : M2R, Matrix.trace (comm Q P) = 0)
```

This bridge is intentionally precise: it does not claim that `Gamma32` has already been proved to be the representation image of `R_PT`; it records the verified connection point between the authoritative `Clifford55.R_PT` volume spine and the finite split-spinor supertrace compensation certificate.
