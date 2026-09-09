# Hestenes-Krein Clifford Algebra: Eliminating External Complex *i*

## Internal vs. External Complex Structure

### The Replacement Principle
Instead of introducing an external imaginary unit **i**, the Hestenes-Krein formalism constructs complex geometry entirely from **internal operators** in the geometric algebra:

1. **Complex structure J** (squares to -1):
   - Defined as a bivector in the algebra (e.g., spatial bivector J₃ = e₁e₂)
   - Replaces the role of *i* in all geometric operations
   - Acts on vectors by grade involution/rotation

2. **Hyperbolic structure B** (squares to +1):
   - Defined as a boost generator (e.g., B = e₃e₀)
   - Handles Lorentzian/hyperbolic transformations
   - Provides split signature structure

### Bilingual Translation Rules

| External Complex | Internal Operator          | File                          |
|------------------|----------------------------|-------------------------------|
| *i* (complex unit) | J = e₁e₂ (spatial bivector) | `CPTComplexStructure.lean`    |
| *e^(iθ)* (rotation) | R(θ) = cos(θ) + J sin(θ)   | `CliffordAction.lean`         |
| *e^(iφ)* (phase)   | U(φ) = cos(φ) + B sin(φ)   | `SplitQuadratic.lean`         |
| *i* in SUSY       | J on odd-graded forms      | `Superalgebra.lean`           |

### Odd-to-Even Conversion
The **grade-lowering projection** uses:
1. Multiplication by vector v: maps odd forms → even forms via contraction
2. Bivector action J: rotates odd/even pairs within the same spinor sector
3. Chiral projector P± = ½(1 ± Γ): splits spinor space into ±1 eigenvectors

### Key Equations
```
J² = -1  (complex structure)
B² = +1  (hyperbolic structure)  
Γ² = +1  (chirality operator)
```

These replace the need for any external *i* in all geometric algebra constructions.