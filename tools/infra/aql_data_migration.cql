// AQL / CQL (Categorical Query Language) Data Migration Schema
// Mapping computational invariants (Macaulay2 / SageMath) to Theorem Provers

typeside Ty = literal {
  java_types
    String = "java.lang.String"
    Integer = "java.lang.Integer"
  java_constants
    String = "return input[0]"
    Integer = "return java.lang.Integer.parseInt(input[0])"
}

// ------------------------------------------------------------------
// 1. Source Schema (S): Computational Output (Macaulay2 / SageMath)
// ------------------------------------------------------------------
schema ComputationalOutput = literal : Ty {
  entities
    PolynomialRing
    Generator
    IdealRelation
  foreign_keys
    gen_ring : Generator -> PolynomialRing
    rel_ring : IdealRelation -> PolynomialRing
  attributes
    ring_name : PolynomialRing -> String
    gen_symbol : Generator -> String
    rel_equation : IdealRelation -> String
    dimension : PolynomialRing -> Integer
}

// ------------------------------------------------------------------
// 2. Target Schema (T): Theorem Prover Specifications (Lean/Isabelle/Coq)
// ------------------------------------------------------------------
schema FormalVerification = literal : Ty {
  entities
    FormalCarrier
    FormalGenerator
    FormalAxiom
  foreign_keys
    has_carrier : FormalGenerator -> FormalCarrier
    axiom_context : FormalAxiom -> FormalCarrier
  attributes
    carrier_type : FormalCarrier -> String
    element_name : FormalGenerator -> String
    axiom_stmt : FormalAxiom -> String
}

// ------------------------------------------------------------------
// 3. Data Migration Functor (F: S -> T)
// ------------------------------------------------------------------
mapping MigrationFunctor = literal : ComputationalOutput -> FormalVerification {
  entity PolynomialRing -> FormalCarrier
  entity Generator -> FormalGenerator
  entity IdealRelation -> FormalAxiom

  foreign_keys
    gen_ring -> has_carrier
    rel_ring -> axiom_context

  attributes
    ring_name -> carrier_type
    gen_symbol -> element_name
    rel_equation -> axiom_stmt
}

// ------------------------------------------------------------------
// Example: Data Instance in the Source Schema (Macaulay2 Gröbner Basis)
// ------------------------------------------------------------------
instance M2_Output = literal : ComputationalOutput {
  generators
    R1 : PolynomialRing
    G1, G2 : Generator
    Rel1 : IdealRelation
  equations
    ring_name(R1) = "KreinDoubledSpace"
    dimension(R1) = "4"
    
    gen_ring(G1) = R1
    gen_symbol(G1) = "sigma_x"
    
    gen_ring(G2) = R1
    gen_symbol(G2) = "sigma_y"
    
    rel_ring(Rel1) = R1
    rel_equation(Rel1) = "sigma_x * sigma_y + sigma_y * sigma_x = 0"
}

// ------------------------------------------------------------------
// Migrate Data: Pushforward (Σ) from Source to Target
// ------------------------------------------------------------------
instance Formal_Input = sigma MigrationFunctor M2_Output
