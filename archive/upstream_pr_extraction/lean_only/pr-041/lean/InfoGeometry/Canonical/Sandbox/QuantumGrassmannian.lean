import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

universe u v

/-- Generators for the Quantum Grassmannian, representing Plücker coordinates p_{ij}. -/
structure QuantumPluckerGenerator (ι : Type v) where
  i : ι
  j : ι
deriving DecidableEq, Repr

/-- The free algebra on the Plücker generators. -/
abbrev FreeQG (R : Type u) [CommRing R] (ι : Type v) := 
  FreeAlgebra R (QuantumPluckerGenerator ι)

/-- 
  The quantum Plücker relations.
  We use a standard un-deformed non-commutative relation: 
  p_{ij} p_{kl} - p_{ik} p_{jl} + p_{il} p_{jk} = 0,
  represented algebraically as p_{ij} p_{kl} + p_{il} p_{jk} = p_{ik} p_{jl}.
-/
inductive QuantumPluckerRel (R : Type u) [CommRing R] (ι : Type v) : FreeQG R ι → FreeQG R ι → Prop
  | plucker (i j k l : ι) : 
      QuantumPluckerRel R ι
        (FreeAlgebra.ι R (QuantumPluckerGenerator.mk i j) * FreeAlgebra.ι R (QuantumPluckerGenerator.mk k l) + 
         FreeAlgebra.ι R (QuantumPluckerGenerator.mk i l) * FreeAlgebra.ι R (QuantumPluckerGenerator.mk j k))
        (FreeAlgebra.ι R (QuantumPluckerGenerator.mk i k) * FreeAlgebra.ι R (QuantumPluckerGenerator.mk j l))

/-- 
  The Quantum Grassmannian coordinate ring as a quotient algebra. 
-/
def QuantumGrassmannian (R : Type u) [CommRing R] (ι : Type v) : Type _ :=
  RingQuot (QuantumPluckerRel R ι)
deriving Inhabited, Ring, Algebra R
