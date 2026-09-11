import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Causal.Alexandrov
import InfoGeometry.Causal.ZornPresheaf
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

open CategoryTheory
open InfoGeometry.Causal
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

namespace InfoGeometry.Causal.ZornPresheafColimitBridge

/-- Direct functorial embedding of stage `n` diagonal cylinder into stage `n+1`. -/
def diagEmbedSuccRingHom (n : ℕ) : DiagAlg n →+* DiagAlg (n + 1) where
  toFun := diagEmbedSucc n
  map_zero' := rfl
  map_one' := rfl
  map_add' := diagEmbedSucc_add n
  map_mul' := fun _ _ => rfl

/-- Successor step embedding of the diagonal algebra in `RingCat`. -/
def diagSuccHom (n : ℕ) : RingCat.of (DiagAlg n) ⟶ RingCat.of (DiagAlg (n + 1)) :=
  RingCat.ofHom (diagEmbedSuccRingHom n)

/-- The diagonal embedding preserves multiplication across the Alexandrov causal step. -/
theorem diag_succ_preserves_mul (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (f * g) = diagEmbedSucc n f * diagEmbedSucc n g := rfl

/-- The diagonal embedding preserves addition across the Alexandrov causal step. -/
theorem diag_succ_preserves_add (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (f + g) = diagEmbedSucc n f + diagEmbedSucc n g :=
  diagEmbedSucc_add n f g

end InfoGeometry.Causal.ZornPresheafColimitBridge
