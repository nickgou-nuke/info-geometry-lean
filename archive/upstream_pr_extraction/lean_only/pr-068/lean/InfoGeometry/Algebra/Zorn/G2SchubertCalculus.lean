import InfoGeometry.Algebra.Zorn.G2BruhatCardinalities

/-!
# Finite Schubert-data interface for the `G₂` Bruhat development

This owner records finite indexing and coefficient data only.  It does not
claim to construct the flag variety, quantum cohomology, or Gromov--Witten
invariants.
-/

namespace InfoGeometry.Algebra.Zorn.G2SchubertCalculus

open InfoGeometry.Algebra.Zorn.G2BruhatCardinalities

abbrev SchubertCoefficients := Fin 12 → ℤ
abbrev SchubertBasisIndex := Fin 12

def schubertDegree (w : SchubertBasisIndex) : ℕ := weylLength w

structure SchubertDatum where
  coefficients : SchubertCoefficients

def schubertAdd (a b : SchubertCoefficients) : SchubertCoefficients :=
  fun i => a i + b i

def convolution (structureConstant : Fin 12 → Fin 12 → Fin 12 → ℤ)
    (a b : SchubertCoefficients) : SchubertCoefficients :=
  fun w => ∑ u : Fin 12, ∑ v : Fin 12,
    a u * b v * structureConstant u v w

theorem schubert_index_card : Fintype.card SchubertBasisIndex = 12 := by
  rfl

theorem schubertDegree_nonnegative (w : SchubertBasisIndex) :
    0 ≤ schubertDegree w := by
  exact Nat.zero_le _

theorem schubertAdd_apply (a b : SchubertCoefficients) (i : Fin 12) :
    schubertAdd a b i = a i + b i := by
  rfl

theorem convolution_apply (structureConstant : Fin 12 → Fin 12 → Fin 12 → ℤ)
    (a b : SchubertCoefficients) (w : Fin 12) :
    convolution structureConstant a b w =
      ∑ u : Fin 12, ∑ v : Fin 12,
        a u * b v * structureConstant u v w := by
  rfl

end InfoGeometry.Algebra.Zorn.G2SchubertCalculus
