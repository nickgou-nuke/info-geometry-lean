import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation

noncomputable section

namespace InfoGeometry.Topology.BinaryCantorCuntzSuperchargeBridge

open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation

def head (b : (ℕ → BinarySector)) : BinarySector := b 0

def tail (b : (ℕ → BinarySector)) : (ℕ → BinarySector) := fun n => b (n + 1)

def prepend (s : BinarySector) (b : (ℕ → BinarySector)) : (ℕ → BinarySector)
  | 0 => s
  | n + 1 => b n

@[simp] theorem head_prepend (s : BinarySector) (b : (ℕ → BinarySector)) :
    head (prepend s b) = s := rfl

@[simp] theorem tail_prepend (s : BinarySector) (b : (ℕ → BinarySector)) :
    tail (prepend s b) = b := by
  funext n
  rfl

@[simp] theorem prepend_head_tail (b : (ℕ → BinarySector)) :
    prepend (head b) (tail b) = b := by
  funext n
  cases n <;> rfl

def creation (s : BinarySector) : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ) where
  toFun f b := if head b = s then f (tail b) else 0
  map_add' f g := by
    funext b
    by_cases h : head b = s <;> simp [h]
  map_smul' c f := by
    funext b
    by_cases h : head b = s <;> simp [h]

def annihilation (s : BinarySector) : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ) where
  toFun f b := f (prepend s b)
  map_add' f g := by funext b; rfl
  map_smul' c f := by funext b; rfl

theorem ortho (s t : BinarySector) :
    annihilation s * creation t =
      if s = t then (1 : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ)) else 0 := by
  ext f b
  by_cases h : s = t
  · subst h
    simp [annihilation, creation]
  · simp [annihilation, creation, h]

theorem partition :
    (∑ s : BinarySector, creation s * annihilation s) =
      (1 : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ)) := by
  ext f b
  cases h : head b with
  | plus =>
      simp [creation, annihilation, h]
      rw [← h, prepend_head_tail]
  | minus =>
      simp [creation, annihilation, h]
      rw [← h, prepend_head_tail]

def generators : CuntzO2Generators (Module.End ℂ ((ℕ → BinarySector) → ℂ)) where
  S1 := creation BinarySector.plus
  S2 := creation BinarySector.minus
  S1star := annihilation BinarySector.plus
  S2star := annihilation BinarySector.minus

theorem generators_isometry_plus :
    generators.S1star * generators.S1 = 1 := by
  simpa [generators] using ortho BinarySector.plus BinarySector.plus

theorem generators_isometry_minus :
    generators.S2star * generators.S2 = 1 := by
  simpa [generators] using ortho BinarySector.minus BinarySector.minus

theorem generators_orthogonal_pm :
    generators.S1star * generators.S2 = 0 := by
  simpa [generators] using ortho BinarySector.plus BinarySector.minus

theorem generators_orthogonal_mp :
    generators.S2star * generators.S1 = 0 := by
  simpa [generators] using ortho BinarySector.minus BinarySector.plus

theorem generators_complete :
    generators.S1 * generators.S1star + generators.S2 * generators.S2star = 1 := by
  ext f b
  cases h : head b with
  | plus =>
      simp [generators, creation, annihilation, h]
      rw [← h, prepend_head_tail]
  | minus =>
      simp [generators, creation, annihilation, h]
      rw [← h, prepend_head_tail]

theorem chiral_supercharge_hamiltonian :
    QPlus generators * QMinus generators + QMinus generators * QPlus generators =
      (1 : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ)) := by
  exact susy_hamiltonian_completeness generators
    generators_isometry_minus generators_isometry_plus generators_complete

theorem chiral_supercharge_nilpotence :
    QPlus generators * QPlus generators = 0 ∧
      QMinus generators * QMinus generators = 0 := by
  constructor
  · exact qplus_nilpotent generators generators_orthogonal_mp
  · exact qminus_nilpotent generators generators_orthogonal_pm

/-- The two mixed odd--odd products are the two first-level Cantor
projections.  This is the concrete product-level part of the chiral
superalgebra, not merely the nilpotence/Hamiltonian readout. -/
theorem chiral_supercharge_mixed_products :
    (QPlus generators * QMinus generators =
        generators.S1 * generators.S1star) ∧
      (QMinus generators * QPlus generators =
        generators.S2 * generators.S2star) := by
  constructor
  · exact qplus_qminus_product generators generators_isometry_minus
  · exact qminus_qplus_product generators generators_isometry_plus

/-- The concrete Cantor parity is an involution. -/
theorem chiral_parity_involution :
    ParityGrading generators * ParityGrading generators =
      (1 : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ)) := by
  exact parity_grading_square generators generators_isometry_plus
    generators_isometry_minus generators_orthogonal_pm generators_orthogonal_mp
    generators_complete

/-- The concrete parity anticommutes with both chiral zero modes. -/
theorem chiral_parity_anticommutation :
    (ParityGrading generators * QPlus generators +
        QPlus generators * ParityGrading generators = 0) ∧
      (ParityGrading generators * QMinus generators +
        QMinus generators * ParityGrading generators = 0) := by
  constructor
  · exact parity_qplus_anticommute generators generators_isometry_plus
      generators_isometry_minus generators_orthogonal_mp
  · exact parity_qminus_anticommute generators generators_isometry_plus
      generators_isometry_minus generators_orthogonal_pm

/-- The odd--odd superbracket on the concrete Cantor carrier is the identity
Hamiltonian. -/
theorem chiral_superbracket_eq_identity :
    QPlus generators * QMinus generators +
        QMinus generators * QPlus generators =
      (1 : ((ℕ → BinarySector) → ℂ) →ₗ[ℂ] ((ℕ → BinarySector) → ℂ)) :=
  chiral_supercharge_hamiltonian

end InfoGeometry.Topology.BinaryCantorCuntzSuperchargeBridge
