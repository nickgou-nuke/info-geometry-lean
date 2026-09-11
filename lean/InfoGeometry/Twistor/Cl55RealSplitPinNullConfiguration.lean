import InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-!
# Split-Pin symmetry of marked `Q55` null configurations

The native real split-Pin action on the projective `Q55` null boundary acts
componentwise on ordered configurations of distinct null rays.  Because this
action commutes with finite reindexing, it descends to the existing unordered
configuration quotient.

Both constructions below are genuine permutation-group actions.  They are
global symmetries of configuration carriers, not exchange paths, fundamental
group elements, braid monodromy, or anyon data.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55RealSplitPinNullConfiguration

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- Componentwise action of one real split-Pin element on ordered distinct
`Q55` null configurations. -/
def realSplitPinOrderedNullEquiv (g : realSplitPin55) (n : ℕ) :
    Ordered Q55 n ≃ Ordered Q55 n where
  toFun p := ⟨fun i => realSplitPinNullAction g (p.1 i), by
    intro i j hij h
    exact p.2 i j hij ((realSplitPinNullAction g).injective h)⟩
  invFun p := ⟨fun i => realSplitPinNullAction g⁻¹ (p.1 i), by
    intro i j hij h
    exact p.2 i j hij ((realSplitPinNullAction g⁻¹).injective h)⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    change realSplitPinNullAction g⁻¹
        (realSplitPinNullAction g (p.1 i)) = p.1 i
    rw [map_inv]
    exact (realSplitPinNullAction g).symm_apply_apply (p.1 i)
  right_inv p := by
    apply Subtype.ext
    funext i
    change realSplitPinNullAction g
        (realSplitPinNullAction g⁻¹ (p.1 i)) = p.1 i
    rw [map_inv]
    exact (realSplitPinNullAction g).apply_symm_apply (p.1 i)

@[simp] theorem realSplitPinOrderedNullEquiv_apply
    (g : realSplitPin55) (n : ℕ) (p : Ordered Q55 n) (i : Fin n) :
    (realSplitPinOrderedNullEquiv g n p).1 i =
      realSplitPinNullAction g (p.1 i) :=
  rfl

@[simp] theorem realSplitPinOrderedNullEquiv_mul
    (g h : realSplitPin55) (n : ℕ) :
    realSplitPinOrderedNullEquiv (g * h) n =
      realSplitPinOrderedNullEquiv g n *
        realSplitPinOrderedNullEquiv h n := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  funext i
  exact congrArg
    (fun e : Equiv.Perm (TwistorSpace Q55) => e (p.1 i))
    (map_mul realSplitPinNullAction g h)

/-- The real split-Pin group acting on ordered marked null configurations. -/
def realSplitPinOrderedNullAction (n : ℕ) :
    realSplitPin55 →* Equiv.Perm (Ordered Q55 n) where
  toFun g := realSplitPinOrderedNullEquiv g n
  map_one' := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    funext i
    exact congrArg
      (fun e : Equiv.Perm (TwistorSpace Q55) => e (p.1 i))
      (map_one realSplitPinNullAction)
  map_mul' g h := realSplitPinOrderedNullEquiv_mul g h n

/-- Componentwise split-Pin symmetry commutes with permutation of the marked
points.  This is the descent datum for the unordered quotient. -/
theorem realSplitPinOrderedNullAction_respects_reindex
    (g : realSplitPin55) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : Ordered Q55 n) :
    realSplitPinOrderedNullAction n g (permute Q55 n σ p) =
      permute Q55 n σ (realSplitPinOrderedNullAction n g p) := by
  apply Subtype.ext
  funext i
  rfl

/-- Descended split-Pin map on the unordered configuration quotient. -/
def realSplitPinUnorderedNullMap (g : realSplitPin55) (n : ℕ) :
    Unordered Q55 n → Unordered Q55 n :=
  Quotient.lift
    (fun p => Quotient.mk' (realSplitPinOrderedNullAction n g p))
    (by
      intro p q hpq
      obtain ⟨σ, rfl⟩ := hpq
      apply Quotient.sound
      exact ⟨σ,
        (realSplitPinOrderedNullAction_respects_reindex g n σ p).symm⟩)

@[simp] theorem realSplitPinUnorderedNullMap_mk
    (g : realSplitPin55) (n : ℕ) (p : Ordered Q55 n) :
    realSplitPinUnorderedNullMap g n (Quotient.mk' p) =
      Quotient.mk' (realSplitPinOrderedNullAction n g p) :=
  rfl

@[simp] theorem realSplitPinUnorderedNullMap_mul
    (g h : realSplitPin55) (n : ℕ) (p : Unordered Q55 n) :
    realSplitPinUnorderedNullMap (g * h) n p =
      realSplitPinUnorderedNullMap g n
        (realSplitPinUnorderedNullMap h n p) := by
  refine Quotient.inductionOn p ?_
  intro p
  exact congrArg Quotient.mk'
    (congrArg (fun e : Equiv.Perm (Ordered Q55 n) => e p)
      (map_mul (realSplitPinOrderedNullAction n) g h))

/-- Each descended split-Pin map is an equivalence of unordered marked null
configurations. -/
def realSplitPinUnorderedNullEquiv (g : realSplitPin55) (n : ℕ) :
    Unordered Q55 n ≃ Unordered Q55 n where
  toFun := realSplitPinUnorderedNullMap g n
  invFun := realSplitPinUnorderedNullMap g⁻¹ n
  left_inv p := by
    rw [← realSplitPinUnorderedNullMap_mul]
    simp only [inv_mul_cancel]
    refine Quotient.inductionOn p ?_
    intro p
    change Quotient.mk' (realSplitPinOrderedNullAction n 1 p) =
      Quotient.mk' p
    rw [map_one]
    rfl
  right_inv p := by
    rw [← realSplitPinUnorderedNullMap_mul]
    simp only [mul_inv_cancel]
    refine Quotient.inductionOn p ?_
    intro p
    change Quotient.mk' (realSplitPinOrderedNullAction n 1 p) =
      Quotient.mk' p
    rw [map_one]
    rfl

/-- The concrete real split-Pin group action on unordered marked projective
`Q55` null configurations. -/
def realSplitPinUnorderedNullAction (n : ℕ) :
    realSplitPin55 →* Equiv.Perm (Unordered Q55 n) where
  toFun g := realSplitPinUnorderedNullEquiv g n
  map_one' := by
    apply Equiv.ext
    intro p
    refine Quotient.inductionOn p ?_
    intro p
    change Quotient.mk' (realSplitPinOrderedNullAction n 1 p) =
      Quotient.mk' p
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    exact realSplitPinUnorderedNullMap_mul g h n

end InfoGeometry.Twistor.Cl55RealSplitPinNullConfiguration
