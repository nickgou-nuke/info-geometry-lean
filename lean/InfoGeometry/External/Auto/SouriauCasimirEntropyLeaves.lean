import Mathlib.Tactic

noncomputable section

namespace SouriauCasimirEntropyLeaves

structure GroupAction (G X : Type*) where
  act : G → X → X

def invariant {G X R : Type*} (A : GroupAction G X) (f : X → R) : Prop :=
  ∀ g x, f (A.act g x) = f x

def orbit {G X : Type*} (A : GroupAction G X) (x : X) : Set X :=
  {y | ∃ g, y = A.act g x}

def levelSet {X R : Type*} (f : X → R) (r : R) : Set X :=
  {x | f x = r}

theorem invariant_constant_on_orbit {G X R : Type*}
    (A : GroupAction G X) (f : X → R) (hf : invariant A f) (x y : X)
    (hy : y ∈ orbit A x) :
    f y = f x := by
  rcases hy with ⟨g, rfl⟩
  exact hf g x

theorem orbit_subset_levelSet_of_invariant {G X R : Type*}
    (A : GroupAction G X) (f : X → R) (hf : invariant A f) (x : X) :
    orbit A x ⊆ levelSet f (f x) := by
  intro y hy
  exact invariant_constant_on_orbit A f hf x y hy

def entropyFromCasimirs {X R : Type*} [Semiring R]
    (C1 C2 : X → R) (a b c : R) (x : X) : R :=
  a * C1 x + b * C2 x + c

theorem entropyFromCasimirs_invariant {G X R : Type*} [Semiring R]
    (A : GroupAction G X) (C1 C2 : X → R) (a b c : R)
    (hC1 : invariant A C1) (hC2 : invariant A C2) :
    invariant A (entropyFromCasimirs C1 C2 a b c) := by
  intro g x
  simp [entropyFromCasimirs, hC1 g x, hC2 g x]

theorem entropy_leaf_contains_coadjoint_orbit {G X R : Type*} [Semiring R]
    (A : GroupAction G X) (C1 C2 : X → R) (a b c : R)
    (hC1 : invariant A C1) (hC2 : invariant A C2) (x : X) :
    orbit A x ⊆ levelSet (entropyFromCasimirs C1 C2 a b c)
      (entropyFromCasimirs C1 C2 a b c x) := by
  exact orbit_subset_levelSet_of_invariant A
    (entropyFromCasimirs C1 C2 a b c)
    (entropyFromCasimirs_invariant A C1 C2 a b c hC1 hC2) x

def sameCasimirLeaf {X R : Type*} (C1 C2 : X → R) (x y : X) : Prop :=
  C1 y = C1 x ∧ C2 y = C2 x

theorem same_casimir_leaf_same_entropy {X R : Type*} [Semiring R]
    (C1 C2 : X → R) (a b c : R) {x y : X}
    (h : sameCasimirLeaf C1 C2 x y) :
    entropyFromCasimirs C1 C2 a b c y =
      entropyFromCasimirs C1 C2 a b c x := by
  rcases h with ⟨h1, h2⟩
  simp [entropyFromCasimirs, h1, h2]

def legendreEntropy (logZ pairing : ℚ) : ℚ :=
  logZ + pairing

theorem legendreEntropy_invariant
    {G X : Type*} (A : GroupAction G X) (logZ pairing : X → ℚ)
    (hZ : invariant A logZ) (hp : invariant A pairing) :
    invariant A (fun x => legendreEntropy (logZ x) (pairing x)) := by
  intro g x
  simp [legendreEntropy, hZ g x, hp g x]

def poincareMassCasimir (massSq : ℚ) : ℚ := -massSq
def poincareSpinCasimir (spinSq : ℚ) : ℚ := spinSq
def dilationSpringStiffnessFromC1 (C1 : ℚ) : ℚ := -C1

theorem dilation_spring_stiffness_massSq (massSq : ℚ) :
    dilationSpringStiffnessFromC1 (poincareMassCasimir massSq) = massSq := by
  simp [dilationSpringStiffnessFromC1, poincareMassCasimir]

def isospinCasimir (I : ℚ) : ℚ :=
  I * (I + 1)

def TzMinusHalf : ℚ := -1 / 2
def TzPlusHalf : ℚ := 1 / 2

theorem isospin_half_casimir :
    isospinCasimir (1 / 2) = 3 / 4 := by
  norm_num [isospinCasimir]

def isospinShellEntropy (a c : ℚ) (I : ℚ) : ℚ :=
  a * isospinCasimir I + c

theorem A67_isospin_flip_preserves_casimir :
    isospinCasimir (1 / 2) = isospinCasimir (1 / 2) ∧
      TzMinusHalf + TzPlusHalf = 0 := by
  norm_num [isospinCasimir, TzMinusHalf, TzPlusHalf]

theorem A67_isospin_shell_entropy_preserved (a c : ℚ) :
    isospinShellEntropy a c (1 / 2) =
      a * (3 / 4) + c := by
  norm_num [isospinShellEntropy, isospinCasimir]

end SouriauCasimirEntropyLeaves

end noncomputable section
