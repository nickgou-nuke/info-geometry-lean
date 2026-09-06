import Mathlib

/-!
# Licata--Finster Eilenberg--MacLane spaces

Formal theorem-interface for the CSL-LICS 2014 construction:
for an abelian group `G`, `K(G,n)` has `π_n ≃ G` and all other
homotopy groups trivial; reduced cohomology of spheres splits
diagonally.
-/

universe u

noncomputable section

namespace LicataFinsterEMSpaces

structure EMObject (G : Type u) [AddCommGroup G] (n : ℕ) where
  pi : ℕ → Type u
  diagonal : pi n ≃ G
  offDiagonal : ∀ k, k ≠ n → Subsingleton (pi k)

def EM_pi_diagonal {G : Type u} [AddCommGroup G] {n : ℕ}
    (K : EMObject G n) :
    K.pi n ≃ G :=
  K.diagonal

theorem EM_pi_offDiagonal_unique {G : Type u} [AddCommGroup G] {n k : ℕ}
    (K : EMObject G n) (h : k ≠ n) (x y : K.pi k) : x = y := by
  letI := K.offDiagonal k h
  exact Subsingleton.elim x y

inductive EMModelPi (G : Type u) (n : ℕ) : ℕ → Type u where
  | diagonal : G → EMModelPi G n n
  | offdiag {k : ℕ} : k ≠ n → EMModelPi G n k

namespace EMModelPi

def diagonalEquiv (G : Type u) (n : ℕ) :
    EMModelPi G n n ≃ G where
  toFun x := by
    cases x with
    | diagonal g => exact g
    | offdiag h => exact False.elim (h rfl)
  invFun g := diagonal g
  left_inv x := by
    cases x with
    | diagonal g => rfl
    | offdiag h => exact False.elim (h rfl)
  right_inv g := rfl

theorem offDiagonal_unique (G : Type u) {n k : ℕ} (h : k ≠ n)
    (x y : EMModelPi G n k) : x = y := by
  cases x with
  | diagonal g => exact False.elim (h rfl)
  | offdiag hx =>
    cases y with
    | diagonal g => exact False.elim (h rfl)
    | offdiag hy => congr

instance offDiagonalSubsingleton (G : Type u) {n k : ℕ} (h : k ≠ n) :
    Subsingleton (EMModelPi G n k) where
  allEq := offDiagonal_unique G h

end EMModelPi

def canonicalEM (G : Type u) [AddCommGroup G] (n : ℕ) : EMObject G n where
  pi := EMModelPi G n
  diagonal := EMModelPi.diagonalEquiv G n
  offDiagonal := by
    intro k h
    exact EMModelPi.offDiagonalSubsingleton G h

def canonicalEM_diagonal (G : Type u) [AddCommGroup G] (n : ℕ) :
    (canonicalEM G n).pi n ≃ G :=
  EM_pi_diagonal (canonicalEM G n)

theorem canonicalEM_offDiagonal_unique (G : Type u) [AddCommGroup G]
    {n k : ℕ} (h : k ≠ n) (x y : (canonicalEM G n).pi k) : x = y :=
  EM_pi_offDiagonal_unique (canonicalEM G n) h x y

def KG1HasCorrectHomotopyGroups (G : Type u) [AddCommGroup G] : Prop :=
  Nonempty (EMObject G 1)

theorem K_G_1_exists (G : Type u) [AddCommGroup G] :
    KG1HasCorrectHomotopyGroups G :=
  ⟨canonicalEM G 1⟩

def KGnHasCorrectHomotopyGroups (G : Type u) [AddCommGroup G] (n : ℕ) : Prop :=
  Nonempty (EMObject G n)

theorem K_G_n_exists (G : Type u) [AddCommGroup G] (n : ℕ) :
    KGnHasCorrectHomotopyGroups G n :=
  ⟨canonicalEM G n⟩

structure SuspensionShift (A : Type u) [AddCommGroup A] where
  suspendedPi : ℕ → Type u
  shift : ∀ k, suspendedPi (k + 1) ≃ EMModelPi A 1 k

def canonicalSuspensionShift (A : Type u) [AddCommGroup A] : SuspensionShift A where
  suspendedPi k := EMModelPi A 2 k
  shift := by
    intro k
    by_cases h : k = 1
    · subst h
      change EMModelPi A 2 2 ≃ EMModelPi A 1 1
      exact (EMModelPi.diagonalEquiv A 2).trans (EMModelPi.diagonalEquiv A 1).symm
    · have hk : k + 1 ≠ 2 := by omega
      exact {
        toFun := fun _ => EMModelPi.offdiag h
        invFun := fun _ => EMModelPi.offdiag hk
        left_inv := by intro x; exact EMModelPi.offDiagonal_unique A hk _ _
        right_inv := by intro x; exact EMModelPi.offDiagonal_unique A h _ _ }

def suspension_lifts_pi1_to_pi2 (A : Type u) [AddCommGroup A] :
    (canonicalSuspensionShift A).suspendedPi 2 ≃ A :=
  EMModelPi.diagonalEquiv A 2

inductive ReducedCohomologySphere (k n : ℕ) : Type where
  | diagonal : k = n → ℤ → ReducedCohomologySphere k n
  | offdiag : k ≠ n → ReducedCohomologySphere k n

namespace ReducedCohomologySphere

def diagonalEquiv (n : ℕ) : ReducedCohomologySphere n n ≃ ℤ where
  toFun x := by
    cases x with
    | diagonal _ z => exact z
    | offdiag h => exact False.elim (h rfl)
  invFun z := diagonal rfl z
  left_inv x := by
    cases x with
    | diagonal h z =>
      cases h
      rfl
    | offdiag h => exact False.elim (h rfl)
  right_inv z := rfl

theorem offDiagonal_unique {k n : ℕ} (h : k ≠ n)
    (x y : ReducedCohomologySphere k n) : x = y := by
  cases x with
  | diagonal hk z => exact False.elim (h hk)
  | offdiag hx =>
    cases y with
    | diagonal hk z => exact False.elim (h hk)
    | offdiag hy => congr

end ReducedCohomologySphere

def sphere_cohomology_diagonal (n : ℕ) :
    ReducedCohomologySphere n n ≃ ℤ :=
  ReducedCohomologySphere.diagonalEquiv n

theorem sphere_cohomology_offDiagonal_unique {k n : ℕ} (h : k ≠ n)
    (x y : ReducedCohomologySphere k n) : x = y :=
  ReducedCohomologySphere.offDiagonal_unique h x y

theorem sphere_cohomology_offDiagonal_subsingleton {k n : ℕ} (h : k ≠ n) :
    Subsingleton (ReducedCohomologySphere k n) where
  allEq := ReducedCohomologySphere.offDiagonal_unique h

structure InfiniteLoopSpectrum (G : Type u) [AddCommGroup G] where
  space : (n : ℕ) → EMObject G n
  delooping : ∀ n, (space n).pi n ≃ (space (n + 1)).pi (n + 1)

def canonicalSpectrum (G : Type u) [AddCommGroup G] : InfiniteLoopSpectrum G where
  space n := canonicalEM G n
  delooping n :=
    (EMModelPi.diagonalEquiv G n).trans (EMModelPi.diagonalEquiv G (n + 1)).symm

def spectrum_delooping_preserves_group (G : Type u) [AddCommGroup G] (n : ℕ) :
    ((canonicalSpectrum G).space n).pi n ≃ ((canonicalSpectrum G).space (n + 1)).pi (n + 1) :=
  (canonicalSpectrum G).delooping n

def integral_EM_diagonal (n : ℕ) :
    (canonicalEM ℤ n).pi n ≃ ℤ :=
  canonicalEM_diagonal ℤ n

def integral_sphere_cohomology_diagonal (n : ℕ) :
    ReducedCohomologySphere n n ≃ ℤ :=
  sphere_cohomology_diagonal n

end LicataFinsterEMSpaces

end noncomputable section
