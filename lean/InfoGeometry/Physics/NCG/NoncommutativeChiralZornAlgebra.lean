import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

/-- A Zorn coordinate with coefficients in an arbitrary (possibly
noncommutative) ring.  No multiplication or associativity is imposed on the
coordinate carrier itself. -/
structure NCZornElement (A : Type*) [Ring A] where
  n_plus : A
  n_minus : A
  sigma_plus : Fin 3 → A
  sigma_minus : Fin 3 → A

namespace NCZornElement

def zornDot (x y : Fin 3 → A) : A :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def zornCross (x y : Fin 3 → A) : Fin 3 → A
  | 0 => x 1 * y 2 - x 2 * y 1
  | 1 => x 2 * y 0 - x 0 * y 2
  | 2 => x 0 * y 1 - x 1 * y 0

@[simp] theorem zornCross_zero :
    zornCross (fun _ : Fin 3 => (0 : A)) (fun _ : Fin 3 => (0 : A)) =
      (fun _ : Fin 3 => (0 : A)) := by
  funext c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp [zornCross]
  · refine Fin.cases ?_ (fun c => ?_) c
    · simp [zornCross]
    · refine Fin.cases ?_ (fun c => ?_) c
      · simp [zornCross]
      · exact Fin.elim0 c

@[simp] theorem zornDot_zero_left (x : Fin 3 → A) :
    zornDot (fun _ : Fin 3 => (0 : A)) x = 0 := by
  simp [zornDot]

@[simp] theorem zornDot_zero_right (x : Fin 3 → A) :
    zornDot x (fun _ : Fin 3 => (0 : A)) = 0 := by
  simp [zornDot]

@[simp] theorem zornDot_zero_zero :
    zornDot (fun _ : Fin 3 => (0 : A)) (fun _ : Fin 3 => (0 : A)) = 0 := by
  simp [zornDot]

@[simp] theorem zornCross_zero_left (x : Fin 3 → A) :
    zornCross (fun _ : Fin 3 => (0 : A)) x = (fun _ : Fin 3 => (0 : A)) := by
  funext c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp [zornCross]
  · refine Fin.cases ?_ (fun c => ?_) c
    · simp [zornCross]
    · refine Fin.cases ?_ (fun c => ?_) c
      · simp [zornCross]
      · exact Fin.elim0 c

@[simp] theorem zornCross_zero_right (x : Fin 3 → A) :
    zornCross x (fun _ : Fin 3 => (0 : A)) = (fun _ : Fin 3 => (0 : A)) := by
  funext c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp [zornCross]
  · refine Fin.cases ?_ (fun c => ?_) c
    · simp [zornCross]
    · refine Fin.cases ?_ (fun c => ?_) c
      · simp [zornCross]
      · exact Fin.elim0 c

@[simp] theorem zornCross_zero_zero_apply (i : Fin 3) :
    zornCross (fun _ : Fin 3 => (0 : A)) (fun _ : Fin 3 => (0 : A)) i = 0 := by
  simpa using congrFun (zornCross_zero (A := A)) i

/-- The noncommutative Zorn multiplication.  Every coefficient product keeps
its displayed order; only the additive laws of `A` are used below. -/
def mul (X Y : NCZornElement A) : NCZornElement A where
  n_plus := X.n_plus * Y.n_plus + zornDot X.sigma_plus Y.sigma_minus
  n_minus := X.n_minus * Y.n_minus + zornDot X.sigma_minus Y.sigma_plus
  sigma_plus := fun c =>
    X.n_plus * Y.sigma_plus c + X.sigma_plus c * Y.n_minus -
      zornCross X.sigma_minus Y.sigma_minus c
  sigma_minus := fun c =>
    X.n_minus * Y.sigma_minus c + X.sigma_minus c * Y.n_plus +
      zornCross X.sigma_plus Y.sigma_plus c

instance : Mul (NCZornElement A) := ⟨mul⟩

def pureNPlus (a : A) : NCZornElement A :=
  ⟨a, 0, fun _ => 0, fun _ => 0⟩

def pureNMinus (a : A) : NCZornElement A :=
  ⟨0, a, fun _ => 0, fun _ => 0⟩

@[simp] theorem pure_n_plus_mul (a b : A) :
    pureNPlus a * pureNPlus b = pureNPlus (a * b) := by
  change mul (pureNPlus a) (pureNPlus b) = pureNPlus (a * b)
  simp [NCZornElement.mul, pureNPlus, zornDot]

@[simp] theorem orthogonal_chiral_projectors_annihilate (a b : A) :
    pureNPlus a * pureNMinus b =
      ⟨0, 0, fun _ => 0, fun _ => 0⟩ := by
  change mul (pureNPlus a) (pureNMinus b) = _
  simp [NCZornElement.mul, pureNPlus, pureNMinus, zornDot]

end NCZornElement
end InfoGeometry.Physics.NCG
