import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Basic

open CliffordAlgebra

namespace InfoGeometry.Clifford

noncomputable section

/-- The dual space of a real vector space `L`. -/
abbrev Dual (L : Type*) [AddCommGroup L] [Module ℝ L] := L →ₗ[ℝ] ℝ

/-- The split vector space $V = L \oplus L^*$. -/
abbrev SplitSpace (L : Type*) [AddCommGroup L] [Module ℝ L] := L × Dual L

/-- The canonical bilinear form $B((u, f), (x, g)) = f(x)$ on $L \oplus L^*$. -/
def Bsplit (L : Type*) [AddCommGroup L] [Module ℝ L] : LinearMap.BilinForm ℝ (SplitSpace L) :=
  LinearMap.mk₂ ℝ (fun v w => v.2 w.1)
    (fun _ _ _ => rfl)
    (fun _ _ _ => rfl)
    (fun v w u => map_add v.2 w.1 u.1)
    (fun c v w => map_smul v.2 c w.1)

/-- The split quadratic form $Q(u, f) = f(u)$ on $L \oplus L^*$. -/
def Qsplit (L : Type*) [AddCommGroup L] [Module ℝ L] : QuadraticForm ℝ (SplitSpace L) :=
  LinearMap.BilinMap.toQuadraticMap (Bsplit L)

/-- The spinor space carrier is the Clifford Algebra over $L$ with $Q=0$ (the Exterior Algebra). -/
abbrev SpinorSpace (L : Type*) [AddCommGroup L] [Module ℝ L] := CliffordAlgebra (0 : QuadraticForm ℝ L)

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- Exterior multiplication on `SpinorSpace L` by a vector `u : L`. -/
def extAction (u : L) : Module.End ℝ (SpinorSpace L) where
  toFun w := ι (0 : QuadraticForm ℝ L) u * w
  map_add' _ _ := by simp only [mul_add]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    change ι 0 u * (r • x) = r • (ι 0 u * x)
    rw [mul_smul_comm]

/-- Left contraction action by a dual vector `f : Dual L`. -/
def intAction (f : Dual L) : Module.End ℝ (SpinorSpace L) :=
  CliffordAlgebra.contractLeft f

/-- The core fermionic anticommutator relation (proven natively using `contractLeft_ι_mul`). -/
theorem ext_int_anticommutator (u : L) (f : Dual L) (w : SpinorSpace L) :
    extAction u (intAction f w) + intAction f (extAction u w) =
      (algebraMap ℝ (SpinorSpace L) (f u)) * w := by
  dsimp [extAction, intAction]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  rw [← Algebra.smul_def]
  abel

/-- The action of a vector `v = (u, f)` in the split space on the spinor space. -/
def spinorAction (v : SplitSpace L) : Module.End ℝ (SpinorSpace L) :=
  extAction v.1 + intAction v.2

/-- Anticommutativity of exterior multiplication. -/
lemma ext_sq_zero (u : L) (w : SpinorSpace L) :
    extAction u (extAction u w) = 0 := by
  dsimp [extAction]
  rw [← mul_assoc]
  have h_sq : ι (0 : QuadraticForm ℝ L) u * ι 0 u = 0 := by
    exact ι_sq_scalar (0 : QuadraticForm ℝ L) u
  rw [h_sq, zero_mul]

/-- Nilpotency of the interior product contraction (proven natively using `contractLeft_contractLeft`). -/
theorem int_sq_zero (f : Dual L) (w : SpinorSpace L) :
    intAction f (intAction f w) = 0 := by
  dsimp [intAction]
  exact CliffordAlgebra.contractLeft_contractLeft f w

/-- The Clifford relation: the spinor action squared matches the split quadratic form. -/
theorem spinorAction_sq (v : SplitSpace L) (w : SpinorSpace L) :
    spinorAction v (spinorAction v w) =
      (algebraMap ℝ (SpinorSpace L) (Qsplit L v)) * w := by
  dsimp [spinorAction, Qsplit, Bsplit]
  rw [map_add, map_add]
  rw [ext_sq_zero, int_sq_zero]
  rw [zero_add, add_zero]
  exact ext_int_anticommutator v.1 v.2 w

/--
**The Coordinateless Spinor Representation:**
Natively constructs the representation of $C\ell(L \oplus L^*, Q)$ on the
Exterior Algebra $\Lambda^\bullet L$ via the universal property of Clifford algebras.
-/
def abstractSpinorRep (L : Type*) [AddCommGroup L] [Module ℝ L] :
    CliffordAlgebra (Qsplit L) →ₐ[ℝ] Module.End ℝ (SpinorSpace L) :=
  CliffordAlgebra.lift (Qsplit L) ⟨
    { toFun := spinorAction
      map_add' := fun x y => by
        apply LinearMap.ext
        intro w
        dsimp [spinorAction, extAction, intAction]
        have h_int : contractLeft (x.2 + y.2) w = contractLeft x.2 w + contractLeft y.2 w := by
          simp only [map_add, LinearMap.add_apply]
        rw [h_int]
        have h_ext : ι (0 : QuadraticForm ℝ L) (x.1 + y.1) = ι (0 : QuadraticForm ℝ L) x.1 + ι (0 : QuadraticForm ℝ L) y.1 := by
          simp only [map_add]
        rw [h_ext, add_mul]
        abel
      map_smul' := fun c x => by
        apply LinearMap.ext
        intro w
        dsimp [spinorAction, extAction, intAction]
        have h_int : contractLeft (c • x.2) w = c • contractLeft x.2 w := by
          simp only [map_smul, LinearMap.smul_apply]
        rw [h_int]
        have h_ext : ι (0 : QuadraticForm ℝ L) (c • x.1) = c • ι (0 : QuadraticForm ℝ L) x.1 := by
          simp only [map_smul]
        rw [h_ext]
        rw [smul_mul_assoc]
        rw [smul_add] },
    fun v => by
      apply LinearMap.ext
      intro w
      dsimp
      rw [spinorAction_sq]
      rfl
  ⟩

end

end InfoGeometry.Clifford
