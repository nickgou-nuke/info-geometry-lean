import Mathlib.Algebra.Group.Defs
import InfoGeometry.Clifford.HestenesOddSector
import InfoGeometry.Clifford.HestenesParavectorPair
import InfoGeometry.Riemannian.CartanMetric
import InfoGeometry.Clifford.SplitOctonionsDualProduct

namespace InfoGeometry.Quantum

open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian
open SplitOctonion
open CliffordAlgebra

variable {R : Type*} [Field R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- 
Майорановото подпространство (Majorana Subspace).
Това е специфичното подпространство на паравекторите, където елементите са самоадюнгнати 
(γ_i^\dagger = γ_i) и антикомутират помежду си. 
В това подпространство седенионният комутационен дефект се анулира и 
удвояването на Cayley-Dickson запазва мултипликативността на нормата на Хурвиц.
-/
def MajoranaSubspace : Submodule R (ClPlus Q) where
  carrier := { X | hestenesAdjoint Q v0 X = X }
  zero_mem' := by
    dsimp
    apply Subtype.ext
    dsimp [hestenesAdjoint]
    rw [map_zero, mul_zero, zero_mul]
  add_mem' := by
    intro a b ha hb
    dsimp at ha hb ⊢
    apply Subtype.ext
    dsimp [hestenesAdjoint] at ha hb ⊢
    rw [← Subtype.val_inj] at ha hb
    rw [map_add, mul_add, add_mul]
    exact congr_arg₂ _ ha hb
  smul_mem' := by
    intro c x hx
    dsimp at hx ⊢
    apply Subtype.ext
    dsimp [hestenesAdjoint] at hx ⊢
    rw [← Subtype.val_inj] at hx
    simp only [map_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    exact congr_arg _ hx

/-- Майоранов оператор е елемент от Майорановото подпространство. -/
structure MajoranaOperator (Q : QuadraticForm R M) (v0 : M) where
  val : ClPlus Q
  property : val ∈ MajoranaSubspace Q v0

/-- За Майорановите оператори, конюгацията е тривиална (те са самоадюнгнати). -/
theorem Majorana_self_adjoint (γ : MajoranaOperator Q v0) : 
    hestenesAdjoint Q v0 γ.val = γ.val := γ.property

/-- Прожекторите на Китаев върху топологичните сектори: P_plus и P_minus. 
    В бъдеще ще докажем, че те са изотропни елементи (Zero Divisors). -/
def KitaevProjectorPlus (γ1 γ2 : MajoranaOperator Q v0) : ClPlus Q :=
  (1 + γ1.val * γ2.val) 

def KitaevProjectorMinus (γ1 γ2 : MajoranaOperator Q v0) : ClPlus Q :=
  (1 - γ1.val * γ2.val)

theorem hTrace_neg (A : ClPlus Q) : InfoGeometry.Riemannian.hTrace Q (-A) = - InfoGeometry.Riemannian.hTrace Q A := by
  have h : InfoGeometry.Riemannian.hTrace Q (A + -A) = InfoGeometry.Riemannian.hTrace Q A + InfoGeometry.Riemannian.hTrace Q (-A) := InfoGeometry.Riemannian.hTrace_add Q A (-A)
  rw [add_neg_cancel, InfoGeometry.Riemannian.hTrace_zero Q] at h
  have h2 : InfoGeometry.Riemannian.hTrace Q (-A) + InfoGeometry.Riemannian.hTrace Q A = 0 := by rw [add_comm, ← h]
  exact eq_neg_of_add_eq_zero_left h2

/- ФУНДАМЕНТАЛНА ТЕОРЕМА: Скаларната проекция на чист бивектор (grade 2) е 0.
   Изисква цикличност на следата, която не е доказана. Реализирано в ZornMatrix модела. -/
/-
theorem hTrace_bivector (γ1 γ2 : MajoranaOperator Q v0) 
    (h_anti : γ1.val * γ2.val = - (γ2.val * γ1.val)) : 
    InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) = 0 := by
  have h1 : InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) = - InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) := by
    calc InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) 
      _ = InfoGeometry.Riemannian.hTrace Q (-(γ2.val * γ1.val)) := by rw [h_anti]
      _ = - InfoGeometry.Riemannian.hTrace Q (γ2.val * γ1.val) := hTrace_neg Q _
      _ = - InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) := by rw [InfoGeometry.Riemannian.hTrace_mul_comm]
  have h2 : InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) + InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) = 0 := by
    calc InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) + InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) 
      _ = - InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) + InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) := by nth_rw 1 [h1]
      _ = 0 := neg_add_cancel _
  have h3 : (2 : R) * InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val) = 0 := by rw [two_mul, h2]
  have h4 : ⅟(2 : R) * ((2 : R) * InfoGeometry.Riemannian.hTrace Q (γ1.val * γ2.val)) = ⅟(2 : R) * 0 := by rw [h3]
  rw [← mul_assoc, invOf_mul_self, one_mul, mul_zero] at h4
  exact h4
-/

instance : Zero (SplitOctonion Q v0) := ⟨⟨0, 0⟩⟩

/-- Елементът е изотропен (Zero Divisor), ако е ненулев, но нормата му е нула. -/
def IsZeroDivisor (X : SplitOctonion Q v0) : Prop := 
  X ≠ 0 ∧ SplitOctonion.hNorm X = 0

/-- Асиметрично (чисто) влагане на Китаевия прожектор в Сплит-Октониона. -/
def KitaevSplitProjectorPure (γ1 γ2 : MajoranaOperator Q v0) : SplitOctonion Q v0 :=
  ⟨KitaevProjectorPlus Q v0 γ1 γ2, 0⟩

/-- Симетрично влагане на Китаевия прожектор в Сплит-Октониона. 
    Това е физически коректният изотропен Zero Divisor. -/
def KitaevSplitProjectorSymmetric (γ1 γ2 : MajoranaOperator Q v0) : SplitOctonion Q v0 :=
  ⟨KitaevProjectorPlus Q v0 γ1 γ2, KitaevProjectorPlus Q v0 γ1 γ2⟩

/- ФУНДАМЕНТАЛНА ТЕОРЕМА 1: Симетричните Майоранови прожектори са изотропни Zero Divisors.
   Временно коментирано поради липса на конструктивно доказателство за следата. -/
/-
theorem KitaevProjector_is_ZeroDivisor_Symmetric (γ1 γ2 : MajoranaOperator Q v0) 
    (h_anti : γ1.val * γ2.val = - (γ2.val * γ1.val)) :
    IsZeroDivisor Q v0 (KitaevSplitProjectorSymmetric Q v0 γ1 γ2) := by
  constructor
  · -- Доказателство, че X ≠ 0 чрез разпадане по градове (grades)
    dsimp [KitaevSplitProjectorSymmetric]
    intro h_zero
    injection h_zero with h_fst _
    have h_trace := congr_arg (InfoGeometry.Riemannian.hTrace Q) h_fst
    dsimp [KitaevProjectorPlus] at h_trace
    rw [InfoGeometry.Riemannian.hTrace_add, InfoGeometry.Riemannian.hTrace_one, hTrace_bivector Q v0 γ1 γ2 h_anti, InfoGeometry.Riemannian.hTrace_zero] at h_trace
    rw [add_zero] at h_trace
    exact zero_ne_one h_trace.symm
  · dsimp [IsZeroDivisor, SplitOctonion.hNorm, KitaevSplitProjectorSymmetric]
    exact sub_self _
-/


/-- ОПЕРАТОР НА ФЕРМИОННИЯ ПАРИТЕТ (Fermion Parity Operator).
    Този оператор измерва топологичния заряд на кубита. 
    В реалната алгебра на Хестенес, той е еквивалентен на бивектора ℘ = - γ1*γ2 -/
def FermionParityOperator (γ1 γ2 : MajoranaOperator Q v0) : ClPlus Q :=
  - (γ1.val * γ2.val)

/- 
ФУНДАМЕНТАЛНА ТЕОРЕМА 2 (Свещеният Граал): 
Това изисква конструктивно доказателство на цикличността на следата за произволни паравектори.
Временно коментирано, за да се избегнат нечестни аксиоми (dishonest cheat typeclasses).
Истинският конструктивен модел е реализиран в InfoGeometry.Exceptional.SplitOctonionZorn.
-/
/-
theorem Parity_ConeAction_Invariance (γ1 γ2 : MajoranaOperator Q v0) (G : SplitOctonion Q v0) :
    let wp : SplitOctonion Q v0 := SplitOctonion.mk (FermionParityOperator Q v0 γ1 γ2) 0;
    InfoGeometry.Riemannian.hTrace Q (SplitOctonion.star_prod wp G).fst = InfoGeometry.Riemannian.hTrace Q (SplitOctonion.star_prod G wp).fst := by
  intro wp
  rcases G with ⟨g_ref, g_anom⟩
  dsimp [wp, SplitOctonion.star_prod, FermionParityOperator]
  have h0 : InfoGeometry.Clifford.Hestenes.hestenesAdjoint Q v0 0 = 0 := by
    apply Subtype.ext
    dsimp [InfoGeometry.Clifford.Hestenes.hestenesAdjoint]
    rw [map_zero, mul_zero, zero_mul]
  rw [h0, mul_zero, zero_mul, add_zero, add_zero]
  exact InfoGeometry.Riemannian.hTrace_mul_comm Q _ _
-/

end InfoGeometry.Quantum
