import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Cartan.Involution
import InfoGeometry.Canonical.HodgeHelmholtzKreinDecomposition
import InfoGeometry.Canonical.HodgeDiracLaplacianBridge
import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.Krein.InvolutiveSelfDualCarrier

namespace InfoGeometry.Canonical.CliffordDiracAlgebra

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def IsElliptic (A : Module.End ℝ V) : Prop := A * A = -(1 : Module.End ℝ V)
def IsHyperbolic (A : Module.End ℝ V) : Prop := A * A = (1 : Module.End ℝ V)
def IsParabolic (A : Module.End ℝ V) : Prop := A * A = (0 : Module.End ℝ V)
def IsProjector (P : Module.End ℝ V) : Prop := P * P = P

def opCom (A B : Module.End ℝ V) : Module.End ℝ V := A * B - B * A

lemma opCom_swap (A B : Module.End ℝ V) : opCom A B = -opCom B A := by
  ext x
  simp [opCom, sub_eq_add_neg]

structure KANTriple (W : Type*) [AddCommGroup W] [Module ℝ W] where
  K : Module.End ℝ W
  A : Module.End ℝ W
  N : Module.End ℝ W
  k_sq : IsElliptic K
  a_sq : IsHyperbolic A
  n_sq : IsParabolic N
  comm_KA : opCom K A = N
  comm_KN : opCom K N = N
  comm_AN : opCom A N = K

namespace KANTriple

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable (T : KANTriple W)

theorem comm_NK : opCom T.N T.K = -T.N := by
  calc
    opCom T.N T.K = -opCom T.K T.N := opCom_swap (A := T.N) (B := T.K)
    _ = -T.N := by simp [T.comm_KN]

theorem comm_NA : opCom T.N T.A = -T.K := by
  calc
    opCom T.N T.A = -opCom T.A T.N := opCom_swap (A := T.N) (B := T.A)
    _ = -T.K := by simp [T.comm_AN]

end KANTriple

def IsInvolution (J : Module.End ℝ V) : Prop := InfoGeometry.Cartan.IsCartanInvolution J

noncomputable def Pplus (J : Module.End ℝ V) : Module.End ℝ V := InfoGeometry.Cartan.Pplus J

noncomputable def Pminus (J : Module.End ℝ V) : Module.End ℝ V := InfoGeometry.Cartan.Pminus J

def IsOddUnder (J N : Module.End ℝ V) : Prop := J * N = - (N * J)

namespace Projector

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable (J : Module.End ℝ W)

theorem Pplus_idempotent (hJ : IsInvolution J) : IsProjector (Pplus J) := by
  simpa [Pplus, IsProjector, IsInvolution] using
    (InfoGeometry.Cartan.Pplus_idempotent (θ := J) (hθ := hJ))

theorem Pminus_idempotent (hJ : IsInvolution J) : IsProjector (Pminus J) := by
  simpa [Pminus, IsProjector, IsInvolution] using
    (InfoGeometry.Cartan.Pminus_idempotent (θ := J) (hθ := hJ))

theorem Pplus_add_Pminus :
    Pplus J + Pminus J = (1 : Module.End ℝ W) := by
  simpa [Pplus, Pminus] using (InfoGeometry.Cartan.Pplus_add_Pminus_eq_id (θ := J))

theorem Pplus_comp_Pminus (hJ : IsInvolution J) : Pplus J * Pminus J = (0 : Module.End ℝ W) := by
  simpa [Pplus, Pminus] using
    (InfoGeometry.Cartan.Pplus_comp_Pminus (θ := J) (hθ := hJ))

end Projector

namespace OddUnder

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem plus_to_minus
    (J N : Module.End ℝ W) (hOdd : IsOddUnder J N) :
    Pplus J * N = N * Pminus J := by
  ext x
  have hOddX : J (N x) = - (N (J x)) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : Module.End ℝ W => f x) hOdd
  simp [Pplus, Pminus, InfoGeometry.Cartan.Pplus_apply, InfoGeometry.Cartan.Pminus_apply,
    hOddX, sub_eq_add_neg, smul_add]

theorem minus_to_plus
    (J N : Module.End ℝ W) (hOdd : IsOddUnder J N) :
  Pminus J * N = N * Pplus J := by
  ext x
  have hOddX : J (N x) = - (N (J x)) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : Module.End ℝ W => f x) hOdd
  simp [Pplus, Pminus, InfoGeometry.Cartan.Pplus_apply, InfoGeometry.Cartan.Pminus_apply,
    hOddX, sub_eq_add_neg, smul_add]

end OddUnder

namespace HodgeDirac

open HodgeHelmholtzKreinDecomposition

variable {R : Type*} [Ring R] {W : Type*} [AddCommGroup W] [Module R W]

def Dirac (H : HodgePacket (R := R) (V := W)) : Module.End R W := H.d + H.δ

theorem dirac_sq_eq_delta (H : HodgePacket (R := R) (V := W)) :
    Dirac H * Dirac H = H.Δ := by
  simp [Dirac, H.Δ_def]
  ext x
  have hd2 : H.d (H.d x) = 0 := by
    simpa using congrArg (fun f : Module.End R W => f x) H.d_sq
  have hdδ2 : H.δ (H.δ x) = 0 := by
    simpa using congrArg (fun f : Module.End R W => f x) H.δ_sq
  simp [LinearMap.add_apply, LinearMap.comp_apply, hd2, hdδ2, add_mul, mul_add,
    add_assoc, add_left_comm, add_comm]

end HodgeDirac

/--
Basic neg-projector (`A^2 = -A`) and real off-diagonal complexifier lemmas.
-/

def IsNegProjector (A : Module.End ℝ V) : Prop := A * A = -A

lemma neg_projector_iff_isProjector_neg (A : Module.End ℝ V) :
    IsNegProjector A ↔ IsProjector (-A) := by
  constructor
  · intro h
    dsimp [IsProjector, IsNegProjector] at h ⊢
    simpa [neg_mul, mul_neg] using h
  · intro h
    dsimp [IsProjector, IsNegProjector] at h ⊢
    simpa [neg_mul, mul_neg] using h

/-- Off-diagonal real “complexifier” on `V × V`: 
	x ↦ (-y, x)
so 
	satisfies `J^2 = -1`. -/
def RealComplexifier (V : Type*) [AddCommGroup V] [Module ℝ V] : Module.End ℝ (V × V) :=
{ toFun := fun p => (-p.2, p.1)
  map_add' := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    ext <;> simp [add_comm]
  map_smul' := by
    intro c ⟨x1, x2⟩
    ext <;> simp }

lemma realComplexifier_sq_eq_neg_one (V : Type*) [AddCommGroup V] [Module ℝ V] :
    RealComplexifier V * RealComplexifier V = -(1 : Module.End ℝ (V × V)) := by
  ext p <;>
    simp [RealComplexifier, Module.End.mul_eq_comp, LinearMap.comp_apply, Module.End.one_apply]

-- Carrier- and Krein-level bridge lemmas for immediate reuse by existing lanes.
namespace CarrierBridge

open InfoGeometry.Carrier
open InfoGeometry.Krein

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

-- `HestenesKreinSpace` fundamental symmetry is a Cartan involution.
theorem hestenesJ_isInvolution [HestenesKreinSpace V] :
    IsInvolution (HestenesKreinSpace.J : Module.End ℝ V) := by
  dsimp [IsInvolution, InfoGeometry.Cartan.IsCartanInvolution]
  simpa [Module.End.mul_eq_comp] using (HestenesKreinSpace.J_involution (V := V))

-- `ε` in an involutive self-dual carrier is a Cartan involution.
-- (using only its defining involutivity axiom).
theorem involutiveSelfDualCarrier_ε_isInvolution (X : InvolutiveSelfDualCarrier) :
    IsInvolution (X.ε.toLinearMap) := by
  dsimp [IsInvolution, InfoGeometry.Cartan.IsCartanInvolution]
  ext x
  simpa [Module.End.mul_eq_comp, LinearMap.comp_apply] using
    (congrArg (fun f : X.H →L[ℝ] X.H => f x) X.ε_sq)

-- Odd generators have even square with respect to the chosen Hodge/phase axis.
theorem odd_square_commutes_hodge {W : Type*} [AddCommGroup W] [Module ℝ W]
    (J N : Module.End ℝ W) (hOdd : IsOddUnder J N) :
    (N * N) * J = J * (N * N) := by
  have hAnti : N * J = -(J * N) := by
    have hOddNeg : -(J * N) = N * J := by
      simpa using congrArg Neg.neg hOdd
    simpa [neg_neg] using hOddNeg.symm
  exact HodgeDiracLaplacianBridge.dirac_sq_commutes_hodge J N hAnti

end CarrierBridge

end InfoGeometry.Canonical.CliffordDiracAlgebra
