import InfoGeometry.Canonical.RealBdG
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# InfoGeometry.Quantum.RealMajorana

Real Majorana/BdG transport scaffold.

This module keeps the primitive quantum layer fully real:
- CAR is encoded on real mode space operators;
- the internal square-minus-one operator is `K := J ∘ ε`;
- Bogoliubov transport is real conjugation by an automorphism.
-/

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace InfoGeometry.Quantum.RealMajorana

open CategoryTheory

section Core

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

/-- Endomorphisms on the real Majorana mode space. -/
abbrev EndS := S →L[ℝ] S

/-- Odd-odd channel used for CAR statements. -/
noncomputable def anticommutator (A B : EndS (S := S)) : EndS (S := S) :=
  A.comp B + B.comp A

/--
Constructive CAR witness for a real Majorana field `γ` with pairing `g`.
-/
def MajoranaCARWitness (g : S → S → ℝ) (γ : S → EndS (S := S)) : Prop :=
  ∀ u v : S,
    anticommutator (γ u) (γ v)
      = (2 * g u v) • ContinuousLinearMap.id ℝ S

/--
Primitive real Majorana datum:
CAR representation and real involutive operator package `(J, ε, Π)`.
-/
structure RealMajoranaDatum where
  gamma : S → EndS (S := S)
  J : EndS (S := S)
  eps : EndS (S := S)
  Pi : EndS (S := S)

  J_sq : J.comp J = ContinuousLinearMap.id ℝ S
  eps_sq : eps.comp eps = ContinuousLinearMap.id ℝ S
  Jeps_anticomm : J.comp eps = -(eps.comp J)
  Pi_sq : Pi.comp Pi = ContinuousLinearMap.id ℝ S

  car :
    ∀ u v : S,
      anticommutator (gamma u) (gamma v)
        = (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S

namespace RealMajoranaDatum

variable (M : RealMajoranaDatum (S := S))

/-- Canonical real pairing used in the Majorana CAR channel. -/
def pairing (u v : S) : ℝ := inner ℝ u v

/--
Primitive constructive CAR theorem: the split-Clifford Majorana field already
realizes CAR in the real channel.
-/
theorem car_realization_of_clifford :
    MajoranaCARWitness (S := S) (pairing (S := S)) M.gamma := by
  intro u v
  simpa [pairing] using M.car u v

/-- Internal square-minus-one operator `K := J ∘ ε`. -/
noncomputable def K : EndS (S := S) :=
  M.J.comp M.eps

/-- `K² = -Id`. -/
theorem K_sq :
    M.K.comp M.K = -(ContinuousLinearMap.id ℝ S) := by
  have hswap : M.eps.comp M.J = -(M.J.comp M.eps) := by
    have hneg : -(M.J.comp M.eps) = M.eps.comp M.J := by
      simpa using congrArg Neg.neg M.Jeps_anticomm
    simpa [eq_comm] using hneg
  unfold K
  calc
    (M.J.comp M.eps).comp (M.J.comp M.eps)
        = M.J.comp ((M.eps.comp M.J).comp M.eps) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = M.J.comp ((-(M.J.comp M.eps)).comp M.eps) := by rw [hswap]
    _ = -((M.J.comp M.J).comp (M.eps.comp M.eps)) := by
          ext x
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(ContinuousLinearMap.id ℝ S) := by
          simp [M.J_sq, M.eps_sq]

/-- Real operators commuting with the internal `K` axis. -/
def KLinear (A : EndS (S := S)) : Prop :=
  A.comp M.K = M.K.comp A

/-- Real operators anticommuting with the internal `K` axis. -/
def KAntilinear (A : EndS (S := S)) : Prop :=
  A.comp M.K = -(M.K.comp A)

/-- `Π`-even endomorphisms commute with parity involution `Π`. -/
def PiEven (A : EndS (S := S)) : Prop :=
  A.comp M.Pi = M.Pi.comp A

/-- `Π`-odd endomorphisms anticommute with parity involution `Π`. -/
def PiOdd (A : EndS (S := S)) : Prop :=
  A.comp M.Pi = -(M.Pi.comp A)

/-- Real Weyl-plus sector, derived from chirality involution `J`. -/
def weylPlus : Submodule ℝ S :=
  (M.J.toLinearMap - LinearMap.id).ker

/-- Real Weyl-minus sector, derived from chirality involution `J`. -/
def weylMinus : Submodule ℝ S :=
  (M.J.toLinearMap + LinearMap.id).ker

lemma mem_weylPlus_iff (x : S) :
    x ∈ M.weylPlus ↔ M.J x = x := by
  constructor
  · intro hx
    change ((M.J.toLinearMap - LinearMap.id : S →ₗ[ℝ] S) x = 0) at hx
    simpa [LinearMap.sub_apply, sub_eq_zero] using hx
  · intro hx
    change ((M.J.toLinearMap - LinearMap.id : S →ₗ[ℝ] S) x = 0)
    simpa [LinearMap.sub_apply, hx]

lemma mem_weylMinus_iff (x : S) :
    x ∈ M.weylMinus ↔ M.J x = -x := by
  constructor
  · intro hx
    change ((M.J.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0) at hx
    simpa [LinearMap.add_apply, eq_neg_iff_add_eq_zero] using hx
  · intro hx
    change ((M.J.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0)
    simpa [LinearMap.add_apply, hx]

/--
Distinction theorem: `K` is not parity `Π` on nontrivial real Majorana space.
-/
theorem K_ne_Pi [Nontrivial S] : M.K ≠ M.Pi := by
  intro hEq
  have hIdNeg : (ContinuousLinearMap.id ℝ S) = -(ContinuousLinearMap.id ℝ S) := by
    calc
      ContinuousLinearMap.id ℝ S = M.Pi.comp M.Pi := by
        simpa using M.Pi_sq.symm
      _ = M.K.comp M.K := by
        simpa [hEq]
      _ = -(ContinuousLinearMap.id ℝ S) := by
        simpa using M.K_sq
  rcases exists_ne (0 : S) with ⟨x, hx⟩
  have hxNeg : x = -x := by
    exact congrArg (fun f : EndS (S := S) => f x) hIdNeg
  have hsum : x + x = 0 := by
    have hxx : x + x = x + (-x) := by
      nth_rewrite 2 [hxNeg]
      rfl
    calc
      x + x = x + (-x) := hxx
      _ = 0 := by simp
  have hxTwo : (2 : ℝ) • x = 0 := by
    simpa [two_smul] using hsum
  have hxZero : x = 0 := by
    exact (smul_eq_zero.mp hxTwo).resolve_left (by norm_num)
  exact hx hxZero

end RealMajoranaDatum

/--
`K`-compatible polarization datum on a real Majorana system.

`P` is an involution defining a `(plus/minus)` split; anti-commutation with `K`
encodes that `K` swaps the two polarized sectors.
-/
structure KPolarization (M : RealMajoranaDatum (S := S)) where
  P : EndS (S := S)
  P_sq : P.comp P = ContinuousLinearMap.id ℝ S
  P_K_anticomm : P.comp M.K = -(M.K.comp P)

namespace KPolarization

variable {M : RealMajoranaDatum (S := S)}
variable (P0 : KPolarization (S := S) M)

/-- `+` polarization subspace of `P`. -/
def plus : Submodule ℝ S :=
  (P0.P.toLinearMap - LinearMap.id).ker

/-- `-` polarization subspace of `P`. -/
def minus : Submodule ℝ S :=
  (P0.P.toLinearMap + LinearMap.id).ker

lemma mem_plus_iff (x : S) :
    x ∈ P0.plus ↔ P0.P x = x := by
  constructor
  · intro hx
    change ((P0.P.toLinearMap - LinearMap.id : S →ₗ[ℝ] S) x = 0) at hx
    simpa [LinearMap.sub_apply, sub_eq_zero] using hx
  · intro hx
    change ((P0.P.toLinearMap - LinearMap.id : S →ₗ[ℝ] S) x = 0)
    simpa [LinearMap.sub_apply, hx]

lemma mem_minus_iff (x : S) :
    x ∈ P0.minus ↔ P0.P x = -x := by
  constructor
  · intro hx
    change ((P0.P.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0) at hx
    simpa [LinearMap.add_apply, eq_neg_iff_add_eq_zero] using hx
  · intro hx
    change ((P0.P.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0)
    simpa [LinearMap.add_apply, hx]

/-- `K` maps the `+` polarization sector into the `-` sector. -/
lemma K_maps_plus_to_minus (x : S) (hx : x ∈ P0.plus) :
    M.K x ∈ P0.minus := by
  rw [mem_plus_iff] at hx
  rw [mem_minus_iff]
  have hanti := congrArg (fun f : EndS (S := S) => f x) P0.P_K_anticomm
  calc
    P0.P (M.K x) = -(M.K (P0.P x)) := by simpa [ContinuousLinearMap.comp_apply] using hanti
    _ = -(M.K x) := by simpa [hx]

/-- `K` maps the `-` polarization sector into the `+` sector. -/
lemma K_maps_minus_to_plus (x : S) (hx : x ∈ P0.minus) :
    M.K x ∈ P0.plus := by
  rw [mem_minus_iff] at hx
  rw [mem_plus_iff]
  have hanti := congrArg (fun f : EndS (S := S) => f x) P0.P_K_anticomm
  calc
    P0.P (M.K x) = -(M.K (P0.P x)) := by simpa [ContinuousLinearMap.comp_apply] using hanti
    _ = -((M.K (-x))) := by simpa [hx]
    _ = M.K x := by simp

end KPolarization

/--
Real Bogoliubov transform on Majorana mode space.
-/
structure RealBogoliubovTransform (M : RealMajoranaDatum (S := S)) where
  B : EndS (S := S)
  Binv : EndS (S := S)
  left_inv : Binv.comp B = ContinuousLinearMap.id ℝ S
  right_inv : B.comp Binv = ContinuousLinearMap.id ℝ S
  preserves_inner : ∀ u v : S, inner ℝ (B u) (B v) = inner ℝ u v
  parity_even : M.Pi.comp B = B.comp M.Pi

namespace RealBogoliubovTransform

variable {M : RealMajoranaDatum (S := S)}
variable (T : RealBogoliubovTransform (S := S) M)

@[simp] lemma Binv_apply_B (x : S) : T.Binv (T.B x) = x := by
  have h := congrArg (fun f : EndS (S := S) => f x) T.left_inv
  simpa using h

@[simp] lemma B_apply_Binv (x : S) : T.B (T.Binv x) = x := by
  have h := congrArg (fun f : EndS (S := S) => f x) T.right_inv
  simpa using h

/-- Transported `J` by real Bogoliubov conjugation. -/
noncomputable def transportJ : EndS (S := S) :=
  T.B.comp (M.J.comp T.Binv)

/-- Transported `ε` by real Bogoliubov conjugation. -/
noncomputable def transportEps : EndS (S := S) :=
  T.B.comp (M.eps.comp T.Binv)

/-- Transported `K` by real Bogoliubov conjugation. -/
noncomputable def transportK : EndS (S := S) :=
  T.B.comp (M.K.comp T.Binv)

/-- Transported parity involution `Π` by real Bogoliubov conjugation. -/
noncomputable def transportPi : EndS (S := S) :=
  T.B.comp (M.Pi.comp T.Binv)

/--
Transported Majorana field by mode-space pushforward.

Here transport acts on the mode argument: `transportGamma v = gamma (B v)`.
This is distinct from conjugation transport on target endomorphisms.
-/
noncomputable def transportGamma (v : S) : EndS (S := S) :=
  M.gamma (T.B v)

/-- Real Weyl-plus sector for transported chirality `J_B`. -/
noncomputable def transportWeylPlus : Submodule ℝ S :=
  ((T.transportJ).toLinearMap - LinearMap.id).ker

/-- Real Weyl-minus sector for transported chirality `J_B`. -/
noncomputable def transportWeylMinus : Submodule ℝ S :=
  ((T.transportJ).toLinearMap + LinearMap.id).ker

lemma mem_transportWeylPlus_iff (x : S) :
    x ∈ T.transportWeylPlus ↔ T.transportJ x = x := by
  constructor
  · intro hx
    change ((T.transportJ.toLinearMap - LinearMap.id : S →ₗ[ℝ] S) x = 0) at hx
    simpa [LinearMap.sub_apply, sub_eq_zero] using hx
  · intro hx
    change ((T.transportJ.toLinearMap - LinearMap.id : S →ₗ[ℝ] S) x = 0)
    simpa [LinearMap.sub_apply, hx]

lemma mem_transportWeylMinus_iff (x : S) :
    x ∈ T.transportWeylMinus ↔ T.transportJ x = -x := by
  constructor
  · intro hx
    change ((T.transportJ.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0) at hx
    simpa [LinearMap.add_apply, eq_neg_iff_add_eq_zero] using hx
  · intro hx
    change ((T.transportJ.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0)
    simpa [LinearMap.add_apply, hx]

lemma transportJ_apply_B (x : S) :
    T.transportJ (T.B x) = T.B (M.J x) := by
  simp [transportJ, ContinuousLinearMap.comp_assoc]

lemma Binv_apply_transportJ (y : S) :
    T.Binv (T.transportJ y) = M.J (T.Binv y) := by
  simp [transportJ, ContinuousLinearMap.comp_assoc]

/-- `B` transports the original Weyl-plus sector into transported Weyl-plus. -/
lemma map_weylPlus (x : S) (hx : x ∈ M.weylPlus) :
    T.B x ∈ T.transportWeylPlus := by
  rw [M.mem_weylPlus_iff] at hx
  rw [mem_transportWeylPlus_iff]
  simpa [hx] using T.transportJ_apply_B x

/-- `B⁻¹` transports transported Weyl-plus back to original Weyl-plus. -/
lemma preimage_weylPlus (y : S) (hy : y ∈ T.transportWeylPlus) :
    T.Binv y ∈ M.weylPlus := by
  rw [mem_transportWeylPlus_iff] at hy
  rw [M.mem_weylPlus_iff]
  have h := congrArg T.Binv hy
  simpa [Binv_apply_transportJ] using h

/-- `B` transports the original Weyl-minus sector into transported Weyl-minus. -/
lemma map_weylMinus (x : S) (hx : x ∈ M.weylMinus) :
    T.B x ∈ T.transportWeylMinus := by
  rw [M.mem_weylMinus_iff] at hx
  rw [mem_transportWeylMinus_iff]
  simpa [hx] using T.transportJ_apply_B x

/-- `B⁻¹` transports transported Weyl-minus back to original Weyl-minus. -/
lemma preimage_weylMinus (y : S) (hy : y ∈ T.transportWeylMinus) :
    T.Binv y ∈ M.weylMinus := by
  rw [mem_transportWeylMinus_iff] at hy
  rw [M.mem_weylMinus_iff]
  have h := congrArg T.Binv hy
  simpa [Binv_apply_transportJ] using h

/-- Explicit linear equivalence between original and transported Weyl-plus sectors. -/
noncomputable def weylPlusEquiv :
    M.weylPlus ≃ₗ[ℝ] T.transportWeylPlus where
  toFun x := ⟨T.B x, T.map_weylPlus x x.property⟩
  invFun y := ⟨T.Binv y, T.preimage_weylPlus y y.property⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' r x := by
    ext
    simp

/-- Explicit linear equivalence between original and transported Weyl-minus sectors. -/
noncomputable def weylMinusEquiv :
    M.weylMinus ≃ₗ[ℝ] T.transportWeylMinus where
  toFun x := ⟨T.B x, T.map_weylMinus x x.property⟩
  invFun y := ⟨T.Binv y, T.preimage_weylMinus y y.property⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' r x := by
    ext
    simp

/--
Image characterization: transported Weyl-plus is exactly the `B`-image of the
original Weyl-plus sector.
-/
theorem map_weylPlus_eq_transportWeylPlus :
    Submodule.map T.B.toLinearMap M.weylPlus = T.transportWeylPlus := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact T.map_weylPlus x hx
  · intro hy
    refine ⟨T.Binv y, T.preimage_weylPlus y hy, ?_⟩
    simpa using (T.B_apply_Binv y)

/--
Image characterization: transported Weyl-minus is exactly the `B`-image of the
original Weyl-minus sector.
-/
theorem map_weylMinus_eq_transportWeylMinus :
    Submodule.map T.B.toLinearMap M.weylMinus = T.transportWeylMinus := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact T.map_weylMinus x hx
  · intro hy
    refine ⟨T.Binv y, T.preimage_weylMinus y hy, ?_⟩
    simpa using (T.B_apply_Binv y)

/-- Transport compatibility: `K_B = J_B ε_B`. -/
theorem transportK_def :
    T.transportK = (T.transportJ).comp (T.transportEps) := by
  ext x
  simp [transportK, transportJ, transportEps, RealMajoranaDatum.K,
    ContinuousLinearMap.comp_assoc]

/-- Transport preserves the square-minus-one law of `K`. -/
theorem transportK_sq :
    T.transportK.comp T.transportK = -(ContinuousLinearMap.id ℝ S) := by
  calc
    T.transportK.comp T.transportK
        = T.B.comp (M.K.comp ((T.Binv.comp T.B).comp (M.K.comp T.Binv))) := by
            simp [transportK, ContinuousLinearMap.comp_assoc]
    _ = T.B.comp (M.K.comp ((ContinuousLinearMap.id ℝ S).comp (M.K.comp T.Binv))) := by
          rw [T.left_inv]
    _ = T.B.comp ((M.K.comp M.K).comp T.Binv) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = T.B.comp ((-(ContinuousLinearMap.id ℝ S)).comp T.Binv) := by
          rw [M.K_sq]
    _ = -(T.B.comp T.Binv) := by
          ext x
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(ContinuousLinearMap.id ℝ S) := by
          simpa [T.right_inv]

/-- Transport preserves parity involution law. -/
theorem transportPi_sq :
    T.transportPi.comp T.transportPi = ContinuousLinearMap.id ℝ S := by
  calc
    T.transportPi.comp T.transportPi
        = T.B.comp (M.Pi.comp ((T.Binv.comp T.B).comp (M.Pi.comp T.Binv))) := by
            simp [transportPi, ContinuousLinearMap.comp_assoc]
    _ = T.B.comp (M.Pi.comp ((ContinuousLinearMap.id ℝ S).comp (M.Pi.comp T.Binv))) := by
          rw [T.left_inv]
    _ = T.B.comp ((M.Pi.comp M.Pi).comp T.Binv) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = T.B.comp ((ContinuousLinearMap.id ℝ S).comp T.Binv) := by
          rw [M.Pi_sq]
    _ = ContinuousLinearMap.id ℝ S := by
          simpa [ContinuousLinearMap.comp_assoc, T.right_inv]

/-- CAR covariance under real Bogoliubov transport. -/
theorem transportGamma_car (u v : S) :
    anticommutator (transportGamma (T := T) u) (transportGamma (T := T) v)
      = (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S := by
  calc
    anticommutator (transportGamma (T := T) u) (transportGamma (T := T) v)
        = (2 * inner ℝ (T.B u) (T.B v)) • ContinuousLinearMap.id ℝ S := by
            simpa [transportGamma] using M.car (T.B u) (T.B v)
    _ = (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S := by
          rw [T.preserves_inner u v]

/--
Constructive CAR theorem after real Bogoliubov transport: CAR is preserved
because transport acts by an isometric real automorphism on the Majorana mode
space.
-/
theorem car_realization_of_clifford :
    MajoranaCARWitness (S := S) (fun u v => inner ℝ u v) (transportGamma (T := T)) := by
  intro u v
  exact T.transportGamma_car u v

/-- Transport a polarization involution by Bogoliubov conjugation. -/
noncomputable def transportP (P0 : KPolarization (S := S) M) : EndS (S := S) :=
  T.B.comp (P0.P.comp T.Binv)

/--
`T` preserves polarization iff it commutes with the polarization involution.
-/
def preservesPolarization (P0 : KPolarization (S := S) M) : Prop :=
  P0.P.comp T.B = T.B.comp P0.P

/-- `mixesPolarization` is the negation of preservation. -/
def mixesPolarization (P0 : KPolarization (S := S) M) : Prop :=
  ¬T.preservesPolarization P0

theorem preservesPolarization_iff_transportP_eq
    (P0 : KPolarization (S := S) M) :
    T.preservesPolarization P0 ↔ T.transportP P0 = P0.P := by
  constructor
  · intro hcomm
    unfold transportP
    calc
      T.B.comp (P0.P.comp T.Binv)
          = (T.B.comp P0.P).comp T.Binv := by simp [ContinuousLinearMap.comp_assoc]
      _ = (P0.P.comp T.B).comp T.Binv := by rw [hcomm.symm]
      _ = P0.P.comp (T.B.comp T.Binv) := by simp [ContinuousLinearMap.comp_assoc]
      _ = P0.P := by simp [T.right_inv]
  · intro htrans
    have hcomp := congrArg (fun F : EndS (S := S) => F.comp T.B) htrans
    have h' : T.B.comp P0.P = P0.P.comp T.B := by
      simpa [transportP, ContinuousLinearMap.comp_assoc, T.left_inv] using hcomp
    exact h'.symm

theorem preserves_or_mixes (P0 : KPolarization (S := S) M) :
    T.preservesPolarization P0 ∨ T.mixesPolarization P0 := by
  by_cases h : T.preservesPolarization P0
  · exact Or.inl h
  · exact Or.inr h

/-- If polarization is preserved, `B` maps `plus` into `plus`. -/
lemma map_plus_of_preserves
    (P0 : KPolarization (S := S) M)
    (hpres : T.preservesPolarization P0)
    (x : S) (hx : x ∈ P0.plus) :
    T.B x ∈ P0.plus := by
  rw [KPolarization.mem_plus_iff] at hx ⊢
  have hcomm := congrArg (fun f : EndS (S := S) => f x) hpres
  calc
    P0.P (T.B x) = T.B (P0.P x) := by simpa [ContinuousLinearMap.comp_apply] using hcomm
    _ = T.B x := by simpa [hx]

/-- If polarization is preserved, `B` maps `minus` into `minus`. -/
lemma map_minus_of_preserves
    (P0 : KPolarization (S := S) M)
    (hpres : T.preservesPolarization P0)
    (x : S) (hx : x ∈ P0.minus) :
    T.B x ∈ P0.minus := by
  rw [KPolarization.mem_minus_iff] at hx ⊢
  have hcomm := congrArg (fun f : EndS (S := S) => f x) hpres
  calc
    P0.P (T.B x) = T.B (P0.P x) := by simpa [ContinuousLinearMap.comp_apply] using hcomm
    _ = T.B (-x) := by simpa [hx]
    _ = -(T.B x) := by simp

end RealBogoliubovTransform

namespace KPolarization

variable {M : RealMajoranaDatum (S := S)}

/-- Morphisms between polarization choices on a fixed real Majorana datum. -/
@[ext] structure Hom (P Q : KPolarization (S := S) M) where
  f : EndS (S := S)
  finv : EndS (S := S)
  left_inv : finv.comp f = ContinuousLinearMap.id ℝ S
  right_inv : f.comp finv = ContinuousLinearMap.id ℝ S
  intertwines : Q.P.comp f = f.comp P.P

noncomputable instance : Category (KPolarization (S := S) M) where
  Hom P Q := Hom P Q
  id P :=
    { f := ContinuousLinearMap.id ℝ S
      finv := ContinuousLinearMap.id ℝ S
      left_inv := by simp
      right_inv := by simp
      intertwines := by simp }
  comp {P Q R} g h :=
    { f := h.f.comp g.f
      finv := g.finv.comp h.finv
      left_inv := by
        ext x
        have hh : h.finv (h.f (g.f x)) = g.f x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F (g.f x)) h.left_inv
        have hg : g.finv (g.f x) = x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F x) g.left_inv
        simpa [ContinuousLinearMap.comp_apply, hh] using hg
      right_inv := by
        ext x
        have hg : g.f (g.finv (h.finv x)) = h.finv x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F (h.finv x)) g.right_inv
        have hh : h.f (h.finv x) = x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F x) h.right_inv
        simpa [ContinuousLinearMap.comp_apply, hg] using hh
      intertwines := by
        calc
          R.P.comp (h.f.comp g.f)
              = (R.P.comp h.f).comp g.f := by simp [ContinuousLinearMap.comp_assoc]
          _ = (h.f.comp Q.P).comp g.f := by rw [h.intertwines]
          _ = h.f.comp (Q.P.comp g.f) := by simp [ContinuousLinearMap.comp_assoc]
          _ = h.f.comp (g.f.comp P.P) := by rw [g.intertwines]
          _ = (h.f.comp g.f).comp P.P := by simp [ContinuousLinearMap.comp_assoc] }

@[simp] lemma hom_id (P : KPolarization (S := S) M) :
    ((𝟙 P : P ⟶ P).f) = ContinuousLinearMap.id ℝ S := rfl

@[simp] lemma hom_comp {P Q R : KPolarization (S := S) M} (f : P ⟶ Q) (g : Q ⟶ R) :
    ((f ≫ g).f) = g.f.comp f.f := rfl

/--
Derived projector split from a polarization involution.

This is **not** primitive CAR ladder data; it is the `(plus/minus)` projector splitting
associated to `P^2 = Id`.
-/
structure PolarizationSplit where
  Pminus : EndS (S := S)
  Pplus : EndS (S := S)
  minus_idem : Pminus.comp Pminus = Pminus
  plus_idem : Pplus.comp Pplus = Pplus
  cross_minus_plus : Pminus.comp Pplus = 0
  cross_plus_minus : Pplus.comp Pminus = 0
  split_sum : Pminus + Pplus = ContinuousLinearMap.id ℝ S

namespace PolarizationSplit

/-- Morphisms in the derived polarization-split category. -/
@[ext] structure Hom (A B : PolarizationSplit (S := S)) where
  f : EndS (S := S)
  finv : EndS (S := S)
  left_inv : finv.comp f = ContinuousLinearMap.id ℝ S
  right_inv : f.comp finv = ContinuousLinearMap.id ℝ S
  intertwines_minus : B.Pminus.comp f = f.comp A.Pminus
  intertwines_plus : B.Pplus.comp f = f.comp A.Pplus

noncomputable instance : Category (PolarizationSplit (S := S)) where
  Hom A B := Hom A B
  id A :=
    { f := ContinuousLinearMap.id ℝ S
      finv := ContinuousLinearMap.id ℝ S
      left_inv := by simp
      right_inv := by simp
      intertwines_minus := by simp
      intertwines_plus := by simp }
  comp {A B C} g h :=
    { f := h.f.comp g.f
      finv := g.finv.comp h.finv
      left_inv := by
        ext x
        have hh : h.finv (h.f (g.f x)) = g.f x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F (g.f x)) h.left_inv
        have hg : g.finv (g.f x) = x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F x) g.left_inv
        simpa [ContinuousLinearMap.comp_apply, hh] using hg
      right_inv := by
        ext x
        have hg : g.f (g.finv (h.finv x)) = h.finv x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F (h.finv x)) g.right_inv
        have hh : h.f (h.finv x) = x := by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun F : EndS (S := S) => F x) h.right_inv
        simpa [ContinuousLinearMap.comp_apply, hg] using hh
      intertwines_minus := by
        calc
          C.Pminus.comp (h.f.comp g.f)
              = (C.Pminus.comp h.f).comp g.f := by simp [ContinuousLinearMap.comp_assoc]
          _ = (h.f.comp B.Pminus).comp g.f := by rw [h.intertwines_minus]
          _ = h.f.comp (B.Pminus.comp g.f) := by simp [ContinuousLinearMap.comp_assoc]
          _ = h.f.comp (g.f.comp A.Pminus) := by rw [g.intertwines_minus]
          _ = (h.f.comp g.f).comp A.Pminus := by simp [ContinuousLinearMap.comp_assoc]
      intertwines_plus := by
        calc
          C.Pplus.comp (h.f.comp g.f)
              = (C.Pplus.comp h.f).comp g.f := by simp [ContinuousLinearMap.comp_assoc]
          _ = (h.f.comp B.Pplus).comp g.f := by rw [h.intertwines_plus]
          _ = h.f.comp (B.Pplus.comp g.f) := by simp [ContinuousLinearMap.comp_assoc]
          _ = h.f.comp (g.f.comp A.Pplus) := by rw [g.intertwines_plus]
          _ = (h.f.comp g.f).comp A.Pplus := by simp [ContinuousLinearMap.comp_assoc] }

@[simp] lemma hom_id (A : PolarizationSplit (S := S)) :
    ((𝟙 A : A ⟶ A).f) = ContinuousLinearMap.id ℝ S := rfl

@[simp] lemma hom_comp {A B C : PolarizationSplit (S := S)} (f : A ⟶ B) (g : B ⟶ C) :
    ((f ≫ g).f) = g.f.comp f.f := rfl

end PolarizationSplit

private lemma half_smul_add_half_smul (y : S) :
  (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y) = (1 / 2 : ℝ) • y := by
  calc
  (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y)
    = (1 / 2 : ℝ) • (((1 / 2 : ℝ) + (1 / 2 : ℝ)) • y) := by
      simp [add_smul]
  _ = (1 / 2 : ℝ) • y := by norm_num

/-- Canonical derived projector split from a polarization involution `P`. -/
noncomputable def splitOfPolarization (P : KPolarization (S := S) M) :
    PolarizationSplit (S := S) where
  Pminus := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S - P.P)
  Pplus := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S + P.P)
  minus_idem := by
    ext x
    have hPP : P.P (P.P x) = x := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun F : EndS (S := S) => F x) P.P_sq
    calc
      (((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S - P.P)).comp
          ((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S - P.P))) x
          = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (x - P.P x) + (1 / 2 : ℝ) • (x - P.P x)) := by
              simp [ContinuousLinearMap.comp_apply, hPP, sub_eq_add_neg,
                smul_add, smul_sub, add_assoc, add_left_comm, add_comm]
      _ = (1 / 2 : ℝ) • (x - P.P x) := by
            simpa using half_smul_add_half_smul (S := S) (y := x - P.P x)
      _ = ((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S - P.P)) x := by
            simp [sub_eq_add_neg, smul_sub]
  plus_idem := by
    ext x
    have hPP : P.P (P.P x) = x := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun F : EndS (S := S) => F x) P.P_sq
    calc
      (((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S + P.P)).comp
          ((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S + P.P))) x
          = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (x + P.P x) + (1 / 2 : ℝ) • (x + P.P x)) := by
              simp [ContinuousLinearMap.comp_apply, hPP, smul_add,
                add_assoc, add_left_comm, add_comm]
      _ = (1 / 2 : ℝ) • (x + P.P x) := by
            simpa using half_smul_add_half_smul (S := S) (y := x + P.P x)
      _ = ((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ S + P.P)) x := by
            simp
  cross_minus_plus := by
    ext x
    have hPP : P.P (P.P x) = x := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun F : EndS (S := S) => F x) P.P_sq
    simp [sub_eq_add_neg, hPP, smul_add, smul_sub,
      add_assoc, add_left_comm, add_comm]
  cross_plus_minus := by
    ext x
    have hPP : P.P (P.P x) = x := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun F : EndS (S := S) => F x) P.P_sq
    simp [sub_eq_add_neg, hPP, smul_add, smul_sub,
      add_assoc, add_left_comm, add_comm]
  split_sum := by
    have hhalf (x : S) : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by
      calc
        (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x
            = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by simp [add_smul]
        _ = x := by norm_num
    ext x
    simpa [sub_eq_add_neg, smul_add, smul_sub, add_assoc, add_left_comm, add_comm]
      using hhalf x

/-- The polarization involution is recovered as `Pplus - Pminus`. -/
lemma plus_sub_minus_eq_P (P : KPolarization (S := S) M) :
    (splitOfPolarization (M := M) P).Pplus
      - (splitOfPolarization (M := M) P).Pminus = P.P := by
  have hhalf (x : S) : (1 / 2 : ℝ) • (P.P x) + (1 / 2 : ℝ) • (P.P x) = P.P x := by
    calc
      (1 / 2 : ℝ) • (P.P x) + (1 / 2 : ℝ) • (P.P x)
          = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (P.P x) := by simp [add_smul]
      _ = P.P x := by norm_num
  ext x
  simpa [splitOfPolarization, sub_eq_add_neg, smul_add, smul_sub, add_assoc, add_left_comm, add_comm]
    using hhalf x

/-- Involution associated to a polarization split datum. -/
noncomputable def involutionOfSplit (A : PolarizationSplit (S := S)) : EndS (S := S) :=
  A.Pplus - A.Pminus

/-- The involution associated to a projector split squares to identity. -/
theorem involutionOfSplit_sq (A : PolarizationSplit (S := S)) :
    (involutionOfSplit (S := S) A).comp (involutionOfSplit (S := S) A)
      = ContinuousLinearMap.id ℝ S := by
  ext x
  have hplus : A.Pplus (A.Pplus x) = A.Pplus x := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndS (S := S) => F x) A.plus_idem
  have hminus : A.Pminus (A.Pminus x) = A.Pminus x := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndS (S := S) => F x) A.minus_idem
  have hcrossPM : A.Pplus (A.Pminus x) = 0 := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndS (S := S) => F x) A.cross_plus_minus
  have hcrossMP : A.Pminus (A.Pplus x) = 0 := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndS (S := S) => F x) A.cross_minus_plus
  have hsum : A.Pplus x + A.Pminus x = x := by
    have h := congrArg (fun F : EndS (S := S) => F x) A.split_sum
    simpa [ContinuousLinearMap.add_apply, add_assoc, add_left_comm, add_comm] using h
  calc
    ((involutionOfSplit (S := S) A).comp (involutionOfSplit (S := S) A)) x
        = A.Pplus (A.Pplus x) - A.Pplus (A.Pminus x)
            - A.Pminus (A.Pplus x) + A.Pminus (A.Pminus x) := by
              simp [involutionOfSplit, sub_eq_add_neg, ContinuousLinearMap.comp_apply,
                add_assoc, add_left_comm, add_comm]
    _ = A.Pplus x + A.Pminus x := by
          simp [hplus, hminus, hcrossPM, hcrossMP, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
    _ = x := hsum

/-- Build a `K`-compatible involution from a split presentation plus compatibility proof. -/
noncomputable def ofSplit
    (A : PolarizationSplit (S := S))
    (hAnti : (involutionOfSplit (S := S) A).comp M.K
      = -(M.K.comp (involutionOfSplit (S := S) A))) :
    KPolarization (S := S) M where
  P := involutionOfSplit (S := S) A
  P_sq := involutionOfSplit_sq (S := S) A
  P_K_anticomm := hAnti

/-- The involution reconstructed from the canonical split is exactly `P`. -/
theorem ofSplit_splitOfPolarization_P (P : KPolarization (S := S) M) :
    (ofSplit (S := S) (M := M)
      (splitOfPolarization (M := M) P)
      (by simpa [involutionOfSplit, plus_sub_minus_eq_P] using P.P_K_anticomm)).P
        = P.P := by
  simpa [ofSplit, involutionOfSplit] using plus_sub_minus_eq_P (M := M) P

/-- Transport a polarization morphism into a split-presentation morphism. -/
noncomputable def Hom.toSplitHom
    {P Q : KPolarization (S := S) M} (h : P ⟶ Q) :
    splitOfPolarization (M := M) P ⟶ splitOfPolarization (M := M) Q where
  f := h.f
  finv := h.finv
  left_inv := h.left_inv
  right_inv := h.right_inv
  intertwines_minus := by
    ext x
    simp [splitOfPolarization, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      h.intertwines, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  intertwines_plus := by
    ext x
    simp [splitOfPolarization, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      h.intertwines, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

/--
Functor from polarization choices to derived split presentations.
This is the canonical projector-splitting bridge.
-/
noncomputable def polarizationToSplit :
    KPolarization (S := S) M ⥤ PolarizationSplit (S := S) where
  obj P := splitOfPolarization (M := M) P
  map h := h.toSplitHom (M := M)
  map_id P := by rfl
  map_comp f g := by rfl

/-- Backward-compatible alias: historical name for split projector data. -/
abbrev LadderPresentation (S : Type*)
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] :=
  PolarizationSplit (S := S)

/-- Backward-compatible alias: historical constructor name. -/
noncomputable abbrev ladderOfPolarization
    (P : KPolarization (S := S) M) : LadderPresentation (S := S) :=
  splitOfPolarization (M := M) P

/-- Backward-compatible theorem alias. -/
lemma creation_sub_annihilation_eq_P (P : KPolarization (S := S) M) :
    (ladderOfPolarization P).Pplus
      - (ladderOfPolarization P).Pminus = P.P :=
  plus_sub_minus_eq_P (M := M) P

/-- Backward-compatible alias for morphism transport into split data. -/
noncomputable abbrev Hom.toLadderHom
    {P Q : KPolarization (S := S) M} (h : P ⟶ Q) :
  ladderOfPolarization P ⟶ ladderOfPolarization Q :=
  Hom.toSplitHom (M := M) h

/-- Backward-compatible alias for the split functor. -/
noncomputable abbrev polarizationToLadder :
  KPolarization (S := S) M ⥤ LadderPresentation (S := S) :=
  polarizationToSplit (M := M)

attribute [deprecated PolarizationSplit (since := "2026-03-16")] LadderPresentation
attribute [deprecated splitOfPolarization (since := "2026-03-16")] ladderOfPolarization
attribute [deprecated plus_sub_minus_eq_P (since := "2026-03-16")] creation_sub_annihilation_eq_P
attribute [deprecated Hom.toSplitHom (since := "2026-03-16")] Hom.toLadderHom
attribute [deprecated polarizationToSplit (since := "2026-03-16")] polarizationToLadder

end KPolarization

end Core

end InfoGeometry.Quantum.RealMajorana
