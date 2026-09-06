import Mathlib.Tactic
import InfoGeometry.Spectral.Homotopy.Suspension
import InfoGeometry.Spectral.Spectrum.Basic

/-!
# Finite Eilenberg--MacLane-style readouts

Mathlib does not provide the unstable `K(G,n)` API expected by the old port.
This file records the finite algebraic readout that the surrounding spectral
bookkeeping actually uses.
-/

noncomputable section

universe u

namespace InfoGeometry.Spectral.Homotopy.EM

open InfoGeometry.Spectral.Homotopy.Suspension
open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Canonical.SplitCliffordTensorBridge

set_option linter.dupNamespace false

/-- Finite `K(G,n)` readout: the carrier is `G` with basepoint `0`. -/
def EM (G : Type*) [Zero G] (_n : ℕ) : PointedReadout :=
  Pointed.mk G 0

/-! ## Functorial finite readout

The old HoTT file develops functoriality of `K(G,n)`.  At this Lean 4
boundary the honest replacement is the pointed map induced by a zero-preserving
function.  This keeps the algebraic content while making no claim about an
unstable Eilenberg--MacLane construction.
-/

def EMMap {G H : Type*} [Zero G] [Zero H] (f : G → H)
    (hf : f 0 = 0) (n : ℕ) : PointedMap (EM G n) (EM H n) where
  toFun := f
  map_base := hf

@[simp]
theorem EMMap_apply {G H : Type*} [Zero G] [Zero H] (f : G → H)
    (hf : f 0 = 0) (n : ℕ) (x : G) :
    EMMap f hf n x = f x :=
  rfl

def EMMap.id {G : Type*} [Zero G] (n : ℕ) :
    PointedMap (EM G n) (EM G n) :=
  PointedMap.id (EM G n)

def EMMap.comp {G H K : Type*} [Zero G] [Zero H] [Zero K]
    (g : H → K) (hg : g 0 = 0) (f : G → H) (hf : f 0 = 0) (n : ℕ) :
    PointedMap (EM G n) (EM K n) :=
  PointedMap.comp (EMMap g hg n) (EMMap f hf n)

@[simp]
theorem EMMap_id_apply {G : Type*} [Zero G] (n : ℕ) (x : G) :
    EMMap.id n x = x :=
  rfl

@[simp]
theorem EMMap_comp_apply {G H K : Type*} [Zero G] [Zero H] [Zero K]
    (g : H → K) (hg : g 0 = 0) (f : G → H) (hf : f 0 = 0) (n : ℕ) (x : G) :
    EMMap.comp g hg f hf n x = g (f x) :=
  rfl

theorem EMMap_comp_id {G H : Type*} [Zero G] [Zero H]
    (f : G → H) (hf : f 0 = 0) (n : ℕ) :
    PointedMap.comp (EMMap f hf n) (EMMap.id n) = EMMap f hf n := by
  exact PointedMap.id_comp (EMMap f hf n)

theorem EMMap_id_comp {G H : Type*} [Zero G] [Zero H]
    (f : G → H) (hf : f 0 = 0) (n : ℕ) :
    PointedMap.comp (EMMap.id n) (EMMap f hf n) = EMMap f hf n := by
  exact PointedMap.comp_id (EMMap f hf n)

theorem EMMap_comp_assoc {G H K L : Type*}
    [Zero G] [Zero H] [Zero K] [Zero L]
    (h : K → L) (hh : h 0 = 0) (g : H → K) (hg : g 0 = 0)
    (f : G → H) (hf : f 0 = 0) (n : ℕ) :
    PointedMap.comp (EMMap h hh n) (EMMap.comp g hg f hf n) =
      PointedMap.comp (EMMap.comp h hh g hg n) (EMMap f hf n) := by
  exact PointedMap.comp_assoc (EMMap h hh n) (EMMap g hg n) (EMMap f hf n)

/-! ## Equivalences -/

def EMEq {G H : Type*} [Zero G] [Zero H] (e : G ≃ H)
    (he : e 0 = 0) (n : ℕ) : PointedEquiv (EM G n) (EM H n) where
  toEquiv := e
  map_base := he

@[simp]
theorem EMEq_apply {G H : Type*} [Zero G] [Zero H] (e : G ≃ H)
    (he : e 0 = 0) (n : ℕ) (x : G) :
    EMEq e he n x = e x :=
  rfl

theorem EMEq_symm_comp_self {G H : Type*} [Zero G] [Zero H]
    (e : G ≃ H) (he : e 0 = 0) (n : ℕ) :
    PointedEquiv.comp (EMEq e he n).symm (EMEq e he n) =
      PointedEquiv.refl (EM G n) := by
  exact PointedEquiv.comp_symm_self (EMEq e he n)

theorem EMEq_comp_self_symm {G H : Type*} [Zero G] [Zero H]
    (e : G ≃ H) (he : e 0 = 0) (n : ℕ) :
    PointedEquiv.comp (EMEq e he n) (EMEq e he n).symm =
      PointedEquiv.refl (EM H n) := by
  exact PointedEquiv.comp_self_symm (EMEq e he n)

/-! ## Bilinear/product readout -/

def EMProduct {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (hzero : ∀ a, f a 0 = 0) (_hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) (a : A) : PointedMap (EM B m) (EM C (m + n)) where
  toFun := f a
  map_base := hzero a

@[simp]
theorem EMProduct_apply {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (hzero : ∀ a, f a 0 = 0) (hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) (a : A) (b : B) :
    EMProduct f hzero hzero' n m a b = f a b :=
  rfl

@[simp]
theorem EMProduct_base_left {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (hzero : ∀ a, f a 0 = 0) (hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) (b : B) :
    EMProduct f hzero hzero' n m 0 b = f 0 b :=
  rfl

theorem EMProduct_zero_left {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (hzero : ∀ a, f a 0 = 0) (hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) :
    EMProduct f hzero hzero' n m 0 =
      ({ toFun := fun _ : B => (0 : C), map_base := rfl } :
        PointedMap (EM B m) (EM C (m + n))) := by
  apply PointedMap.ext
  intro b
  exact hzero' b

/-! The fully curried pointed product, corresponding to the old
`EM0EMadd1product` boundary. -/

def EMProductCurried {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (_hzero : ∀ a, f a 0 = 0) (hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) : PointedMap (EM A n) (EM (B → C) m) where
  toFun := fun a => f a
  map_base := by
    funext b
    exact hzero' b

@[simp]
theorem EMProductCurried_apply {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (hzero : ∀ a, f a 0 = 0) (hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) (a : A) (b : B) :
    EMProductCurried f hzero hzero' n m a b = f a b :=
  rfl

theorem EMProductCurried_zero {A B C : Type*} [Zero A] [Zero B] [Zero C]
    (f : A → B → C) (hzero : ∀ a, f a 0 = 0) (hzero' : ∀ b, f 0 b = 0)
    (n m : ℕ) :
    EMProductCurried f hzero hzero' n m (0 : A) = (fun _ => 0) := by
  funext b
  exact hzero' b

/-! Ring multiplication is the first concrete instance of the product
readout used by the old `EMRing` development. -/

def EMRingProduct (R : Type*) [NonUnitalNonAssocSemiring R] (n m : ℕ) (a : R) :
    PointedMap (EM R m) (EM R (m + n)) :=
  EMProduct (A := R) (B := R) (C := R)
    (fun x y : R => x * y) (fun x => mul_zero x) (fun y => zero_mul y) n m a

@[simp]
theorem EMRingProduct_apply (R : Type*) [NonUnitalNonAssocSemiring R]
    (n m : ℕ) (a b : R) :
    EMRingProduct R n m a b = a * b :=
  rfl

theorem EMRingProduct_zero_left (R : Type*) [NonUnitalNonAssocSemiring R]
    (n m : ℕ) :
    EMRingProduct R n m 0 =
      ({ toFun := fun _ : R => (0 : R), map_base := rfl } :
        PointedMap (EM R m) (EM R (m + n))) := by
  apply PointedMap.ext
  intro b
  change (0 : R) * (show R from b) = 0
  exact zero_mul (show R from b)

theorem EMRingProduct_natural {R S : Type*}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (φ : R →+* S) (n m : ℕ) (a b : R) :
    EMMap φ φ.map_zero n (EMRingProduct R n m a b) =
      EMRingProduct S n m (φ a) (φ b) := by
  simp only [EMMap_apply, EMRingProduct_apply]
  exact φ.map_mul a b

theorem EMRingProduct_map {R S : Type*}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (φ : R →+* S) (n m : ℕ) (a : R) :
    PointedMap.comp (EMRingProduct S n m (φ a)) (EMMap φ φ.map_zero m) =
      PointedMap.comp (EMMap φ φ.map_zero (m + n)) (EMRingProduct R n m a) := by
  apply PointedMap.ext
  intro b
  change φ a * φ (show R from b) = φ (a * (show R from b))
  exact (φ.map_mul (a := a) (b := (show R from b))).symm

theorem EMRingProduct_equiv {R S : Type*}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (e : R ≃+* S) (n m : ℕ) (a : R) :
    PointedMap.comp (EMRingProduct S n m (e a)) (EMMap e e.map_zero m) =
      PointedMap.comp (EMMap e e.map_zero (m + n)) (EMRingProduct R n m a) := by
  exact EMRingProduct_map e.toRingHom n m a

def EMRingProductCurried (R : Type*) [NonAssocSemiring R] (n m : ℕ) :
    PointedMap (EM R n) (EM (R → R) m) :=
  EMProductCurried (fun a b : R => a * b) (fun a => mul_zero a)
    (fun b => zero_mul b) n m

@[simp]
theorem EMRingProductCurried_apply (R : Type*) [NonAssocSemiring R]
    (n m : ℕ) (a b : R) :
    EMRingProductCurried R n m a b = a * b :=
  rfl

theorem EMRingProductCurried_zero (R : Type*) [NonAssocSemiring R]
    (n m : ℕ) :
    EMRingProductCurried R n m (0 : R) = (fun _ : R => (0 : R)) := by
  exact EMProductCurried_zero (fun a b : R => a * b)
    (fun a => mul_zero a) (fun b => zero_mul b) n m

@[simp]
theorem EM_base (G : Type*) [Zero G] (n : ℕ) :
    (EM G n).base = (0 : G) :=
  rfl

/-- Constant Eilenberg--MacLane-style prespectrum for a ring. -/
def EMRing (R : Type*) [Ring R] : Prespectrum :=
  Prespectrum.ofFun (fun _ => R) (fun _ x => x)

@[simp]
theorem EMRing_space (R : Type*) [Ring R] (n : ℕ) :
    (EMRing R).space n = R :=
  rfl

@[simp]
theorem EMRing_step (R : Type*) [Ring R] (n : ℕ) (x : R) :
    (EMRing R).step n x = x :=
  rfl

/-- Alias retained for the old port name. -/
def EMPrespectrum (R : Type*) [Ring R] : Prespectrum :=
  EMRing R

/-- Finite split-Clifford homotopy readout: iterated loops are carrier identity. -/
def SplitCliffordHomotopyGroup (n k : ℕ) : Type :=
  (IteratedLoopSpace k (SplitCliffordSuspension n)).carrier

@[simp]
theorem SplitCliffordHomotopyGroup_zero (n : ℕ) :
    SplitCliffordHomotopyGroup n 0 = (SplitCliffordSuspension n).carrier :=
  rfl

/-- Finite homology readout for an EM carrier. -/
def EMHomology (G : Type u) [Zero G] (_n _i : ℕ) : Type u :=
  G

/-- Split-Clifford Postnikov bookkeeping as the finite prespectrum already owned. -/
def SplitCliffordPostnikov (_n : ℕ) : Prespectrum :=
  SplitCliffordPrespectrum

@[simp]
theorem SplitCliffordPostnikov_space (n k : ℕ) :
    (SplitCliffordPostnikov n).space k = SplitClNNAlg k :=
  rfl

end InfoGeometry.Spectral.Homotopy.EM
