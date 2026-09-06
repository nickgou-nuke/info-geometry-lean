import Mathlib
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Canonical.Arithmetic.ZetaEulerProductBridge
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Arithmetic.SplitMajoranaPrimon

Finite split-Majorana primon surface.

This file packages the finite-cutoff algebraic bridge

* split-Majorana mode data `c = ε + ι`, `d = ε - ι`, `Π = cd = 1 - 2N`;
* finite Boolean occupation chirality;
* the finite Dirichlet/Witten character
  `∑_{S⊆P} (-1)^|S| ∏_{p∈S} q p = ∏_{p∈P} (1 - q p)`;
* the finite block-Pfaffian product shadow;
* the spinor square-root pairing `1 - r_p^2 = 1 - q_p`;
* the stable-vs-raw hyperbolic branch guardrail.

No infinite Euler product, analytic continuation, RH theorem, or genuine
matrix Pfaffian API is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SplitMajoranaPrimon

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/--
Witness packet for one split-Majorana mode.

This records the local operator data without constructing a concrete exterior
algebra representation in this file.
-/
structure SplitMajoranaMode (Op : Type*) [Ring Op] where
  eps : Op
  iota : Op
  c : Op
  d : Op
  N : Op
  Pi : Op
  eps_sq : eps * eps = 0
  iota_sq : iota * iota = 0
  car : iota * eps + eps * iota = 1
  c_def : c = eps + iota
  d_def : d = eps - iota
  N_def : N = eps * iota
  Pi_def : Pi = c * d
  Pi_eq_one_sub_twoN : Pi = 1 - (2 : Op) * N

namespace SplitMajoranaMode

variable {Op : Type*} [Ring Op]
variable (M : SplitMajoranaMode Op)

/-- The supplied local parity formula is available. -/
theorem parity_eq_one_sub_twoN :
    M.Pi = 1 - (2 : Op) * M.N :=
  M.Pi_eq_one_sub_twoN

/-- The supplied CAR law is available. -/
theorem car_valid :
    M.iota * M.eps + M.eps * M.iota = 1 :=
  M.car

end SplitMajoranaMode

/-! ## Boolean finite occupation chirality -/

/-- Integer occupation number of mode `p` in a finite occupation set. -/
def occupationInt (p : ℕ) (S : Finset ℕ) : ℤ :=
  if p ∈ S then 1 else 0

/-- Local split-Majorana parity `1 - 2N_p` on a Boolean occupation set. -/
def localMajoranaParity (p : ℕ) (S : Finset ℕ) : ℤ :=
  1 - 2 * occupationInt p S

@[simp]
theorem occupationInt_of_mem {p : ℕ} {S : Finset ℕ} (hp : p ∈ S) :
    occupationInt p S = 1 := by
  simp [occupationInt, hp]

@[simp]
theorem occupationInt_of_notMem {p : ℕ} {S : Finset ℕ} (hp : p ∉ S) :
    occupationInt p S = 0 := by
  simp [occupationInt, hp]

theorem localMajoranaParity_of_mem {p : ℕ} {S : Finset ℕ} (hp : p ∈ S) :
    localMajoranaParity p S = -1 := by
  simp [localMajoranaParity, hp]

theorem localMajoranaParity_of_notMem {p : ℕ} {S : Finset ℕ} (hp : p ∉ S) :
    localMajoranaParity p S = 1 := by
  simp [localMajoranaParity, hp]

/-- Global finite-cutoff chirality `Γ_Λ = ∏ Π_p`. -/
def globalMajoranaChirality
    (P : PrimeRegister) (S : Finset ℕ) : ℤ :=
  P.primes.prod (fun p => localMajoranaParity p S)

/-- Global chirality is `(-1)^|S|` on subsets of the register. -/
theorem globalMajoranaChirality_eq_neg_one_pow_card
    (P : PrimeRegister) (S : Finset ℕ) (hS : S ⊆ P.primes) :
    globalMajoranaChirality P S = (-1 : ℤ) ^ S.card := by
  classical
  unfold globalMajoranaChirality
  calc
    P.primes.prod (fun p => localMajoranaParity p S)
        = S.prod (fun p => localMajoranaParity p S) := by
          exact (Finset.prod_subset hS (by
            intro p _hp hpS
            exact localMajoranaParity_of_notMem hpS)).symm
    _ = S.prod (fun _p => (-1 : ℤ)) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact localMajoranaParity_of_mem hp
    _ = (-1 : ℤ) ^ S.card := by
          simp

/-- Global chirality is the Möbius value of the represented squarefree product. -/
theorem globalMajoranaChirality_eq_mobius_primeProduct
    (P : PrimeRegister) (S : Finset ℕ) (hS : S ⊆ P.primes) :
    globalMajoranaChirality P S =
      ArithmeticFunction.moebius (∏ p ∈ S, p) := by
  rw [globalMajoranaChirality_eq_neg_one_pow_card P S hS]
  exact (mobius_prime_product_eq_parity S (fun p hp => P.prime_mem p (hS hp))).symm

/-! ## Finite Dirichlet/Witten character -/

/-- Finite real Dirichlet/Witten character over squarefree prime occupations. -/
def dirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.primes.powerset,
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, q p

/-- Finite Euler product readout. -/
def finiteEulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P.primes, (1 - q p)

/-- The finite real Witten character equals the finite reciprocal Euler product. -/
theorem dirichletWittenCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    dirichletWittenCharacter P q = finiteEulerProduct P q := by
  classical
  unfold dirichletWittenCharacter finiteEulerProduct
  calc
    (∑ S ∈ P.primes.powerset, (-1 : ℝ) ^ S.card * ∏ p ∈ S, q p)
        =
      ∑ S ∈ P.primes.powerset,
        (-1 : ℝ) ^ S.card * (∏ p ∈ P.primes \ S, (1 : ℝ)) * ∏ p ∈ S, q p := by
        refine Finset.sum_congr rfl ?_
        intro S _hS
        simp
    _ = ∏ p ∈ P.primes, (1 - q p) := by
        exact (Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) q P.primes).symm

/-- Finite Witten character as a finite Möbius sum over squarefree products. -/
theorem dirichletWittenCharacter_eq_mobius_sum
    (P : PrimeRegister) (q : ℕ → ℝ) :
    dirichletWittenCharacter P q =
      ∑ S ∈ P.primes.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) *
          ∏ p ∈ S, q p := by
  classical
  unfold dirichletWittenCharacter
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
  have hμ :
      ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card :=
    mobius_prime_product_eq_parity S (fun p hp => P.prime_mem p (hSub hp))
  simp [hμ]

/-! ## Finite block-Pfaffian shadow -/

/--
Pfaffian of the real `2 × 2` skew block
`[[0, a], [-a, 0]]`.
-/
def skewBlockPfaffian (a : ℝ) : ℝ :=
  a

/-- Finite product of local Majorana skew-block Pfaffians. -/
def majoranaPfaffianProduct
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P.primes, skewBlockPfaffian (1 - q p)

/-- The finite block-Pfaffian product equals the finite Dirichlet/Witten character. -/
theorem majoranaPfaffianProduct_eq_dirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    majoranaPfaffianProduct P q =
      dirichletWittenCharacter P q := by
  rw [dirichletWittenCharacter_eq_eulerProduct]
  rfl

/-! ## Spinor square-root Euler factor -/

/-- Local spinor pairing `⟨ω_+,ω_-⟩ = 1 - r²`. -/
def localSpinorPairing (r : ℝ) : ℝ :=
  1 - r ^ 2

/-- If `q = r²`, the local spinor pairing is the reciprocal Euler factor. -/
theorem localSpinorPairing_eq_eulerFactor
    (r q : ℝ) (hq : q = r ^ 2) :
    localSpinorPairing r = 1 - q := by
  simp [localSpinorPairing, hq]

/-- Finite product of local spinor pairings. -/
def globalSpinorPairingProduct
    (P : PrimeRegister) (r : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P.primes, localSpinorPairing (r p)

/-- The spinor pairing product equals the finite Majorana Pfaffian product if `q_p=r_p²`. -/
theorem globalSpinorPairingProduct_eq_majoranaPfaffianProduct
    (P : PrimeRegister) (r q : ℕ → ℝ)
    (hq : ∀ p ∈ P.primes, q p = (r p) ^ 2) :
    globalSpinorPairingProduct P r =
      majoranaPfaffianProduct P q := by
  unfold globalSpinorPairingProduct majoranaPfaffianProduct skewBlockPfaffian
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact localSpinorPairing_eq_eulerFactor (r p) (q p) (hq p hp)

/-! ## Stable branch versus raw hyperbolic branch -/

/-- Stable projected Mellin/Majorana branch. -/
def stableProjectedChiralIndex
    (P : PrimeRegister) (qStable : ℕ → ℝ) : ℝ :=
  dirichletWittenCharacter P qStable

/-- Raw hyperbolic branch: stable branch minus unstable branch. -/
def rawHyperbolicChiralIndex
    (P : PrimeRegister) (qStable qUnstable : ℕ → ℝ) : ℝ :=
  stableProjectedChiralIndex P qStable -
    stableProjectedChiralIndex P qUnstable

/-- The raw hyperbolic index is the difference of finite Pfaffian/Witten products. -/
theorem rawHyperbolicChiralIndex_eq_pfaffian_difference
    (P : PrimeRegister) (qStable qUnstable : ℕ → ℝ) :
    rawHyperbolicChiralIndex P qStable qUnstable =
      majoranaPfaffianProduct P qStable -
        majoranaPfaffianProduct P qUnstable := by
  unfold rawHyperbolicChiralIndex stableProjectedChiralIndex
  rw [majoranaPfaffianProduct_eq_dirichletWittenCharacter,
    majoranaPfaffianProduct_eq_dirichletWittenCharacter]

/-! ## Infinite/zeta bridge socket -/

/-- Mathlib-backed infinite Euler-product readout on the standard half-plane. -/
@[bridge_target_tag]
theorem infiniteEulerProductZeta_readout {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) = riemannZeta s := by
  simpa using InfoGeometry.Canonical.Arithmetic.zeta_euler_product_bridge hs

/--
Witness-gated infinite Euler product bridge.

For a concrete analytic model this should state that, on an admissible domain,
the infinite cutoff limit of the finite character equals `1 / ζ(s)`.
The actual prime-product readout is reexported above from the canonical
mathlib-backed bridge.
-/
@[socket_debt_tag]
structure InfiniteEulerProductZetaBridge
    (Param Scalar : Type*) where
  IsAdmissible : Param → Prop
  finiteCutoffCharacter : ℕ → Param → Scalar
  reciprocalZeta : Param → Scalar
  cutoff_limit_law : Prop
  cutoff_limit_certificate : cutoff_limit_law

namespace InfiniteEulerProductZetaBridge

variable {Param Scalar : Type*}
variable (B : InfiniteEulerProductZetaBridge Param Scalar)

/-- The supplied cutoff-limit law is available. -/
@[bridge_target_tag]
theorem cutoff_limit_valid :
    B.cutoff_limit_law :=
  B.cutoff_limit_certificate

end InfiniteEulerProductZetaBridge

end InfoGeometry.Arithmetic.SplitMajoranaPrimon
