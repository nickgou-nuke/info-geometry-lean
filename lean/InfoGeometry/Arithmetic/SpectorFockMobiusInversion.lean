/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.SpectorPrimonGasBridge
import InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.Convolution

/-!
# Spector (1990): Supersymmetric Fock Space and the Möbius Inversion Function

This module formalizes §§2–4 of Donald Spector,
*Supersymmetry and the Möbius Inversion Function*, Commun. Math. Phys. 127 (1990), 239–252:

1. **Full Gödel Fock-state bijection (§2, Eqs. 2.4–2.10)**:
   Equivalences between bosonic/fermionic Fock states
   `(ℕ →₀ ℕ) × Finset Nat.Primes` (indexing the `k`-th prime mode via `Nat.nth Nat.Prime`),
   prime-supported `Finsupp` pairs `{α : ℕ →₀ ℕ // ∀ p ∈ α.support, Nat.Prime p} × Finset Nat.Primes`,
   `(Nat.Primes →₀ ℕ) × Finset Nat.Primes`, and Gödel pairs
   `{nd : ℕ+ × ℕ+ // Squarefree nd.2.val ∧ nd.2.val ∣ nd.1.val}`,
   proving `(-1 : ℤ) ^ β.card = ArithmeticFunction.moebius d.val`, embedding
   `PrimeBitWittenIndex` as the bosonic-vacuum slice, and exhibiting the non-squarefree
   state `|12, 2⟩`.
2. **`N`-sector supertrace & Bose–Fermi pairing involution (§2, Eqs. 2.11–2.12)**:
   `∑ d ∈ N.val.divisors, μ d = if N = 1 then 1 else 0` via the explicit Bose–Fermi
   involution `boseFermiToggle` on prime divisors of `N > 1`, together with equivalence to
   `PrimeBitWittenIndex.finite_divisor_mobius_sum_cancel`.
3. **3-sector `(A, B, F)` Fock-space Möbius inversion & thermal identity (§4, Eqs. 4.10–4.19)**:
   Double-grouping over `(A, B, F)` states in any `[AddCommGroup R]` and noncommutative
   `[Ring R]`, plus finite-box and summable `tsum` thermal expectation identities
   `Tr_s(h̃ e^{-β(H_a + H_b + H_f)}) = Tr(h̃ e^{-β H_a})`.
4. **Totally multiplicative inverse series (§3, Eqs. 3.7–3.8)**:
   `(∑' n, M n) * (∑' n, (μ n : ℂ) * M n) = 1` for `M 0 = 0`, `M 1 = 1`, totally
   multiplicative on positive integers with `Summable (fun n => ‖M n‖)`, specialized to
   `n ^ (-s)` (`1 < s.re`) via `ActualRiemannZetaMobiusLSeriesBridge`.
5. **Totient supertrace (§3, Eq. 3.9)**:
   `spectorPhi s N = ∑ d ∈ N.val.divisors, (μ d : ℂ) * ((N.val / d : ℕ) : ℂ) ^ s`,
   Fock-state trace equality at `s = β * ω`, and `spectorPhi 1 N = (Nat.totient N.val : ℂ)`.
6. **Dirichlet derivative & `OperatorDirichlet.logMul` (§3, Eq. 3.10)**:
   `⟨N | h̃ H_b | N⟩ = ω log(N) h(N)` and `-(1/ω) ⟨N | h̃ H_b | N⟩ = -logMul h N`,
   product rule via `OperatorDirichlet.logMul_mul`, and prime-mode expansion via
   `PrimeBosonFermionGas.log_prod_prime_pow_of_prime`.
-/

namespace InfoGeometry.Arithmetic.SpectorFockMobiusInversion

open scoped BigOperators ArithmeticFunction.Moebius

/-! ## Section 1: Constructive Fock State Carrier & T17 Witnesses (No Active Variables) -/

/-- A state in Spector's supersymmetric primon Fock space:
`boson k` is the bosonic occupation number `α_k ∈ ℕ` of the `k`-th prime mode `p_k`,
and `fermion` is the finite set of occupied fermionic prime modes (`β_p ∈ {0, 1}`). -/
structure SpectorFockState where
  boson : ℕ →₀ ℕ
  fermion : Finset Nat.Primes

/-- Constructive vacuum state `|1, 1⟩` (`α = 0, β = ∅`). -/
def spectorVacuumState : SpectorFockState :=
  ⟨0, ∅⟩

instance : Inhabited SpectorFockState :=
  ⟨spectorVacuumState⟩

private def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- Constructive non-squarefree Fock state `|12, 2⟩`:
`p₀ = 2` has `(α₀ = 1, β₀ = 1)` (`2^(1+1) = 4`), `p₁ = 3` has `(α₁ = 1, β₁ = 0)` (`3^1 = 3`),
giving `N = 12` and squarefree fermionic divisor `d = 2`. -/
noncomputable def spectorState12_d2 : SpectorFockState :=
  ⟨Finsupp.single 0 1 + Finsupp.single 1 1, {primeTwo}⟩

/-! ## Section 2: Full Gödel Fock-State Bijection & Möbius Parity (§§2.1–2.10) -/

noncomputable section

/-- Prime-supported bosonic occupation numbers `α : ℕ →₀ ℕ` (`∀ p ∈ α.support, Nat.Prime p`). -/
abbrev PrimeBosonOcc := { α : ℕ →₀ ℕ // ∀ p ∈ α.support, Nat.Prime p }

/-- Gödel state pairs `(N, d)` of positive integers with `Squarefree d` and `d ∣ N`. -/
abbrev GodelPair := { nd : ℕ+ × ℕ+ // Squarefree nd.2.val ∧ nd.2.val ∣ nd.1.val }

private def primeValEmb : Nat.Primes ↪ ℕ :=
  ⟨Subtype.val, Subtype.coe_injective⟩

/-- Indexing equivalence `ℕ ≃ Nat.Primes` sending `k` to the `k`-th prime `p_k = Nat.nth Nat.Prime k`. -/
def primeIndexEquiv : ℕ ≃ Nat.Primes where
  toFun k := ⟨Nat.nth Nat.Prime k, Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩
  invFun p := Nat.count Nat.Prime p.1
  left_inv k := Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime k
  right_inv p := Subtype.ext (Nat.nth_count p.2)

/-- Equivalence between prime-indexed `Finsupp` `(Nat.Primes →₀ ℕ)` and prime-supported
`ℕ →₀ ℕ` (`PrimeBosonOcc`). -/
def primeBosonFinsuppEquiv : (Nat.Primes →₀ ℕ) ≃ PrimeBosonOcc where
  toFun β :=
    ⟨β.embDomain primeValEmb, by
      intro p hp
      have hp' : p ∈ (β.embDomain primeValEmb).support := hp
      have hmem : p ∈ β.support.map primeValEmb := by
        simpa only [Finsupp.support_embDomain] using hp'
      rcases Finset.mem_map.mp hmem with ⟨q, _, rfl⟩
      exact q.2⟩
  invFun α := α.1.subtypeDomain Nat.Prime
  left_inv β := by
    ext p
    change (Finsupp.subtypeDomain Nat.Prime (β.embDomain primeValEmb)) p = β p
    rw [Finsupp.subtypeDomain_apply]
    exact Finsupp.embDomain_apply_self primeValEmb β p
  right_inv α := by
    ext p
    by_cases hp : Nat.Prime p
    · let q : Nat.Primes := ⟨p, hp⟩
      have h1 :
          ((α.1.subtypeDomain Nat.Prime).embDomain primeValEmb) (primeValEmb q) =
            (α.1.subtypeDomain Nat.Prime) q :=
        Finsupp.embDomain_apply_self primeValEmb (α.1.subtypeDomain Nat.Prime) q
      exact h1.trans Finsupp.subtypeDomain_apply
    · have hzero : α.1 p = 0 := by
        by_contra hne
        exact hp (α.2 p (Finsupp.mem_support_iff.mpr hne))
      rw [hzero]
      change (Finsupp.embDomain primeValEmb (α.1.subtypeDomain Nat.Prime)) p = 0
      refine Finsupp.embDomain_of_notMem_range primeValEmb (α.1.subtypeDomain Nat.Prime) p ?_
      rintro ⟨q, rfl⟩
      exact hp q.2

/-- Equivalence between mode-indexed bosonic occupations `ℕ →₀ ℕ` (with `k ↦ p_k`)
and prime-supported `ℕ →₀ ℕ`. -/
def bosonModesEquivPrimeSupport : (ℕ →₀ ℕ) ≃ PrimeBosonOcc :=
  (Finsupp.equivCongrLeft primeIndexEquiv).trans primeBosonFinsuppEquiv

/-- Equivalence between prime-supported bosonic occupations and `ℕ+`, via `Nat.factorizationEquiv`. -/
def bosonOccEquivPNat : PrimeBosonOcc ≃ ℕ+ :=
  Nat.factorizationEquiv.symm

/-- Equivalence between mode-indexed bosonic occupations `ℕ →₀ ℕ` and `ℕ+`. -/
def bosonModesEquivPNat : (ℕ →₀ ℕ) ≃ ℕ+ :=
  bosonModesEquivPrimeSupport.trans bosonOccEquivPNat

private theorem fermionProd_pos (β : Finset Nat.Primes) :
    0 < ∏ p ∈ β, (p : ℕ) :=
  Finset.prod_pos fun p _ => p.2.pos

private theorem fermionProd_squarefree (β : Finset Nat.Primes) :
    Squarefree (∏ p ∈ β, (p : ℕ)) := by
  let S : Finset ℕ := β.map primeValEmb
  have hS : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨q, _, rfl⟩
    exact q.2
  have hprod : (∏ p ∈ β, (p : ℕ)) = ∏ p ∈ S, p :=
    (Finset.prod_map β primeValEmb (fun n => n)).symm
  rw [hprod]
  refine ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ?_
  rw [PrimeBitWittenIndex.mobius_prime_product_eq_parity S hS]
  exact pow_ne_zero _ (by decide)

/-- Equivalence between finite sets of primes `Finset Nat.Primes` and squarefree positive integers. -/
def fermionSetEquivSquarefree : Finset Nat.Primes ≃ { d : ℕ+ // Squarefree d.val } where
  toFun β := ⟨⟨∏ p ∈ β, (p : ℕ), fermionProd_pos β⟩, fermionProd_squarefree β⟩
  invFun d :=
    Finset.map
      ⟨fun p : { x : ℕ // x ∈ d.1.val.primeFactors } =>
          (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes),
       fun _ _ h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩
      d.1.val.primeFactors.attach
  left_inv β := by
    ext p
    have hprime : ∀ q ∈ β.map primeValEmb, Nat.Prime q := by
      intro q hq
      rcases Finset.mem_map.mp hq with ⟨r, _, rfl⟩
      exact r.2
    have hpf : (∏ q ∈ β, (q : ℕ)).primeFactors = β.map primeValEmb := by
      have h1 : (∏ q ∈ β, (q : ℕ)) = ∏ q ∈ β.map primeValEmb, q :=
        (Finset.prod_map β primeValEmb (fun n => n)).symm
      rw [h1]
      exact Nat.primeFactors_prod hprime
    dsimp only
    rw [Finset.mem_map]
    constructor
    · rintro ⟨⟨q, hq⟩, _, hqp⟩
      change q ∈ (∏ r ∈ β, (r : ℕ)).primeFactors at hq
      rw [hpf, Finset.mem_map] at hq
      rcases hq with ⟨r, hr, hrq⟩
      have hrp : r = p := Subtype.ext (hrq.trans (congrArg (fun x : Nat.Primes => (x : ℕ)) hqp))
      simpa [hrp] using hr
    · intro hp
      have hq : p.1 ∈ (∏ q ∈ β, (q : ℕ)).primeFactors := by
        rw [hpf, Finset.mem_map]
        exact ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, hq⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  right_inv d := by
    apply Subtype.ext
    apply PNat.coe_injective
    dsimp only
    have h1 :
        (∏ p ∈ Finset.map
            ⟨fun p : { x : ℕ // x ∈ d.1.val.primeFactors } =>
                (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes),
             fun _ _ h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩
            d.1.val.primeFactors.attach, (p : ℕ)) =
          ∏ p ∈ d.1.val.primeFactors.attach, p.1 := by
      rw [Finset.prod_map]
      rfl
    have h2 : (∏ p ∈ d.1.val.primeFactors.attach, p.1) = ∏ p ∈ d.1.val.primeFactors, p :=
      Finset.prod_attach d.1.val.primeFactors (fun p => p)
    exact h1.trans (h2.trans (Nat.prod_primeFactors_of_squarefree d.2))

/-- Helper equivalence decomposing `{nd : ℕ+ × ℕ+ // Squarefree nd.2.val ∧ nd.2.val ∣ nd.1.val}`
into bosonic quotient `B = N / d : ℕ+` and fermionic squarefree divisor `d`. -/
def pnatDivisorEquivGodelPair : (ℕ+ × { d : ℕ+ // Squarefree d.val }) ≃ GodelPair where
  toFun x := ⟨(x.1 * x.2.1, x.2.1), x.2.2, dvd_mul_left x.2.1.val x.1.val⟩
  invFun y :=
    (⟨y.1.1.val / y.1.2.val,
        Nat.div_pos (Nat.le_of_dvd y.1.1.pos y.2.2) y.1.2.pos⟩,
     ⟨y.1.2, y.2.1⟩)
  left_inv x := by
    apply Prod.ext
    · apply PNat.coe_injective
      exact Nat.mul_div_cancel x.1.val x.2.1.pos
    · rfl
  right_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · apply PNat.coe_injective
      exact Nat.div_mul_cancel y.2.2
    · rfl

/-- **Full Spector Gödel Fock-state equivalence (Spector 1990, Eqs. 2.4–2.5)**:
`(ℕ →₀ ℕ) × Finset Nat.Primes ≃ {nd : ℕ+ × ℕ+ // Squarefree nd.2.val ∧ nd.2.val ∣ nd.1.val}`,
where the `k`-th bosonic mode is the `k`-th prime `Nat.nth Nat.Prime k`. -/
def spectorGodelEquiv : ((ℕ →₀ ℕ) × Finset Nat.Primes) ≃ GodelPair :=
  (Equiv.prodCongr bosonModesEquivPNat fermionSetEquivSquarefree).trans pnatDivisorEquivGodelPair

/-- **Direct prime-keyed Gödel Fock-state equivalence**:
`{α : ℕ →₀ ℕ // ∀ p ∈ α.support, Nat.Prime p} × Finset Nat.Primes ≃ GodelPair`
via `Nat.factorizationEquiv`. -/
def spectorPrimeSupportGodelEquiv : (PrimeBosonOcc × Finset Nat.Primes) ≃ GodelPair :=
  (Equiv.prodCongr bosonOccEquivPNat fermionSetEquivSquarefree).trans pnatDivisorEquivGodelPair

/-- **`Nat.Primes →₀ ℕ` Gödel Fock-state equivalence**:
`(Nat.Primes →₀ ℕ) × Finset Nat.Primes ≃ GodelPair`. -/
def spectorPrimesFinsuppGodelEquiv : ((Nat.Primes →₀ ℕ) × Finset Nat.Primes) ≃ GodelPair :=
  (Equiv.prodCongr (primeBosonFinsuppEquiv.trans bosonOccEquivPNat) fermionSetEquivSquarefree).trans
    pnatDivisorEquivGodelPair

/-- `SpectorFockState ≃ GodelPair`. -/
def spectorFockStateEquiv : SpectorFockState ≃ GodelPair where
  toFun s := spectorGodelEquiv (s.boson, s.fermion)
  invFun g := let p := spectorGodelEquiv.symm g; ⟨p.1, p.2⟩
  left_inv s := by
    rcases s with ⟨b, f⟩
    simp
  right_inv g := by simp

/-- Fermion parity operator `(-1)^(|supp β|)` on fermionic Fock states. -/
def fockFermionParity (β : Finset Nat.Primes) : ℤ :=
  (-1 : ℤ) ^ β.card

/-- **Spector Eq. (2.9)**: On any Fock state `(α, β)` representing `|N, d⟩`, the fermion
parity `(-1)^(|supp β|)` equals `ArithmeticFunction.moebius d.val`. -/
theorem fockFermionParity_eq_moebius (β : Finset Nat.Primes) :
    fockFermionParity β =
      ArithmeticFunction.moebius (fermionSetEquivSquarefree β).1.val := by
  let S : Finset ℕ := β.map primeValEmb
  have hS : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨q, _, rfl⟩
    exact q.2
  have hprod : (fermionSetEquivSquarefree β).1.val = ∏ p ∈ S, p := by
    change (∏ p ∈ β, (p : ℕ)) = ∏ p ∈ β.map primeValEmb, p
    rw [Finset.prod_map]
    rfl
  have hcard : S.card = β.card := Finset.card_map _
  rw [hprod, PrimeBitWittenIndex.mobius_prime_product_eq_parity S hS, hcard, fockFermionParity]

/-- State-level parity theorem `(-1)^|β| = μ(d)` via `spectorGodelEquiv`. -/
theorem spectorGodelEquiv_parity_eq_moebius (s : (ℕ →₀ ℕ) × Finset Nat.Primes) :
    fockFermionParity s.2 = ArithmeticFunction.moebius (spectorGodelEquiv s).1.2.val :=
  fockFermionParity_eq_moebius s.2

/-- Embed a squarefree `PrimeBitWittenIndex` state as the bosonic-vacuum `(0, β)` slice of
`SpectorFockState`. -/
def ofPrimeBitState
    (P : PrimeBitWittenIndex.PrimeRegister) (ψ : PrimeBitWittenIndex.PrimeBitState P) :
    SpectorFockState where
  boson := 0
  fermion :=
    Finset.map
      ⟨fun p : { x : ℕ // x ∈ PrimeBitWittenIndex.occupiedPrimeSet P ψ } =>
          (⟨p.1, P.prime_mem p.1 (PrimeBitWittenIndex.occupiedPrimeSet_subset P ψ p.2)⟩ :
            Nat.Primes),
       fun _ _ h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩
      (PrimeBitWittenIndex.occupiedPrimeSet P ψ).attach

theorem bosonModesEquivPNat_zero : bosonModesEquivPNat 0 = 1 := by
  have hzero : (bosonModesEquivPrimeSupport 0).1 = 0 := by
    ext p
    change (Finsupp.embDomain primeValEmb (Finsupp.equivCongrLeft primeIndexEquiv 0)) p = 0
    rw [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_zero, Finsupp.embDomain_zero]
    rfl
  apply PNat.coe_injective
  change (Nat.factorizationEquiv.symm (bosonModesEquivPrimeSupport 0)).1 = 1
  rw [Nat.factorizationEquiv_symm_apply_coe, hzero]
  simp

theorem ofPrimeBitState_fermion_val
    (P : PrimeBitWittenIndex.PrimeRegister) (ψ : PrimeBitWittenIndex.PrimeBitState P) :
    (fermionSetEquivSquarefree (ofPrimeBitState P ψ).fermion).1.val =
      PrimeBitWittenIndex.representedNatOfState P ψ := by
  change (∏ p ∈ (ofPrimeBitState P ψ).fermion, (p : ℕ)) =
    PrimeBitWittenIndex.representedNatOfState P ψ
  unfold ofPrimeBitState PrimeBitWittenIndex.representedNatOfState
  rw [Finset.prod_map]
  exact Finset.prod_attach (PrimeBitWittenIndex.occupiedPrimeSet P ψ) (fun p => p)

/-- `PrimeBitWittenIndex` embeds cleanly as the bosonic-vacuum `(0, β)` slice (`N = d`)
of `SpectorFockState`, recovering `PrimeBitWittenIndex.mobius_representedNatOfState_eq_fermionParity`. -/
theorem ofPrimeBitState_godel_and_parity
    (P : PrimeBitWittenIndex.PrimeRegister) (ψ : PrimeBitWittenIndex.PrimeBitState P) :
    (spectorFockStateEquiv (ofPrimeBitState P ψ)).1.1.val =
        PrimeBitWittenIndex.representedNatOfState P ψ ∧
      (spectorFockStateEquiv (ofPrimeBitState P ψ)).1.2.val =
        PrimeBitWittenIndex.representedNatOfState P ψ ∧
      fockFermionParity (ofPrimeBitState P ψ).fermion =
        PrimeBitWittenIndex.fermionParityOfState P ψ := by
  have hbos : bosonModesEquivPNat (ofPrimeBitState P ψ).boson = 1 := by
    simpa [ofPrimeBitState] using bosonModesEquivPNat_zero
  have hferm : (fermionSetEquivSquarefree (ofPrimeBitState P ψ).fermion).1.val =
      PrimeBitWittenIndex.representedNatOfState P ψ :=
    ofPrimeBitState_fermion_val P ψ
  refine ⟨?_, ?_, ?_⟩
  · change (bosonModesEquivPNat (ofPrimeBitState P ψ).boson *
      (fermionSetEquivSquarefree (ofPrimeBitState P ψ).fermion).1).val = _
    rw [hbos, one_mul, hferm]
  · exact hferm
  · rw [fockFermionParity_eq_moebius, hferm]
    exact PrimeBitWittenIndex.mobius_representedNatOfState_eq_fermionParity P ψ

/-- Explicit non-squarefree Fock state witness: `spectorState12_d2` maps to `|N = 12, d = 2⟩`,
where `¬ Squarefree 12` and `μ(12) = 0` (so `N = 12` lies strictly outside the squarefree
`PrimeBitWittenIndex` slice, while `(-1)^1 = -1 = μ(2)`). -/
theorem spectorState12_d2_witness :
    (spectorFockStateEquiv spectorState12_d2).1.1.val = 12 ∧
      (spectorFockStateEquiv spectorState12_d2).1.2.val = 2 ∧
      ¬ Squarefree (spectorFockStateEquiv spectorState12_d2).1.1.val ∧
      ArithmeticFunction.moebius (spectorFockStateEquiv spectorState12_d2).1.1.val = 0 ∧
      fockFermionParity spectorState12_d2.fermion = -1 := by
  have h0 : primeIndexEquiv 0 = primeTwo := Subtype.ext Nat.nth_prime_zero_eq_two
  have h1 : primeIndexEquiv 1 = primeThree := Subtype.ext Nat.nth_prime_one_eq_three
  have hbos_occ :
      (bosonModesEquivPrimeSupport spectorState12_d2.boson).1 =
        Finsupp.single 2 1 + Finsupp.single 3 1 := by
    have hmap :
        Finsupp.equivCongrLeft primeIndexEquiv spectorState12_d2.boson =
          Finsupp.single primeTwo 1 + Finsupp.single primeThree 1 := by
      ext p
      simp only [spectorState12_d2, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply,
        Finsupp.add_apply, Finsupp.single_apply]
      have hs0 : (0 = primeIndexEquiv.symm p) ↔ (primeTwo = p) := by
        constructor
        · intro h; rw [← h0, h, Equiv.apply_symm_apply]
        · intro h; rw [← h, ← h0, Equiv.symm_apply_apply]
      have hs1 : (1 = primeIndexEquiv.symm p) ↔ (primeThree = p) := by
        constructor
        · intro h; rw [← h1, h, Equiv.apply_symm_apply]
        · intro h; rw [← h, ← h1, Equiv.symm_apply_apply]
      simp [hs0, hs1]
    change ((primeBosonFinsuppEquiv
        (Finsupp.equivCongrLeft primeIndexEquiv spectorState12_d2.boson)).1) = _
    rw [hmap]
    ext q
    change ((Finsupp.embDomain primeValEmb
        (Finsupp.single primeTwo 1 + Finsupp.single primeThree 1)) q) =
      ((Finsupp.single 2 1 + Finsupp.single 3 1 : ℕ →₀ ℕ) q)
    rw [Finsupp.embDomain_add, Finsupp.add_apply, Finsupp.add_apply]
    have e2 : Finsupp.embDomain primeValEmb (Finsupp.single primeTwo 1) =
        Finsupp.single 2 1 := Finsupp.embDomain_single primeValEmb primeTwo 1
    have e3 : Finsupp.embDomain primeValEmb (Finsupp.single primeThree 1) =
        Finsupp.single 3 1 := Finsupp.embDomain_single primeValEmb primeThree 1
    rw [e2, e3]
  have hbos_val : (bosonModesEquivPNat spectorState12_d2.boson).val = 6 := by
    change (Nat.factorizationEquiv.symm (bosonModesEquivPrimeSupport spectorState12_d2.boson)).1 = 6
    rw [Nat.factorizationEquiv_symm_apply_coe, hbos_occ]
    rw [Finsupp.prod_add_index' (by simp) Nat.pow_add]
    norm_num [Finsupp.prod_single_index]
  have hferm_val : (fermionSetEquivSquarefree spectorState12_d2.fermion).1.val = 2 := by
    change (∏ p ∈ spectorState12_d2.fermion, (p : ℕ)) = 2
    rw [spectorState12_d2, Finset.prod_singleton]
    rfl
  have hN : (spectorFockStateEquiv spectorState12_d2).1.1.val = 12 := by
    change (bosonModesEquivPNat spectorState12_d2.boson).val *
      (fermionSetEquivSquarefree spectorState12_d2.fermion).1.val = 12
    rw [hbos_val, hferm_val]
  have hd : (spectorFockStateEquiv spectorState12_d2).1.2.val = 2 := hferm_val
  have hnsq : ¬ Squarefree (12 : ℕ) := by
    intro hsq
    have h2 : IsUnit (2 : ℕ) := hsq 2 (by norm_num)
    norm_num at h2
  refine ⟨hN, hd, ?_, ?_, ?_⟩
  · simpa [hN] using hnsq
  · rw [hN]
    exact PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree hnsq
  · change (-1 : ℤ) ^ spectorState12_d2.fermion.card = -1
    rw [spectorState12_d2, Finset.card_singleton]
    norm_num

/-! ## Section 3: N-Sector Supertrace & Bose–Fermi Pairing Involution (§2, Eqs. 2.11–2.12) -/

/-- Squarefree divisors of `N : ℕ+`, corresponding to allowed fermionic sectors `d ∣ N`. -/
def squarefreeDivisors (N : ℕ+) : Finset ℕ :=
  N.val.divisors.filter Squarefree

/-- Explicit Bose–Fermi pairing involution on the `N`-sector (`1 < N.val`), toggling
the least prime factor `p₀ = N.val.minFac` between bosonic (`¬ p₀ ∣ d`) and fermionic
(`p₀ ∣ d`) occupation: `(α_{p₀}, 1) ↔ (α_{p₀} + 1, 0)`. -/
def boseFermiToggle (N : ℕ+) (d : ℕ) : ℕ :=
  let p₀ := N.val.minFac
  if p₀ ∣ d then d / p₀ else d * p₀

theorem boseFermiToggle_mem {N : ℕ+} (hN : 1 < N.val) {d : ℕ}
    (hd : d ∈ squarefreeDivisors N) :
    boseFermiToggle N d ∈ squarefreeDivisors N := by
  have hp : N.val.minFac.Prime := Nat.minFac_prime (Nat.ne_of_gt hN)
  have hpN : N.val.minFac ∣ N.val := Nat.minFac_dvd N.val
  rcases Finset.mem_filter.mp hd with ⟨hdDiv, hdsq⟩
  have hdN : d ∣ N.val := Nat.dvd_of_mem_divisors hdDiv
  rw [squarefreeDivisors, Finset.mem_filter, Nat.mem_divisors]
  by_cases hpd : N.val.minFac ∣ d
  · simp only [boseFermiToggle, hpd, ↓reduceIte]
    refine ⟨⟨Nat.div_dvd_of_dvd hpd |>.trans hdN, N.pos.ne'⟩, ?_⟩
    exact hdsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)
  · simp only [boseFermiToggle, hpd, ↓reduceIte]
    have hcop : Nat.Coprime d N.val.minFac := hp.coprime_iff_not_dvd.mpr hpd |>.symm
    refine ⟨⟨hcop.mul_dvd_of_dvd_of_dvd hdN hpN, N.pos.ne'⟩, ?_⟩
    exact (Nat.squarefree_mul hcop).mpr ⟨hdsq, hp.squarefree⟩

theorem boseFermiToggle_involutive {N : ℕ+} (hN : 1 < N.val) {d : ℕ}
    (hd : d ∈ squarefreeDivisors N) :
    boseFermiToggle N (boseFermiToggle N d) = d := by
  have hp : N.val.minFac.Prime := Nat.minFac_prime (Nat.ne_of_gt hN)
  rcases Finset.mem_filter.mp hd with ⟨_, hdsq⟩
  by_cases hpd : N.val.minFac ∣ d
  · have hnot : ¬ N.val.minFac ∣ (d / N.val.minFac) := by
      intro hdiv
      have hsq : N.val.minFac * N.val.minFac ∣ d := by
        simpa [Nat.mul_div_cancel' hpd] using Nat.mul_dvd_mul_left N.val.minFac hdiv
      exact hp.ne_one (Nat.isUnit_iff.mp (hdsq N.val.minFac hsq))
    simp only [boseFermiToggle, hpd, ↓reduceIte, hnot]
    exact Nat.div_mul_cancel hpd
  · have hdvd : N.val.minFac ∣ d * N.val.minFac := dvd_mul_left N.val.minFac d
    simp only [boseFermiToggle, hpd, ↓reduceIte, hdvd]
    exact Nat.mul_div_cancel d hp.pos

theorem boseFermiToggle_ne {N : ℕ+} (hN : 1 < N.val) {d : ℕ}
    (hd : d ∈ squarefreeDivisors N) :
    boseFermiToggle N d ≠ d := by
  have hp : N.val.minFac.Prime := Nat.minFac_prime (Nat.ne_of_gt hN)
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  by_cases hpd : N.val.minFac ∣ d
  · simp only [boseFermiToggle, hpd, ↓reduceIte]
    exact Nat.ne_of_lt (Nat.div_lt_self hdpos hp.one_lt)
  · simp only [boseFermiToggle, hpd, ↓reduceIte]
    exact Nat.ne_of_gt (lt_mul_of_one_lt_right hdpos hp.one_lt)

theorem moebius_boseFermiToggle {N : ℕ+} (hN : 1 < N.val) {d : ℕ}
    (hd : d ∈ squarefreeDivisors N) :
    ArithmeticFunction.moebius (boseFermiToggle N d) = -ArithmeticFunction.moebius d := by
  have hp : N.val.minFac.Prime := Nat.minFac_prime (Nat.ne_of_gt hN)
  have hdsq : Squarefree d := (Finset.mem_filter.mp hd).2
  by_cases hpd : N.val.minFac ∣ d
  · have hnot : ¬ N.val.minFac ∣ (d / N.val.minFac) := by
      intro hdiv
      have hsq : N.val.minFac * N.val.minFac ∣ d := by
        simpa [Nat.mul_div_cancel' hpd] using Nat.mul_dvd_mul_left N.val.minFac hdiv
      exact hp.ne_one (Nat.isUnit_iff.mp (hdsq N.val.minFac hsq))
    have hcop : Nat.Coprime (d / N.val.minFac) N.val.minFac :=
      (hp.coprime_iff_not_dvd.mpr hnot).symm
    have hmul : ArithmeticFunction.moebius d =
        ArithmeticFunction.moebius (d / N.val.minFac) * ArithmeticFunction.moebius N.val.minFac := by
      conv_lhs => rw [← Nat.div_mul_cancel hpd]
      exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    rw [ArithmeticFunction.moebius_apply_prime hp, mul_neg_one] at hmul
    simp only [boseFermiToggle, hpd, ↓reduceIte, hmul, neg_neg]
  · have hcop : Nat.Coprime d N.val.minFac := (hp.coprime_iff_not_dvd.mpr hpd).symm
    simp only [boseFermiToggle, hpd, ↓reduceIte]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, mul_neg_one]

/-- **Spector Eqs. (2.11)–(2.12), squarefree sector supertrace**:
For `1 < N.val`, the Bose–Fermi pairing involution `boseFermiToggle` cancels the
`N`-sector supertrace `∑_{d ∣ N, Squarefree d} μ(d) = 0`. -/
theorem spector_squarefree_divisor_sum_cancel {N : ℕ+} (hN : 1 < N.val) :
    (∑ d ∈ squarefreeDivisors N, ArithmeticFunction.moebius d) = 0 := by
  refine Finset.sum_involution (fun d _ => boseFermiToggle N d) ?_ ?_ ?_ ?_
  · intro d hd
    rw [moebius_boseFermiToggle hN hd, add_neg_cancel]
  · intro d hd _
    exact boseFermiToggle_ne hN hd
  · intro d hd
    exact boseFermiToggle_mem hN hd
  · intro d hd
    exact boseFermiToggle_involutive hN hd

/-- **Spector Eqs. (2.11)–(2.12), full divisor sum**:
`∑ d ∈ N.val.divisors, μ(d) = if N = 1 then 1 else 0`. -/
theorem spector_divisor_sum_moebius (N : ℕ+) :
    (∑ d ∈ N.val.divisors, ArithmeticFunction.moebius d) = if N = 1 then 1 else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not N.val.divisors Squarefree]
  have hnonSq :
      (∑ d ∈ N.val.divisors.filter (fun d => ¬ Squarefree d),
        ArithmeticFunction.moebius d) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    exact PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree (Finset.mem_filter.mp hd).2
  rw [hnonSq, add_zero]
  by_cases h1 : N = 1
  · subst h1
    rw [PNat.val_ofNat, Nat.divisors_one]
    rw [Finset.filter_eq_self.mpr (fun x hx => by simp at hx; subst hx; exact squarefree_one)]
    simp
  · have hN : 1 < N.val := lt_of_le_of_ne N.pos (fun h => h1 (PNat.coe_injective h.symm))
    simp only [h1, ↓reduceIte]
    exact spector_squarefree_divisor_sum_cancel hN

/-- Prime register of a positive integer `N : ℕ+`, linking `SpectorFockMobiusInversion`
to `PrimeBitWittenIndex`. -/
def primeRegisterOfPNat (N : ℕ+) : PrimeBitWittenIndex.PrimeRegister :=
  ⟨N.val.primeFactors, fun _ hp => Nat.prime_of_mem_primeFactors hp⟩

/-- Equivalence between `squarefreeDivisors N` supertrace and `PrimeBitWittenIndex`'s
squarefree powerset sum over `(primeRegisterOfPNat N).primes.powerset`. -/
theorem spector_squarefreeDivisors_eq_powerset_sum (N : ℕ+) :
    (∑ d ∈ squarefreeDivisors N, ArithmeticFunction.moebius d) =
      ∑ S ∈ (primeRegisterOfPNat N).primes.powerset,
        ArithmeticFunction.moebius (∏ p ∈ S, p) := by
  rw [squarefreeDivisors, Nat.sum_divisors_filter_squarefree N.pos.ne']
  have hset :
      (UniqueFactorizationMonoid.normalizedFactors N.val).toFinset =
        (primeRegisterOfPNat N).primes := by
    ext p
    rw [Multiset.mem_toFinset, UniqueFactorizationMonoid.mem_normalizedFactors_iff N.pos.ne',
      ← Nat.prime_iff]
    change (Nat.Prime p ∧ p ∣ N.val) ↔ p ∈ N.val.primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨fun ⟨hp, hdvd⟩ => ⟨hp, hdvd, N.pos.ne'⟩, fun ⟨hp, hdvd, _⟩ => ⟨hp, hdvd⟩⟩
  rw [hset]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']

/-- Alternative `PrimeBitWittenIndex`-linked proof of cancellation for `1 < N.val`. -/
theorem spector_squarefreeDivisors_cancel_via_primeBit {N : ℕ+} (hN : 1 < N.val) :
    (∑ d ∈ squarefreeDivisors N, ArithmeticFunction.moebius d) = 0 := by
  rw [spector_squarefreeDivisors_eq_powerset_sum]
  have hne : (primeRegisterOfPNat N).primes.Nonempty := by
    refine ⟨N.val.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime hN.ne', Nat.minFac_dvd N.val, N.pos.ne'⟩⟩
  exact PrimeBitWittenIndex.finite_divisor_mobius_sum_cancel (primeRegisterOfPNat N) hne

/-! ## Section 4: 3-Sector `(A, B, F)` Möbius Inversion & Thermal Expectation (§4, Eqs. 4.10–4.19) -/

/-- Constructive finite set of 3-sector `(A, B, F)` states in the `N`-level eigenspace:
`A * B * F = N` with `Squarefree F`. -/
def threeSectorSet (N : ℕ+) : Finset (ℕ × ℕ × ℕ) :=
  N.val.divisorsAntidiagonal.biUnion fun x =>
    (x.2.divisorsAntidiagonal.filter (fun y => Squarefree y.2)).image fun y => (x.1, y.1, y.2)

theorem mem_threeSectorSet {N : ℕ+} {t : ℕ × ℕ × ℕ} :
    t ∈ threeSectorSet N ↔
      0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
        t.1 * t.2.1 * t.2.2 = N.val ∧ Squarefree t.2.2 := by
  simp only [threeSectorSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Nat.mem_divisorsAntidiagonal, Prod.exists]
  constructor
  · rintro ⟨A, m, ⟨hAm, hN0⟩, B, F, ⟨⟨hBF, hm0⟩, hFsq⟩, hEq⟩
    have hEq' : (A, B, F) = (t.1, t.2.1, t.2.2) := hEq
    cases t with
    | mk t1 t2 =>
      cases t2 with
      | mk t21 t22 =>
        have h1 : A = t1 := congrArg Prod.fst hEq'
        have h2 : B = t21 := congrArg (fun p => p.2.1) hEq'
        have h3 : F = t22 := congrArg (fun p => p.2.2) hEq'
        subst h1; subst h2; subst h3
        have hA0 : A ≠ 0 := fun h => hN0 (by rw [← hAm, h, zero_mul])
        have hB0 : B ≠ 0 := fun h => hm0 (by rw [← hBF, h, zero_mul])
        have hF0 : F ≠ 0 := fun h => hm0 (by rw [← hBF, h, mul_zero])
        exact ⟨Nat.pos_of_ne_zero hA0, Nat.pos_of_ne_zero hB0, Nat.pos_of_ne_zero hF0,
          by rw [mul_assoc, hBF, hAm], hFsq⟩
  · rintro ⟨_, _, _, hprod, hFsq⟩
    refine ⟨t.1, t.2.1 * t.2.2, ⟨by rw [← mul_assoc, hprod], N.pos.ne'⟩,
      t.2.1, t.2.2, ⟨⟨rfl, ?_⟩, hFsq⟩, rfl⟩
    intro hm0
    exact N.pos.ne' (by rw [← hprod, mul_assoc, hm0, mul_zero])

/-- Equivalence between `threeSectorSet N` and 3-sector `ℕ+` triples `A * B * F = N`
with `Squarefree F`. -/
def threeSectorEquiv (N : ℕ+) :
    { t : ℕ × ℕ × ℕ // t ∈ threeSectorSet N } ≃
      { t : ℕ+ × ℕ+ × ℕ+ // t.1 * t.2.1 * t.2.2 = N ∧ Squarefree t.2.2.val } where
  toFun t :=
    let ht := mem_threeSectorSet.mp t.2
    ⟨(⟨t.1.1, ht.1⟩, ⟨t.1.2.1, ht.2.1⟩, ⟨t.1.2.2, ht.2.2.1⟩),
      ⟨PNat.coe_injective ht.2.2.2.1, ht.2.2.2.2⟩⟩
  invFun t :=
    ⟨(t.1.1.val, t.1.2.1.val, t.1.2.2.val),
      mem_threeSectorSet.mpr ⟨t.1.1.pos, t.1.2.1.pos, t.1.2.2.pos,
        congrArg PNat.val t.2.1, t.2.2⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, b, f⟩, ht⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨f, hf⟩⟩, ht⟩
    rfl

/-- Concrete `N = 12` 3-sector inhabitant `(A = 3, B = 2, F = 2)`. -/
theorem spectorThreeSector_12 : (3, 2, 2) ∈ threeSectorSet (12 : ℕ+) := by
  rw [mem_threeSectorSet]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact Nat.prime_two.squarefree

/-- 3-sector Fock-space supertrace at level `N` (Spector Eq. 4.13):
`∑_{A * B * F = N, Squarefree F} μ(F) • h(A)` over an arbitrary `[AddCommGroup R]`. -/
def threeSectorTrace {R : Type*} [AddCommGroup R] (h : ℕ → R) (N : ℕ+) : R :=
  ∑ t ∈ threeSectorSet N, ArithmeticFunction.moebius t.2.2 • h t.1

private theorem threeSectorTrace_eq_nested_antidiagonal {R : Type*} [AddCommGroup R]
    (h : ℕ → R) (N : ℕ+) :
    threeSectorTrace h N =
      ∑ x ∈ N.val.divisorsAntidiagonal,
        ∑ y ∈ x.2.divisorsAntidiagonal, ArithmeticFunction.moebius y.2 • h x.1 := by
  unfold threeSectorTrace
  have hdisj :
      (N.val.divisorsAntidiagonal : Set (ℕ × ℕ)).PairwiseDisjoint fun x =>
        (x.2.divisorsAntidiagonal.filter (fun y => Squarefree y.2)).image fun y => (x.1, y.1, y.2) := by
    intro x₁ _ x₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht₁ ht₂
    simp only [Finset.mem_image, Finset.mem_filter, Nat.mem_divisorsAntidiagonal,
      Prod.exists] at ht₁ ht₂
    rcases ht₁ with ⟨B₁, F₁, ⟨⟨hBF₁, _⟩, _⟩, hEq₁⟩
    rcases ht₂ with ⟨B₂, F₂, ⟨⟨hBF₂, _⟩, _⟩, hEq₂⟩
    have hEq := hEq₁.trans hEq₂.symm
    have hA : x₁.1 = x₂.1 := congrArg (Prod.fst : ℕ × ℕ × ℕ → ℕ) hEq
    have hB : B₁ = B₂ := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hEq
    have hF : F₁ = F₂ := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hEq
    apply hne
    ext
    · exact hA
    · rw [← hBF₁, ← hBF₂, hB, hF]
  rw [threeSectorSet, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image]
  · rw [← Finset.sum_filter_add_sum_filter_not x.2.divisorsAntidiagonal (fun y => Squarefree y.2)]
    have hzero :
        (∑ y ∈ x.2.divisorsAntidiagonal.filter (fun y => ¬ Squarefree y.2),
          ArithmeticFunction.moebius y.2 • h x.1) = 0 := by
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree (Finset.mem_filter.mp hy).2,
        zero_smul]
    rw [hzero, add_zero]
  · intro y₁ _ y₂ _ hEq
    have hB : y₁.1 = y₂.1 := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hEq
    have hF : y₁.2 = y₂.2 := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hEq
    exact Prod.ext hB hF

/-- **Spector Eqs. (4.14)–(4.16) (Grouping 1, by `A` and `(B, F)`)**:
`∑_{A B F = N} μ(F) • h(A) = h(N)`. -/
theorem threeSectorTrace_eq_self {R : Type*} [AddCommGroup R] (h : ℕ → R) (N : ℕ+) :
    threeSectorTrace h N = h N.val := by
  rw [threeSectorTrace_eq_nested_antidiagonal]
  have hinner :
      ∀ x ∈ N.val.divisorsAntidiagonal,
        (∑ y ∈ x.2.divisorsAntidiagonal, ArithmeticFunction.moebius y.2 • h x.1) =
          if x.2 = 1 then h N.val else 0 := by
    intro x hx
    rw [← Finset.sum_smul]
    have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hx).2
    let m : ℕ+ := ⟨x.2, hx2pos⟩
    have hm :
        (∑ y ∈ x.2.divisorsAntidiagonal, ArithmeticFunction.moebius y.2) =
          if m = 1 then 1 else 0 := by
      rw [Nat.sum_divisorsAntidiagonal' (f := fun _ b => ArithmeticFunction.moebius b)]
      exact spector_divisor_sum_moebius m
    rw [hm]
    by_cases hm1 : m = 1
    · have hx2 : x.2 = 1 := congrArg PNat.val hm1
      have hx1 : x.1 = N.val := by
        have hmul := (Nat.mem_divisorsAntidiagonal.mp hx).1
        simpa [hx2] using hmul
      simp [hm1, hx2, hx1]
    · have hx2 : x.2 ≠ 1 := fun h => hm1 (PNat.coe_injective h)
      simp [hm1, hx2]
  rw [Finset.sum_congr rfl hinner]
  have hmem : (N.val, 1) ∈ N.val.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one N.val, N.pos.ne'⟩
  rw [Finset.sum_eq_single (N.val, 1)]
  · simp
  · intro x hx hne
    by_cases hx2 : x.2 = 1
    · exfalso
      apply hne
      have hx1 : x.1 = N.val := by
        simpa [hx2] using (Nat.mem_divisorsAntidiagonal.mp hx).1
      exact Prod.ext hx1 hx2
    · simp [hx2]
  · intro habs
    exact False.elim (habs hmem)

/-- **Spector Eq. (4.17) (Grouping 2, by `F` and `(A, B)`)**:
`∑_{A B F = N} μ(F) • h(A) = ∑ F ∈ N.val.divisors, μ(F) • (∑ A ∈ (N.val / F).divisors, h A)`. -/
theorem threeSectorTrace_eq_moebius_divisorSum {R : Type*} [AddCommGroup R]
    (h : ℕ → R) (N : ℕ+) :
    threeSectorTrace h N =
      ∑ F ∈ N.val.divisors,
        ArithmeticFunction.moebius F • (∑ A ∈ (N.val / F).divisors, h A) := by
  rw [threeSectorTrace_eq_nested_antidiagonal]
  have hsigma :
      (∑ x ∈ N.val.divisorsAntidiagonal,
          ∑ y ∈ x.2.divisorsAntidiagonal, ArithmeticFunction.moebius y.2 • h x.1) =
        ∑ z ∈ N.val.divisorsAntidiagonal,
          ArithmeticFunction.moebius z.2 • (∑ w ∈ z.1.divisorsAntidiagonal, h w.1) := by
    simp_rw [Finset.smul_sum]
    have hL := Finset.sum_sigma' N.val.divisorsAntidiagonal (fun x => x.2.divisorsAntidiagonal)
        (fun x y => ArithmeticFunction.moebius y.2 • h x.1)
    have hR := Finset.sum_sigma' N.val.divisorsAntidiagonal (fun z => z.1.divisorsAntidiagonal)
        (fun z w => ArithmeticFunction.moebius z.2 • h w.1)
    rw [hL, hR]
    refine Finset.sum_bij
      (fun p _ => ⟨(p.1.1 * p.2.1, p.2.2), (p.1.1, p.2.1)⟩) ?_ ?_ ?_ ?_
    · rintro ⟨⟨A, m⟩, ⟨B, F⟩⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hp ⊢
      rcases hp with ⟨⟨hAm, hN0⟩, ⟨hBF, _⟩⟩
      refine ⟨⟨by rw [mul_assoc, hBF, hAm], hN0⟩, trivial, ?_⟩
      intro hAB0
      exact hN0 (by rw [← hAm, ← hBF, ← mul_assoc, hAB0, zero_mul])
    · rintro ⟨⟨A₁, m₁⟩, ⟨B₁, F₁⟩⟩ hp₁ ⟨⟨A₂, m₂⟩, ⟨B₂, F₂⟩⟩ hp₂ hEq
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hp₁ hp₂
      have hz := congrArg Sigma.fst hEq
      have hF : F₁ = F₂ := congrArg Prod.snd hz
      have hw : (A₁, B₁) = (A₂, B₂) := eq_of_heq (Sigma.ext_iff.mp hEq).2
      rcases Prod.mk.inj hw with ⟨rfl, rfl⟩
      have hm : m₁ = m₂ := by rw [← hp₁.2.1, ← hp₂.2.1, hF]
      subst hm; subst hF; rfl
    · rintro ⟨⟨m', F⟩, ⟨A, B⟩⟩ hq
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hq
      rcases hq with ⟨⟨hmF, hN0⟩, ⟨hAB, _⟩⟩
      refine ⟨⟨(A, B * F), (B, F)⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
        refine ⟨⟨by rw [← mul_assoc, hAB, hmF], hN0⟩, trivial, ?_⟩
        intro hBF0
        exact hN0 (by rw [← hmF, ← hAB, mul_assoc, hBF0, mul_zero])
      · exact Sigma.ext (Prod.ext hAB rfl) (heq_of_eq rfl)
    · rintro ⟨⟨A, m⟩, ⟨B, F⟩⟩ _
      rfl
  rw [hsigma]
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun a b => ArithmeticFunction.moebius b • (∑ w ∈ a.divisorsAntidiagonal, h w.1))]
  refine Finset.sum_congr rfl fun F _ => ?_
  congr 1
  exact Nat.sum_divisorsAntidiagonal (f := fun A _ => h A)

/-- **Way 3 (Grouping by `d = A * F`, with `B = N / d`)**:
`∑_{A B F = N} μ(F) • h(A) = ∑ d ∈ N.val.divisors, ∑ F ∈ d.divisors, μ(F) • h(d / F)`. -/
theorem threeSectorTrace_eq_divisorSum_moebius_div {R : Type*} [AddCommGroup R]
    (h : ℕ → R) (N : ℕ+) :
    threeSectorTrace h N =
      ∑ d ∈ N.val.divisors,
        ∑ F ∈ d.divisors, ArithmeticFunction.moebius F • h (d / F) := by
  rw [threeSectorTrace_eq_nested_antidiagonal]
  have hsigma :
      (∑ x ∈ N.val.divisorsAntidiagonal,
          ∑ y ∈ x.2.divisorsAntidiagonal, ArithmeticFunction.moebius y.2 • h x.1) =
        ∑ d ∈ N.val.divisorsAntidiagonal,
          ∑ w ∈ d.1.divisorsAntidiagonal, ArithmeticFunction.moebius w.2 • h w.1 := by
    have hL := Finset.sum_sigma' N.val.divisorsAntidiagonal (fun x => x.2.divisorsAntidiagonal)
        (fun x y => ArithmeticFunction.moebius y.2 • h x.1)
    have hR := Finset.sum_sigma' N.val.divisorsAntidiagonal (fun d => d.1.divisorsAntidiagonal)
        (fun _ w => ArithmeticFunction.moebius w.2 • h w.1)
    rw [hL, hR]
    refine Finset.sum_bij
      (fun p _ => ⟨(p.1.1 * p.2.2, p.2.1), (p.1.1, p.2.2)⟩) ?_ ?_ ?_ ?_
    · rintro ⟨⟨A, m⟩, ⟨B, F⟩⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hp ⊢
      rcases hp with ⟨⟨hAm, hN0⟩, ⟨hBF, _⟩⟩
      refine ⟨⟨by calc A * F * B = A * (B * F) := by ring
        _ = A * m := by rw [hBF]
        _ = N.val := hAm, hN0⟩, trivial, ?_⟩
      intro hAF0
      exact hN0 (by rw [← hAm, ← hBF]; calc A * (B * F) = A * F * B := by ring
        _ = 0 * B := by rw [hAF0]
        _ = 0 := zero_mul B)
    · rintro ⟨⟨A₁, m₁⟩, ⟨B₁, F₁⟩⟩ hp₁ ⟨⟨A₂, m₂⟩, ⟨B₂, F₂⟩⟩ hp₂ hEq
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hp₁ hp₂
      have hz := congrArg Sigma.fst hEq
      have hB : B₁ = B₂ := congrArg Prod.snd hz
      have hw : (A₁, F₁) = (A₂, F₂) := eq_of_heq (Sigma.ext_iff.mp hEq).2
      rcases Prod.mk.inj hw with ⟨rfl, rfl⟩
      have hm : m₁ = m₂ := by rw [← hp₁.2.1, ← hp₂.2.1, hB]
      subst hm; subst hB; rfl
    · rintro ⟨⟨d, B⟩, ⟨A, F⟩⟩ hq
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hq
      rcases hq with ⟨⟨hdB, hN0⟩, ⟨hAF, _⟩⟩
      refine ⟨⟨(A, B * F), (B, F)⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
        refine ⟨⟨by calc A * (B * F) = A * F * B := by ring
          _ = d * B := by rw [hAF]
          _ = N.val := hdB, hN0⟩, trivial, ?_⟩
        intro hBF0
        exact hN0 (by rw [← hdB, ← hAF]; calc A * F * B = A * (B * F) := by ring
          _ = A * 0 := by rw [hBF0]
          _ = 0 := mul_zero A)
      · exact Sigma.ext (Prod.ext hAF rfl) (heq_of_eq rfl)
    · rintro ⟨⟨A, m⟩, ⟨B, F⟩⟩ _
      rfl
  rw [hsigma]
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun d _ => ∑ w ∈ d.divisorsAntidiagonal, ArithmeticFunction.moebius w.2 • h w.1)]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact Nat.sum_divisorsAntidiagonal' (f := fun a b => ArithmeticFunction.moebius b • h a)

/-- **Spector Eqs. (4.18)–(4.19): 3-sector `(A, B, F)` Fock-space Möbius inversion**
over any `[AddCommGroup R]` (valid for arbitrary `ℕ+`-indexed operators/vectors). -/
theorem spector_three_sector_mobius_inversion {R : Type*} [AddCommGroup R]
    (g h : ℕ+ → R) :
    (∀ N : ℕ+, g N = ∑ d ∈ N.val.divisors.attach, h ⟨d.1, Nat.pos_of_mem_divisors d.2⟩) ↔
      (∀ N : ℕ+, h N = ∑ F ∈ N.val.divisors.attach,
        ArithmeticFunction.moebius F.1 •
          g ⟨N.val / F.1, Nat.div_pos (Nat.le_of_dvd N.pos (Nat.dvd_of_mem_divisors F.2))
            (Nat.pos_of_mem_divisors F.2)⟩) := by
  let extH : ℕ → R := fun n => if hn : 0 < n then h ⟨n, hn⟩ else 0
  let extG : ℕ → R := fun n => if hn : 0 < n then g ⟨n, hn⟩ else 0
  have hextH : ∀ n : ℕ+, extH n.val = h n := fun n => dite_eq_left n.pos
  have hextG : ∀ n : ℕ+, extG n.val = g n := fun n => dite_eq_left n.pos
  have hsumH :
      ∀ m : ℕ+, (∑ A ∈ m.val.divisors, extH A) =
        ∑ d ∈ m.val.divisors.attach, h ⟨d.1, Nat.pos_of_mem_divisors d.2⟩ := by
    intro m
    rw [← Finset.sum_attach (s := m.val.divisors) (f := extH)]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact dite_eq_left (Nat.pos_of_mem_divisors d.2)
  constructor
  · intro hg N
    have h1 := (threeSectorTrace_eq_self extH N).symm
    rw [threeSectorTrace_eq_moebius_divisorSum extH N] at h1
    rw [← hextH N, h1]
    rw [← Finset.sum_attach (s := N.val.divisors)]
    refine Finset.sum_congr rfl fun F _ => ?_
    have hdivpos : 0 < N.val / F.1 :=
      Nat.div_pos (Nat.le_of_dvd N.pos (Nat.dvd_of_mem_divisors F.2))
        (Nat.pos_of_mem_divisors F.2)
    let q : ℕ+ := ⟨N.val / F.1, hdivpos⟩
    have hsub : (∑ A ∈ (N.val / F.1).divisors, extH A) = g q := by
      change (∑ A ∈ q.val.divisors, extH A) = g q
      rw [hsumH q, hg q]
    rw [hsub]
  · intro hh N
    have h1 := (threeSectorTrace_eq_self extG N).symm
    rw [threeSectorTrace_eq_divisorSum_moebius_div extG N] at h1
    rw [← hextG N, h1]
    rw [← Finset.sum_attach (s := N.val.divisors)]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hdpos : 0 < d.1 := Nat.pos_of_mem_divisors d.2
    rw [hh ⟨d.1, hdpos⟩]
    rw [← Finset.sum_attach (s := d.1.divisors)]
    refine Finset.sum_congr rfl fun F _ => ?_
    have hFpos : 0 < F.1 := Nat.pos_of_mem_divisors F.2
    have hFdvd : F.1 ∣ d.1 := Nat.dvd_of_mem_divisors F.2
    have hdivpos : 0 < d.1 / F.1 := Nat.div_pos (Nat.le_of_dvd hdpos hFdvd) hFpos
    congr 1
    exact (dite_eq_left hdivpos).trans (congrArg g (PNat.coe_injective rfl))

/-- **Noncommutative `[Ring R]` 3-sector Möbius inversion** (preserving operator order,
with both left-scalar `(μ F : R) * g ...` and right-scalar `g ... * (μ F : R)` forms). -/
theorem spector_three_sector_mobius_inversion_ring {R : Type*} [Ring R]
    (g h : ℕ+ → R) :
    (∀ N : ℕ+, g N = ∑ d ∈ N.val.divisors.attach, h ⟨d.1, Nat.pos_of_mem_divisors d.2⟩) ↔
      (∀ N : ℕ+, h N = ∑ F ∈ N.val.divisors.attach,
        (ArithmeticFunction.moebius F.1 : R) *
          g ⟨N.val / F.1, Nat.div_pos (Nat.le_of_dvd N.pos (Nat.dvd_of_mem_divisors F.2))
            (Nat.pos_of_mem_divisors F.2)⟩) := by
  simpa only [zsmul_eq_mul] using spector_three_sector_mobius_inversion g h

theorem spector_three_sector_mobius_inversion_ring_right {R : Type*} [Ring R]
    (g h : ℕ+ → R) :
    (∀ N : ℕ+, g N = ∑ d ∈ N.val.divisors.attach, h ⟨d.1, Nat.pos_of_mem_divisors d.2⟩) ↔
      (∀ N : ℕ+, h N = ∑ F ∈ N.val.divisors.attach,
        g ⟨N.val / F.1, Nat.div_pos (Nat.le_of_dvd N.pos (Nat.dvd_of_mem_divisors F.2))
          (Nat.pos_of_mem_divisors F.2)⟩ * (ArithmeticFunction.moebius F.1 : R)) := by
  rw [spector_three_sector_mobius_inversion_ring]
  refine ⟨fun hh N => ?_, fun hh N => ?_⟩
  · rw [hh N]
    refine Finset.sum_congr rfl fun F _ => ?_
    exact Int.cast_commute (ArithmeticFunction.moebius F.1) _
  · rw [hh N]
    refine Finset.sum_congr rfl fun F _ => ?_
    exact (Int.cast_commute (ArithmeticFunction.moebius F.1) _).symm

/-- **Spector Eq. (4.10), finite-stage thermal expectation identity**:
Over `[AddCommGroup R] [Module ℝ R]`, for finite cutoffs `M, K : ℕ` (`1 ≤ K`) and
`E_bf 1 = 0`, the `(B, F)` supertrace decouples and collapses to `1`:
`Tr_s(h̃ e^{-β(H_a + H_b + H_f)}) = Tr(h̃ e^{-β H_a})`. -/
theorem spector_thermal_expectation_finite {R : Type*} [AddCommGroup R] [Module ℝ R]
    (M K : ℕ) (hK : 1 ≤ K) (β : ℝ) (E_a E_bf : ℕ+ → ℝ) (hE_bf1 : E_bf 1 = 0)
    (h : ℕ+ → R) :
    (∑ A ∈ (Finset.Icc 1 M).attach,
      ∑ m ∈ (Finset.Icc 1 K).attach,
        ∑ y ∈ m.1.divisorsAntidiagonal,
          (ArithmeticFunction.moebius y.2 : ℝ) •
            (Real.exp (-β * (E_a ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩ +
                E_bf ⟨m.1, (Finset.mem_Icc.mp m.2).1⟩)) •
              h ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩)) =
      ∑ A ∈ (Finset.Icc 1 M).attach,
        Real.exp (-β * E_a ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩) •
          h ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩ := by
  refine Finset.sum_congr rfl fun A _ => ?_
  have hm_term :
      ∀ m ∈ (Finset.Icc 1 K).attach,
        (∑ y ∈ m.1.divisorsAntidiagonal,
          (ArithmeticFunction.moebius y.2 : ℝ) •
            (Real.exp (-β * (E_a ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩ +
                E_bf ⟨m.1, (Finset.mem_Icc.mp m.2).1⟩)) •
              h ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩)) =
          if m.1 = 1 then
            Real.exp (-β * E_a ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩) •
              h ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩
          else 0 := by
    intro m _
    rw [← Finset.sum_smul]
    let mPos : ℕ+ := ⟨m.1, (Finset.mem_Icc.mp m.2).1⟩
    have hm_sum :
        (∑ y ∈ m.1.divisorsAntidiagonal, (ArithmeticFunction.moebius y.2 : ℝ)) =
          if mPos = 1 then 1 else 0 := by
      have hZ := spector_divisor_sum_moebius mPos
      rw [← Nat.sum_divisorsAntidiagonal' (f := fun _ b => ArithmeticFunction.moebius b)] at hZ
      have hR := congrArg (Int.cast (R := ℝ)) hZ
      push_cast at hR
      exact hR
    rw [hm_sum]
    by_cases hm1 : mPos = 1
    · have hm1' : m.1 = 1 := congrArg PNat.val hm1
      have hm_eq : (⟨m.1, (Finset.mem_Icc.mp m.2).1⟩ : ℕ+) = 1 := hm1
      rw [hm_eq]
      simp only [hm1, hm1', ↓reduceIte, one_smul]
      exact congrArg (fun x : ℝ => Real.exp (-β * x) • h ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩)
        ((congrArg (fun y : ℝ => E_a ⟨A.1, (Finset.mem_Icc.mp A.2).1⟩ + y) hE_bf1).trans
          (add_zero _))
    · have hm1' : m.1 ≠ 1 := fun h => hm1 (PNat.coe_injective h)
      simp [hm1, hm1']
  rw [Finset.sum_congr rfl hm_term]
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_refl 1, hK⟩
  rw [Finset.sum_eq_single ⟨1, h1mem⟩]
  · simp
  · intro m _ hne
    have hm1' : m.1 ≠ 1 := fun h => hne (Subtype.ext h)
    simp [hm1']
  · intro habs
    exact False.elim (habs (Finset.mem_attach _ ⟨1, h1mem⟩))

/-- **Spector Eq. (4.10), infinite summable `tsum` thermal expectation identity**:
Over `[NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]`, for summable
`A`-sector thermal operator trace and `(B, F)`-sector partition weight with `E_bf 1 = 0`,
`Tr_s(h̃ e^{-β(H_a + H_b + H_f)}) = Tr(h̃ e^{-β H_a})`. -/
theorem spector_thermal_expectation_tsum {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
    (β : ℝ) (E_a E_bf : ℕ+ → ℝ) (hE_bf1 : E_bf 1 = 0) (h : ℕ+ → R)
    (hSumA : Summable fun A : ℕ+ => ‖Real.exp (-β * E_a A) • h A‖)
    (hSumBF : Summable fun p : ℕ+ × { F : ℕ+ // Squarefree F.val } =>
      Real.exp (-β * E_bf (p.1 * p.2.1))) :
    (∑' x : ℕ+ × (ℕ+ × { F : ℕ+ // Squarefree F.val }),
      (ArithmeticFunction.moebius x.2.2.1.val : ℝ) •
        (Real.exp (-β * (E_a x.1 + E_bf (x.2.1 * x.2.2.1))) • h x.1)) =
      ∑' A : ℕ+, Real.exp (-β * E_a A) • h A := by
  let fBF : ℕ+ × { F : ℕ+ // Squarefree F.val } → ℝ := fun p =>
    (ArithmeticFunction.moebius p.2.1.val : ℝ) * Real.exp (-β * E_bf (p.1 * p.2.1))
  let fA : ℕ+ → R := fun A => Real.exp (-β * E_a A) • h A
  have hBF_norm : Summable fun p => ‖fBF p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hSumBF
    have hμ : ‖(ArithmeticFunction.moebius p.2.1.val : ℝ)‖ ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := p.2.1.val)
      rw [Real.norm_eq_abs]
      exact_mod_cast this
    calc
      ‖fBF p‖ = ‖(ArithmeticFunction.moebius p.2.1.val : ℝ)‖ * ‖Real.exp (-β * E_bf (p.1 * p.2.1))‖ :=
        norm_mul _ _
      _ ≤ 1 * Real.exp (-β * E_bf (p.1 * p.2.1)) := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_right hμ (Real.exp_pos _).le
      _ = Real.exp (-β * E_bf (p.1 * p.2.1)) := one_mul _
  have hAnorm : Summable fun A => ‖fA A‖ := hSumA
  have hSummBF : Summable fBF := hBF_norm.of_norm
  have hSummA : Summable fA := hSumA.of_norm
  have hSummProd_norm : Summable fun x : (ℕ+ × { F : ℕ+ // Squarefree F.val }) × ℕ+ =>
      ‖fBF x.1 • fA x.2‖ := by
    have hmul := Summable.mul_of_nonneg hBF_norm hAnorm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    simpa only [norm_smul] using hmul
  have hSummProd : Summable fun x : (ℕ+ × { F : ℕ+ // Squarefree F.val }) × ℕ+ =>
      fBF x.1 • fA x.2 := hSummProd_norm.of_norm
  have hrew' :
      (∑' x : ℕ+ × (ℕ+ × { F : ℕ+ // Squarefree F.val }),
        (ArithmeticFunction.moebius x.2.2.1.val : ℝ) •
          (Real.exp (-β * (E_a x.1 + E_bf (x.2.1 * x.2.2.1))) • h x.1)) =
        (∑' p : ℕ+ × { F : ℕ+ // Squarefree F.val }, fBF p) • (∑' A : ℕ+, fA A) := by
    have hprod_eq :
        (∑' x : ℕ+ × (ℕ+ × { F : ℕ+ // Squarefree F.val }),
          (ArithmeticFunction.moebius x.2.2.1.val : ℝ) •
            (Real.exp (-β * (E_a x.1 + E_bf (x.2.1 * x.2.2.1))) • h x.1)) =
          ∑' x : (ℕ+ × { F : ℕ+ // Squarefree F.val }) × ℕ+, fBF x.1 • fA x.2 := by
      have hcomm := Equiv.tsum_eq (Equiv.prodComm (ℕ+ × { F : ℕ+ // Squarefree F.val }) ℕ+)
        (fun x : ℕ+ × (ℕ+ × { F : ℕ+ // Squarefree F.val }) =>
          (ArithmeticFunction.moebius x.2.2.1.val : ℝ) •
            (Real.exp (-β * (E_a x.1 + E_bf (x.2.1 * x.2.2.1))) • h x.1))
      rw [← hcomm]
      refine tsum_congr fun x => ?_
      dsimp [fBF, fA]
      rw [smul_smul, smul_smul]
      congr 1
      rw [mul_add, Real.exp_add]
      ring
    rw [hprod_eq]
    exact (tsum_smul_tsum hSummBF hSummA hSummProd).symm
  rw [hrew']
  have hBF_fib :
      (∑' p : ℕ+ × { F : ℕ+ // Squarefree F.val }, fBF p) = 1 := by
    have hfib := (hSummBF.hasSum.tsum_fiberwise (fun p : ℕ+ × { F : ℕ+ // Squarefree F.val } => p.1 * p.2.1)).tsum_eq
    rw [← hfib]
    have hfiber_val :
        ∀ K : ℕ+,
          (∑' p : (fun p : ℕ+ × { F : ℕ+ // Squarefree F.val } => p.1 * p.2.1) ⁻¹' {K},
            fBF p.1) = if K = 1 then 1 else 0 := by
      intro K
      let mkBF : { x : ℕ // x ∈ K.val.divisors.filter Squarefree } →
          ℕ+ × { F : ℕ+ // Squarefree F.val } := fun d =>
        (⟨K.val / d.1, Nat.div_pos (Nat.le_of_dvd K.pos
            (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp d.2).1))
          (Nat.pos_of_mem_divisors (Finset.mem_filter.mp d.2).1)⟩,
         ⟨⟨d.1, Nat.pos_of_mem_divisors (Finset.mem_filter.mp d.2).1⟩,
          (Finset.mem_filter.mp d.2).2⟩)
      let S : Finset (ℕ+ × { F : ℕ+ // Squarefree F.val }) :=
        (K.val.divisors.filter Squarefree).attach.map
          ⟨mkBF, fun d₁ d₂ hEq => by
            apply Subtype.ext
            exact congrArg (fun p : ℕ+ × { F : ℕ+ // Squarefree F.val } => p.2.1.val) hEq⟩
      have hpre : (fun p : ℕ+ × { F : ℕ+ // Squarefree F.val } => p.1 * p.2.1) ⁻¹' {K} = (S : Set _) := by
        ext ⟨B, ⟨F, hFsq⟩⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, S, Finset.mem_map,
          Finset.mem_attach, true_and, Subtype.exists]
        constructor
        · intro hBF
          have hFdvd : F.val ∣ K.val := ⟨B.val, by rw [mul_comm]; exact congrArg PNat.val hBF.symm⟩
          have hFmem : F.val ∈ K.val.divisors.filter Squarefree :=
            Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hFdvd, K.pos.ne'⟩, hFsq⟩
          refine ⟨F.val, hFmem, ?_⟩
          have hmul : B.val * F.val = K.val := congrArg PNat.val hBF
          apply Prod.ext
          · apply PNat.coe_injective
            change K.val / F.val = B.val
            exact Nat.div_eq_of_eq_mul_left F.pos hmul.symm
          · apply Subtype.ext
            apply PNat.coe_injective
            rfl
        · rintro ⟨d, hd, hEq⟩
          have hB : B.val = K.val / d := congrArg (fun p => p.1.val) hEq.symm
          have hF : F.val = d := congrArg (fun p => p.2.1.val) hEq.symm
          have hdvd : d ∣ K.val := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
          apply PNat.coe_injective
          change B.val * F.val = K.val
          rw [hB, hF]
          exact Nat.div_mul_cancel hdvd
      rw [hpre, Finset.tsum_subtype' S fBF, Finset.sum_map]
      have hsum_eq :
          (∑ d ∈ (K.val.divisors.filter Squarefree).attach, fBF (mkBF d)) =
            (∑ d ∈ squarefreeDivisors K, (ArithmeticFunction.moebius d : ℝ)) *
              Real.exp (-β * E_bf K) := by
        rw [Finset.sum_mul]
        rw [← Finset.sum_attach (s := squarefreeDivisors K)]
        refine Finset.sum_congr rfl fun d _ => ?_
        have hmulK : (mkBF d).1 * (mkBF d).2.1 = K := by
          apply PNat.coe_injective
          exact Nat.div_mul_cancel (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp d.2).1)
        change (ArithmeticFunction.moebius d.1 : ℝ) * Real.exp (-β * E_bf ((mkBF d).1 * (mkBF d).2.1)) =
          (ArithmeticFunction.moebius d.1 : ℝ) * Real.exp (-β * E_bf K)
        rw [hmulK]
      change (∑ d ∈ (K.val.divisors.filter Squarefree).attach, fBF (mkBF d)) = _
      rw [hsum_eq]
      have hsup :
          (∑ d ∈ squarefreeDivisors K, (ArithmeticFunction.moebius d : ℝ)) =
            if K = 1 then 1 else 0 := by
        have hZ := spector_divisor_sum_moebius K
        have hsqZ : (∑ d ∈ squarefreeDivisors K, ArithmeticFunction.moebius d) =
            ∑ d ∈ K.val.divisors, ArithmeticFunction.moebius d := by
          rw [← Finset.sum_filter_add_sum_filter_not K.val.divisors Squarefree]
          have hzero :
              (∑ d ∈ K.val.divisors.filter (fun d => ¬ Squarefree d),
                ArithmeticFunction.moebius d) = 0 :=
            Finset.sum_eq_zero fun d hd =>
              PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree (Finset.mem_filter.mp hd).2
          rw [hzero, add_zero, squarefreeDivisors]
        rw [← hsqZ] at hZ
        have hR := congrArg (Int.cast (R := ℝ)) hZ
        push_cast at hR
        exact hR
      rw [hsup]
      by_cases hK1 : K = 1
      · subst hK1; simp [hE_bf1]
      · simp [hK1]
    rw [tsum_congr hfiber_val]
    rw [tsum_eq_single (1 : ℕ+) (fun K hK => by simp [hK])]
    simp
  rw [hBF_fib, one_smul]

/-! ## Section 5: Totally Multiplicative Inverse Series & Totient Supertrace (§3, Eqs. 3.7–3.9) -/

/-- **Spector Eqs. (3.7)–(3.8): Totally multiplicative inverse series**:
If `M : ℕ → ℂ` satisfies `M 0 = 0`, `M 1 = 1`, `M (a * b) = M a * M b` for `0 < a, b`,
and `Summable (fun n => ‖M n‖)`, then
`(∑' n, M n) * (∑' n, (μ n : ℂ) * M n) = 1`. -/
theorem spector_totally_multiplicative_inverse_series
    (M : ℕ → ℂ) (hM0 : M 0 = 0) (hM1 : M 1 = 1)
    (hMmul : ∀ a b : ℕ, 0 < a → 0 < b → M (a * b) = M a * M b)
    (hMsum : Summable fun n => ‖M n‖) :
    (∑' n : ℕ, M n) * (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * M n) = 1 := by
  let G : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ) * M n
  have hG0 : G 0 = 0 := by simp [G]
  have hGnorm : Summable fun n => ‖G n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hMsum
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    calc
      ‖G n‖ = ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖M n‖ := norm_mul _ _
      _ ≤ 1 * ‖M n‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖M n‖ := one_mul _
  have hSummM : Summable M := hMsum.of_norm
  have hSummG : Summable G := hGnorm.of_norm
  have htermM : LSeries.term M 0 = M := by
    ext n
    by_cases hn : n = 0
    · simp [hn, hM0]
    · simp [LSeries.term_of_ne_zero hn]
  have htermG : LSeries.term G 0 = G := by
    ext n
    by_cases hn : n = 0
    · simp [hn, hG0]
    · simp [LSeries.term_of_ne_zero hn]
  have hLM : LSeriesSummable M 0 := by
    rw [LSeriesSummable, htermM]
    exact hSummM
  have hLG : LSeriesSummable G 0 := by
    rw [LSeriesSummable, htermG]
    exact hSummG
  have hLvalM : LSeries M 0 = ∑' n : ℕ, M n := by
    simp [LSeries, htermM]
  have hLvalG : LSeries G 0 = ∑' n : ℕ, G n := by
    simp [LSeries, htermG]
  have hconv : LSeries.convolution M G = LSeries.delta := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.delta]
    · rw [LSeries.convolution_def]
      dsimp only
      have hterm :
          ∀ p ∈ n.divisorsAntidiagonal,
            M p.1 * G p.2 = (ArithmeticFunction.moebius p.2 : ℂ) * M n := by
        intro p hp
        obtain ⟨hp_mul, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
        obtain ⟨hp1, hp2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
        dsimp [G]
        rw [mul_left_comm, ← hMmul p.1 p.2 (Nat.pos_of_ne_zero hp1) (Nat.pos_of_ne_zero hp2),
          hp_mul]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      have hsum_div :
          (∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.2 : ℂ)) =
            if (⟨n, Nat.pos_of_ne_zero hn⟩ : ℕ+) = 1 then 1 else 0 := by
        have hZ := spector_divisor_sum_moebius ⟨n, Nat.pos_of_ne_zero hn⟩
        rw [← Nat.sum_divisorsAntidiagonal' (f := fun _ b => ArithmeticFunction.moebius b)] at hZ
        have hC := congrArg (Int.cast (R := ℂ)) hZ
        push_cast at hC
        exact hC
      rw [hsum_div]
      by_cases hn1 : n = 1
      · subst hn1
        have h1 : (⟨1, Nat.pos_of_ne_zero hn⟩ : ℕ+) = 1 := rfl
        simp [h1, hM1, LSeries.delta]
      · have hne : (⟨n, Nat.pos_of_ne_zero hn⟩ : ℕ+) ≠ 1 :=
          fun h => hn1 (congrArg PNat.val h)
        simp [hne, hn1, LSeries.delta]
  calc
    (∑' n : ℕ, M n) * (∑' n : ℕ, G n) = LSeries M 0 * LSeries G 0 := by
      rw [hLvalM, hLvalG]
    _ = LSeries (LSeries.convolution M G) 0 := (LSeries_convolution' hLM hLG).symm
    _ = LSeries LSeries.delta 0 := by rw [hconv]
    _ = 1 := by rw [LSeries_delta]; rfl

/-- Specialization of `spector_totally_multiplicative_inverse_series` to `M n = n ^ (-s)`
for `1 < s.re`, linked directly to `ActualRiemannZetaMobiusLSeriesBridge`. -/
theorem spector_zeta_mobius_inverse_series {s : ℂ} (hs : 1 < s.re) :
    let M : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
    (∑' n : ℕ, M n) * (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * M n) = 1 ∧
      (∑' n : ℕ, M n) = riemannZeta s ∧
      (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * M n) =
        LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  intro M
  have hM0 : M 0 = 0 := by simp [M]
  have hM1 : M 1 = 1 := by simp [M]
  have hMmul : ∀ a b : ℕ, 0 < a → 0 < b → M (a * b) = M a * M b := by
    intro a b ha hb
    have hab : a * b ≠ 0 := Nat.mul_ne_zero ha.ne' hb.ne'
    simp only [M, ha.ne', hb.ne', hab, ↓reduceIte, Nat.cast_mul]
    exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-s)
  have hMsum : Summable fun n => ‖M n‖ := by
    have hZ : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
      ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    have hnorm : Summable fun n => ‖LSeries.term (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s n‖ :=
      hZ.norm
    refine hnorm.congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn, M]
    · simp [hn, M, LSeries.term_of_ne_zero, ArithmeticFunction.zeta_apply, Complex.cpow_neg]
  have hinv := spector_totally_multiplicative_inverse_series M hM0 hM1 hMmul hMsum
  have hzeta : (∑' n : ℕ, M n) = riemannZeta s := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    simp only [LSeries]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn, M]
    · simp [hn, M, LSeries.term_of_ne_zero, ArithmeticFunction.zeta_apply, Complex.cpow_neg]
  have hmob :
      (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * M n) =
        LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
    simp only [LSeries]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn, M]
    · simp [hn, M, LSeries.term_of_ne_zero, Complex.cpow_neg, div_eq_mul_inv]
  have hbridge := ActualRiemannZetaMobiusLSeriesBridge.actualRiemannZeta_mul_mobius_LSeries_eq_one hs
  have hmob_coe :
      (⇑(ArithmeticFunction.moebius : ArithmeticFunction ℂ)) =
        fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) := by
    ext n
    exact ArithmeticFunction.intCoe_apply
  rw [hmob_coe] at hbridge
  rw [← hzeta, ← hmob] at hbridge
  exact ⟨hbridge, hzeta, hmob⟩

/-- **Spector Eq. (3.9): Totient supertrace**:
`Φ(s, N) = ∑_{d ∣ N} μ(d) * (N / d) ^ s`. -/
def spectorPhi (s : ℂ) (N : ℕ+) : ℂ :=
  ∑ d ∈ N.val.divisors, (ArithmeticFunction.moebius d : ℂ) * ((N.val / d : ℕ) : ℂ) ^ s

/-- Fock-state trace equality for `s = β * ω` (`spectorPhi ((β * ω : ℝ) : ℂ) N`):
restricts to `squarefreeDivisors N` and equals `∑' d∣N, Squarefree d` with bosonic
Boltzmann weight `exp(β * (ω * log (N / d)))`. -/
theorem spectorPhi_eq_fock_supertrace (β ω : ℝ) (N : ℕ+) :
    spectorPhi ((β * ω : ℝ) : ℂ) N =
      ∑ d ∈ squarefreeDivisors N,
        (ArithmeticFunction.moebius d : ℂ) *
          (Real.exp (β * (ω * Real.log ((N.val / d : ℕ) : ℝ))) : ℂ) := by
  unfold spectorPhi
  rw [← Finset.sum_filter_add_sum_filter_not N.val.divisors Squarefree]
  have hzero :
      (∑ d ∈ N.val.divisors.filter (fun d => ¬ Squarefree d),
        (ArithmeticFunction.moebius d : ℂ) * ((N.val / d : ℕ) : ℂ) ^ ((β * ω : ℝ) : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree (Finset.mem_filter.mp hd).2]
    simp
  rw [hzero, add_zero, squarefreeDivisors]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ N.val := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hqpos : 0 < N.val / d := Nat.div_pos (Nat.le_of_dvd N.pos hdvd) hdpos
  have hqR : (0 : ℝ) < ((N.val / d : ℕ) : ℝ) := by exact_mod_cast hqpos
  congr 1
  rw [← Complex.ofReal_natCast (N.val / d), ← Complex.ofReal_cpow hqR.le (β * ω),
    Real.rpow_def_of_pos hqR]
  congr 1
  ring

/-- **Spector Eq. (3.9): Totient theorem `Φ(1, N) = φ(N)`**. -/
theorem spectorPhi_one_eq_totient (N : ℕ+) :
    spectorPhi 1 N = (Nat.totient N.val : ℂ) := by
  unfold spectorPhi
  simp_rw [Complex.cpow_one]
  rw [← Nat.sum_divisorsAntidiagonal (f := fun a b => (ArithmeticFunction.moebius a : ℂ) * (b : ℂ))]
  have htot :
      ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, (Nat.totient d : ℂ) = (n : ℂ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  have hmob := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ)
    (f := fun n => (Nat.totient n : ℂ)) (g := fun n => (n : ℂ))).mp htot N.val N.pos
  exact hmob

/-! ## Section 6: Dirichlet Derivative & `OperatorDirichlet.logMul` Bridge (§3, Eq. 3.10) -/

/-- Bosonic Hamiltonian expectation `⟨N | h̃ H_b | N⟩ = (ω * log N) • h(N)` for an
arithmetic operator `h : ArithmeticFunction A` (`[Ring A] [Algebra ℝ A]`). -/
def bosonicHamExpectation {A : Type*} [Ring A] [Algebra ℝ A]
    (ω : ℝ) (h : ArithmeticFunction A) (N : ℕ+) : A :=
  (ω * Real.log (N.val : ℝ)) • h N.val

/-- Spector Eq. (3.10) Dirichlet derivative `h'(N) = -(1/ω) ⟨N | h̃ H_b | N⟩`. -/
def spectorDirichletDeriv {A : Type*} [Ring A] [Algebra ℝ A]
    (ω : ℝ) (h : ArithmeticFunction A) (N : ℕ+) : A :=
  (-ω⁻¹) • bosonicHamExpectation ω h N

/-- `⟨N | h̃ H_b | N⟩ = ω • logMul h N`. -/
theorem bosonicHamExpectation_eq_smul_logMul {A : Type*} [Ring A] [Algebra ℝ A]
    (ω : ℝ) (h : ArithmeticFunction A) (N : ℕ+) :
    bosonicHamExpectation ω h N =
      ω • InfoGeometry.OperatorAlgebra.OperatorDirichlet.logMul h N.val := by
  simp [bosonicHamExpectation, InfoGeometry.OperatorAlgebra.OperatorDirichlet.logMul_apply, mul_smul]

/-- **Spector Eq. (3.10)** linked directly to `OperatorDirichlet.logMul`:
for `ω ≠ 0`, `-(1/ω) ⟨N | h̃ H_b | N⟩ = -(logMul h N)`. -/
theorem spectorDirichletDeriv_eq_neg_logMul {A : Type*} [Ring A] [Algebra ℝ A]
    {ω : ℝ} (hω : ω ≠ 0) (h : ArithmeticFunction A) (N : ℕ+) :
    spectorDirichletDeriv ω h N =
      -(InfoGeometry.OperatorAlgebra.OperatorDirichlet.logMul h N.val) := by
  rw [spectorDirichletDeriv, bosonicHamExpectation_eq_smul_logMul, smul_smul, neg_mul,
    inv_mul_cancel₀ hω, neg_one_smul]

/-- Product-rule linkage with `OperatorDirichlet.logMul_mul`. -/
theorem spectorDirichletDeriv_mul {A : Type*} [Ring A] [Algebra ℝ A]
    {ω : ℝ} (hω : ω ≠ 0) (f g : ArithmeticFunction A) (N : ℕ+) :
    spectorDirichletDeriv ω (f * g) N =
      -(InfoGeometry.OperatorAlgebra.OperatorDirichlet.logMul f * g +
        f * InfoGeometry.OperatorAlgebra.OperatorDirichlet.logMul g) N.val := by
  rw [spectorDirichletDeriv_eq_neg_logMul hω (f * g) N,
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.logMul_mul]

/-- Prime-mode expansion of `⟨N | h̃ H_b | N⟩` via `PrimeBosonFermionGas.log_prod_prime_pow_of_prime`:
`⟨N | h̃ H_b | N⟩ = (∑ p ∈ N.val.factorization.support, v_p(N) * (ω log p)) • h(N)`. -/
theorem bosonicHamExpectation_prime_mode_expansion {A : Type*} [Ring A] [Algebra ℝ A]
    (ω : ℝ) (h : ArithmeticFunction A) (N : ℕ+) :
    bosonicHamExpectation ω h N =
      (∑ p ∈ N.val.factorization.support,
        (N.val.factorization p : ℝ) * (ω * Real.log (p : ℝ))) • h N.val := by
  have hprime : ∀ p ∈ N.val.factorization.support, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprod :
      (N.val : ℝ) = ∏ p ∈ N.val.factorization.support, (p : ℝ) ^ (N.val.factorization p) := by
    have hnat : N.val = ∏ p ∈ N.val.factorization.support, p ^ (N.val.factorization p) :=
      (Nat.prod_factorization_pow_eq_self N.pos.ne').symm
    conv_lhs => rw [hnat]
    push_cast
    rfl
  have hlog :
      Real.log (N.val : ℝ) =
        ∑ p ∈ N.val.factorization.support, (N.val.factorization p : ℝ) * Real.log (p : ℝ) := by
    rw [hprod]
    exact PrimeBosonFermionGas.log_prod_prime_pow_of_prime
      N.val.factorization.support N.val.factorization hprime
  rw [bosonicHamExpectation, hlog, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => by ring

/-! ## Section 7: OpenGauss `T16` Non-Commutativity Witnesses & Concrete `N = 12` Matrix Check -/

/-- `T16` non-commutativity ground witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem exists_noncomm_mat2c_pair :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨InfoGeometry.Algebra.FiniteSpin.J_plus,
   InfoGeometry.Algebra.FiniteSpin.J_minus,
   InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Operator-Dirichlet matrix generator `J₊` placed at `n = 1`. -/
def spectorDirichletJPlus : ArithmeticFunction (Matrix (Fin 2) (Fin 2) ℂ) :=
  InfoGeometry.OperatorAlgebra.OperatorDirichlet.atOne InfoGeometry.Algebra.FiniteSpin.J_plus

/-- Operator-Dirichlet matrix generator `J₋` placed at `n = 1`. -/
def spectorDirichletJMinus : ArithmeticFunction (Matrix (Fin 2) (Fin 2) ℂ) :=
  InfoGeometry.OperatorAlgebra.OperatorDirichlet.atOne InfoGeometry.Algebra.FiniteSpin.J_minus

/-- `T16` non-commutativity witness in `ArithmeticFunction (Matrix (Fin 2) (Fin 2) ℂ)`. -/
theorem spector_dirichlet_noncomm_witness :
    spectorDirichletJPlus * spectorDirichletJMinus ≠
      spectorDirichletJMinus * spectorDirichletJPlus := by
  intro h
  have h1 := congrArg (fun F : ArithmeticFunction (Matrix (Fin 2) (Fin 2) ℂ) => F 1) h
  simp only [spectorDirichletJPlus, spectorDirichletJMinus,
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.atOne_mul_atOne_one] at h1
  exact InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne h1

/-- Concrete noncommutative matrix-valued `ℕ+`-indexed operator `h_mat : ℕ+ → Mat2C`. -/
def spectorMatrixTestOp (n : ℕ+) : Matrix (Fin 2) (Fin 2) ℂ :=
  if n = 1 then InfoGeometry.Algebra.FiniteSpin.J_plus else InfoGeometry.Algebra.FiniteSpin.J_minus

/-- `spectorMatrixTestOp` has non-commuting values at `1` and `2`. -/
theorem spectorMatrixTestOp_noncomm :
    spectorMatrixTestOp (1 : ℕ+) * spectorMatrixTestOp (2 : ℕ+) ≠
      spectorMatrixTestOp (2 : ℕ+) * spectorMatrixTestOp (1 : ℕ+) := by
  simp only [spectorMatrixTestOp, ↓reduceIte]
  have h21 : (2 : ℕ+) ≠ 1 := by decide
  simp only [h21, ↓reduceIte]
  exact InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne

/-- Concrete `N = 12` noncommutative 3-sector Möbius inversion witness on
`Matrix (Fin 2) (Fin 2) ℂ`: for `g(N) = ∑_{d∣N} spectorMatrixTestOp(d)`,
`spectorMatrixTestOp(12) = ∑_{F∣12} μ(F) * g(12 / F)`. -/
theorem spector_three_sector_mobius_inversion_mat12 :
    let g : ℕ+ → Matrix (Fin 2) (Fin 2) ℂ := fun N =>
      ∑ d ∈ N.val.divisors.attach, spectorMatrixTestOp ⟨d.1, Nat.pos_of_mem_divisors d.2⟩
    spectorMatrixTestOp (12 : ℕ+) =
      ∑ F ∈ ((12 : ℕ+).val.divisors.attach),
        (ArithmeticFunction.moebius F.1 : Matrix (Fin 2) (Fin 2) ℂ) *
          g ⟨(12 : ℕ+).val / F.1,
            Nat.div_pos (Nat.le_of_dvd (12 : ℕ+).pos (Nat.dvd_of_mem_divisors F.2))
              (Nat.pos_of_mem_divisors F.2)⟩ := by
  intro g
  exact (spector_three_sector_mobius_inversion_ring g spectorMatrixTestOp).mp
    (fun _ => rfl) (12 : ℕ+)

end

end InfoGeometry.Arithmetic.SpectorFockMobiusInversion
