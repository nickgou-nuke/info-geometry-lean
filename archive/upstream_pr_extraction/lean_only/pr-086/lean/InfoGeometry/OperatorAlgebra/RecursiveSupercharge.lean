import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.OperatorAlgebra.SupergradedClosure
import InfoGeometry.Canonical.ErlangenInductiveClosure

namespace InfoGeometry.OperatorAlgebra.RecursiveSupercharge
open InfoGeometry.OperatorAlgebra.SupergradedClosure

/--
The square of a recursively extended odd supercharge.

For `Qnext = Q + R`, the new square is the old square plus the
odd--odd cross bracket plus the new square.
-/
@[rep_depth thermo]
theorem recursive_supercharge_square
    {A : Type*} [Ring A]
    (Q R : A) :
    (Q + R) * (Q + R) =
      Q * Q + (Q * R + R * Q) + R * R := by
  noncomm_ring

/--
If both odd layers are nilpotent, the recursive supercharge square is exactly
the odd--odd anticommutator.
-/
@[rep_depth thermo]
theorem recursive_nilpotent_supercharge_square_eq_anticommutator
    {A : Type*} [Ring A]
    {Q R : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0) :
    (Q + R) * (Q + R) = Q * R + R * Q := by
  calc
    (Q + R) * (Q + R)
        = Q * Q + (Q * R + R * Q) + R * R := by
          exact recursive_supercharge_square Q R
    _ = 0 + (Q * R + R * Q) + 0 := by
          rw [hQ, hR]
    _ = Q * R + R * Q := by
          simp

/--
Central-charge extraction from two nilpotent recursive supercharges.
-/
@[rep_depth thermo]
theorem recursive_nilpotent_supercharge_square_eq_centralCharge
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z) :
    (Q + R) * (Q + R) = Z := by
  rw [recursive_nilpotent_supercharge_square_eq_anticommutator hQ hR]
  exact hZ

/--
If the odd--odd cross bracket is a central element `Z`, then the recursive
supercharge square is central.
-/
@[rep_depth thermo]
theorem recursive_supercharge_square_is_central
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z)
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ X : A, ((Q + R) * (Q + R)) * X = X * ((Q + R) * (Q + R)) := by
  intro X
  rw [recursive_nilpotent_supercharge_square_eq_centralCharge hQ hR hZ]
  exact hCentral X

/--
Finite three-layer expansion: next step toward recursive supercharge towers.
-/
@[rep_depth thermo]
theorem three_supercharge_square
    {A : Type*} [Ring A]
    (Q₁ Q₂ Q₃ : A) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) =
      Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
  noncomm_ring

/--
Odd-odd anticommutator.
-/
@[rep_depth thermo]
def oddAnticomm {A : Type*} [Ring A] (X Y : A) : A := X * Y + Y * X

/--
Finite four-layer supercharge square expansion.

This is the explicit cutoff-4 recursive tower identity:
diagonal squares plus all pairwise odd-odd anticommutators.
-/
@[rep_depth thermo]
theorem four_supercharge_square
    {A : Type*} [Ring A]
    (Q₁ Q₂ Q₃ Q₄ : A) :
    (Q₁ + Q₂ + Q₃ + Q₄) * (Q₁ + Q₂ + Q₃ + Q₄) =
      (Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃ + Q₄ * Q₄)
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₁ * Q₄ + Q₄ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂)
      + (Q₂ * Q₄ + Q₄ * Q₂)
      + (Q₃ * Q₄ + Q₄ * Q₃) := by
  noncomm_ring

/--
Finite four-layer nilpotent reduction:
if `Qᵢ^2=0` for all four odd generators, the square is exactly the sum of
pairwise odd-odd anticommutators.
-/
@[rep_depth thermo]
theorem four_nilpotent_supercharge_square_eq_pairwise_oddAnticomm
    {A : Type*} [Ring A]
    {Q₁ Q₂ Q₃ Q₄ : A}
    (h₁ : Q₁ * Q₁ = 0)
    (h₂ : Q₂ * Q₂ = 0)
    (h₃ : Q₃ * Q₃ = 0)
    (h₄ : Q₄ * Q₄ = 0) :
    (Q₁ + Q₂ + Q₃ + Q₄) * (Q₁ + Q₂ + Q₃ + Q₄) =
      oddAnticomm Q₁ Q₂
      + oddAnticomm Q₁ Q₃
      + oddAnticomm Q₁ Q₄
      + oddAnticomm Q₂ Q₃
      + oddAnticomm Q₂ Q₄
      + oddAnticomm Q₃ Q₄ := by
  calc
    (Q₁ + Q₂ + Q₃ + Q₄) * (Q₁ + Q₂ + Q₃ + Q₄)
        =
      (Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃ + Q₄ * Q₄)
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₁ * Q₄ + Q₄ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂)
      + (Q₂ * Q₄ + Q₄ * Q₂)
      + (Q₃ * Q₄ + Q₄ * Q₃) := by
          exact four_supercharge_square Q₁ Q₂ Q₃ Q₄
    _ =
      (0 + 0 + 0 + 0)
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₁ * Q₄ + Q₄ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂)
      + (Q₂ * Q₄ + Q₄ * Q₂)
      + (Q₃ * Q₄ + Q₄ * Q₃) := by
          rw [h₁, h₂, h₃, h₄]
    _ =
      oddAnticomm Q₁ Q₂
      + oddAnticomm Q₁ Q₃
      + oddAnticomm Q₁ Q₄
      + oddAnticomm Q₂ Q₃
      + oddAnticomm Q₂ Q₄
      + oddAnticomm Q₃ Q₄ := by
          simp [oddAnticomm, add_assoc, add_left_comm, add_comm]

/--
Finite `N=2` graded-SUSY closure:
for odd charges `Q₁,Q₂` with `Qᵢ²=0`, the extended square is exactly the
odd-odd anticommutator.
-/
@[rep_depth thermo]
theorem n2_supercharge_square_eq_oddAnticomm
    {A : Type*} [Ring A]
    {Q₁ Q₂ : A}
    (hQ₁ : Q₁ * Q₁ = 0)
    (hQ₂ : Q₂ * Q₂ = 0) :
    (Q₁ + Q₂) * (Q₁ + Q₂) = oddAnticomm Q₁ Q₂ := by
  simpa [oddAnticomm] using
    recursive_nilpotent_supercharge_square_eq_anticommutator (Q := Q₁) (R := Q₂) hQ₁ hQ₂

/--
Finite `N=2` closure with explicit even/central split in the odd-odd bracket:
if `{Q₁,Q₂} = H + Z`, then `(Q₁+Q₂)^2 = H + Z`.
-/
@[rep_depth thermo]
theorem n2_supercharge_square_eq_hamiltonian_plus_central
    {A : Type*} [Ring A]
    {Q₁ Q₂ H Z : A}
    (hQ₁ : Q₁ * Q₁ = 0)
    (hQ₂ : Q₂ * Q₂ = 0)
    (hsplit : oddAnticomm Q₁ Q₂ = H + Z) :
    (Q₁ + Q₂) * (Q₁ + Q₂) = H + Z := by
  calc
    (Q₁ + Q₂) * (Q₁ + Q₂) = oddAnticomm Q₁ Q₂ := by
      exact n2_supercharge_square_eq_oddAnticomm (Q₁ := Q₁) (Q₂ := Q₂) hQ₁ hQ₂
    _ = H + Z := hsplit

/--
Duality transport of odd-odd anticommutators across a ring equivalence.
-/
@[rep_depth thermo]
theorem duality_transport_oddAnticomm
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B) (X Y : A) :
    Dual (oddAnticomm X Y) = oddAnticomm (Dual X) (Dual Y) := by
  simp [oddAnticomm, map_add, map_mul]

/--
Duality transport of finite `N=2` square closure:
if `(Q₁+Q₂)^2 = H + Z` in `A`, then the transported charges satisfy
the same closure in `B`.
-/
@[rep_depth thermo]
theorem duality_transport_n2_square_closure
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B)
    {Q₁ Q₂ H Z : A}
    (hclosure : (Q₁ + Q₂) * (Q₁ + Q₂) = H + Z) :
    (Dual Q₁ + Dual Q₂) * (Dual Q₁ + Dual Q₂) = Dual H + Dual Z := by
  simpa [map_add, map_mul] using congrArg Dual hclosure

/--
Duality transport preserves centrality of the transported central term.
-/
@[rep_depth thermo]
theorem duality_transport_centrality
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B)
    {Z : A}
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ Y : B, Dual Z * Y = Y * Dual Z := by
  intro Y
  rcases Dual.surjective Y with ⟨X, rfl⟩
  simpa [map_mul] using congrArg Dual (hCentral X)

/--
Dimension doubling identity for the finite Bott ladder:
`2^(n+1) = 2 * 2^n`.
-/
@[rep_depth thermo]
theorem two_pow_succ (n : ℕ) :
    2 ^ (n + 1) = 2 * 2 ^ n := by
  simpa [pow_succ, Nat.mul_comm] using (pow_succ 2 n).symm

/--
Two Bott steps: `2^(n+2) = 4 * 2^n`.
-/
@[rep_depth thermo]
theorem two_pow_add_two (n : ℕ) :
    2 ^ (n + 2) = 4 * 2 ^ n := by
  calc
    2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by simpa [Nat.add_assoc] using two_pow_succ (n + 1)
    _ = 2 * (2 * 2 ^ n) := by rw [two_pow_succ n]
    _ = 4 * 2 ^ n := by ring

/--
Factorwise odd-odd anticommutator on product rings.

This is the finite tensor surrogate:
`{(x₁,x₂),(y₁,y₂)} = ({x₁,y₁},{x₂,y₂})`.
-/
@[rep_depth thermo]
theorem oddAnticomm_prod_factorwise
    {A B : Type*} [Ring A] [Ring B]
    (x₁ y₁ : A) (x₂ y₂ : B) :
    oddAnticomm (A := A × B) (x₁, x₂) (y₁, y₂) =
      (oddAnticomm (A := A) x₁ y₁, oddAnticomm (A := B) x₂ y₂) := by
  simp [oddAnticomm, Prod.snd_mul, Prod.fst_mul, Prod.snd_add, Prod.fst_add]

/--
Finite Bott/tensor step for `N=2` closure:
if closure holds in `A` and in `B`, it holds in `A × B`.
-/
@[rep_depth thermo]
theorem supergradedClosureAt_prod
    {A B : Type*} [Ring A] [Ring B]
    {QA QAsharp : A} {QB QBsharp : B}
    (hA : SupergradedClosureAt (R := A) QA QAsharp)
    (hB : SupergradedClosureAt (R := B) QB QBsharp) :
    SupergradedClosureAt (R := A × B) (QA, QB) (QAsharp, QBsharp) := by
  rcases hA with ⟨hA1, hA2, hA3, hA4⟩
  rcases hB with ⟨hB1, hB2, hB3, hB4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext <;> simp [SupergradedClosureAt, hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4]

/--
Central-charge transport under finite tensor/product step:
if each side has an odd-odd split `{Q,Q♯}=H+Z`, the product side has
componentwise split.
-/
@[rep_depth thermo]
theorem n2_hamiltonian_central_split_prod
    {A B : Type*} [Ring A] [Ring B]
    {QA QAsharp HA ZA : A}
    {QB QBsharp HB ZB : B}
    (hA : oddAnticomm (A := A) QA QAsharp = HA + ZA)
    (hB : oddAnticomm (A := B) QB QBsharp = HB + ZB) :
    oddAnticomm (A := A × B) (QA, QB) (QAsharp, QBsharp) =
      (HA, HB) + (ZA, ZB) := by
  ext
  · simpa [oddAnticomm] using hA
  · simpa [oddAnticomm] using hB

/--
Indexed formal inductive chain (`A₀ → A₁ → A₂ → …`) via bonding maps.
-/
@[rep_depth thermo]
structure IndexedInductiveChain where
  Stage : ℕ → Type*
  step : ∀ n, Stage n → Stage (n + 1)

namespace IndexedInductiveChain

variable (C : IndexedInductiveChain)

/--
Iterated embedding from stage `0` to stage `n`.
-/
@[rep_depth thermo]
def iterEmbed : ∀ n, C.Stage 0 → C.Stage n
  | 0, x => x
  | n + 1, x => C.step n (iterEmbed n x)

/--
Stepwise preservation of a symmetry-adapted local invariant.
-/
@[rep_depth thermo]
def Preserves (Inv : ∀ n, C.Stage n → Prop) : Prop :=
  ∀ n x, Inv n x → Inv (n + 1) (C.step n x)

/--
If an invariant is true at stage `0` and preserved by each bonding map,
it is true along the full finite inductive chain.
-/
@[rep_depth thermo]
theorem invariant_along_chain
    (Inv : ∀ n, C.Stage n → Prop)
    (hPres : C.Preserves Inv)
    {x0 : C.Stage 0}
    (h0 : Inv 0 x0) :
    ∀ n, Inv n (C.iterEmbed n x0) := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      exact hPres n (C.iterEmbed n x0) ih

/--
Two invariants preserved stepwise are preserved jointly along the chain.
-/
@[rep_depth thermo]
theorem invariant_pair_along_chain
    (Inv₁ Inv₂ : ∀ n, C.Stage n → Prop)
    (hPres₁ : C.Preserves Inv₁)
    (hPres₂ : C.Preserves Inv₂)
    {x0 : C.Stage 0}
    (h0₁ : Inv₁ 0 x0)
    (h0₂ : Inv₂ 0 x0) :
    ∀ n, Inv₁ n (C.iterEmbed n x0) ∧ Inv₂ n (C.iterEmbed n x0) := by
  intro n
  constructor
  · exact C.invariant_along_chain Inv₁ hPres₁ h0₁ n
  · exact C.invariant_along_chain Inv₂ hPres₂ h0₂ n

end IndexedInductiveChain

/-!
The finite invariant packet and its transition map are owned by the
Erlangen inductive-closure module. These aliases preserve the historical
RecursiveSupercharge API while ensuring both subsystems use the same native
structure and proof fields.
-/
abbrev SupergradedInvariantAt (A : Type*) [Ring A] :=
  InfoGeometry.Canonical.ErlangenInductiveClosure.SupergradedClosureAt A

abbrev BondingIntertwiner
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A) (invB : SupergradedInvariantAt B) :=
  InfoGeometry.Canonical.ErlangenInductiveClosure.BondingIntertwiner invA invB

/--
Core transport lemma: odd nilpotency is stable under a valid bonding intertwiner.
-/
@[rep_depth thermo]
theorem invariant_transport_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A)
    (invB : SupergradedInvariantAt B)
    (f : BondingIntertwiner invA invB)
    (x : A) (hx : invA.is_odd x) :
    (f.map x) * (f.map x) = 0 := by
  have h_odd_map : invB.is_odd (f.map x) := f.preserves_odd x hx
  exact invB.odd_nilpotency (f.map x) h_odd_map

/--
Transport of odd-odd closure through a bonding intertwiner.
-/
@[rep_depth thermo]
theorem oddOdd_closure_transport
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A)
    (invB : SupergradedInvariantAt B)
    (f : BondingIntertwiner invA invB)
    (x y : A) (hx : invA.is_odd x) (hy : invA.is_odd y) :
    invB.is_even ((f.map x) * (f.map y) + (f.map y) * (f.map x)) := by
  have hx' : invB.is_odd (f.map x) := f.preserves_odd x hx
  have hy' : invB.is_odd (f.map y) := f.preserves_odd y hy
  simpa [map_add, map_mul] using invB.odd_odd_closure (f.map x) (f.map y) hx' hy'

/--
Transport of central-lane commutation through a bonding intertwiner.
-/
@[rep_depth thermo]
theorem central_lane_transport
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A)
    (invB : SupergradedInvariantAt B)
    (f : BondingIntertwiner invA invB)
    (c x : A) (hc : invA.is_central c) :
    (f.map c) * (f.map x) = (f.map x) * (f.map c) := by
  have hc' : invB.is_central (f.map c) := f.preserves_central c hc
  exact invB.central_lane (f.map c) (f.map x) hc'

/--
Finite chain packet: each stage has an invariant packet and each edge is a
bonding intertwiner.
-/
structure FiniteInvariantChain where
  Stage : ℕ → Type*
  stageRing : ∀ n, Ring (Stage n)
  Invariant : ∀ n, SupergradedInvariantAt (Stage n)
  Bonding :
    ∀ n,
      @BondingIntertwiner
        (Stage n) (Stage (n + 1))
        (stageRing n) (stageRing (n + 1))
        (Invariant n) (Invariant (n + 1))

attribute [instance] FiniteInvariantChain.stageRing

namespace FiniteInvariantChain

variable (C : FiniteInvariantChain)

/-- Iterated embedding map from stage `0` into stage `n`. -/
def iterMap : ∀ n, C.Stage 0 → C.Stage n
  | 0, x => x
  | n + 1, x => (C.Bonding n).map (iterMap n x)

/-- Stagewise odd invariance along the inductive chain. -/
@[rep_depth thermo]
theorem odd_preserved_along_chain
    {x0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_odd x0) :
    ∀ n, (C.Invariant n).is_odd (C.iterMap n x0) := by
  intro n
  induction n with
  | zero =>
      simpa using hx0
  | succ n ih =>
      exact (C.Bonding n).preserves_odd _ ih

/-- Stagewise odd nilpotency along the inductive chain. -/
@[rep_depth thermo]
theorem odd_nilpotent_along_chain
    {x0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_odd x0) :
    ∀ n, (C.iterMap n x0) * (C.iterMap n x0) = 0 := by
  intro n
  have hodd : (C.Invariant n).is_odd (C.iterMap n x0) := C.odd_preserved_along_chain hx0 n
  exact (C.Invariant n).odd_nilpotency (C.iterMap n x0) hodd
end FiniteInvariantChain

end InfoGeometry.OperatorAlgebra.RecursiveSupercharge
