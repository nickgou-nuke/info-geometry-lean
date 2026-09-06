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

/-- Invariant packet at one finite stage of an inductive operator chain. -/
structure SupergradedInvariantAt (A : Type*) [Ring A] where
  is_odd : A → Prop
  is_even : A → Prop
  is_central : A → Prop
  odd_nilpotency : ∀ x, is_odd x → x * x = 0
  odd_odd_closure : ∀ x y, is_odd x → is_odd y → is_even (x * y + y * x)
  central_lane : ∀ c x, is_central c → c * x = x * c
  projector_identity : ∃ P, is_even P ∧ P * P = P

/--
Bonding intertwiner between two stages; transports the grading/central lanes.
-/
structure BondingIntertwiner
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A) (invB : SupergradedInvariantAt B) where
  map : A →+* B
  preserves_odd : ∀ x, invA.is_odd x → invB.is_odd (map x)
  preserves_even : ∀ x, invA.is_even x → invB.is_even (map x)
  preserves_central : ∀ c, invA.is_central c → invB.is_central (map c)

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
