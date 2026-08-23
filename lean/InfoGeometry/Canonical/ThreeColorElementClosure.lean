import InfoGeometry.Canonical.ZornChiralPeirceDecomposition

/-!
# Element-level closure of the three-colour split-octonion basis

The eight chiral Peirce generators already span the whole Zorn carrier.  This
owner makes the corresponding closure statement explicit: adjoining all
commutators and anticommutators therefore adds no element directions.  Larger
Lie algebras arise only after multiplication expressions are externalised as
linear operators.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

variable {R : Type*} [CommRing R]

def chiralBasisSet : Set (ZornMatrix R) :=
  ({zornPlus} : Set (ZornMatrix R)) ∪
    {zornMinus} ∪ Set.range chiralUpperBasis ∪ Set.range chiralLowerBasis

def chiralBasisSpan : Submodule R (ZornMatrix R) :=
  Submodule.span R (chiralBasisSet (R := R))

def elementCommutator (x y : ZornMatrix R) : ZornMatrix R := x * y - y * x

def elementAnticommutator (x y : ZornMatrix R) : ZornMatrix R := x * y + y * x

def commutatorClosureSet (W : Submodule R (ZornMatrix R)) : Set (ZornMatrix R) :=
  {z | ∃ x ∈ W, ∃ y ∈ W, z = elementCommutator x y}

def anticommutatorClosureSet (W : Submodule R (ZornMatrix R)) : Set (ZornMatrix R) :=
  {z | ∃ x ∈ W, ∃ y ∈ W, z = elementAnticommutator x y}

def elementClosureStep (W : Submodule R (ZornMatrix R)) : Submodule R (ZornMatrix R) :=
  W ⊔ Submodule.span R
    (commutatorClosureSet W ∪ anticommutatorClosureSet W)

def elementClosure : ℕ → Submodule R (ZornMatrix R)
  | 0 => chiralBasisSpan (R := R)
  | n + 1 => elementClosureStep (elementClosure n)

theorem mul_mem_of_commutator_mem_anticommutator_mem
    {R : Type*} [Field R] [CharZero R]
    (W : Submodule R (ZornMatrix R))
    {x y : ZornMatrix R}
    (hcomm : elementCommutator x y ∈ W)
    (hanti : elementAnticommutator x y ∈ W) :
    x * y ∈ W := by
  have hsum :
      elementCommutator x y + elementAnticommutator x y =
        (2 : R) • (x * y) := by
    simp [elementCommutator, elementAnticommutator, two_smul]
  have htwo : (2 : R) ≠ 0 := by norm_num
  have hrecover :
      x * y = (2 : R)⁻¹ •
        (elementCommutator x y + elementAnticommutator x y) := by
    rw [hsum, smul_smul]
    simp [htwo]
  rw [hrecover]
  exact W.smul_mem (2 : R)⁻¹ (W.add_mem hcomm hanti)

theorem chiralBasisSpan_eq_top :
    chiralBasisSpan (R := R) = ⊤ := by
  apply top_unique
  intro Z hZ
  rw [zorn_peirce_decomposition Z]
  have hPlus : zornPlus (R := R) ∈ chiralBasisSpan (R := R) :=
    Submodule.subset_span (by simp [chiralBasisSet])
  have hMinus : zornMinus (R := R) ∈ chiralBasisSpan (R := R) :=
    Submodule.subset_span (by simp [chiralBasisSet])
  have hUpper (i : Fin 3) : chiralUpperBasis i ∈ chiralBasisSpan (R := R) :=
    Submodule.subset_span (by simp [chiralBasisSet])
  have hLower (i : Fin 3) : chiralLowerBasis i ∈ chiralBasisSpan (R := R) :=
    Submodule.subset_span (by simp [chiralBasisSet])
  have hUpperSum :
      (∑ i : Fin 3, Z.x i • chiralUpperBasis i) ∈
        chiralBasisSpan (R := R) := by
    exact (chiralBasisSpan (R := R)).sum_mem (fun i hi =>
      (chiralBasisSpan (R := R)).smul_mem (Z.x i) (hUpper i))
  have hLowerSum :
      (∑ i : Fin 3, Z.y i • chiralLowerBasis i) ∈
        chiralBasisSpan (R := R) := by
    exact (chiralBasisSpan (R := R)).sum_mem (fun i hi =>
      (chiralBasisSpan (R := R)).smul_mem (Z.y i) (hLower i))
  have hpp : peirceComponent zornPlus zornPlus Z ∈
      chiralBasisSpan (R := R) := by
    rw [peirce_plus_plus_apply]
    convert (chiralBasisSpan (R := R)).smul_mem Z.a hPlus using 1
    · apply ZornMatrix.ext
      · simp [zornPlus]
      · simp [zornPlus]
      · funext i
        change 0 = Z.a • (0 : R)
        simp
      · funext i
        change 0 = Z.a • (0 : R)
        simp
  have hmm : peirceComponent zornMinus zornMinus Z ∈
      chiralBasisSpan (R := R) := by
    rw [peirce_minus_minus_apply]
    convert (chiralBasisSpan (R := R)).smul_mem Z.b hMinus using 1
    · apply ZornMatrix.ext
      · simp [zornMinus]
      · simp [zornMinus]
      · funext i
        change 0 = Z.b • (0 : R)
        simp
      · funext i
        change 0 = Z.b • (0 : R)
        simp
  have hcolor : colorProject Z ∈ chiralBasisSpan (R := R) := by
    rw [colorProject_eq_chiralUpper_sum]
    exact hUpperSum
  have hanticolor : anticolorProject Z ∈ chiralBasisSpan (R := R) := by
    rw [anticolorProject_eq_chiralLower_sum]
    exact hLowerSum
  exact (chiralBasisSpan (R := R)).add_mem
    ((chiralBasisSpan (R := R)).add_mem
      ((chiralBasisSpan (R := R)).add_mem hpp hcolor) hanticolor) hmm

theorem chiralBasisSpan_mem_commutatorClosureSet
    {x y : ZornMatrix R}
    (hx : x ∈ chiralBasisSpan (R := R))
    (hy : y ∈ chiralBasisSpan (R := R)) :
    elementCommutator x y ∈ commutatorClosureSet (chiralBasisSpan (R := R)) := by
  exact ⟨x, hx, y, hy, rfl⟩

theorem chiralBasisSpan_mem_anticommutatorClosureSet
    {x y : ZornMatrix R}
    (hx : x ∈ chiralBasisSpan (R := R))
    (hy : y ∈ chiralBasisSpan (R := R)) :
    elementAnticommutator x y ∈ anticommutatorClosureSet
      (chiralBasisSpan (R := R)) := by
  exact ⟨x, hx, y, hy, rfl⟩

theorem elementClosureStep_chiralBasisSpan_eq :
    elementClosureStep (chiralBasisSpan (R := R)) =
      chiralBasisSpan (R := R) := by
  rw [chiralBasisSpan_eq_top (R := R)]
  simp [elementClosureStep]

theorem elementClosure_zero_eq_top :
    elementClosure (R := R) 0 = ⊤ := by
  exact chiralBasisSpan_eq_top (R := R)

theorem elementClosure_succ_eq_top (n : ℕ) :
    elementClosure (R := R) (n + 1) = ⊤ := by
  induction n with
  | zero =>
      change elementClosureStep (chiralBasisSpan (R := R)) = ⊤
      rw [elementClosureStep_chiralBasisSpan_eq (R := R)]
      exact chiralBasisSpan_eq_top (R := R)
  | succ n ih =>
      rw [elementClosure]
      rw [ih]
      simp [elementClosureStep]

theorem elementClosure_eq_top (n : ℕ) :
    elementClosure (R := R) n = ⊤ := by
  cases n with
  | zero => exact elementClosure_zero_eq_top (R := R)
  | succ n => exact elementClosure_succ_eq_top (R := R) n

theorem elementClosure_eq_initial_span (n : ℕ) :
    elementClosure (R := R) n = chiralBasisSpan (R := R) := by
  rw [elementClosure_eq_top (R := R) n, chiralBasisSpan_eq_top (R := R)]

end InfoGeometry.Canonical
