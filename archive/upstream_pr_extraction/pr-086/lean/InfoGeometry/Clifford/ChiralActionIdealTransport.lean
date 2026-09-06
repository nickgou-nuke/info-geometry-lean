import InfoGeometry.Clifford.SplitOctonionChiralLeftIdeals

/-!
# Ideal transport for the existing chained chiral-action algebras

The left and right chained-action algebras are different subalgebra carriers.
The existing Cayley-conjugation algebra equivalence transports principal
ideals between them.  This file records only that transport; it introduces no
new ideal carrier.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

open Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

abbrev LeftActionAlgebra :=
  ↥chiralCayleyChainedLeftActionAlgebra

abbrev RightActionAlgebra :=
  ↥chiralCayleyChainedRightActionAlgebra

theorem chiralCayleyChainedActionAlgEquiv_map_principalLeftIdeal
    (f : LeftActionAlgebra) :
    chiralCayleyChainedActionAlgEquiv ''
        (Set.range (fun a : LeftActionAlgebra => a * f)) =
      Set.range (fun b : RightActionAlgebra =>
        b * chiralCayleyChainedActionAlgEquiv f) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv a, ?_⟩
    rw [map_mul]
  · rintro ⟨b, rfl⟩
    let y : LeftActionAlgebra :=
      chiralCayleyChainedActionAlgEquiv.symm
        (b * chiralCayleyChainedActionAlgEquiv f)
    refine ⟨y, ?_, ?_⟩
    · refine ⟨chiralCayleyChainedActionAlgEquiv.symm b, ?_⟩
      apply chiralCayleyChainedActionAlgEquiv.injective
      simp [y, map_mul]
    · simp [y]

theorem chiralCayleyChainedActionAlgEquiv_principalLeftIdeal_iff
    (f : LeftActionAlgebra)
    (x : RightActionAlgebra) :
    x ∈ Set.range (fun b : RightActionAlgebra =>
      b * chiralCayleyChainedActionAlgEquiv f) ↔
      chiralCayleyChainedActionAlgEquiv.symm x ∈
        Set.range (fun a : LeftActionAlgebra => a * f) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv.symm b, ?_⟩
    simpa using congrArg chiralCayleyChainedActionAlgEquiv.symm hb
  · rintro ⟨a, ha⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv a, ?_⟩
    simpa using congrArg chiralCayleyChainedActionAlgEquiv ha

theorem chiralCayleyChainedActionAlgEquiv_map_principalRightIdeal
    (f : LeftActionAlgebra) :
    chiralCayleyChainedActionAlgEquiv ''
        (Set.range (fun a : LeftActionAlgebra => f * a)) =
      Set.range (fun b : RightActionAlgebra =>
        chiralCayleyChainedActionAlgEquiv f * b) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv a, ?_⟩
    rw [map_mul]
  · rintro ⟨b, rfl⟩
    let y : LeftActionAlgebra :=
      chiralCayleyChainedActionAlgEquiv.symm
        (chiralCayleyChainedActionAlgEquiv f * b)
    refine ⟨y, ?_, ?_⟩
    · refine ⟨chiralCayleyChainedActionAlgEquiv.symm b, ?_⟩
      apply chiralCayleyChainedActionAlgEquiv.injective
      simp [y, map_mul]
    · simp [y]

theorem chiralCayleyChainedActionAlgEquiv_symm_map_principalLeftIdeal
    (f : RightActionAlgebra) :
    chiralCayleyChainedActionAlgEquiv.symm ''
        (Set.range (fun b : RightActionAlgebra => b * f)) =
      Set.range (fun a : LeftActionAlgebra =>
        a * chiralCayleyChainedActionAlgEquiv.symm f) := by
  ext x
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv.symm b, ?_⟩
    rw [map_mul]
  · rintro ⟨a, rfl⟩
    let y : RightActionAlgebra :=
      chiralCayleyChainedActionAlgEquiv
        (a * chiralCayleyChainedActionAlgEquiv.symm f)
    refine ⟨y, ?_, ?_⟩
    · refine ⟨chiralCayleyChainedActionAlgEquiv a, ?_⟩
      apply chiralCayleyChainedActionAlgEquiv.symm.injective
      simp [y, map_mul]
    · simp [y]

theorem chiralCayleyChainedActionAlgEquiv_symm_map_principalRightIdeal
    (f : RightActionAlgebra) :
    chiralCayleyChainedActionAlgEquiv.symm ''
        (Set.range (fun b : RightActionAlgebra => f * b)) =
      Set.range (fun a : LeftActionAlgebra =>
        chiralCayleyChainedActionAlgEquiv.symm f * a) := by
  ext x
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv.symm b, ?_⟩
    rw [map_mul]
  · rintro ⟨a, rfl⟩
    let y : RightActionAlgebra :=
      chiralCayleyChainedActionAlgEquiv
        (chiralCayleyChainedActionAlgEquiv.symm f * a)
    refine ⟨y, ?_, ?_⟩
    · refine ⟨chiralCayleyChainedActionAlgEquiv a, ?_⟩
      apply chiralCayleyChainedActionAlgEquiv.symm.injective
      simp [y, map_mul]
    · simp [y, map_mul]

theorem chiralCayleyChainedActionAlgEquiv_map_peirceCorner
    (f g : LeftActionAlgebra)
    {x : LeftActionAlgebra}
    (hx : f * x * g = x) :
    chiralCayleyChainedActionAlgEquiv f *
        chiralCayleyChainedActionAlgEquiv x *
        chiralCayleyChainedActionAlgEquiv g =
      chiralCayleyChainedActionAlgEquiv x := by
  rw [← map_mul, ← map_mul, hx]

theorem chiralCayleyChainedActionAlgEquiv_map_peirceCorner_iff
    (f g : LeftActionAlgebra)
    (x : LeftActionAlgebra) :
    f * x * g = x ↔
      chiralCayleyChainedActionAlgEquiv f *
          chiralCayleyChainedActionAlgEquiv x *
          chiralCayleyChainedActionAlgEquiv g =
        chiralCayleyChainedActionAlgEquiv x := by
  constructor
  · exact chiralCayleyChainedActionAlgEquiv_map_peirceCorner f g
  · intro hx
    have h := congrArg chiralCayleyChainedActionAlgEquiv.symm hx
    simpa using h

theorem chiralCayleyChainedActionAlgEquiv_map_twoSidedGenerators
    (f : LeftActionAlgebra) :
    chiralCayleyChainedActionAlgEquiv ''
        (Set.range (fun p :
          LeftActionAlgebra × LeftActionAlgebra => p.1 * f * p.2)) =
      Set.range (fun p :
        RightActionAlgebra × RightActionAlgebra =>
            p.1 * chiralCayleyChainedActionAlgEquiv f * p.2) := by
  ext x
  constructor
  · rintro ⟨y, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    refine ⟨⟨chiralCayleyChainedActionAlgEquiv a,
      chiralCayleyChainedActionAlgEquiv b⟩, ?_⟩
    rw [map_mul, map_mul]
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨chiralCayleyChainedActionAlgEquiv.symm
        (a * chiralCayleyChainedActionAlgEquiv f * b), ?_, ?_⟩
    · refine ⟨⟨chiralCayleyChainedActionAlgEquiv.symm a,
          chiralCayleyChainedActionAlgEquiv.symm b⟩, ?_⟩
      simp [map_mul]
    · simp [map_mul]

end InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
