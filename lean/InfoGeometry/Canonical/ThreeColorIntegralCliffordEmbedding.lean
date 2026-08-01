import Mathlib.Tactic
import InfoGeometry.Canonical.IntegralChiralCliffordOrder

/- Coordinate-only eight-slot carrier and three linear embeddings for the
integral three-color corridor.  This file does not introduce a multiplication
table; the product structure is handled by the separate Zorn multiplication
owner. -/
namespace InfoGeometry.Canonical

inductive IntegralSplitBasis
  | one | l | i | il | j | jl | k | kl
deriving DecidableEq, Fintype

abbrev StandardIntegralSplitOctonion := IntegralSplitBasis → ℤ

def splitBasisVector (b : IntegralSplitBasis) : StandardIntegralSplitOctonion :=
  Pi.single b 1

def oneOct := splitBasisVector .one
def lOct   := splitBasisVector .l
def iOct   := splitBasisVector .i
def ilOct  := splitBasisVector .il
def jOct   := splitBasisVector .j
def jlOct  := splitBasisVector .jl
def kOct   := splitBasisVector .k
def klOct  := splitBasisVector .kl

abbrev ChiralOrderCoordinates := Fin 4 → ℤ

def coordinatesToOrder : ChiralOrderCoordinates →ₗ[ℤ] integerChiralOrder where
  toFun c := ⟨c 0 • chiralI + c 1 • chiralL + c 2 • chiralJ + c 3 • chiralX, by
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · apply Submodule.smul_mem; apply Submodule.subset_span; simp
        · apply Submodule.smul_mem; apply Submodule.subset_span; simp
      · apply Submodule.smul_mem; apply Submodule.subset_span; simp
    · apply Submodule.smul_mem; apply Submodule.subset_span; simp⟩
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> { dsimp [chiralI, chiralL, chiralJ, chiralX]; ring }
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> { dsimp [chiralI, chiralL, chiralJ, chiralX]; ring }

lemma parity_diff_even {a b : ℤ} (h : Int.ModEq 2 a b) : ∃ k : ℤ, a - b = 2 * k := by
  use (a - b) / 2
  have h1 : 2 ∣ (a - b) := Int.modEq_iff_dvd.mp h.symm
  simpa [mul_comm] using (Int.ediv_mul_cancel h1).symm

theorem coordinatesToOrder_bijective : Function.Bijective coordinatesToOrder := by
  constructor
  · intro x y h
    have h1 : (coordinatesToOrder x : M2Z) = (coordinatesToOrder y : M2Z) := congrArg Subtype.val h
    have h00 : x 0 + x 1 = y 0 + y 1 := by
      simpa [coordinatesToOrder, chiralI, chiralL, chiralJ, chiralX] using
        congrArg (fun M => M 0 0) h1
    have h11 : x 0 - x 1 = y 0 - y 1 := by
      simpa [coordinatesToOrder, chiralI, chiralL, chiralJ, chiralX] using
        congrArg (fun M => M 1 1) h1
    have h01 : -x 2 + x 3 = -y 2 + y 3 := by
      simpa [coordinatesToOrder, chiralI, chiralL, chiralJ, chiralX] using
        congrArg (fun M => M 0 1) h1
    have h10 : x 2 + x 3 = y 2 + y 3 := by
      simpa [coordinatesToOrder, chiralI, chiralL, chiralJ, chiralX] using
        congrArg (fun M => M 1 0) h1
    funext k
    fin_cases k
    · change x 0 = y 0
      omega
    · change x 1 = y 1
      omega
    · change x 2 = y 2
      omega
    · change x 3 = y 3
      omega
  · rintro ⟨A, hA⟩
    have hH : (integerChiralOrder : Set M2Z) = paritySubring := integerChiralOrder_eq_paritySubring
    have hA_subring : A ∈ paritySubring := by
      change A ∈ (integerChiralOrder : Set M2Z) at hA
      rw [hH] at hA
      exact hA
    have hA1 : Int.ModEq 2 (A 0 0) (A 1 1) := hA_subring.1
    have hA2 : Int.ModEq 2 (A 0 1) (A 1 0) := hA_subring.2
    rcases parity_diff_even hA1 with ⟨k, hk⟩
    rcases parity_diff_even hA2 with ⟨m, hm⟩
    let c0 := A 1 1 + k
    let c1 := k
    let c2 := -m
    let c3 := A 1 0 + m
    use fun i => if i = 0 then c0 else if i = 1 then c1 else if i = 2 then c2 else c3
    ext i j
    have hk2 : A 0 0 = A 1 1 + 2 * k := by omega
    have hm2 : A 0 1 = A 1 0 + 2 * m := by omega
    fin_cases i <;> fin_cases j <;> {
      dsimp [coordinatesToOrder, chiralI, chiralL, chiralJ, chiralX]
      ring_nf
      try omega
    }

noncomputable def chiralOrderCoordinateEquiv : ChiralOrderCoordinates ≃ₗ[ℤ] integerChiralOrder :=
  LinearEquiv.ofBijective coordinatesToOrder coordinatesToOrder_bijective

def redCoordinateEmbedding : ChiralOrderCoordinates →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun c := c 0 • oneOct + c 1 • lOct + c 2 • iOct + c 3 • ilOct
  map_add' x y := by ext idx; fin_cases idx <;> { dsimp [oneOct, lOct, iOct, ilOct, splitBasisVector]; ring }
  map_smul' r x := by ext idx; fin_cases idx <;> { dsimp [oneOct, lOct, iOct, ilOct, splitBasisVector]; ring }

def greenCoordinateEmbedding : ChiralOrderCoordinates →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun c := c 0 • oneOct + c 1 • lOct + c 2 • jOct + c 3 • jlOct
  map_add' x y := by ext idx; fin_cases idx <;> { dsimp [oneOct, lOct, jOct, jlOct, splitBasisVector]; ring }
  map_smul' r x := by ext idx; fin_cases idx <;> { dsimp [oneOct, lOct, jOct, jlOct, splitBasisVector]; ring }

def blueCoordinateEmbedding : ChiralOrderCoordinates →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun c := c 0 • oneOct + c 1 • lOct + c 2 • kOct + c 3 • klOct
  map_add' x y := by ext idx; fin_cases idx <;> { dsimp [oneOct, lOct, kOct, klOct, splitBasisVector]; ring }
  map_smul' r x := by ext idx; fin_cases idx <;> { dsimp [oneOct, lOct, kOct, klOct, splitBasisVector]; ring }

noncomputable def redEmbedding : integerChiralOrder →ₗ[ℤ] StandardIntegralSplitOctonion :=
  redCoordinateEmbedding.comp chiralOrderCoordinateEquiv.symm.toLinearMap

noncomputable def greenEmbedding : integerChiralOrder →ₗ[ℤ] StandardIntegralSplitOctonion :=
  greenCoordinateEmbedding.comp chiralOrderCoordinateEquiv.symm.toLinearMap

noncomputable def blueEmbedding : integerChiralOrder →ₗ[ℤ] StandardIntegralSplitOctonion :=
  blueCoordinateEmbedding.comp chiralOrderCoordinateEquiv.symm.toLinearMap

theorem redEmbedding_injective : Function.Injective redEmbedding := by
  intro x y h
  apply chiralOrderCoordinateEquiv.symm.injective
  have h1 : redCoordinateEmbedding (chiralOrderCoordinateEquiv.symm x) = redCoordinateEmbedding (chiralOrderCoordinateEquiv.symm y) := h
  ext idx
  fin_cases idx
  · have hk := congrArg (fun f => f IntegralSplitBasis.one) h1
    dsimp [redCoordinateEmbedding, oneOct, lOct, iOct, ilOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.l) h1
    dsimp [redCoordinateEmbedding, oneOct, lOct, iOct, ilOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.i) h1
    dsimp [redCoordinateEmbedding, oneOct, lOct, iOct, ilOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.il) h1
    dsimp [redCoordinateEmbedding, oneOct, lOct, iOct, ilOct, splitBasisVector] at hk
    simp at hk
    exact hk

theorem greenEmbedding_injective : Function.Injective greenEmbedding := by
  intro x y h
  apply chiralOrderCoordinateEquiv.symm.injective
  have h1 : greenCoordinateEmbedding (chiralOrderCoordinateEquiv.symm x) = greenCoordinateEmbedding (chiralOrderCoordinateEquiv.symm y) := h
  ext idx
  fin_cases idx
  · have hk := congrArg (fun f => f IntegralSplitBasis.one) h1
    dsimp [greenCoordinateEmbedding, oneOct, lOct, jOct, jlOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.l) h1
    dsimp [greenCoordinateEmbedding, oneOct, lOct, jOct, jlOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.j) h1
    dsimp [greenCoordinateEmbedding, oneOct, lOct, jOct, jlOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.jl) h1
    dsimp [greenCoordinateEmbedding, oneOct, lOct, jOct, jlOct, splitBasisVector] at hk
    simp at hk
    exact hk

theorem blueEmbedding_injective : Function.Injective blueEmbedding := by
  intro x y h
  apply chiralOrderCoordinateEquiv.symm.injective
  have h1 : blueCoordinateEmbedding (chiralOrderCoordinateEquiv.symm x) = blueCoordinateEmbedding (chiralOrderCoordinateEquiv.symm y) := h
  ext idx
  fin_cases idx
  · have hk := congrArg (fun f => f IntegralSplitBasis.one) h1
    dsimp [blueCoordinateEmbedding, oneOct, lOct, kOct, klOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.l) h1
    dsimp [blueCoordinateEmbedding, oneOct, lOct, kOct, klOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.k) h1
    dsimp [blueCoordinateEmbedding, oneOct, lOct, kOct, klOct, splitBasisVector] at hk
    simp at hk
    exact hk
  · have hk := congrArg (fun f => f IntegralSplitBasis.kl) h1
    dsimp [blueCoordinateEmbedding, oneOct, lOct, kOct, klOct, splitBasisVector] at hk
    simp at hk
    exact hk

def redIntegralSector : Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x | x .j = 0 ∧ x .jl = 0 ∧ x .k = 0 ∧ x .kl = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro a x hx; simp_all

def greenIntegralSector : Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x | x .i = 0 ∧ x .il = 0 ∧ x .k = 0 ∧ x .kl = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro a x hx; simp_all

def blueIntegralSector : Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x | x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro a x hx; simp_all

theorem range_redEmbedding : LinearMap.range redEmbedding = redIntegralSector := by
  apply le_antisymm
  · rintro x ⟨c, rfl⟩
    dsimp [redEmbedding, redCoordinateEmbedding, redIntegralSector, splitBasisVector, oneOct, lOct, iOct, ilOct]
    simp
  · intro x hx
    dsimp [redIntegralSector] at hx
    rcases hx with ⟨hj, hjl, hk, hkl⟩
    let c : ChiralOrderCoordinates := fun i => if i = 0 then x .one else if i = 1 then x .l else if i = 2 then x .i else x .il
    use chiralOrderCoordinateEquiv c
    dsimp [redEmbedding]
    rw [LinearEquiv.symm_apply_apply]
    ext idx
    fin_cases idx <;> {
      dsimp [redCoordinateEmbedding, c, oneOct, lOct, iOct, ilOct, splitBasisVector]
      simp
      try { exact hj.symm }
      try { exact hjl.symm }
      try { exact hk.symm }
      try { exact hkl.symm }
    }

theorem range_greenEmbedding : LinearMap.range greenEmbedding = greenIntegralSector := by
  apply le_antisymm
  · rintro x ⟨c, rfl⟩
    dsimp [greenEmbedding, greenCoordinateEmbedding, greenIntegralSector, splitBasisVector, oneOct, lOct, jOct, jlOct]
    simp
  · intro x hx
    dsimp [greenIntegralSector] at hx
    rcases hx with ⟨hi, hil, hk, hkl⟩
    let c : ChiralOrderCoordinates := fun i => if i = 0 then x .one else if i = 1 then x .l else if i = 2 then x .j else x .jl
    use chiralOrderCoordinateEquiv c
    dsimp [greenEmbedding]
    rw [LinearEquiv.symm_apply_apply]
    ext idx
    fin_cases idx <;> {
      dsimp [greenCoordinateEmbedding, c, oneOct, lOct, jOct, jlOct, splitBasisVector]
      simp
      try { exact hi.symm }
      try { exact hil.symm }
      try { exact hk.symm }
      try { exact hkl.symm }
    }

theorem range_blueEmbedding : LinearMap.range blueEmbedding = blueIntegralSector := by
  apply le_antisymm
  · rintro x ⟨c, rfl⟩
    dsimp [blueEmbedding, blueCoordinateEmbedding, blueIntegralSector, splitBasisVector, oneOct, lOct, kOct, klOct]
    simp
  · intro x hx
    dsimp [blueIntegralSector] at hx
    rcases hx with ⟨hi, hil, hj, hjl⟩
    let c : ChiralOrderCoordinates := fun i => if i = 0 then x .one else if i = 1 then x .l else if i = 2 then x .k else x .kl
    use chiralOrderCoordinateEquiv c
    dsimp [blueEmbedding]
    rw [LinearEquiv.symm_apply_apply]
    ext idx
    fin_cases idx <;> {
      dsimp [blueCoordinateEmbedding, c, oneOct, lOct, kOct, klOct, splitBasisVector]
      simp
      try { exact hi.symm }
      try { exact hil.symm }
      try { exact hj.symm }
      try { exact hjl.symm }
    }

def sharedIntegralHyperbolicAxis : Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x | x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0 ∧ x .k = 0 ∧ x .kl = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro a x hx; simp_all

theorem sharedIntegralHyperbolicAxis_eq_span :
    sharedIntegralHyperbolicAxis = Submodule.span ℤ {oneOct, lOct} := by
  apply le_antisymm
  · intro x hx
    dsimp [sharedIntegralHyperbolicAxis] at hx
    rcases hx with ⟨hi, hil, hj, hjl, hk, hkl⟩
    let c0 := x .one
    let c1 := x .l
    have hx_decomp : x = c0 • oneOct + c1 • lOct := by
      ext idx
      fin_cases idx <;> {
        dsimp [c0, c1, oneOct, lOct, splitBasisVector]
        simp
        try { exact hi }
        try { exact hil }
        try { exact hj }
        try { exact hjl }
        try { exact hk }
        try { exact hkl }
      }
    rw [hx_decomp]
    apply Submodule.add_mem
    · apply Submodule.smul_mem; apply Submodule.subset_span; simp
    · apply Submodule.smul_mem; apply Submodule.subset_span; simp
  · rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · dsimp [sharedIntegralHyperbolicAxis, oneOct, splitBasisVector]
      simp
    · dsimp [sharedIntegralHyperbolicAxis, lOct, splitBasisVector]
      simp

theorem red_green_intersection_eq_sharedAxis :
    LinearMap.range redEmbedding ⊓ LinearMap.range greenEmbedding = sharedIntegralHyperbolicAxis := by
  rw [range_redEmbedding, range_greenEmbedding]
  ext x
  dsimp [redIntegralSector, greenIntegralSector, sharedIntegralHyperbolicAxis]
  simp
  aesop

theorem green_blue_intersection_eq_sharedAxis :
    LinearMap.range greenEmbedding ⊓ LinearMap.range blueEmbedding = sharedIntegralHyperbolicAxis := by
  rw [range_greenEmbedding, range_blueEmbedding]
  ext x
  dsimp [greenIntegralSector, blueIntegralSector, sharedIntegralHyperbolicAxis]
  simp
  aesop

theorem blue_red_intersection_eq_sharedAxis :
    LinearMap.range blueEmbedding ⊓ LinearMap.range redEmbedding = sharedIntegralHyperbolicAxis := by
  rw [range_blueEmbedding, range_redEmbedding]
  ext x
  dsimp [blueIntegralSector, redIntegralSector, sharedIntegralHyperbolicAxis]
  simp
  aesop

theorem threeColor_intersection_eq_sharedAxis :
    LinearMap.range redEmbedding ⊓ LinearMap.range greenEmbedding ⊓ LinearMap.range blueEmbedding = sharedIntegralHyperbolicAxis := by
  rw [range_redEmbedding, range_greenEmbedding, range_blueEmbedding]
  ext x
  dsimp [redIntegralSector, greenIntegralSector, blueIntegralSector, sharedIntegralHyperbolicAxis]
  simp
  aesop

theorem master_three_color_embedding_synthesis :
    (LinearMap.range redEmbedding ⊓ LinearMap.range greenEmbedding = sharedIntegralHyperbolicAxis) ∧
    (LinearMap.range greenEmbedding ⊓ LinearMap.range blueEmbedding = sharedIntegralHyperbolicAxis) ∧
    (LinearMap.range blueEmbedding ⊓ LinearMap.range redEmbedding = sharedIntegralHyperbolicAxis) :=
  ⟨red_green_intersection_eq_sharedAxis,
   green_blue_intersection_eq_sharedAxis,
   blue_red_intersection_eq_sharedAxis⟩

end InfoGeometry.Canonical
