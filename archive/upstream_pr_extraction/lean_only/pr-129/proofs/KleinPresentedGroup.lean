import proofs.ProjectiveUnitary6

/-!
# The algebraic presented Klein group and its projective `PU(6)` representation

This owner constructs only the group presentation

`⟨a, b | a b a⁻¹ b = 1⟩`.

It does not identify this presentation with a topological fundamental group,
and it does not construct a local system or an associated bundle.
-/

namespace KleinPresentedGroup

inductive KleinGenerator
  | a
  | b
  deriving DecidableEq

abbrev KleinFree := FreeGroup KleinGenerator

def genA : KleinFree := FreeGroup.of KleinGenerator.a
def genB : KleinFree := FreeGroup.of KleinGenerator.b

def kleinRelator : KleinFree := genA * genB * genA⁻¹ * genB

def KleinRelators : Set KleinFree := {kleinRelator}
def KleinNormal : Subgroup KleinFree :=
  Subgroup.normalClosure KleinRelators
abbrev KleinGroup := KleinFree ⧸ KleinNormal

instance : KleinNormal.Normal := Subgroup.normalClosure_normal

abbrev toKlein : KleinFree →* KleinGroup :=
  QuotientGroup.mk' KleinNormal

theorem kleinRelator_mem_normal : kleinRelator ∈ KleinNormal := by
  exact Subgroup.subset_normalClosure (Set.mem_singleton kleinRelator)

theorem kleinRelator_eq_one : toKlein kleinRelator = 1 := by
  change (QuotientGroup.mk' KleinNormal) kleinRelator = 1
  exact (QuotientGroup.eq_one_iff kleinRelator).2 kleinRelator_mem_normal

/-- The universal free-group representation for a Klein relation. -/
def freeKleinRep {G : Type*} [Group G] (A B : G)
    (_hrel : A * B * A⁻¹ = B⁻¹) : KleinFree →* G :=
  FreeGroup.lift fun g =>
    match g with
    | KleinGenerator.a => A
    | KleinGenerator.b => B

theorem freeKleinRep_relator_mem_kernel
    {G : Type*} [Group G] (A B : G)
    (hrel : A * B * A⁻¹ = B⁻¹) :
    kleinRelator ∈ (freeKleinRep A B hrel).ker := by
  change freeKleinRep A B hrel kleinRelator = 1
  simp [freeKleinRep, kleinRelator, genA, genB]
  rw [hrel]
  simp

def kleinRep {G : Type*} [Group G] (A B : G)
    (hrel : A * B * A⁻¹ = B⁻¹) : KleinGroup →* G :=
  QuotientGroup.lift KleinNormal (freeKleinRep A B hrel) <| by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact freeKleinRep_relator_mem_kernel A B hrel

theorem kleinRep_relator_relation
    {G : Type*} [Group G] (A B : G)
    (hrel : A * B * A⁻¹ = B⁻¹) :
    kleinRep A B hrel (toKlein genA) = A ∧
    kleinRep A B hrel (toKlein genB) = B := by
  change freeKleinRep A B hrel genA = A ∧
    freeKleinRep A B hrel genB = B
  constructor <;> simp [freeKleinRep, genA, genB]

/-- Concrete projective `PU(6)` representation after a central-sign relation. -/
def freeProjectiveRep (Theta T z : ProjectiveUnitary6.U6)
    (hz : z ∈ ProjectiveUnitary6.CenterU6)
    (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    KleinFree →* ProjectiveUnitary6.PU6 :=
  freeKleinRep
    (ProjectiveUnitary6.toPU6 Theta)
    (ProjectiveUnitary6.toPU6 T)
    (ProjectiveUnitary6.projective_conjugation_relation Theta T z hz hpin)

def kleinProjectiveRep (Theta T z : ProjectiveUnitary6.U6)
    (hz : z ∈ ProjectiveUnitary6.CenterU6)
    (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    KleinGroup →* ProjectiveUnitary6.PU6 :=
  kleinRep
    (ProjectiveUnitary6.toPU6 Theta)
    (ProjectiveUnitary6.toPU6 T)
    (ProjectiveUnitary6.projective_conjugation_relation Theta T z hz hpin)

theorem klein_projective_rep_generators
    (Theta T z : ProjectiveUnitary6.U6)
    (hz : z ∈ ProjectiveUnitary6.CenterU6)
    (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    kleinProjectiveRep Theta T z hz hpin (toKlein genA) =
        ProjectiveUnitary6.toPU6 Theta ∧
    kleinProjectiveRep Theta T z hz hpin (toKlein genB) =
        ProjectiveUnitary6.toPU6 T := by
  exact kleinRep_relator_relation
    (ProjectiveUnitary6.toPU6 Theta)
    (ProjectiveUnitary6.toPU6 T)
    (ProjectiveUnitary6.projective_conjugation_relation Theta T z hz hpin)

end KleinPresentedGroup
