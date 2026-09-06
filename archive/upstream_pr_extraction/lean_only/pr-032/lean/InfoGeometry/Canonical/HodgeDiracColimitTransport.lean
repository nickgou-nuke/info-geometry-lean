import InfoGeometry.Canonical.HodgeDiracLaplacianBridge

namespace InfoGeometry.Canonical.HodgeDiracColimitTransport

open HodgeDiracLaplacianBridge

/-!
# Hodge--Dirac chirality on a compatible cone

This owner isolates the algebraic transport needed by a directed-colimit
construction.  The maps into the target are explicit ring homomorphisms and
the component equations are explicit hypotheses.  Thus the result does not
pretend that an arbitrary target is a categorical colimit: once a genuine
colimit carrier supplies these cone equations, the theorem applies directly.
-/

variable {OpInf : Type*} [Ring OpInf]
variable {Op : ℕ → Type*} [∀ n, Ring (Op n)]

def componentChiral
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n)) (n : ℕ) : Prop :=
  IsDiracHodgeChiral (stage n)

/--
Transport of the Dirac--Hodge anticommutation law from one compatible stage
to the target cone.  The `hcompat` equations identify the stage operators
with their target images.  A separate directed-system owner may supply the
maps `map`; no transition law is needed for this operator identity once the
component equations are available.
-/
theorem colimit_dirac_hodge_chiral
    (map : ∀ n, Op n →+* OpInf)
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n))
    (target : HodgeDiracLaplacianCarrier OpInf)
    (hcompatStar : ∀ n,
      map n (hodgeStar (stage n)) = hodgeStar target)
    (hcompatDirac : ∀ n,
      map n (dirac (stage n)) = dirac target)
    (hstage : ∀ n, componentChiral stage n) :
    IsDiracHodgeChiral target := by
  have h := hstage 0
  have hmapped := congrArg (map 0) h
  simpa [IsDiracHodgeChiral, componentChiral, map_mul, map_neg,
    hcompatStar 0, hcompatDirac 0] using hmapped

theorem colimit_dirac_hodge_chiral_of_stage
    (map : ∀ n, Op n →+* OpInf)
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n))
    (target : HodgeDiracLaplacianCarrier OpInf)
    (hcompatStar : ∀ n,
      map n (hodgeStar (stage n)) = hodgeStar target)
    (hcompatDirac : ∀ n,
      map n (dirac (stage n)) = dirac target)
    (hstage : ∀ n, IsDiracHodgeChiral (stage n)) :
    IsDiracHodgeChiral target := by
  exact colimit_dirac_hodge_chiral map stage target
    hcompatStar hcompatDirac hstage

/-- Directed-system version of the chiral transport theorem. -/
theorem colimit_dirac_hodge_chiral_of_directed_system
    (transition : ∀ n, Op n →+* Op (n + 1))
    (map : ∀ n, Op n →+* OpInf)
    (map_compat : ∀ n x,
      map (n + 1) (transition n x) = map n x)
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n))
    (target : HodgeDiracLaplacianCarrier OpInf)
    (hcompatStar : ∀ n,
      map n (hodgeStar (stage n)) = hodgeStar target)
    (hcompatDirac : ∀ n,
      map n (dirac (stage n)) = dirac target)
    (hstage : ∀ n, IsDiracHodgeChiral (stage n)) :
    IsDiracHodgeChiral target := by
  exact colimit_dirac_hodge_chiral_of_stage map stage target
    hcompatStar hcompatDirac hstage

/-!
Transport of the Dirac-square closure from the compatible stages to the
target cone.  This is the second compatibility property needed before the
finite Hodge-evenness theorem can be applied at the colimit carrier.
-/
theorem colimit_laplacian_from_dirac
    (map : ∀ n, Op n →+* OpInf)
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n))
    (target : HodgeDiracLaplacianCarrier OpInf)
    (hcompatLaplacian : ∀ n,
      map n (laplacian (stage n)) = laplacian target)
    (hcompatDirac : ∀ n,
      map n (dirac (stage n)) = dirac target)
    (hstage : ∀ n, IsLaplacianFromDirac (stage n)) :
    IsLaplacianFromDirac target := by
  have h := hstage 0
  have hmapped := congrArg (map 0) h
  simpa [IsLaplacianFromDirac, map_mul,
    hcompatLaplacian 0, hcompatDirac 0] using hmapped

/-! The target Laplacian is Hodge-even after both closure witnesses transfer. -/
theorem colimit_laplacian_commutes_hodge
    (map : ∀ n, Op n →+* OpInf)
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n))
    (target : HodgeDiracLaplacianCarrier OpInf)
    (hcompatStar : ∀ n,
      map n (hodgeStar (stage n)) = hodgeStar target)
    (hcompatDirac : ∀ n,
      map n (dirac (stage n)) = dirac target)
    (hcompatLaplacian : ∀ n,
      map n (laplacian (stage n)) = laplacian target)
    (hstageChiral : ∀ n, IsDiracHodgeChiral (stage n))
    (hstageLaplacian : ∀ n, IsLaplacianFromDirac (stage n)) :
    laplacian target * hodgeStar target =
      hodgeStar target * laplacian target := by
  exact laplacian_commutes_hodge_of_dirac_closure target
    (colimit_dirac_hodge_chiral map stage target
      hcompatStar hcompatDirac hstageChiral)
    (colimit_laplacian_from_dirac map stage target
      hcompatLaplacian hcompatDirac hstageLaplacian)

/-- Directed-system version of the Laplacian/Hodge commutation transport. -/
theorem colimit_laplacian_commutes_hodge_of_directed_system
    (transition : ∀ n, Op n →+* Op (n + 1))
    (map : ∀ n, Op n →+* OpInf)
    (map_compat : ∀ n x,
      map (n + 1) (transition n x) = map n x)
    (stage : ∀ n, HodgeDiracLaplacianCarrier (Op n))
    (target : HodgeDiracLaplacianCarrier OpInf)
    (hcompatStar : ∀ n,
      map n (hodgeStar (stage n)) = hodgeStar target)
    (hcompatDirac : ∀ n,
      map n (dirac (stage n)) = dirac target)
    (hcompatLaplacian : ∀ n,
      map n (laplacian (stage n)) = laplacian target)
    (hstageChiral : ∀ n, IsDiracHodgeChiral (stage n))
    (hstageLaplacian : ∀ n, IsLaplacianFromDirac (stage n)) :
    laplacian target * hodgeStar target =
      hodgeStar target * laplacian target := by
  exact colimit_laplacian_commutes_hodge map stage target
    hcompatStar hcompatDirac hcompatLaplacian hstageChiral hstageLaplacian

end InfoGeometry.Canonical.HodgeDiracColimitTransport
