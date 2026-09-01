import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Physics.NuclearZ2Superalgebra
import InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge
import InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge
import InfoGeometry.Physics.NuclearFiniteNilpotentSoul
import InfoGeometry.Physics.NuclearExteriorGrassmannSoul
import InfoGeometry.Physics.NuclearOperatorSchurComplement
import InfoGeometry.Physics.NuclearZornAssociatorOperatorBridge

/-!
# Audited theorem DAG for the nuclear supergeometry lane

This file is metadata over existing theorem owners. It does not add a new
physical interpretation. Each formal node names an exact Lean declaration;
open debt deliberately has no owner.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.NuclearSuperGeometryLogosMap

inductive Status where
  | definition
  | theorem
  | structuralBridge
  | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | internalParity
  | internalReflection
  | externalReflection
  | totalSuperInvariance
  | z2Superalgebra
  | homogeneousSuperbracket
  | peirceChannelAssignment
  | operatorZornRealization
  | finiteNilpotentSoul
  | exteriorGrassmannSoul
  | noncommutativeSchurElimination
  | zornAssociatorOperatorDefect
  | berezinianOwner
  | berezinianBlockFactorization
  | genericTaylorGrassmannCalculus
  | spectralGapTermination
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

/-- Directed dependency edges of the formal supergeometry corridor. -/
inductive Edge where
  | parity_to_reflection
  | parity_to_superinvariance
  | parity_to_superalgebra
  | superalgebra_to_peirce
  | superalgebra_to_operatorZorn
  | nilpotent_to_grassmann
  | nilpotent_to_schur
  | zorn_to_associatorDefect
  deriving DecidableEq, Repr, Inhabited

/-- Source and target of each theorem-DAG edge. -/
def edgeEndpoints : Edge → Concept × Concept
  | .parity_to_reflection => (.internalParity, .internalReflection)
  | .parity_to_superinvariance => (.internalParity, .totalSuperInvariance)
  | .parity_to_superalgebra => (.internalParity, .z2Superalgebra)
  | .superalgebra_to_peirce => (.z2Superalgebra, .peirceChannelAssignment)
  | .superalgebra_to_operatorZorn => (.z2Superalgebra, .operatorZornRealization)
  | .nilpotent_to_grassmann => (.finiteNilpotentSoul, .exteriorGrassmannSoul)
  | .nilpotent_to_schur => (.finiteNilpotentSoul, .noncommutativeSchurElimination)
  | .zorn_to_associatorDefect => (.operatorZornRealization, .zornAssociatorOperatorDefect)

/-- All concepts covered by the audit. -/
def allConcepts : List Concept :=
  [ .internalParity
  , .internalReflection
  , .externalReflection
  , .totalSuperInvariance
  , .z2Superalgebra
  , .homogeneousSuperbracket
  , .peirceChannelAssignment
  , .operatorZornRealization
  , .finiteNilpotentSoul
  , .exteriorGrassmannSoul
  , .noncommutativeSchurElimination
  , .zornAssociatorOperatorDefect
  , .berezinianOwner
  , .berezinianBlockFactorization
  , .genericTaylorGrassmannCalculus
  , .spectralGapTermination
  ]

/-- Exact owner ledger. -/
def entry : Concept → Entry
  | .internalParity =>
      ⟨.internalParity, "internal Z2 parity", .definition,
        some ``InfoGeometry.Physics.NuclearOperatorSuperSoloviev.InternalParity,
        "An involutive grading element in an associative ring."⟩
  | .internalReflection =>
      ⟨.internalReflection, "internal Soloviev reflection", .theorem,
        some ``InfoGeometry.Physics.NuclearInternalExternalParityFactorization.internalParity_reflection_of_even_diagonal_odd_offDiagonal,
        "diag(Gamma,Gamma) reflects internally odd off-diagonal channels."⟩
  | .externalReflection =>
      ⟨.externalReflection, "external Fock reflection", .theorem,
        some ``InfoGeometry.Physics.NuclearInternalExternalParityFactorization.externalFockParity_reflection,
        "diag(1,-1) reflects both off-diagonal channels without internal hypotheses."⟩
  | .totalSuperInvariance =>
      ⟨.totalSuperInvariance, "total super-Hamiltonian invariance", .theorem,
        some ``InfoGeometry.Physics.NuclearInternalExternalParityFactorization.totalParity_invariance_from_double_reflection,
        "For internally odd transitions the internal and external signs cancel."⟩
  | .z2Superalgebra =>
      ⟨.z2Superalgebra, "typed Z2 superalgebra", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearZ2Superalgebra.homogeneous_mul,
        "Homogeneous products carry the mod-two product degree."⟩
  | .homogeneousSuperbracket =>
      ⟨.homogeneousSuperbracket, "homogeneous superbracket", .theorem,
        some ``InfoGeometry.Physics.NuclearZ2Superalgebra.superBracket_homogeneous,
        "Odd-odd uses the anticommutator; other degree pairs use the commutator."⟩
  | .peirceChannelAssignment =>
      ⟨.peirceChannelAssignment, "proof-carrying Peirce channel assignment", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge.PeirceCompatibleBlock.peirce_channel_packet,
        "Channel-to-grade membership must be supplied; no physical sector identity is assumed."⟩
  | .operatorZornRealization =>
      ⟨.operatorZornRealization, "associative operator-Zorn realization", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge.diracSuperHamiltonian_invariant,
        "Uses the transported associative OperatorZornMatrix carrier, not raw octonion multiplication."⟩
  | .finiteNilpotentSoul =>
      ⟨.finiteNilpotentSoul, "finite nilpotent soul", .theorem,
        some ``InfoGeometry.Physics.NuclearFiniteNilpotentSoul.FiniteSoul.finite_soul_packet,
        "Certified nilpotence gives exact finite polynomial truncation and unipotent inversion."⟩
  | .exteriorGrassmannSoul =>
      ⟨.exteriorGrassmannSoul, "Mathlib exterior/Grassmann soul", .theorem,
        some ``InfoGeometry.Physics.NuclearExteriorGrassmannSoul.grassmann_one_form_packet,
        "One exterior generator squares to zero and anticommutes with other generators."⟩
  | .noncommutativeSchurElimination =>
      ⟨.noncommutativeSchurElimination, "noncommutative Schur elimination", .theorem,
        some ``InfoGeometry.Physics.NuclearOperatorSchurComplement.soul_schur_packet,
        "Uses proof-carrying inverse data; no determinant is required."⟩
  | .zornAssociatorOperatorDefect =>
      ⟨.zornAssociatorOperatorDefect, "Zorn associator as operator-composition defect", .theorem,
        some ``InfoGeometry.Physics.NuclearZornAssociatorOperatorBridge.leftOp_multiplicative_at_iff_associator_zero,
        "Raw nonassociativity is preserved as failure of left-regular multiplicativity."⟩
  | .berezinianOwner =>
      ⟨.berezinianOwner, "finite Berezinian owner", .openDebt, none,
        "No superdeterminant/Berezinian definition has yet been promoted to this lane."⟩
  | .berezinianBlockFactorization =>
      ⟨.berezinianBlockFactorization, "Berezinian Schur-factorization theorem", .openDebt, none,
        "Schur elimination is formalized; determinant/Berezinian factorization is not."⟩
  | .genericTaylorGrassmannCalculus =>
      ⟨.genericTaylorGrassmannCalculus, "generic Taylor-Grassmann functional calculus", .openDebt, none,
        "Nilpotent polynomial truncation does not by itself imply a Taylor theorem for arbitrary functions."⟩
  | .spectralGapTermination =>
      ⟨.spectralGapTermination, "spectral-gap Grassmann termination", .openDebt, none,
        "Requires a formal spectral functional calculus and hypotheses not yet owned."⟩

/-- Formal nodes are those with a non-debt owner. -/
def Concept.isFormalized (c : Concept) : Bool :=
  match (entry c).status, (entry c).owner with
  | .openDebt, _ => false
  | _, some _ => true
  | _, none => false

/-- Audit exact declaration ownership and enforce ownerless open debt. -/
def auditNuclearSuperGeometryLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n =>
        failures := failures.push s!"open-debt entry unexpectedly names owner {n}"
    | _, none =>
        failures := failures.push s!"formal entry has no owner: {repr c}"
    | _, some n =>
        if env.contains n then pure ()
        else failures := failures.push s!"missing owner declaration: {n} ({repr c})"
  if failures.isEmpty then
    logInfo m!"NuclearSuperGeometry Logos audit PASS: {allConcepts.length} concepts."
  else
    for failure in failures do
      logError m!"NUCLEAR SUPERGEOMETRY LOGOS FAILURE: {failure}"
    throwError "NuclearSuperGeometry Logos audit failed"

elab "#audit_nuclear_supergeometry_logos" : command => do
  Command.liftCoreM auditNuclearSuperGeometryLogos

attribute [spine_object]
  Concept Entry
  InfoGeometry.Physics.NuclearOperatorSuperSoloviev.InternalParity

end InfoGeometry.Physics.NuclearSuperGeometryLogosMap
