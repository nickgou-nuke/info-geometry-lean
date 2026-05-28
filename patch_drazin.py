import re

with open("lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean", "r") as f:
    content = f.read()

# 1. SelfAdjointIdempotentPair
content = re.sub(
    r"structure SelfAdjointIdempotentPair \(A : Type\*\) \[Ring A\] where\n  support : A\n  residue : A\n  support_idem : support \* support = support\n  residue_idem : residue \* residue = residue\n  support_residue_zero : support \* residue = 0\n  residue_support_zero : residue \* support = 0\n  support_add_residue : support \+ residue = 1\n  selfAdjointLaw : Prop\n  selfAdjointCertificate : selfAdjointLaw",
    r"structure SelfAdjointIdempotentPair (A : Type*) [Ring A] [StarRing A] where\n  support : A\n  residue : A\n  support_idem : support * support = support\n  residue_idem : residue * residue = residue\n  support_residue_zero : support * residue = 0\n  residue_support_zero : residue * support = 0\n  support_add_residue : support + residue = 1\n  support_selfAdjoint : star support = support\n  residue_selfAdjoint : star residue = residue",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"theorem selfAdjoint_valid : P.selfAdjointLaw :=\n  P.selfAdjointCertificate\n\n",
    "",
    content,
    flags=re.MULTILINE
)

# 2. RelativeCoreNilpotentDecomposition
content = re.sub(
    r"structure RelativeCoreNilpotentDecomposition \(A : Type\*\) \[Ring A\] where\n  projections : SelfAdjointIdempotentPair A",
    r"structure RelativeCoreNilpotentDecomposition (A : Type*) [Ring A] [StarRing A] where\n  projections : SelfAdjointIdempotentPair A",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"  coreInv_mul_nilpotent :\n    coreInv \* nilpotentPart = 0\n  nilpotentResidueLaw : Prop\n  nilpotentResidueCertificate : nilpotentResidueLaw",
    r"  coreInv_mul_nilpotent :\n    coreInv * nilpotentPart = 0\n  nilpotent_isNilpotent : IsNilpotent nilpotentPart",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"theorem nilpotentResidue_valid : D.nilpotentResidueLaw :=\n  D.nilpotentResidueCertificate\n\n",
    "",
    content,
    flags=re.MULTILINE
)

# 3. DivisionResidueBlockPacket
content = re.sub(
    r"structure DivisionResidueBlockPacket where\n  Block : Type\*\n  DivisionCarrier : Block → Type\*\n  residueProjection : Block → Type\*\n  simpleResidueLaw : Prop\n  simpleResidueCertificate : simpleResidueLaw",
    r"structure DivisionResidueBlockPacket where\n  Block : Type*\n  DivisionCarrier : Block → Type*\n  residueProjection : Block → Type*\n  carrier_divisionRing : ∀ b, DivisionRing (DivisionCarrier b)",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"theorem simpleResidue_valid : P.simpleResidueLaw :=\n  P.simpleResidueCertificate\n\n",
    "",
    content,
    flags=re.MULTILINE
)

# 4. FrobeniusSelfDualPacket
content = re.sub(
    r"structure FrobeniusSelfDualPacket \(A : Type\*\) \[Mul A\] where",
    r"structure FrobeniusSelfDualPacket (A : Type*) [Ring A] where",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"  pairing_mul_left_eq_pairing_mul_right :\n    ∀ a b c : A, pairing \(a \* b\) c = pairing a \(b \* c\)\n  nondegeneracyLaw : Prop\n  nondegeneracyCertificate : nondegeneracyLaw",
    r"  pairing_mul_left_eq_pairing_mul_right :\n    ∀ a b c : A, pairing (a * b) c = pairing a (b * c)\n  nondegenerate : ∀ a, (∀ b, pairing a b = 0) → a = 0",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"theorem nondegeneracy_valid : P.nondegeneracyLaw :=\n  P.nondegeneracyCertificate\n\n",
    "",
    content,
    flags=re.MULTILINE
)

# 5. SpectralDivisorStratification
content = re.sub(
    r"structure SpectralDivisorStratification \(A : Type\*\) \[Ring A\] where",
    r"structure SpectralDivisorStratification (A : Type*) [Ring A] [StarRing A] where",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"  singularLocus : Set Point\n  locusCoverLaw : Prop\n  locusCoverCertificate : locusCoverLaw",
    r"  singularLocus : Set Point\n  locusCover : regularLocus ∪ singularLocus = Set.univ",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"theorem locusCover_valid : S.locusCoverLaw :=\n  S.locusCoverCertificate\n\n",
    "",
    content,
    flags=re.MULTILINE
)

# 6. TwoProjectionDrazinLocalizationPacket
content = re.sub(
    r"structure TwoProjectionDrazinLocalizationPacket \(A : Type\*\) \[Ring A\] where",
    r"structure TwoProjectionDrazinLocalizationPacket (A : Type*) [Ring A] [StarRing A] where",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"  residueBlocks : DivisionResidueBlockPacket\n  localizationLaw : Prop\n  localizationCertificate : localizationLaw",
    r"  residueBlocks : DivisionResidueBlockPacket\n  drazin_localization_eq : decomposition.coreInv = decomposition.coreInv * decomposition.element * decomposition.coreInv",
    content,
    flags=re.MULTILINE
)

content = re.sub(
    r"theorem localization_valid : P.localizationLaw :=\n  P.localizationCertificate\n\n",
    "",
    content,
    flags=re.MULTILINE
)

with open("lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean", "w") as f:
    f.write(content)

print("Patched DrazinProjectionLocalization.lean")
