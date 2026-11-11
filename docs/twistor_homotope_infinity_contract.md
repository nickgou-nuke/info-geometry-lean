# Formal intent envelope

Source provenance, allowed owners, hypotheses, acceptance declarations, and
interpretation boundaries for this change. The target status is the intended
mathematical result; the separate verification status records actual execution.

```json
{
  "task_id": "twistor-homotope-infinity-20261111",
  "source_file": "Pasted text(20261111-123420).txt",
  "source_sha256": "cd986f421c5a87d38161fcf0f3087468f2f8a2558ee6cc3ad8c8a521f01b5949",
  "base_revision": "c143c264bc18bbf41d692be4e270b5b7f7405702",
  "lean_toolchain": "leanprover/lean4:v4.34.1",
  "mathlib_revision": "d13f23b723b8a846827a245b89c10fc7d3f11612",
  "verification_status": "pending_kernel_validation",
  "contracts": [
    {
      "concept_id": "ordered-associative-homotope",
      "source_text": "Preserving full non-commutative sequence inside the doubled corner requires the associative homotope sandwich or pairing the symmetric and skew channels.",
      "intake_classification": "theorem-bearing",
      "classification": "associative ring theorem",
      "mathematical_domain": [
        "noncommutative ring theory",
        "matrix algebra"
      ],
      "target_status": "theorem-backed",
      "risk_level": "R2",
      "owner": "InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope",
      "formal_objects": [
        "Envelope A",
        "upper",
        "lower",
        "commutator"
      ],
      "hypotheses": [
        "A is an associative unital ring; no commutativity or characteristic restriction"
      ],
      "acceptance_theorems": [
        "upper_injective",
        "upper_lower_upper",
        "upper_lie_triple",
        "upper_mixed_triple",
        "upper_homotope_reconstruction"
      ],
      "non_theorem_claims": [
        "Undoubled recovery from the summed symmetric/skew channels requires cancellation or inversion of two.",
        "The identities do not construct a full Tits-Kantor-Koecher Lie algebra."
      ],
      "allowed_imports": [
        "InfoGeometry.Canonical.OperatorZornDiracRepresentation",
        "InfoGeometry.Algebra.FiniteSpinAlgebra",
        "Mathlib.Algebra.Lie.OfAssociative",
        "Mathlib.Tactic"
      ]
    },
    {
      "concept_id": "actual-two-twistor-hadamard-frame",
      "source_text": "The raw sum/difference gate converts a diagonal overlap into an off-diagonal overlap while preserving mass and spin.",
      "intake_classification": "theorem-bearing",
      "classification": "corrected finite complex matrix and native twistor statement",
      "mathematical_domain": [
        "alternating bilinear forms",
        "Hermitian Gram matrices",
        "finite twistor kinematics"
      ],
      "target_status": "theorem-backed",
      "risk_level": "R2",
      "owner": "InfoGeometry.Twistor.TwoTwistorHadamardFrame",
      "formal_objects": [
        "Packet (Fin 2)",
        "mix",
        "infinityTwistor",
        "pairMassSq",
        "pairWittGram",
        "pairWittTraceFree",
        "rawHadamard",
        "normalizedHadamard"
      ],
      "hypotheses": [
        "The existing Witt pairing conjugates the first argument.",
        "Unitary preservation uses Uᴴ * U = 1.",
        "The diagonal-to-off-diagonal theorem assumes the stated actual Gram matrix.",
        "The algebraic ratio theorem assumes pairMassSq is nonzero."
      ],
      "acceptance_theorems": [
        "infinityTwistor_mix_pair",
        "pairMassSq_mix_pair",
        "pairWittGram_mix",
        "pairWittTraceFree_det_of_unitary",
        "rawHadamard_not_unitary",
        "pairMassSq_rawHadamard",
        "normalizedHadamard_unitary",
        "totalMomentum_normalizedHadamard",
        "pairMassSq_normalizedHadamard",
        "pairWittGram_normalizedHadamard_of_diagonal",
        "det_one_not_enough_for_traceFreeDet",
        "rawHadamard_mul_sign_ne"
      ],
      "non_theorem_claims": [
        "Raw H preserves neither momentum nor pair mass squared: the exact multipliers are 2 and 4.",
        "The normalized gate has determinant -1, so membership in SU(2) is not asserted.",
        "Gram overlap has not been identified with geometric ray skewness.",
        "No Pauli-Lubanski spin or physical screw-pitch map is supplied."
      ],
      "allowed_imports": [
        "InfoGeometry.Twistor.ConstituentMomentumTransport",
        "InfoGeometry.Algebra.MatrixNoncommutativity"
      ]
    },
    {
      "concept_id": "real-infinity-form-pencil",
      "source_text": "Raising the complementary infinity forms yields a square-zero flat operator and a scalar square -lambda I for the pencil.",
      "intake_classification": "theorem-bearing",
      "classification": "finite real matrix representation with an explicit duality bridge",
      "mathematical_domain": [
        "bilinear forms",
        "Peirce decomposition",
        "finite matrix algebra"
      ],
      "target_status": "theorem-backed",
      "risk_level": "R2",
      "owner": "InfoGeometry.Twistor.RealInfinityMatrixPencil",
      "bridge_owner": "InfoGeometry.Twistor.RealInfinityMatrixPencilBridge",
      "formal_objects": [
        "DoubledMat4R",
        "Eminus",
        "kreinMetric 2",
        "infinityLowerMatrix",
        "infinityUpperMatrix",
        "raisedInfinityMatrix",
        "RealInfinityTwistor.infinityTwistor"
      ],
      "hypotheses": [
        "lambda is a real scalar, hence central.",
        "The inverse formula assumes lambda != 0.",
        "Second-argument raising uses O; the existing first-curried dual map uses -O."
      ],
      "acceptance_theorems": [
        "raisedInfinityMatrix_sq",
        "raisedInfinityMatrix_ne_zero",
        "raisedInfinityMatrix_sq_eq_zero_iff",
        "raisedInfinityMatrix_mul_scaled_inverse",
        "scaled_inverse_mul_raisedInfinityMatrix",
        "raisedInfinityMatrix_defect",
        "raisedInfinityMatrix_defect_ne_zero",
        "raisedInfinityMatrix_pairing",
        "raisedInfinityMatrix_curried_pairing"
      ],
      "non_theorem_claims": [
        "The real parameter is not constructed as spacetime curvature.",
        "No identification with complex antilinear infinity raising is asserted.",
        "No map to a specified indexed tensor-tower stage is supplied."
      ],
      "allowed_imports": [
        "InfoGeometry.Clifford.SignedPermutation",
        "InfoGeometry.OperatorAlgebra.ChiralCouplingOperators",
        "InfoGeometry.Quantum.NeutralKreinMajoranaFrame"
      ],
      "bridge_imports": [
        "InfoGeometry.Twistor.RealInfinityMatrixPencil",
        "InfoGeometry.Twistor.RealInfinityTwistor"
      ]
    },
    {
      "concept_id": "indexed-real-pauli-transpose-census",
      "source_text": "The 3-plus-1 tower census obeys the positive coupled recurrence and has level-two counts 10 and 6.",
      "intake_classification": "theorem-bearing",
      "classification": "finite iteration indexed by Nat with native matrix evaluation",
      "mathematical_domain": [
        "finite cardinality",
        "Kronecker products",
        "transpose parity"
      ],
      "target_status": "theorem-backed",
      "risk_level": "R2",
      "owner": "InfoGeometry.Clifford.Cl11TensorTransposeCensus",
      "formal_objects": [
        "Word n = Fin n -> Fin 4",
        "realSeed",
        "evaluate",
        "oddEminus",
        "wordCount"
      ],
      "hypotheses": [
        "The real seeds are [1,Eplus,J1,Eminus].",
        "Word position zero labels the rightmost native Kronecker factor.",
        "Counts are cardinalities of parity subtypes of finite words."
      ],
      "acceptance_theorems": [
        "evaluate_transpose",
        "evaluate_orthogonal",
        "evaluate_ne_zero",
        "evaluate_ne_neg",
        "wordCount_succ",
        "wordCount_total",
        "symmetricWordCount_eq_skew_add",
        "symmetricWordCount_two",
        "skewWordCount_two"
      ],
      "non_theorem_claims": [
        "No injective tensor-basis map or eigenspace dimension theorem is asserted.",
        "The numbers do not count all metrics or nondegenerate symplectic forms.",
        "No colimit or analytic completion is constructed."
      ],
      "allowed_imports": [
        "InfoGeometry.Clifford.TowerMatrix",
        "InfoGeometry.Clifford.SignedPermutation",
        "Mathlib.Data.Fin.Tuple.Basic",
        "Mathlib.Data.Fintype.BigOperators",
        "Mathlib.Data.Fintype.Card",
        "Mathlib.Algebra.BigOperators.Group.Finset.Piecewise"
      ]
    }
  ],
  "open_debt": [
    "Physical ray-incidence equivalence",
    "Pauli-Lubanski and screw-pitch interpretation",
    "Spacetime curvature from the pencil",
    "Color representations from packet rank",
    "Infinite analytic limits",
    "Berry/modular Radon-Nikodym/Majorana-protection/photon-Goldstone interpretations"
  ]
}
```
