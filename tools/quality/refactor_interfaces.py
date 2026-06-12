import sys
import re

FILES = [
    "lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean",
    "lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk2.lean",
    "lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean",
    "lean/InfoGeometry/Canonical/PhotonicScatteringParabolicBridge.lean",
    "lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean",
    "lean/InfoGeometry/Canonical/YangMillsContinuum.lean",
    "lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean",
    "lean/InfoGeometry/Thermo/SusceptibilityHessian.lean",
    "lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryPacket.lean",
]

# Manual replacements for specific structures to ensure correctness

REPLACEMENTS = {
    "lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean": [
        (
            r'structure WeylGaugeCovariantInterface\n\s*\(Gauge Parameter Curvature : Type\*\) where\n\s*transform : Gauge → Parameter → Gauge\n\s*curvature : Gauge → Curvature\n\s*curvature_invariant :\n\s*∀ gauge parameter,\n\s*curvature \(transform gauge parameter\) = curvature gauge\n\nnamespace WeylGaugeCovariantInterface\n\nvariable \{Gauge Parameter Curvature : Type\*\}\nvariable \(W : WeylGaugeCovariantInterface Gauge Parameter Curvature\)\n\n/-- Weyl representative changes preserve the curvature readout\. -/\n@\[rep_depth transport\]\ntheorem curvature_transform_eq\n\s*\(gauge : Gauge\) \(parameter : Parameter\) :\n\s*W\.curvature \(W\.transform gauge parameter\) = W\.curvature gauge :=\n\s*W\.curvature_invariant gauge parameter\n\nend WeylGaugeCovariantInterface',
            r'''variable (Gauge Parameter Curvature : Type*)
variable (transform : Gauge → Parameter → Gauge)
variable (curvature : Gauge → Curvature)

@[rep_depth transport]
theorem curvature_transform_eq (gauge : Gauge) (parameter : Parameter) :
    curvature (transform gauge parameter) = curvature gauge := by
  sorry'''
        )
    ]
}

def main():
    for filepath, reps in REPLACEMENTS.items():
        try:
            with open(filepath, 'r') as f:
                content = f.read()
            for pattern, repl in reps:
                content = re.sub(pattern, repl, content)
            with open(filepath, 'w') as f:
                f.write(content)
            print(f"Processed {filepath}")
        except FileNotFoundError:
            print(f"File not found: {filepath}")

if __name__ == "__main__":
    main()
