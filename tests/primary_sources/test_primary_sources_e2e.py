"""Comprehensive unittest.TestCase suite for Primary-Source E2E verification (Tiers 1-4 & R3)."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

from unittest.mock import patch

from tests.primary_sources import (
    ARCHETYPES_DOC_REL,
    BRIDGE_FILE_REL,
    CANONICAL_ALL_REL,
    FOUNDER_YEAR_SPEC,
    MANIFEST_REL,
    PAPERS_ROOT_REL,
    PILLAR_DIR_MAP,
    REPO_ROOT,
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    TRIANGLE_BRIDGE_REL,
)
from tests.primary_sources.lean_audit import (
    check_traceability_kernel,
    parse_axiom_index_output,
    run_olean_axiom_audits,
    run_print_axioms_probe,
    run_r3_kernel_probe,
)
from tests.primary_sources.manifest_checker import (
    check_papers_git_hygiene,
    expand_traceability_work_ids,
    parse_traceability_matrix,
    validate_archetypes_doc,
    validate_manifest,
)
from tests.primary_sources.quality_and_r3 import (
    check_apache_header_byte0,
    check_feature_lean_presence,
    check_forbidden_tokens_and_prop_wrappers,
    check_r3_compliance,
    check_repo_lean_invariants,
    parse_lean_declarations,
    run_scoped_quality_tools,
)
from tests.primary_sources.verify_primary_sources_e2e import main as cli_main, run_suite


def _build_synthetic_repo(root: Path, *, include_lean_files: bool = True, include_m1: bool = True) -> dict[str, Any]:
    """Create a complete, valid synthetic repo tree under `root` for deterministic E2E testing."""
    (root / ".gitignore").write_text(".papers/\n/scratch/\n", encoding="utf-8")
    (root / "lakefile.lean").write_text(
        'lean_lib InfoGeometryTestSuite where\n  srcDir := "../tests"\n  roots := #[]\n  globs := #[]\n',
        encoding="utf-8",
    )
    (root / "tests" / "primary_sources").mkdir(parents=True, exist_ok=True)
    (root / "tests" / "primary_sources" / "__init__.py").write_text("", encoding="utf-8")

    manifest_data: dict[str, Any] = {"total_works": len(FOUNDER_YEAR_SPEC), "works": []}

    if include_m1:
        papers_root = root / PAPERS_ROOT_REL
        for pdir in PILLAR_DIR_MAP.values():
            (papers_root / pdir).mkdir(parents=True, exist_ok=True)

        doc_lines = [
            "# Primary-Source Mathematical Archetypes",
            "",
            "## Pillar 1: R2 / F2.5 (Grassmann, Plücker, Lie, Klein, Pfaff, Darboux, Cartan, Zorn)",
            "Preserves R3.2 metric-free SL(V)-covariant regressive products.",
            "",
            "## Pillar 2: R3 (Clifford, Lipschitz, Witt, Riesz, Kähler, Hestenes, Jordan-Wigner, ABS)",
            "Preserves R3.2 basis-free O(Q) and R3.3 Koszul Z/2-graded tensor products.",
            "",
            "## Pillar 3: R1 (Peirce, Maurer-Cartan, CE, Koszul, Dubois-Violette, Karoubi, Connes, Fréchet, Onsager-Casimir-Kubo-Bogoliubov-Mori)",
            "Preserves R3.4 faithfulness-free LieActionLane and Peirce/nilpotent soldering.",
            "",
            "## Pillar 4: R2 / M3.2-M3.5 (Dirac, Pauli, Pontryagin, Krein, Tomita-Takesaki, Kasparov, Connes, Strohmaier)",
            "Preserves R3.1 separation of J_Krein, gradeCLM, K_phase, and J_real.",
            "",
            "## Source-to-Declaration Traceability",
            "",
            "| Work ID | Pillar | Author & Year | Extracted Archetype | R3 Principle | Lean Module | Lean Declaration(s) | Status |",
            "|---|---|---|---|---|---|---|---|",
        ]

        owner_mod_by_feat = {
            3: ("InfoGeometry.Projective.GrassmannPrimarySources", "grassmannRegressiveSL"),
            4: ("InfoGeometry.Projective.GrassmannPrimarySources", "kleinQuadricDecomposable"),
            5: ("InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary", "erlangenSubgeometryLattice"),
            6: ("InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary", "pfaffianDerivedClass"),
            7: ("InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary", "zornSplitOctonionMoufang"),
            8: ("InfoGeometry.Clifford.LipschitzWittRieszPrimary", "lipschitzTwistedIsometry"),
            9: ("InfoGeometry.Clifford.LipschitzWittRieszPrimary", "wittHyperbolicCancellation"),
            10: ("InfoGeometry.Clifford.KahlerHestenesJWABSPrimary", "kahlerDiracSquare"),
            11: ("InfoGeometry.Clifford.KahlerHestenesJWABSPrimary", "hestenesMovingFrameRotor"),
            12: ("InfoGeometry.Clifford.KahlerHestenesJWABSPrimary", "absGradedModuleBridge"),
            13: ("InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary", "peirceOrthogonalIdempotent"),
            14: ("InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary", "maurerCartanSoldering"),
            15: ("InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary", "koszulConnectionCurvature"),
            16: ("InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary", "duboisVioletteUniversalComparison"),
            17: ("InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary", "frechetCartanHomotopy"),
            18: ("InfoGeometry.Thermo.OnsagerCasimirKBMPrimary", "casimirJReciprocity"),
            19: ("InfoGeometry.Krein.PontryaginSpace", "kreinIndefiniteContrast"),
            20: ("InfoGeometry.Krein.PontryaginSpace", "pontryaginInvariantSubspace"),
            21: ("InfoGeometry.KK.KreinSpectralTriplePrimary", "tomitaKasparovCycle"),
            22: ("InfoGeometry.KK.KreinSpectralTriplePrimary", "kreinSpectralTripleSeparated"),
        }

        for idx, spec in enumerate(FOUNDER_YEAR_SPEC):
            years_str = "/".join(yg[0] for yg in spec.required_year_groups)
            author_name = spec.label.split("(")[0].strip()
            mod_name, decl_name = owner_mod_by_feat[spec.feature_id]
            r3_tag = {
                "r2_f25": "R3.2",
                "r3": "R3.3" if spec.feature_id == 12 else "R3.2",
                "r1": "R3.4",
                "r2_m35": "R3.1",
            }[spec.pillar]

            if idx == 0:
                status = "substituted"
                rel_pdf = f"{PAPERS_ROOT_REL}/{spec.pillar_dir}/{spec.spec_id}.pdf"
                pdf_bytes = f"%PDF-1.4\n% Synthetic primary source {spec.label}\n".encode("utf-8")
                (root / rel_pdf).write_bytes(pdf_bytes)
                sha = hashlib.sha256(pdf_bytes).hexdigest()
                entry = {
                    "id": spec.spec_id,
                    "pillar": spec.pillar_dir,
                    "author": author_name,
                    "year": years_str,
                    "title": f"Work {spec.label}",
                    "status": status,
                    "r3_principles": [r3_tag],
                    "source_url": "https://example.org/open-access-edition.pdf",
                    "local_path": rel_pdf,
                    "size_bytes": len(pdf_bytes),
                    "sha256": sha,
                    "substitute": "Authoritative 1878 critical edition scan",
                    "gap_reason": "Original 1844 imprint scan paywalled; using open-access 1878 critical edition.",
                }
                doc_lines.append(
                    f"| `{spec.spec_id}` | {spec.pillar_dir} | {spec.label} | Archetype for {spec.label} (substitute OA edition) | {r3_tag} | `{mod_name}` | `{decl_name}` | `substituted` |"
                )
            elif idx == 1:
                status = "gap_recorded"
                entry = {
                    "id": spec.spec_id,
                    "pillar": spec.pillar_dir,
                    "author": author_name,
                    "year": years_str,
                    "title": f"Work {spec.label}",
                    "status": status,
                    "r3_principles": [r3_tag],
                    "source_url": "",
                    "gap_reason": "Publisher archive restricted; bibliographic summary recorded from secondary survey.",
                }
                doc_lines.append(
                    f"| `{spec.spec_id}` | {spec.pillar_dir} | {spec.label} | Archetype summary (gap_recorded: publisher restricted) | {r3_tag} | `{mod_name}` | `{decl_name}` | `gap_recorded` |"
                )
            else:
                status = "downloaded"
                rel_pdf = f"{PAPERS_ROOT_REL}/{spec.pillar_dir}/{spec.spec_id}.pdf"
                pdf_bytes = f"%PDF-1.4\n% Synthetic primary source {spec.label}\n".encode("utf-8")
                (root / rel_pdf).write_bytes(pdf_bytes)
                sha = hashlib.sha256(pdf_bytes).hexdigest()
                entry = {
                    "id": spec.spec_id,
                    "pillar": spec.pillar_dir,
                    "author": author_name,
                    "year": years_str,
                    "title": f"Work {spec.label}",
                    "status": status,
                    "r3_principles": [r3_tag],
                    "source_url": f"https://example.org/{spec.spec_id}.pdf",
                    "local_path": rel_pdf,
                    "size_bytes": len(pdf_bytes),
                    "sha256": sha,
                }
                doc_lines.append(
                    f"| `{spec.spec_id}` | {spec.pillar_dir} | {spec.label} | Archetype for {spec.label} | {r3_tag} | `{mod_name}` | `{decl_name}` | `downloaded` |"
                )

            manifest_data["works"].append(entry)

        (root / MANIFEST_REL).write_text(json.dumps(manifest_data, indent=2), encoding="utf-8")
        doc_path = root / ARCHETYPES_DOC_REL
        doc_path.parent.mkdir(parents=True, exist_ok=True)
        doc_path.write_text("\n".join(doc_lines) + "\n", encoding="utf-8")

    if include_lean_files:
        lean_fixtures: dict[str, str] = {
            "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.Projective.GrassmannPrimarySources

def grassmannRegressiveSL (V : Type*) : Type* := V
def syncyclicContractLeft (V : Type*) : Type* := V
def pluckerLineCoord (V : Type*) : Type* := V

theorem kleinQuadricDecomposable (V : Type*) (SL : LinearMap.det) (x : V) : x = x := by
  rfl

end InfoGeometry.Projective.GrassmannPrimarySources
""",
            "lean/InfoGeometry/Erlangen/LieKleinPfaffCartanPrimary.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary

structure ErlangenSubgeometryLattice where
  carrier : Type*
  lineSphere : Nat
  cayleyKlein : Nat

def pfaffianDerivedClass : Nat := 3
def cartanG2Flag : Nat := 5
def zornSplitOctonionMoufang : Nat := 8

theorem erlangenSubgeometryLattice_valid : pfaffianDerivedClass + 2 = cartanG2Flag := by
  rfl

theorem darbouzPfaffCharacteristic : zornSplitOctonionMoufang = 8 := by
  rfl

end InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary
""",
            "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.Clifford.LipschitzWittRieszPrimary

def lipschitzGroup (R M : Type*) (Q : QuadraticForm R M) : Type* := M
def rieszGradeSplit (K V : Type*) (Q : QuadraticForm K V) : Type* := V
def equivExteriorReverse (K V : Type*) (Q : QuadraticForm K V) : Type* := V

theorem lipschitzTwistedIsometry (R M : Type*) (Q : QuadraticForm R M) : Q = Q := by
  rfl

theorem wittHyperbolicCancellation (K V : Type*) (Q : QuadraticForm K V) : Q = Q := by
  rfl

end InfoGeometry.Clifford.LipschitzWittRieszPrimary
""",
            "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary

def kahlerInnerOuterCodiff : Nat := 1
def hestenesMovingFrameRotor : Nat := 2
def jwParityStringEvenOdd : Nat := 3
def absGradedTensorGrothendieck (A : Type*) [GradedTensorProduct] [CliffordAlgebra.evenOdd] : Type* := A

theorem kahlerDiracSquare : kahlerInnerOuterCodiff + 1 = hestenesMovingFrameRotor := by
  rfl

theorem absGradedModuleBridge : (-1 : ℤˣ) ^ 2 = 1 := by
  rfl

end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary
""",
            "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary

structure PeirceDecomp where
  peirceIdempotent : Nat
  nilpotentRadical : Nat

def maurerCartanActionThetaL (K : LieActionLane) : Nat := 0
def duboisVioletteCenterLieRinehart (K : IsLeibnizAction) : Nat := 1
def karoubiConnesUniversalOneForm : Nat := 2
def frechetFderivBanachCartanHomotopy : Nat := 3

theorem peirceOrthogonalIdempotent (e : Nat) (he : e = 1) : e * e = e := by
  subst he
  rfl
theorem koszulConnectionCurvature (K : LieActionLane) : maurerCartanActionThetaL K = 0 := rfl

end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary
""",
            "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.Thermo.OnsagerCasimirKBMPrimary

def onsagerCasimirReciprocity : Nat := 1
def kuboBogoliubovDuhamelMori : Nat := 2

theorem casimirJReciprocity : onsagerCasimirReciprocity = 1 := by
  rfl

end InfoGeometry.Thermo.OnsagerCasimirKBMPrimary
""",
            "lean/InfoGeometry/Krein/PontryaginSpace.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.Krein.PontryaginSpace

class PontryaginSpace (H : Type*) extends KreinSpace H where
  kappa : Nat

def diracPauliKreinInner : Nat := 1
def isKreinIsometryWitness : Nat := 2
def isKreinSkewAdjointWitness : Nat := 3

theorem kreinIndefiniteContrast (H : Type*) [PontryaginSpace H] :
    (PontryaginSpace.kappa (H := H)) = PontryaginSpace.kappa := by
  rfl

theorem pontryaginInvariantSubspace : diracPauliKreinInner + 1 = isKreinIsometryWitness := by
  rfl

end InfoGeometry.Krein.PontryaginSpace
""",
            "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean": f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
namespace InfoGeometry.KK.KreinSpectralTriplePrimary

structure KreinSpectralTriplePrimary where
  jCLM : Nat
  gradeCLM : Nat
  chi : Nat
  K : Nat
  J_real : Nat
  modularDelta : Nat
  kasparovEvenOdd : Nat
  realKreinCompat : Nat

theorem tomitaKasparovCycle : (1 : Nat) = 1 := rfl
theorem kreinSpectralTripleSeparated (T : KreinSpectralTriplePrimary) : T.jCLM = T.jCLM := rfl

end InfoGeometry.KK.KreinSpectralTriplePrimary
""",
            BRIDGE_FILE_REL: f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
import InfoGeometry.Projective.GrassmannPrimarySources
import InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary
import InfoGeometry.Clifford.LipschitzWittRieszPrimary
import InfoGeometry.Clifford.KahlerHestenesJWABSPrimary
import InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary
import InfoGeometry.Thermo.OnsagerCasimirKBMPrimary
import InfoGeometry.Krein.PontryaginSpace
import InfoGeometry.KK.KreinSpectralTriplePrimary

namespace InfoGeometry.Canonical.PrimarySourceFourPillarBridge

def fourPillarWitness : Nat := 4

theorem fourPillarUnifiedBridge : fourPillarWitness = 4 := rfl

end InfoGeometry.Canonical.PrimarySourceFourPillarBridge
""",
            TRIANGLE_BRIDGE_REL: f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
import InfoGeometry.Canonical.PrimarySourceFourPillarBridge
namespace InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
def ok : Nat := 1
end InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
""",
            CANONICAL_ALL_REL: f"""{REQUIRED_LEAN_COPYRIGHT_HEADER}
import InfoGeometry.Canonical.PrimarySourceFourPillarBridge
""",
        }
        for rel, content in lean_fixtures.items():
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content, encoding="utf-8")

    return manifest_data


class PrimarySourcesE2ETests(unittest.TestCase):
    def test_founder_year_spec_covers_46_works_across_4_pillars(self) -> None:
        self.assertEqual(len(FOUNDER_YEAR_SPEC), 46)
        pillars = {s.pillar for s in FOUNDER_YEAR_SPEC}
        self.assertEqual(pillars, {"r2_f25", "r3", "r1", "r2_m35"})

    def test_no_lean_files_inside_tests_primary_sources(self) -> None:
        ps_dir = REPO_ROOT / "tests" / "primary_sources"
        self.assertEqual(list(ps_dir.rglob("*.lean")), [])

    def test_valid_synthetic_repo_passes_tiers_1_to_3_strict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=True)
            report = run_suite(
                repo_root=root,
                tier="all",
                mode="strict",
                run_lean_commands=False,
            )
            self.assertEqual(report["exit_code"], 0, msg=json.dumps(report, indent=2))
            self.assertEqual(report["summary"]["failed"], 0)
            self.assertEqual(report["summary"]["pending"], 0)

    def test_corrupted_sha256_fails_manifest_even_in_partial_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            m_path = root / MANIFEST_REL
            data = json.loads(m_path.read_text(encoding="utf-8"))
            data["works"][0]["sha256"] = "0" * 64
            m_path.write_text(json.dumps(data), encoding="utf-8")

            out, _ = validate_manifest(root)
            self.assertEqual(out.status, "FAIL")
            self.assertIn("sha256 mismatch", out.summary)

            report = run_suite(repo_root=root, tier="1", mode="partial", run_lean_commands=False)
            self.assertEqual(report["exit_code"], 1)

    def test_missing_founder_work_fails_manifest_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            m_path = root / MANIFEST_REL
            data = json.loads(m_path.read_text(encoding="utf-8"))
            data["works"] = [w for w in data["works"] if w["id"] != "r1_onsager_1931"]
            data["total_works"] = len(data["works"])
            m_path.write_text(json.dumps(data), encoding="utf-8")

            out, _ = validate_manifest(root)
            self.assertEqual(out.status, "FAIL")
            self.assertIn("Onsager (1931)", out.summary)

    def test_path_traversal_in_manifest_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            m_path = root / MANIFEST_REL
            data = json.loads(m_path.read_text(encoding="utf-8"))
            data["works"][0]["local_path"] = "../../etc/passwd"
            m_path.write_text(json.dumps(data), encoding="utf-8")

            out, _ = validate_manifest(root)
            self.assertEqual(out.status, "FAIL")
            self.assertIn("escapes", out.summary)

    def test_honest_gap_parity_omission_fails_archetypes_doc(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            doc_path = root / ARCHETYPES_DOC_REL
            txt = doc_path.read_text(encoding="utf-8")
            txt = txt.replace("gap_recorded: publisher restricted", "full derivation verified")
            txt = txt.replace("`gap_recorded`", "`downloaded`")
            doc_path.write_text(txt, encoding="utf-8")

            out, _ = validate_archetypes_doc(root, manifest=manifest)
            self.assertEqual(out.status, "FAIL")
            self.assertIn("Honest gap parity", out.summary)

    def test_missing_apache_header_and_sorry_native_decide_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=True)
            target = root / "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean"
            bad_body = (
                "\n"
                + target.read_text(encoding="utf-8")
                + "\ntheorem bad_hole : 1 = 1 := by sorry\n"
                + "theorem bad_nd : 1 = 1 := by native_decide\n"
            )
            target.write_text(bad_body, encoding="utf-8")

            hdr = check_apache_header_byte0(["lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean"], root)
            self.assertEqual(hdr.status, "FAIL")
            fb = check_forbidden_tokens_and_prop_wrappers(["lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean"], root)
            self.assertEqual(fb.status, "FAIL")
            self.assertIn("sorry", fb.summary)

    def test_tracked_papers_file_fails_git_hygiene_even_in_partial_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "Test"], cwd=root, check=True)
            (root / ".gitignore").write_text("/scratch/\n", encoding="utf-8")
            (root / ".papers" / "primary_sources").mkdir(parents=True, exist_ok=True)
            (root / ".papers" / "primary_sources" / "leaked.pdf").write_bytes(b"%PDF-1.4\n")
            subprocess.run(["git", "add", ".gitignore", ".papers/primary_sources/leaked.pdf"], cwd=root, check=True)

            out = check_papers_git_hygiene(root)
            self.assertEqual(out.status, "FAIL")

            report = run_suite(repo_root=root, tier="all", mode="partial", run_lean_commands=False)
            self.assertEqual(report["exit_code"], 1)

    def test_stray_lean_file_in_tests_primary_sources_fails_hygiene(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / ".gitignore").write_text(".papers/\n", encoding="utf-8")
            (root / "tests" / "primary_sources").mkdir(parents=True, exist_ok=True)
            (root / "tests" / "primary_sources" / "StrayProbe.lean").write_text("def x := 1\n", encoding="utf-8")

            out = check_papers_git_hygiene(root)
            self.assertEqual(out.status, "FAIL")
            self.assertIn("Forbidden .lean files", out.summary)

    def test_r31_wick_collapse_and_retired_stub_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=False)
            p1 = root / "lean/InfoGeometry/Krein/PontryaginSpace.lean"
            p1.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}import InfoGeometry.Krein.KreinPontryaginCPTBridge\ndef J := ContinuousLinearMap.id\n",
                encoding="utf-8",
            )
            p2 = root / "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean"
            p2.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}theorem bad : gradeCLM = jCLM := rfl\n",
                encoding="utf-8",
            )
            res = check_r3_compliance(
                [
                    "lean/InfoGeometry/Krein/PontryaginSpace.lean",
                    "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean",
                ],
                root,
            )
            by_id = {r.check_id: r for r in res}
            self.assertIn("T2-R3.1-KREIN-SEPARATION", by_id)
            self.assertEqual(by_id["T2-R3.1-KREIN-SEPARATION"].status, "FAIL")

    def test_r32_metric_dependent_grassmann_and_matrix_clifford_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=False)
            g = root / "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean"
            g.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "def regressiveBad (V : Type*) [InnerProductSpace ℝ V] : V := ExteriorRegressive.hodge\n",
                encoding="utf-8",
            )
            c = root / "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean"
            c.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "theorem lipschitzBad (Q : QuadraticForm ℝ (Fin 4 → ℝ)) : True := trivial\n",
                encoding="utf-8",
            )
            res = check_r3_compliance(
                [
                    "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean",
                    "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean",
                ],
                root,
            )
            by_id = {r.check_id: r for r in res}
            self.assertIn("T2-R3.2-METRIC-BASIS-FREE", by_id)
            self.assertEqual(by_id["T2-R3.2-METRIC-BASIS-FREE"].status, "FAIL")
            self.assertIn("InnerProductSpace", by_id["T2-R3.2-METRIC-BASIS-FREE"].summary)

    def test_r33_ungraded_tensor_alghom_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=False)
            k = root / "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean"
            k.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "def absUngraded (A B : Type*) : TensorProduct A B →ₐ[ℝ] A := sorry\n",
                encoding="utf-8",
            )
            res = check_r3_compliance(["lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean"], root)
            by_id = {r.check_id: r for r in res}
            self.assertIn("T2-R3.3-KOSZUL-Z2-GRADING", by_id)
            self.assertEqual(by_id["T2-R3.3-KOSZUL-Z2-GRADING"].status, "FAIL")

    def test_r34_faithful_required_and_global_diamond_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=False)
            p = root / "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean"
            p.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "open scoped Erlangen20Unification\n"
                "instance instAlgebraClTower : Nat := 0\n"
                "theorem coreCE (K : DerivationLieLane) (h : DerivationLieLane.faithful) : True := trivial\n",
                encoding="utf-8",
            )
            res = check_r3_compliance(["lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean"], root)
            self.assertEqual(len(res), 1)
            self.assertEqual(res[0].status, "FAIL")

    def test_hallucinated_or_empty_traceability_row_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = _build_synthetic_repo(root, include_lean_files=True, include_m1=True)
            doc_path = root / ARCHETYPES_DOC_REL
            txt = doc_path.read_text(encoding="utf-8").replace("`casimirJReciprocity`", "`TBD`")
            doc_path.write_text(txt, encoding="utf-8")
            rows = parse_traceability_matrix(txt)
            out = check_traceability_kernel(rows, manifest, repo_root=root, run_lean_kernel=False)
            self.assertEqual(out.status, "FAIL")

    def test_strict_vs_partial_mode_and_half_started_milestones(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=False, include_m1=False)

            # 1. Completely empty M1-M6: strict fails (exit 1), partial passes (exit 0) with PENDING_MISSING
            strict_rep = run_suite(repo_root=root, tier="all", mode="strict", run_lean_commands=False)
            self.assertEqual(strict_rep["exit_code"], 1)
            self.assertGreater(strict_rep["summary"]["failed"], 0)

            partial_rep = run_suite(repo_root=root, tier="all", mode="partial", run_lean_commands=False)
            self.assertEqual(partial_rep["exit_code"], 0)
            self.assertTrue(partial_rep["partial_banner"])
            self.assertGreater(partial_rep["summary"]["pending"], 0)

            # 2. Half-started M2 (one file present, sibling absent): fails EVEN in partial mode!
            m2_one = root / "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean"
            m2_one.parent.mkdir(parents=True, exist_ok=True)
            m2_one.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}namespace GrassmannPrimarySources\ndef regressiveSL := 1\ntheorem slCov : regressiveSL = 1 := rfl\nend GrassmannPrimarySources\n",
                encoding="utf-8",
            )
            half_rep = run_suite(repo_root=root, tier="all", mode="partial", run_lean_commands=False)
            self.assertEqual(half_rep["exit_code"], 1)
            half_ids = {o["check_id"] for o in half_rep["outcomes"] if o["status"] == "FAIL"}
            self.assertIn("T1-M2-HALF-STARTED", half_ids)

    def test_live_repo_git_hygiene_and_lean_invariant(self) -> None:
        git_out = check_papers_git_hygiene(REPO_ROOT)
        self.assertEqual(git_out.status, "PASS", msg=git_out.summary)
        inv_out = check_repo_lean_invariants(REPO_ROOT, require_m6_in_all=False)
        self.assertEqual(inv_out.status, "PASS", msg=inv_out.summary)

    def test_live_repo_anchor_r3_and_forbidden_checks(self) -> None:
        anchors = [
            "lean/InfoGeometry/Canonical/R1R2R3UnifiedTriangleBridge.lean",
            "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
            "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
            "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
            "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean",
            "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean",
        ]
        fb = check_forbidden_tokens_and_prop_wrappers(anchors, REPO_ROOT)
        self.assertEqual(fb.status, "PASS", msg=fb.summary)
        r3_outs = check_r3_compliance(anchors, REPO_ROOT)
        for out in r3_outs:
            self.assertEqual(out.status, "PASS", msg=f"{out.check_id}: {out.summary}")

    def test_parse_axiom_index_output_strict_validation(self) -> None:
        mods = ["InfoGeometry.Foo", "InfoGeometry.Bar"]
        clean_stdout = (
            "Scanning 2 module(s)...\n"
            "  [1/2] InfoGeometry.Foo: ✓ 12 decls, 0✗ 0p 0u\n"
            "  [2/2] InfoGeometry.Bar: ✓ 8 decls, 0✗ 0p 0u\n"
            '{"modules": 2, "declarations": 20, "axiom_usage": {"propext": 5, "Classical.choice": 2}, "axiomless": ["InfoGeometry.Foo", "InfoGeometry.Bar"], "suspicious": {}}\n'
        )
        ok, summary, details = parse_axiom_index_output(clean_stdout, mods)
        self.assertTrue(ok, msg=summary)
        self.assertEqual(details["per_module"]["InfoGeometry.Foo"]["decls"], 12)

        # sorryAx in axiom_usage + nstd > 0 must fail
        sorry_stdout = (
            "  [1/2] InfoGeometry.Foo: ! 12 decls, 1✗ 0p 0u\n"
            "  [2/2] InfoGeometry.Bar: ✓ 8 decls, 0✗ 0p 0u\n"
            '{"modules": 2, "declarations": 20, "axiom_usage": {"propext": 5, "sorryAx": 1}, "axiomless": ["InfoGeometry.Bar"], "suspicious": {}}\n'
        )
        ok_s, sum_s, _ = parse_axiom_index_output(sorry_stdout, mods)
        self.assertFalse(ok_s)
        self.assertIn("sorryAx", sum_s)

        # partial/unsafe counts > 0 must fail even if axiom_usage is clean
        part_stdout = (
            "  [1/2] InfoGeometry.Foo: ✓ 12 decls, 0✗ 1p 0u\n"
            "  [2/2] InfoGeometry.Bar: ✓ 8 decls, 0✗ 0p 1u\n"
            '{"modules": 2, "declarations": 20, "axiom_usage": {"propext": 5}, "axiomless": ["InfoGeometry.Foo", "InfoGeometry.Bar"], "suspicious": {}}\n'
        )
        ok_p, sum_p, _ = parse_axiom_index_output(part_stdout, mods)
        self.assertFalse(ok_p)
        self.assertIn("p=1", sum_p)
        self.assertIn("u=1", sum_p)

        # missing module line must fail
        missing_stdout = (
            "  [1/2] InfoGeometry.Foo: ✓ 12 decls, 0✗ 0p 0u\n"
            '{"modules": 1, "declarations": 12, "axiom_usage": {"propext": 5}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n'
        )
        ok_m, sum_m, _ = parse_axiom_index_output(missing_stdout, mods)
        self.assertFalse(ok_m)
        self.assertIn("InfoGeometry.Bar", sum_m)

    def test_run_olean_axiom_audits_uses_axiom_index_by_default(self) -> None:
        clean_stdout = (
            "  [1/1] InfoGeometry.Foo: ✓ 4 decls, 0✗ 0p 0u\n"
            '{"modules": 1, "declarations": 4, "axiom_usage": {"propext": 1}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n'
        )
        calls: list[list[str]] = []

        def fake_run(cmd: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
            calls.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, stdout=clean_stdout, stderr="")

        with patch("tests.primary_sources.lean_audit.subprocess.run", side_effect=fake_run):
            outcomes = run_olean_axiom_audits(["InfoGeometry.Foo"])

        self.assertEqual([o.check_id for o in outcomes], ["T4-OLEAN-AXIOM-INDEX"])
        self.assertEqual(outcomes[0].status, "PASS")
        self.assertEqual(len(calls), 1)
        self.assertTrue(calls[0][1].endswith("tools/infra/axiom_index.py"))
        self.assertIn("--batch", calls[0])
        self.assertIn("--json", calls[0])

    # ---- Iteration 2 Regression Tests for All Verifier Counterexamples ----

    def test_composed_r3_bypass_rejected_strict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=True)

            (root / "lean/InfoGeometry/Krein/PontryaginSpace.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Krein.PontryaginSpace\n"
                "abbrev PontryaginSpace (H : Type*) := HilbertSpace H\n"
                "private def _unused (_ : KreinSpace Nat) : Nat := 0\n"
                "def J := fun x : Nat => x\n"
                "def diracPauliKreinInner : Nat := 1\n"
                "theorem kreinIndefiniteContrast : diracPauliKreinInner = 1 := rfl\n"
                "theorem pontryaginInvariantSubspace : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Krein.PontryaginSpace\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.KK.KreinSpectralTriplePrimary\n"
                "def jCLM : (Nat →L[ℝ] Nat) := ContinuousLinearMap.id ℝ Nat\n"
                "def gradeCLM := jCLM\n"
                "def archimedean := 0\n"
                "def J_real : Nat := 1\n"
                "def modularDelta : Nat := 1\n"
                "def kasparovEvenOdd : Nat := 1\n"
                "theorem tomitaKasparovCycle : (1 : Nat) = 1 := rfl\n"
                "theorem kreinSpectralTripleSeparated : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.KK.KreinSpectralTriplePrimary\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Projective.GrassmannPrimarySources\n"
                "section\n"
                "variable (V : Type*) [InnerProductSpace ℝ V] [Module.Basis Nat ℝ V]\n"
                "def grassmannRegressiveSL (V : Type*) (SL : LinearMap.det) : Type* := V\n"
                "end\n"
                "def regressiveNoHodge (V : Type*) : V := ExteriorRegressive.hodge\n"
                "def regressiveBridge (x : Nat) : Nat := ExteriorRegressive.hodge x\n"
                "def pluckerLineCoord : Nat := 1\n"
                "theorem kleinQuadricDecomposable : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Projective.GrassmannPrimarySources\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.LipschitzWittRieszPrimary\n"
                "def lipschitzGroup (n : Nat := 0) (Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 4))) : Nat := n\n"
                "def wittCore (Q : QuadraticForm ℝ (Matrix Nat Nat ℝ)) : Nat := 0\n"
                "def rieszCore (Q : QuadraticForm K (Fin 4 -> K)) : Nat := 0\n"
                "theorem lipschitzTwistedIsometry : (1 : Nat) = 1 := rfl\n"
                "theorem wittHyperbolicCancellation : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Clifford.LipschitzWittRieszPrimary\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n"
                "private def _unusedGradedTensorProduct := 0\n"
                "def koszulNote := 0\n"
                "def kahlerInnerOuterCodiff : Nat := 1\n"
                "def hestenesMovingFrameRotor : Nat := 2\n"
                "def myCarMap (A B : Type*) : (A ⊗[ℝ] B) →ₐ[ℝ] A := by\n"
                "  let parity := 0\n"
                "  exact sorry\n"
                "theorem kahlerDiracSquare : kahlerInnerOuterCodiff + 1 = hestenesMovingFrameRotor := rfl\n"
                "theorem absGradedModuleBridge : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "import Mathlib.RingTheory.Derivation.Lie\n"
                "open scoped Foo Erlangen20Unification\n"
                "noncomputable instance instAlgebraClTower : Nat := 0\n"
                "namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n"
                "section\n"
                "variable (hf : DerivationLieLane.faithful)\n"
                "def koszulCore (K : LieActionLane) [CommRing A] [Derivation ℝ A A] : Nat := 0\n"
                "end\n"
                "theorem peirceOrthogonalIdempotent (h : Function.Injective act) (K : LieActionLane) : True := trivial\n"
                "theorem koszulConnectionCurvature : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n",
                encoding="utf-8",
            )

            report = run_suite(repo_root=root, tier="all", mode="strict", run_lean_commands=False)
            self.assertEqual(report["exit_code"], 1)
            by_id = {o["check_id"]: o for o in report["outcomes"]}
            for r3_cid in (
                "T2-R3.1-KREIN-SEPARATION",
                "T2-R3.2-METRIC-BASIS-FREE",
                "T2-R3.3-KOSZUL-Z2-GRADING",
                "T2-R3.4-LIE-PEIRCE-DIAMONDS",
            ):
                self.assertIn(r3_cid, by_id)
                self.assertEqual(by_id[r3_cid]["status"], "FAIL", msg=f"{r3_cid} unexpectedly passed: {by_id[r3_cid]}")

    def test_placeholder_audit_catches_stub_name_and_scans_temp_repo_root(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            rel = "lean/InfoGeometry/TestDummy.lean"
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}\n"
                "def stub_dummy_impl : Nat := 0\n"
                "theorem stub_theorem : 1 = 1 := rfl\n",
                encoding="utf-8",
            )
            strict_outs = {o.check_id: o for o in run_scoped_quality_tools([rel], root, strict_placeholder_names=True)}
            self.assertEqual(strict_outs["T2-PLACEHOLDER-AUDIT"].status, "FAIL")
            self.assertIn("stub_dummy_impl", strict_outs["T2-PLACEHOLDER-AUDIT"].summary)

            anchor_outs = {o.check_id: o for o in run_scoped_quality_tools([rel], root, strict_placeholder_names=False)}
            self.assertEqual(anchor_outs["T2-PLACEHOLDER-AUDIT"].status, "PASS")

    def test_quality_gate_hardening_crlf_interpolated_sorry_indented_prop_wrappers(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # 1. CRLF header must fail byte-0 check
            crlf_rel = "lean/InfoGeometry/Crlf.lean"
            (root / crlf_rel).parent.mkdir(parents=True, exist_ok=True)
            (root / crlf_rel).write_bytes(
                REQUIRED_LEAN_COPYRIGHT_HEADER.replace("\n", "\r\n").encode("utf-8") + b"def ok : Nat := 1\n"
            )
            self.assertEqual(check_apache_header_byte0([crlf_rel], root).status, "FAIL")

            # 2. Interpolated s!"{by sorry}", @[inline] opaque, 5-space unsafe/partial, 1-field & by constructor Prop wrappers
            bad_rel = "lean/InfoGeometry/BadGates.lean"
            (root / bad_rel).write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                'def msg : String := s!"{by sorry}"\n'
                "@[inline] opaque sneakyOpaque : Nat\n"
                "     unsafe def sneakyUnsafe : Nat := 0\n"
                "     partial def sneakyPartial (n : Nat) : Nat := sneakyPartial n\n"
                "structure SingleProp : Prop where\n  w : ∀ x : Nat, True\n"
                "theorem single_wrap : SingleProp := ⟨fun _ => trivial⟩\n"
                "structure TwoProp : Prop where\n  a : True\n  b : True\n"
                "theorem two_wrap : TwoProp := by constructor\n  trivial\n  trivial\n",
                encoding="utf-8",
            )
            fb = check_forbidden_tokens_and_prop_wrappers([bad_rel], root)
            self.assertEqual(fb.status, "FAIL")
            joined = "\n".join(fb.details["failures"])
            self.assertIn("sorry", joined)
            self.assertIn("opaque", joined)
            self.assertIn("unsafe", joined)
            self.assertIn("partial", joined)
            self.assertIn("SingleProp", joined)
            self.assertIn("TwoProp", joined)

            # 3. Parser handles 5-space indent, (n : Nat := 0) binder, >40-line header, and section variables
            long_binders = "\n".join(f"  (x{i} : Nat)" for i in range(45))
            parsed = parse_lean_declarations(
                "section\n"
                "variable [InnerProductSpace ℝ V]\n"
                "     theorem indented_thm (n : Nat := 0) :\n"
                f"{long_binders}\n"
                "  → True := by trivial\n"
                "end\n"
            )
            self.assertEqual([d.short_name for d in parsed], ["indented_thm"])
            self.assertIn("InnerProductSpace", parsed[0].effective_header)
            self.assertIn("x44", parsed[0].header_text)

    def test_feature_presence_rejects_namespace_spoof_and_allows_f17_either_m4_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            p_rel = "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean"
            t_rel = "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean"
            (root / p_rel).parent.mkdir(parents=True, exist_ok=True)
            (root / t_rel).parent.mkdir(parents=True, exist_ok=True)
            (root / p_rel).write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n"
                "def dummy : Nat := 1\n"
                "theorem dummy_thm : dummy = 1 := rfl\n"
                "end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n",
                encoding="utf-8",
            )
            self.assertEqual(check_feature_lean_presence(13, root).status, "FAIL")
            self.assertEqual(check_feature_lean_presence(15, root).status, "FAIL")

            # Feature #17 passes in OnsagerCasimirKBMPrimary.lean per M1 docs/PRIMARY_SOURCE_ARCHETYPES.md
            (root / t_rel).write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Thermo.OnsagerCasimirKBMPrimary\n"
                "def frechetBanachForm : Nat := 1\n"
                "theorem cartanHomotopy_thm : frechetBanachForm = 1 := rfl\n"
                "end InfoGeometry.Thermo.OnsagerCasimirKBMPrimary\n",
                encoding="utf-8",
            )
            self.assertEqual(check_feature_lean_presence(17, root).status, "PASS")

    def test_traceability_ranges_multimodule_gap_spoofing_and_planned_strict(self) -> None:
        self.assertEqual(expand_traceability_work_ids("S2-03..S2-04 Plücker"), ["S2-03", "S2-04"])
        self.assertEqual(expand_traceability_work_ids("S2-01, S2-02"), ["S2-01", "S2-02"])
        self.assertEqual(
            expand_traceability_work_ids("S3-01..10 Peirce, Maurer-Cartan"),
            [f"S3-{i:02d}" for i in range(1, 11)],
        )
        with self.assertRaises(ValueError):
            expand_traceability_work_ids("S2-05..03")
        with self.assertRaises(ValueError):
            expand_traceability_work_ids("S2-01..99")
        with self.assertRaises(ValueError):
            expand_traceability_work_ids("S2-03..")

        # Multi-module M6 row parsing + garbage rejection
        rows = parse_traceability_matrix(
            "| Work ID | Pillar | Author | Archetype | R3 | Lean Module | Lean Declaration(s) | Status |\n"
            "|---|---|---|---|---|---|---|---|\n"
            "| `M6` | all | All | Unified | All `R3.1`–`R3.4` | `M6`: `lean/InfoGeometry/Canonical/PrimarySourceFourPillarBridge.lean`, `R1R2R3UnifiedTriangleBridge.lean`, `docs/PRIMARY_SOURCE_ARCHETYPES.md` | `fourPillarUnifiedBridge` | `PLANNED` |\n"
            "| `S2-01` | pillar_r2_f25 | Grassmann | Meet | `R3.2` | `lean/InfoGeometry/Foo.lean GARBAGE` | `foo` | `IMPLEMENTED` |\n"
        )
        self.assertEqual(
            rows[0].lean_modules,
            (
                "InfoGeometry.Canonical.PrimarySourceFourPillarBridge",
                "InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge",
            ),
        )
        self.assertEqual(rows[0].module_errors, ())
        self.assertTrue(rows[1].module_errors)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = _build_synthetic_repo(root, include_lean_files=True, include_m1=True)
            doc_path = root / ARCHETYPES_DOC_REL
            txt = doc_path.read_text(encoding="utf-8")

            # Spoof non-gap work r2f25_grassmann_1844 as gap_recorded in traceability table
            spoof_txt = txt.replace(
                "| `r2f25_grassmann_1844` | pillar_r2_f25 | Grassmann (1844) | Archetype for Grassmann (1844) (substitute OA edition) | R3.2 | `InfoGeometry.Projective.GrassmannPrimarySources` | `grassmannRegressiveSL` | `substituted` |",
                "| `r2f25_grassmann_1844` | pillar_r2_f25 | Grassmann (1844) | Archetype for Grassmann (1844) | R3.2 | `INVALID_MODULE` | `[M2 TBD]` | `gap_recorded` |",
            )
            spoof_rows = parse_traceability_matrix(spoof_txt)
            out_gap = check_traceability_kernel(spoof_rows, manifest, repo_root=root, run_lean_kernel=False)
            self.assertEqual(out_gap.status, "FAIL")
            self.assertIn("gap_recorded", out_gap.summary)

            # PLANNED row must FAIL in strict mode even when run_lean_commands=False
            planned_txt = txt.replace("`casimirJReciprocity` | `downloaded`", "`[M4 TBD]` | `PLANNED`")
            doc_path.write_text(planned_txt, encoding="utf-8")
            strict_rep = run_suite(repo_root=root, tier="3", mode="strict", run_lean_commands=False)
            self.assertEqual(strict_rep["exit_code"], 1)

    def test_m1_completeness_r3_tags_bytes_and_gap_parity_hardening(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            m_path = root / MANIFEST_REL

            # 1. Deleting S2-07 (Klein 1871/1873) and S3-01 (B. Peirce) even with updated total_works fails
            data = json.loads(m_path.read_text(encoding="utf-8"))
            data["works"] = [
                w for w in data["works"]
                if w["id"] not in {"r2f25_klein_1871_1873", "r1_b_peirce_1870_1881"}
            ]
            data["total_works"] = len(data["works"])
            m_path.write_text(json.dumps(data), encoding="utf-8")
            out_del, _ = validate_manifest(root)
            self.assertEqual(out_del.status, "FAIL")

            # 2. Empty r3_principles and omitted size_bytes fail
            _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            data2 = json.loads(m_path.read_text(encoding="utf-8"))
            data2["works"][0]["r3_principles"] = []
            del data2["works"][2]["size_bytes"]
            m_path.write_text(json.dumps(data2), encoding="utf-8")
            out_r3, _ = validate_manifest(root)
            self.assertEqual(out_r3.status, "FAIL")
            errs_joined = "\n".join(out_r3.details["errors"])
            self.assertIn("r3_principles", errs_joined)
            self.assertIn("bytes", errs_joined)

            # 3. TBD R3 column + "1st edition" gap_recorded bypass fail validate_archetypes_doc
            _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            doc_path = root / ARCHETYPES_DOC_REL
            doc_txt = doc_path.read_text(encoding="utf-8")
            bad_doc = doc_txt.replace("gap_recorded: publisher restricted", "1st edition").replace("`gap_recorded`", "`downloaded`")
            bad_doc = bad_doc.replace("| R3.2 |", "| TBD |", 1)
            doc_path.write_text(bad_doc, encoding="utf-8")
            out_doc, _ = validate_archetypes_doc(root, manifest=manifest)
            self.assertEqual(out_doc.status, "FAIL")
            doc_errs = "\n".join(out_doc.details["errors"])
            self.assertIn("R3.1-R3.4", doc_errs)
            self.assertIn("Honest gap parity", doc_errs)

    def test_cli_tier_pillar_check_id_isolation_and_contradictory_flags(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=True)

            # Contradictory --mode strict --partial-ok -> exit 2
            self.assertEqual(
                cli_main(["--repo-root", str(root), "--tier", "1", "--mode", "strict", "--partial-ok", "--no-reports"]),
                2,
            )

            # --tier 1 must NOT include T2-GIT-HYGIENE; --tier 3 must NOT include T2-GIT-HYGIENE
            r_t1 = run_suite(repo_root=root, tier="1", mode="partial", run_lean_commands=False)
            self.assertNotIn("T2-GIT-HYGIENE", {o["check_id"] for o in r_t1["outcomes"]})
            r_t3 = run_suite(repo_root=root, tier="3", mode="partial", run_lean_commands=False)
            self.assertNotIn("T2-GIT-HYGIENE", {o["check_id"] for o in r_t3["outcomes"]})

            # --pillar r2_f25 must NOT include T2-R3.4 or M6 T1-F23 / T3-FOUR-PILLAR-BRIDGE
            r_p1 = run_suite(repo_root=root, tier="all", mode="strict", pillar="r2_f25", run_lean_commands=False)
            p1_ids = {o["check_id"] for o in r_p1["outcomes"]}
            self.assertNotIn("T2-R3.4-LIE-PEIRCE-DIAMONDS", p1_ids)
            self.assertNotIn("T1-F23", p1_ids)
            self.assertNotIn("T3-FOUR-PILLAR-BRIDGE", p1_ids)

            # --check-id T4-REPO-LEAN-INVARIANT must NOT invoke run_batched_lake_build
            with patch("tests.primary_sources.verify_primary_sources_e2e.run_batched_lake_build") as mock_build:
                r_cid = run_suite(
                    repo_root=root,
                    tier="4",
                    mode="strict",
                    check_id="T4-REPO-LEAN-INVARIANT",
                    run_lean_commands=True,
                )
                mock_build.assert_not_called()
            self.assertEqual([o["check_id"] for o in r_cid["outcomes"]], ["T4-REPO-LEAN-INVARIANT"])

    def test_parse_axiom_index_output_rejects_zero_decls_and_multiple_json(self) -> None:
        mods = ["InfoGeometry.Foo"]
        zero_stdout = (
            "  [1/1] InfoGeometry.Foo: ✓ 0 decls, 0✗ 0p 0u\n"
            '{"modules": 1, "declarations": 0, "axiom_usage": {}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n'
        )
        ok_z, sum_z, _ = parse_axiom_index_output(zero_stdout, mods)
        self.assertFalse(ok_z)
        self.assertIn("0 decls", sum_z)

        dual_json = (
            "  [1/1] InfoGeometry.Foo: ✓ 5 decls, 0✗ 0p 0u\n"
            '{"modules": 1, "declarations": 5, "axiom_usage": {"sorryAx": 1}, "axiomless": [], "suspicious": {}}\n'
            '{"modules": 1, "declarations": 5, "axiom_usage": {}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n'
        )
        with self.assertRaises(ValueError):
            parse_axiom_index_output(dual_json, mods)

    def test_r3_kernel_probe_uses_core_string_contains_and_checks_pontryagin_krein(self) -> None:
        # Verify probe generation uses Lean 4.34.1 core String.contains (never deprecated Batteries containsSubstr)
        # and checks PontryaginSpace.toKreinSpace/mk + KreinSpectralTriplePrimary + Module.Basis + LipschitzWittRieszPrimary
        captured: list[str] = []

        def fake_probe(probe_name: str, imports: list[str], body: str, **kwargs: Any) -> tuple[bool, int, str, str, str]:
            captured.append(body)
            return True, 0, "", "", ""

        with patch("tests.primary_sources.lean_audit.run_locked_lean_probe", side_effect=fake_probe):
            out = run_r3_kernel_probe(
                [
                    "InfoGeometry.Krein.PontryaginSpace",
                    "InfoGeometry.KK.KreinSpectralTriplePrimary",
                    "InfoGeometry.Projective.GrassmannPrimarySources",
                    "InfoGeometry.Clifford.LipschitzWittRieszPrimary",
                    "InfoGeometry.Clifford.KahlerHestenesJWABSPrimary",
                    "InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary",
                ]
            )
        self.assertEqual(out.status, "PASS")
        self.assertEqual(len(captured), 1)
        body = captured[0]
        self.assertNotIn("containsSubstr", body)
        self.assertIn(".contains", body)
        self.assertIn(".toKreinSpace", body)
        self.assertIn("isProjectionFn", body)
        self.assertIn("isIdentityExpr", body)
        self.assertIn("KreinSpectralTriplePrimary", body)
        self.assertIn("Module.Basis", body)
        self.assertIn("MetricSpace", body)
        self.assertIn("NormedSpace", body)
        self.assertIn("LipschitzWittRieszPrimary", body)
        self.assertIn("expandExprConsts", body)
        self.assertIn("KahlerHestenesJWABSPrimary", body)

    # ---- Iteration 3 Regression Tests for Challenger 1 & Challenger 2/Reviewer 2 Findings ----

    def test_in_prefixes_multiline_attrs_f_interp_char_literals_and_prop_wrappers(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bad_rel = "lean/InfoGeometry/TestAxioms.lean"
            (root / bad_rel).parent.mkdir(parents=True, exist_ok=True)
            (root / bad_rel).write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.TestAxioms\n"
                "open Classical in unsafe def sneakyInUnsafe : Nat := 0\n"
                "set_option maxHeartbeats 0 in partial def sneakyInPartial (n : Nat) : Nat := sneakyInPartial n\n"
                "open Classical in axiom sneakyInAxiom : False\n"
                "open Classical in set_option pp.all true in theorem sneaky_bad : (1 : Nat) = 2 := sorry\n"
                "private\n@[simp,\n  ext]\ndef secretPrivate : Nat := 1\n"
                "private\n@[simp,\n  ext]\ntheorem priv_multiline : (2 : Nat) = 2 := rfl\n"
                'def f_interp : String := toString f!"{by sorry}"\n'
                'def brace_char : String := s!"{let c := \'}\'; by sorry}"\n'
                'def brace_open : String := s!"{let c := \'{\'; by admit}"\n'
                "structure MultiLineProp (α : Type*)\n    : Prop where\n  w : ∀ x : α, True\n"
                "theorem ml_wrap : MultiLineProp Nat := ⟨fun _ => trivial⟩\n"
                "structure IsParamProp (α : Type*) : Prop where\n  w : True\n"
                "structure SingleProp : Prop where\n  w : ∀ x : Nat, True\n"
                "theorem single_brace : SingleProp := by exact { w := fun _ => trivial }\n"
                "theorem single_refine : SingleProp := by refine { w := fun _ => trivial }\n"
                "end InfoGeometry.TestAxioms\n",
                encoding="utf-8",
            )
            decls = parse_lean_declarations((root / bad_rel).read_text(encoding="utf-8"))
            by_name = {d.short_name: d for d in decls}
            self.assertIn("sneakyInUnsafe", by_name)
            self.assertIn("sneakyInPartial", by_name)
            self.assertIn("sneakyInAxiom", by_name)
            self.assertIn("sneaky_bad", by_name)
            self.assertIn("secretPrivate", by_name)
            self.assertTrue(by_name["secretPrivate"].is_private)
            self.assertIn("priv_multiline", by_name)
            self.assertTrue(by_name["priv_multiline"].is_private)

            fb = check_forbidden_tokens_and_prop_wrappers([bad_rel], root)
            self.assertEqual(fb.status, "FAIL")
            joined = "\n".join(fb.details["failures"])
            for expected_msg in ("unsafe", "partial", "axiom", "sorry", "admit", "MultiLineProp", "IsParamProp", "SingleProp"):
                self.assertIn(expected_msg, joined, msg=joined)

            # Verify run_print_axioms_probe emits sneaky_bad and omits priv_multiline
            emitted_cmds: list[str] = []

            def fake_probe(probe_name: str, imports: list[str], body: str, **kwargs: Any) -> tuple[bool, int, str, str, str]:
                emitted_cmds.append(body)
                return (
                    True,
                    0,
                    "'InfoGeometry.TestAxioms.sneaky_bad' depends on axioms: [propext]\n"
                    "'InfoGeometry.TestAxioms.ml_wrap' depends on axioms: [propext]\n"
                    "'InfoGeometry.TestAxioms.single_brace' depends on axioms: [propext]\n"
                    "'InfoGeometry.TestAxioms.single_refine' depends on axioms: [propext]\n",
                    "",
                    "",
                )

            with patch("tests.primary_sources.lean_audit.run_locked_lean_probe", side_effect=fake_probe):
                pa_out = run_print_axioms_probe([bad_rel], repo_root=root)
            self.assertEqual(pa_out.status, "PASS", msg=pa_out.summary)
            self.assertIn("#print axioms InfoGeometry.TestAxioms.sneaky_bad", emitted_cmds[0])
            self.assertNotIn("priv_multiline", emitted_cmds[0])

    def test_composed_r3_r2_challenger1_bypass_suite_rejected_strict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=True)

            (root / "lean/InfoGeometry/Krein/PontryaginSpace.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Krein.PontryaginSpace\n"
                "structure PontryaginSpace (H : Type*) where\n"
                "  hilbert : HilbertSpace H\n"
                "  unusedTag : Type* := KreinSpace H\n"
                "def J (x : Nat) : Nat := x\n"
                "def jCLM : (Nat →L[ℝ] Nat) := (ContinuousLinearMap.id ℝ Nat)\n"
                "def diracPauliKreinInner : Nat := 1\n"
                "theorem kreinIndefiniteContrast : diracPauliKreinInner = 1 := rfl\n"
                "theorem pontryaginInvariantSubspace : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Krein.PontryaginSpace\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.KK.KreinSpectralTriplePrimary\n"
                "def jCLM (x : Nat) : Nat := x\n"
                "def gradeCLM : Nat → Nat := (jCLM)\n"
                "def J_real : Nat → Nat := jCLM\n"
                "def modularDelta : Nat := 1\n"
                "def kasparovEvenOdd : Nat := 1\n"
                "theorem tomitaKasparovCycle : (1 : Nat) = 1 := rfl\n"
                "theorem kreinSpectralTripleSeparated : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.KK.KreinSpectralTriplePrimary\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "open Module\n"
                "namespace InfoGeometry.Projective.GrassmannPrimarySources\n"
                "def grassmannRegressiveSL (V : Type*) [Basis Nat ℝ V] (SL : LinearMap.det) : Type* := V\n"
                "def grassmannMetric (V : Type*) [MetricSpace V] : Type* := V\n"
                "def grassmannNormed (V : Type*) [NormedSpace ℝ V] : Type* := V\n"
                "def pluckerLineCoord : Nat := 1\n"
                "theorem kleinQuadricDecomposable [InnerProductSpace ℝ V] [Module.Basis Nat ℝ V] (regressive : V) : regressive = regressive := rfl\n"
                "end InfoGeometry.Projective.GrassmannPrimarySources\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.LipschitzWittRieszPrimary\n"
                "abbrev Vec4 := Fin 4 → ℝ\n"
                "def lipschitzFinGroup (Q : QuadraticForm ℝ (Fin (n + 1) → ℝ)) : Nat := 0\n"
                "def wittMatrixCancel (Q : QuadraticForm ℝ (Matrix Nat Nat ℝ)) : Nat := 0\n"
                "def spinorAction (x : EuclideanSpace ℝ (Fin 4)) : Nat := 0\n"
                "def rieszCore (Q : QuadraticForm ℝ Vec4) : Nat := 0\n"
                "theorem lipschitzTwistedIsometry : (1 : Nat) = 1 := rfl\n"
                "theorem wittHyperbolicCancellation : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Clifford.LipschitzWittRieszPrimary\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n"
                "def kahlerInnerOuterCodiff : Nat := 1\n"
                "def hestenesMovingFrameRotor : Nat := 2\n"
                "def jwParityStringEvenOdd : Nat := 3\n"
                "abbrev ClTower (A B : Type*) := A ⊗[ℝ] B\n"
                "def myCarMap (A B : Type*) : (A ⊗[ℝ] B) →ₐ[ℝ] A := by\n"
                "  let parityString := 0\n"
                "  exact sorry\n"
                "def absGradedModuleBridgeImpl (A B : Type*) : ClTower A B →ₐ[ℝ] A := sorry\n"
                'def msg : String := toString f!"{by sorry}"\n'
                "open Classical in unsafe def sneaky : Nat := 0\n"
                "theorem kahlerDiracSquare : kahlerInnerOuterCodiff + 1 = hestenesMovingFrameRotor := rfl\n"
                "theorem absGradedModuleBridge : (-1 : ℤˣ) ^ 2 = 1 := rfl\n"
                "end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "open InfoGeometry.Canonical (Erlangen20Unification)\n"
                "attribute [instance] InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis.instAlgebraClTower\n"
                "namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n"
                "structure PeirceDecomp where\n  peirceIdempotent : Nat\n  nilpotentRadical : Nat\n"
                "def dvCore (K : LieActionLane) (D : Derivation ℝ A A) : Nat := 0\n"
                "private theorem helper_priv (h : DerivationLieLane.faithful) : h = h := rfl\n"
                "theorem koszulFaithfulCurvature (h : DerivationLieLane.faithful) : h = h := rfl\n"
                "theorem peirceOrthogonalIdempotent (e : Nat) : e = e := rfl\n"
                "theorem koszulConnectionCurvature : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n",
                encoding="utf-8",
            )

            report = run_suite(repo_root=root, tier="all", mode="strict", run_lean_commands=False)
            self.assertEqual(report["exit_code"], 1)
            by_id = {o["check_id"]: o for o in report["outcomes"]}
            for cid in (
                "T2-FORBIDDEN-SCAN",
                "T2-R3.1-KREIN-SEPARATION",
                "T2-R3.2-METRIC-BASIS-FREE",
                "T2-R3.3-KOSZUL-Z2-GRADING",
                "T2-R3.4-LIE-PEIRCE-DIAMONDS",
            ):
                self.assertIn(cid, by_id)
                self.assertEqual(by_id[cid]["status"], "FAIL", msg=f"{cid} unexpectedly passed: {by_id[cid]}")
                if cid == "T2-R3.2-METRIC-BASIS-FREE":
                    errs = "\n".join(by_id[cid]["details"]["errors"])
                    for tok in ("Basis", "MetricSpace", "NormedSpace", "kleinQuadricDecomposable", "lipschitzFinGroup", "wittMatrixCancel", "spinorAction", "Vec4"):
                        self.assertIn(tok, errs, msg=errs)
                if cid == "T2-R3.3-KOSZUL-Z2-GRADING":
                    errs = "\n".join(by_id[cid]["details"]["errors"])
                    self.assertIn("myCarMap", errs, msg=errs)
                    self.assertIn("absGradedModuleBridgeImpl", errs, msg=errs)
                if cid == "T2-R3.4-LIE-PEIRCE-DIAMONDS":
                    errs = "\n".join(by_id[cid]["details"]["errors"])
                    for tok in ("dvCore", "helper_priv", "koszulFaithfulCurvature", "Erlangen20Unification", "instAlgebraClTower"):
                        self.assertIn(tok, errs, msg=errs)

    def test_residual_hardening_planned_strict_multipillar_bool_modules_and_work_id_binding(self) -> None:
        # 1. parse_axiom_index_output rejects bool modules and declarations mismatch
        ok_bool, _, _ = parse_axiom_index_output(
            '  [1/1] InfoGeometry.Foo: ✓ 5 decls, 0✗ 0p 0u\n'
            '{"modules": true, "declarations": 5, "axiom_usage": {}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n',
            ["InfoGeometry.Foo"],
        )
        self.assertFalse(ok_bool)

        ok_decl_mismatch, _, _ = parse_axiom_index_output(
            '  [1/1] InfoGeometry.Foo: ✓ 5 decls, 0✗ 0p 0u\n'
            '{"modules": 1, "declarations": 0, "axiom_usage": {}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n',
            ["InfoGeometry.Foo"],
        )
        self.assertFalse(ok_decl_mismatch)

        # 2. _normalize_traceability_modules rejects double slash
        bad_rows = parse_traceability_matrix(
            "| Work ID | Pillar | Author | Archetype | R3 | Lean Module | Lean Declaration(s) | Status |\n"
            "|---|---|---|---|---|---|---|---|\n"
            "| `S2-01` | pillar_r2_f25 | Grassmann | Meet | `R3.2` | `lean/InfoGeometry//Foo.lean` | `foo` | `IMPLEMENTED` |\n"
        )
        self.assertTrue(bad_rows[0].module_errors)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = _build_synthetic_repo(root, include_lean_files=True, include_m1=True)
            doc_path = root / ARCHETYPES_DOC_REL
            doc_txt = doc_path.read_text(encoding="utf-8")

            # 3. PLANNED row WITH non-empty declarations & missing module MUST fail strict mode even when run_lean_kernel=False
            planned_nonempty = doc_txt.replace(
                "`InfoGeometry.Thermo.OnsagerCasimirKBMPrimary` | `casimirJReciprocity` | `downloaded`",
                "`InfoGeometry.Thermo.NonExistentModule` | `fakeDecl` | `PLANNED`",
                1,
            )
            doc_path.write_text(planned_nonempty, encoding="utf-8")
            strict_rep = run_suite(repo_root=root, tier="3", mode="strict", run_lean_commands=False)
            self.assertEqual(strict_rep["exit_code"], 1)

            # 4. Multi-pillar range row spanning r2_f25 and r3 checked when pillar_filter="r3"
            doc_path.write_text(doc_txt, encoding="utf-8")
            multi_rows = parse_traceability_matrix(
                "| Work ID | Pillar | Author | Archetype | R3 | Lean Module | Lean Declaration(s) | Status |\n"
                "|---|---|---|---|---|---|---|---|\n"
                "| `S2-10..11` | pillar_r2_f25 | Zorn & Clifford | Bridge | `R3.2` | `INVALID_MODULE` | `badDecl` | `IMPLEMENTED` |\n"
                "| `S2-12` | pillar_r3 | Lipschitz | Group | `R3.2` | `InfoGeometry.Clifford.LipschitzWittRieszPrimary` | `lipschitzTwistedIsometry` | `IMPLEMENTED` |\n"
            )
            r3_out = check_traceability_kernel(multi_rows, None, repo_root=root, pillar_filter="r3", run_lean_kernel=False)
            self.assertEqual(r3_out.status, "FAIL")

            # 5. validate_manifest binds work_id (using S2-01..S3-28 IDs) and rejects S2-07 swap into S2-06.notes
            m_path = root / MANIFEST_REL
            m_data = json.loads(m_path.read_text(encoding="utf-8"))
            for idx, spec in enumerate(FOUNDER_YEAR_SPEC):
                m_data["works"][idx]["id"] = spec.work_id
            # Gut S2-07 (index 6) and stuff Klein 1871/1873 into S2-06.notes (index 5)
            m_data["works"][6]["author"] = "Completely Fake Author"
            m_data["works"][6]["year"] = "2099"
            m_data["works"][6]["title"] = "Unrelated Bogus Paper"
            m_data["works"][5]["notes"] = "Successor to Klein 1871 and 1873."
            m_path.write_text(json.dumps(m_data), encoding="utf-8")
            m_out, _ = validate_manifest(root)
            self.assertEqual(m_out.status, "FAIL")
            self.assertIn("S2-07", m_out.summary + "\n".join(m_out.details["errors"]))

            # 6. Negation phrase "not unavailable" must NOT satisfy honest gap parity
            _build_synthetic_repo(root, include_lean_files=False, include_m1=True)
            manifest2 = json.loads(m_path.read_text(encoding="utf-8"))
            neg_doc = (root / ARCHETYPES_DOC_REL).read_text(encoding="utf-8")
            neg_doc = neg_doc.replace("gap_recorded: publisher restricted", "not unavailable").replace("`gap_recorded`", "`archived`")
            (root / ARCHETYPES_DOC_REL).write_text(neg_doc, encoding="utf-8")
            neg_out, _ = validate_archetypes_doc(root, manifest=manifest2)
            self.assertEqual(neg_out.status, "FAIL")
            self.assertIn("Honest gap parity", neg_out.summary)

    # ---- Iteration 4 Regression Tests: Challenger 1 Bypasses + Reviewer 1/2 False-Positive Reconciliation ----

    def test_iter4_multiline_in_unicode_forall_prop_and_substantive_is_predicates(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # 1. Multi-line `... in`, dropped active_opens after `private`, omitted `#print axioms`, Unicode ∀ Is*/class/MultiLineProp
            bad_rel = "lean/InfoGeometry/Iter4Bad.lean"
            (root / bad_rel).parent.mkdir(parents=True, exist_ok=True)
            (root / bad_rel).write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Iter4Bad\n"
                "open Classical (\n  propDecidable) in unsafe def hiddenUnsafe : Nat := 0\n"
                "set_option pp.all\n  true in axiom hiddenAxiom : False\n"
                "open Classical (a)\n  in axiom splitOpenIn : False\n"
                "open Classical (\n  propDecidable) in theorem sneaky_omitted : (1 : Nat) = 2 := rfl\n"
                "open Classical in private\n@[simp]\ntheorem priv_after_open : True := trivial\n"
                "structure MultiLineProp (α : Type*)\n    : Prop where\n  w : ∀ x : α, True\n"
                "structure IsParamTrivial (α : Type*) : Prop where\n  w : ∀ x : α, True\n"
                "theorem is_param_wrap (α : Type*) : IsParamTrivial α := ⟨fun _ => trivial⟩\n"
                "class TrivialClassProp (α : Type*) : Prop where\n  w : ∀ x : α, x = x\n"
                "structure IsValidMulti (x y : Nat) : Prop where\n  pos_x : 0 < x\n  lt_xy : x < y\n"
                "theorem proxy_bundle (h1 : 0 < x) (h2 : x < y) : IsValidMulti x y := ⟨h1, h2⟩\n"
                "end InfoGeometry.Iter4Bad\n",
                encoding="utf-8",
            )
            decls = parse_lean_declarations((root / bad_rel).read_text(encoding="utf-8"))
            by_name = {d.short_name: d for d in decls}
            self.assertIn("sneaky_omitted", by_name)
            self.assertIn("priv_after_open", by_name)
            self.assertTrue(by_name["priv_after_open"].is_private)
            self.assertEqual(by_name["priv_after_open"].active_opens, ("open Classical",))

            fb = check_forbidden_tokens_and_prop_wrappers([bad_rel], root)
            self.assertEqual(fb.status, "FAIL")
            joined = "\n".join(fb.details["failures"])
            for expected_tok in ("unsafe", "axiom", "MultiLineProp", "IsParamTrivial", "TrivialClassProp", "proxy_bundle"):
                self.assertIn(expected_tok, joined, msg=joined)

            emitted: list[str] = []

            def fake_probe(probe_name: str, imports: list[str], body: str, **kwargs: Any) -> tuple[bool, int, str, str, str]:
                emitted.append(body)
                return (
                    True,
                    0,
                    "'InfoGeometry.Iter4Bad.sneaky_omitted' depends on axioms: [propext]\n"
                    "'InfoGeometry.Iter4Bad.is_param_wrap' depends on axioms: [propext]\n"
                    "'InfoGeometry.Iter4Bad.proxy_bundle' depends on axioms: [propext]\n",
                    "",
                    "",
                )

            with patch("tests.primary_sources.lean_audit.run_locked_lean_probe", side_effect=fake_probe):
                pa_out = run_print_axioms_probe([bad_rel], repo_root=root)
            self.assertEqual(pa_out.status, "PASS", msg=pa_out.summary)
            self.assertIn("#print axioms InfoGeometry.Iter4Bad.sneaky_omitted", emitted[0])
            self.assertNotIn("priv_after_open", emitted[0])

            # 2. Substantive parameterized Is* predicates proved with `by constructor` or `by refine { ... }` MUST PASS
            good_rel = "lean/InfoGeometry/Iter4GoodIs.lean"
            (root / good_rel).write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Iter4GoodIs\n"
                "structure IsValidSingle (x : Nat) : Prop where\n  pos : 0 < x\n"
                "theorem one_is_valid_single : IsValidSingle 1 := by\n  constructor\n  exact Nat.zero_lt_one\n"
                "structure IsValidMulti (x y : Nat) : Prop where\n  pos_x : 0 < x\n  lt_xy : x < y\n"
                "theorem valid_multi_refine : IsValidMulti 1 2 := by\n  refine { pos_x := Nat.zero_lt_one, lt_xy := Nat.one_lt_two }\n"
                "theorem valid_multi_ctor : IsValidMulti 1 2 := by\n  constructor\n  exact Nat.zero_lt_one\n  exact Nat.one_lt_two\n"
                "end InfoGeometry.Iter4GoodIs\n",
                encoding="utf-8",
            )
            fb_good = check_forbidden_tokens_and_prop_wrappers([good_rel], root)
            self.assertEqual(fb_good.status, "PASS", msg=fb_good.summary)

    def test_iter4_challenger1_composed_r3_r2_and_m1_bypasses_rejected_strict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=True)

            # Multi-space negated gap parity `"not  unavailable"` MUST FAIL
            doc_path = root / ARCHETYPES_DOC_REL
            doc_txt = doc_path.read_text(encoding="utf-8")
            bad_doc = doc_txt.replace("gap_recorded: publisher restricted", "not  unavailable").replace("`gap_recorded`", "`archived`")
            doc_path.write_text(bad_doc, encoding="utf-8")

            # Missing `"declarations"` key in axiom_index JSON MUST FAIL
            ok_missing_decls, _, _ = parse_axiom_index_output(
                '  [1/1] InfoGeometry.Foo: ✓ 5 decls, 0✗ 0p 0u\n'
                '{"modules": 1, "axiom_usage": {}, "axiomless": ["InfoGeometry.Foo"], "suspicious": {}}\n',
                ["InfoGeometry.Foo"],
            )
            self.assertFalse(ok_missing_decls)

            # R3.1 bypasses: extends Nat (KreinSpace H), (x : Nat) type ascription, eta-expanded & 2-hop aliases
            (root / "lean/InfoGeometry/Krein/PontryaginSpace.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Krein.PontryaginSpace\n"
                "structure PontryaginSpace (H : Type*) extends Nat (KreinSpace H) where\n  kappa : Nat\n"
                "def J : Nat → Nat := fun x => (x : Nat)\n"
                "def jCLM : Nat → Nat := fun x => (x : Nat)\n"
                "def diracPauliKreinInner : Nat := 1\n"
                "theorem kreinIndefiniteContrast : diracPauliKreinInner = 1 := rfl\n"
                "theorem pontryaginInvariantSubspace : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Krein.PontryaginSpace\n",
                encoding="utf-8",
            )
            (root / "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.KK.KreinSpectralTriplePrimary\n"
                "def jCLM : Nat → Nat := fun x => (x : Nat)\n"
                "def gradeCLM : Nat → Nat := fun x => jCLM x\n"
                "def helperAlias := jCLM\n"
                "def J_real := helperAlias\n"
                "def modularDelta : Nat := 1\n"
                "def kasparovEvenOdd : Nat := 1\n"
                "theorem tomitaKasparovCycle : (1 : Nat) = 1 := rfl\n"
                "theorem kreinSpectralTripleSeparated : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.KK.KreinSpectralTriplePrimary\n",
                encoding="utf-8",
            )

            # R3.2 Grassmann bypasses: `{B : Basis ...}`, `abbrev MyBasis := Basis`, dummy `(hodge : V)` + `[MetricSpace V]`
            (root / "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Projective.GrassmannPrimarySources\n"
                "abbrev MyBasis := Basis\n"
                "def grassmannRegressiveSL (V : Type*) {B : Basis Nat ℝ V} (SL : LinearMap.det) : Type* := V\n"
                "def grassmannAlias (V : Type*) [MyBasis Nat ℝ V] : Type* := V\n"
                "def pluckerLineCoord : Nat := 1\n"
                "theorem regressive_hodge_cheat [MetricSpace V] (regressive hodge : V) : regressive = hodge := sorry\n"
                "end InfoGeometry.Projective.GrassmannPrimarySources\n",
                encoding="utf-8",
            )

            # R3.2 Lipschitz/Witt bypasses: `Fin 4→ℝ` (no space), `structure Vec4Struct`, `abbrev MyFin := Fin 4` + `MyFin → ℝ`
            (root / "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.LipschitzWittRieszPrimary\n"
                "abbrev MyFin := Fin 4\n"
                "structure Vec4Struct where\n  v : Fin 4 → ℝ\n"
                "def lipschitzNoSpace (Q : QuadraticForm ℝ (Fin 4→ℝ)) : Nat := 0\n"
                "def wittMyFin (v : MyFin → ℝ) : Nat := 0\n"
                "def rieszStruct (x : Vec4Struct) : Nat := 0\n"
                "theorem lipschitzTwistedIsometry : (1 : Nat) = 1 := rfl\n"
                "theorem wittHyperbolicCancellation : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Clifford.LipschitzWittRieszPrimary\n",
                encoding="utf-8",
            )

            # R3.3 bypasses: unused `(parityString : Nat)` parameter, `abbrev MyAlgHom`, dead `have _dead := GradedTensorProduct.of`
            (root / "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n"
                "def dummy (parityString : Nat) : Nat := 0\n"
                "abbrev MyAlgHom (X Y : Type*) := X →ₐ[ℝ] Y\n"
                "def myCarMap (A B : Type*) : MyAlgHom (A ⊗[ℝ] B) A := by\n"
                "  have _dead := GradedTensorProduct.of\n"
                "  exact sorry\n"
                "def kahlerInnerOuterCodiff : Nat := 1\n"
                "def hestenesMovingFrameRotor : Nat := 2\n"
                "theorem kahlerDiracSquare : kahlerInnerOuterCodiff + 1 = hestenesMovingFrameRotor := rfl\n"
                "theorem absGradedModuleBridge : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n",
                encoding="utf-8",
            )

            # R3.4 bypasses: `commutativ` & `faithfulnessFree` name spoofs, multi-line & `open ... in attribute [instance]`
            (root / "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "open Classical in attribute [instance] Foo.instAlgebraClTower\n"
                "attribute [instance]\n  Bar.instAlgebraClTower\n"
                "namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n"
                "structure PeirceDecomp where\n  peirceIdempotent : Nat\n  nilpotentRadical : Nat\n"
                "def dvNoncommutativityCheat (K : LieActionLane) (D : Derivation ℝ A A) : Nat := 0\n"
                "theorem koszul_faithfulnessFree_cheat (h : DerivationLieLane.faithful) : True := trivial\n"
                "theorem peirceOrthogonalIdempotent (e : Nat) : e = e := rfl\n"
                "theorem koszulConnectionCurvature : (1 : Nat) = 1 := rfl\n"
                "end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n",
                encoding="utf-8",
            )

            report = run_suite(repo_root=root, tier="all", mode="strict", run_lean_commands=False)
            self.assertEqual(report["exit_code"], 1)
            by_id = {o["check_id"]: o for o in report["outcomes"]}
            for cid in (
                "T1-M1-ARCHETYPES-DOC",
                "T2-FORBIDDEN-SCAN",
                "T2-R3.1-KREIN-SEPARATION",
                "T2-R3.2-METRIC-BASIS-FREE",
                "T2-R3.3-KOSZUL-Z2-GRADING",
                "T2-R3.4-LIE-PEIRCE-DIAMONDS",
            ):
                self.assertEqual(by_id[cid]["status"], "FAIL", msg=f"{cid} unexpectedly passed: {by_id[cid]}")

            r31_errs = "\n".join(by_id["T2-R3.1-KREIN-SEPARATION"]["details"]["errors"])
            for tok in ("PontryaginSpace", "J", "jCLM", "gradeCLM", "J_real"):
                self.assertIn(tok, r31_errs, msg=r31_errs)
            r32_errs = "\n".join(by_id["T2-R3.2-METRIC-BASIS-FREE"]["details"]["errors"])
            for tok in ("grassmannRegressiveSL", "grassmannAlias", "regressive_hodge_cheat", "lipschitzNoSpace", "wittMyFin", "rieszStruct"):
                self.assertIn(tok, r32_errs, msg=r32_errs)
            r33_errs = "\n".join(by_id["T2-R3.3-KOSZUL-Z2-GRADING"]["details"]["errors"])
            self.assertIn("missing Koszul", r33_errs, msg=r33_errs)
            self.assertIn("myCarMap", r33_errs, msg=r33_errs)
            r34_errs = "\n".join(by_id["T2-R3.4-LIE-PEIRCE-DIAMONDS"]["details"]["errors"])
            for tok in ("dvNoncommutativityCheat", "koszul_faithfulnessFree_cheat", "instAlgebraClTower"):
                self.assertIn(tok, r34_errs, msg=r34_errs)

    def test_iter4_valid_mathlib_idioms_no_false_positives_and_kernel_template(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _build_synthetic_repo(root, include_lean_files=True, include_m1=False)

            # Grassmann: basis-free signature using `Module.finBasis` only inside `by` proof body MUST PASS
            (root / "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Projective.GrassmannPrimarySources\n"
                "def grassmannRegressiveSL (V : Type*) (SL : LinearMap.det) : Type* := V\n"
                "theorem map_top_exteriorPower_eq_det_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]\n"
                "    (g : V →ₗ[K] V) : True := by\n"
                "  let b := Module.finBasis K V\n"
                "  trivial\n"
                "end InfoGeometry.Projective.GrassmannPrimarySources\n",
                encoding="utf-8",
            )

            # Lipschitz/Witt: abstract `Fin k → V` tuple AND `hyperbolicSumQuad : QuadraticForm K (Fin m → K × K)` MUST PASS
            (root / "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.LipschitzWittRieszPrimary\n"
                "def hyperbolicSumQuad (K : Type*) [CommRing K] (m : ℕ) : QuadraticForm K (Fin m → K × K) := sorry\n"
                "theorem cartan_dieudonne_basis_free {K V : Type*} [Field K] [AddCommGroup V] [Module K V]\n"
                "    (Q : QuadraticForm K V) (v : Fin k → V) : Q = Q := rfl\n"
                "theorem witt_cancellation {K V M₁ M₂ : Type*} [Field K] [AddCommGroup V] [Module K V]\n"
                "    (Q : QuadraticForm K V) : Q = Q := rfl\n"
                "end InfoGeometry.Clifford.LipschitzWittRieszPrimary\n",
                encoding="utf-8",
            )

            # Kahler/ABS: explicit scalar base-change `ℂ ⊗[ℝ] CliffordAlgebra Q` MUST PASS
            (root / "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n"
                "def koszulCliffordProdEquiv {R M₁ M₂ : Type*} (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :\n"
                "    CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (CliffordAlgebra.evenOdd Q₁ ᵍ⊗[R] CliffordAlgebra.evenOdd Q₂) := sorry\n"
                "def baseChangeComplex (Q : QuadraticForm ℝ V) :\n"
                "    CliffordAlgebra Q →ₐ[ℝ] (ℂ ⊗[ℝ] CliffordAlgebra Q) := sorry\n"
                "end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n",
                encoding="utf-8",
            )

            # Peirce/Koszul: `[Field K] [CommRing S]` on Kähler 1953 + declaration-local `open scoped Erlangen20Unification in` MUST PASS
            (root / "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n"
                "def peirceCore (K : LieActionLane) (e : Nat) (he : e * e = e) : Nat := e\n"
                "theorem kaehler1953_field_compat (K S : Type*) [Field K] [CommRing S] (D : Derivation K S S) : True := trivial\n"
                "open scoped Erlangen20Unification in\n"
                "theorem local_scoped_in_ok : True := trivial\n"
                "theorem nonFaithful_not_inj (K : LieActionLane) : ¬ Function.Injective K.act := by\n  sorry\n"
                "end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary\n",
                encoding="utf-8",
            )

            outs = check_r3_compliance(
                [
                    "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean",
                    "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean",
                    "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean",
                    "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
                ],
                root,
            )
            for out in outs:
                self.assertEqual(out.status, "PASS", msg=f"{out.check_id} false positive: {out.summary}")

            # Also verify `CliffordAlgebra Q₁ ⊗[ℝ] CliffordAlgebra Q₂` still FAILS R3.3
            (root / "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean").write_text(
                f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
                "namespace InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n"
                "def koszulCliffordProdEquiv {R M₁ M₂ : Type*} (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :\n"
                "    CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (CliffordAlgebra.evenOdd Q₁ ᵍ⊗[R] CliffordAlgebra.evenOdd Q₂) := sorry\n"
                "def badTower (Q₁ : QuadraticForm ℝ V) (Q₂ : QuadraticForm ℝ W) :\n"
                "    (CliffordAlgebra Q₁ ⊗[ℝ] CliffordAlgebra Q₂) →ₐ[ℝ] CliffordAlgebra Q₁ := sorry\n"
                "end InfoGeometry.Clifford.KahlerHestenesJWABSPrimary\n",
                encoding="utf-8",
            )
            r33_fail = check_r3_compliance(["lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean"], root)
            self.assertEqual(r33_fail[0].status, "FAIL")
            self.assertIn("badTower", r33_fail[0].summary)

            # Verify kernel probe template includes Iteration 4 hardening checks
            captured: list[str] = []

            def fake_kernel_probe(probe_name: str, imports: list[str], body: str, **kwargs: Any) -> tuple[bool, int, str, str, str]:
                captured.append(body)
                return True, 0, "", "", ""

            with patch("tests.primary_sources.lean_audit.run_locked_lean_probe", side_effect=fake_kernel_probe):
                k_out = run_r3_kernel_probe(
                    [
                        "InfoGeometry.Krein.PontryaginSpace",
                        "InfoGeometry.KK.KreinSpectralTriplePrimary",
                        "InfoGeometry.Projective.GrassmannPrimarySources",
                        "InfoGeometry.Clifford.LipschitzWittRieszPrimary",
                        "InfoGeometry.Clifford.KahlerHestenesJWABSPrimary",
                        "InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary",
                    ]
                )
            self.assertEqual(k_out.status, "PASS")
            kbody = captured[0]
            for expected_k in ("_private.", ".match_", "hasCoordFinExpr", "hasFaithfulHypothesis", "non_faithful", "no_faithful", "isScalarBaseChangeExpr"):
                self.assertIn(expected_k, kbody)
            self.assertNotIn("faithfulnessFree", kbody)
            self.assertNotIn('s.contains "parity"', kbody)


if __name__ == "__main__":
    unittest.main()
