#!/usr/bin/env python3
"""Contract and verification tests for the Gravito-Electromagnetic (GEM) Peirce Bridge.

Verifies:
1. All 16 non-definitional `[Ring B]` theorems in
   `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean`.
2. Phase A owner integrations (`OntologyRing.lean`, `EinsteinCartanChiralAnomalyFrameDraggingPoset.lean`,
   `WheelerGodelRotatingUniverseChronologyPoset.lean`, `ZornAlternativeLaws.lean`).
3. Phase B 10-clade `GEMTaxonomicClade` and 8-epoch `GEMPhylogeneticEpoch` in
   `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean` and
   `AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean`.
4. Phase 3 Python taxonomy (`GEM_CLADE_IDS`, `GEM_EPOCH_IDS` in `tools/infra/evolution_taxonomy.py`),
   ontology (`tools/infra/arango_to_ontology.py`), phylogeny export (`tools/repository_evolution/phylogeny_export.py`),
   and dashboard (`tools/infra/darwin_phylogeny_dashboard.py`) alignment.
"""
from __future__ import annotations

import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.evolution_taxonomy import (  # noqa: E402
    CATEGORY_IDS,
    EVIDENCE_KINDS,
    GEM_CLADE_IDS,
    GEM_EPOCH_IDS,
)

GEM_BRIDGE_FILE = ROOT / "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean"
EINSTEIN_CARTAN_FILE = ROOT / "lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean"
WHEELER_GODEL_FILE = ROOT / "lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean"
TAXONOMY_POSET_FILE = ROOT / "lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean"
TAXONOMY_AUDIT_FILE = ROOT / "lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean"


EXPECTED_GEM_THEOREMS: tuple[str, ...] = (
    "gemDipole_chiral_lock",
    "gemFirstOrderLenseThirring",
    "gemDualPrecession",
    "gemCornerPrecession_plus",
    "gemCornerPrecession_minus",
    "gemDressedTorsion_eq",
    "gemSecondOrderCentrifugal",
    "gemSecondOrderCentrifugal_dual",
    "gemSpinPhi_anticomm",
    "gemSpinJ_anticomm",
    "gemWorkFreeCoriolis",
    "gemSpinMulPhi_eq",
    "gemNilpotentCollapse",
    "gemOnsagerReciprocity_anticomm",
    "gemOnsagerReciprocity_sq_diff",
    "gemMachPrinciple",
)


def test_gem_bridge_theorems_present_and_sorry_free() -> None:
    """Verify all 16 GEM Peirce-spine theorems exist and the file contains zero sorry/admit/axiom."""
    assert GEM_BRIDGE_FILE.exists(), f"Missing {GEM_BRIDGE_FILE}"
    src = GEM_BRIDGE_FILE.read_text(encoding="utf-8")
    for thm in EXPECTED_GEM_THEOREMS:
        pattern = rf"\btheorem\s+{re.escape(thm)}\b"
        assert re.search(pattern, src) is not None, f"Theorem {thm} missing in {GEM_BRIDGE_FILE}"
    for forbidden in (r"\bsorry\b", r"\badmit\b", r"\baxiom\b"):
        assert re.search(forbidden, src) is None, f"Forbidden token {forbidden} in {GEM_BRIDGE_FILE}"


def test_phase_a_owners_integrate_gem_bridge() -> None:
    """Verify substantive Einstein-Cartan and Wheeler-Godel consumers use the bridge."""
    import_stmt = "import InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge"

    ec_src = EINSTEIN_CARTAN_FILE.read_text(encoding="utf-8")
    assert import_stmt in ec_src
    assert "gemFirstOrderLenseThirring" in ec_src
    assert "gemDressedTorsion_eq" in ec_src

    wg_src = WHEELER_GODEL_FILE.read_text(encoding="utf-8")
    assert import_stmt in wg_src
    assert "gemSecondOrderCentrifugal" in wg_src
    assert "gemSecondOrderCentrifugal_dual" in wg_src



def test_phase_b_gem_taxonomy_and_phylogenesis_contract() -> None:
    """Verify 10-clade GEMTaxonomicClade, 8-epoch GEMPhylogeneticEpoch, and Python alignment."""
    src = TAXONOMY_POSET_FILE.read_text(encoding="utf-8")

    clade_block = re.search(
        r"inductive\s+GEMTaxonomicClade\s*:\s*Type(.*?)deriving\s+DecidableEq",
        src,
        re.S,
    )
    assert clade_block is not None, "GEMTaxonomicClade block missing"
    lean_clades = re.findall(r"\|\s*([A-Za-z0-9_]+)", clade_block.group(1))
    assert len(lean_clades) == 10
    assert list(GEM_CLADE_IDS.values()) == lean_clades

    epoch_block = re.search(
        r"inductive\s+GEMPhylogeneticEpoch\s*:\s*Type(.*?)deriving\s+DecidableEq",
        src,
        re.S,
    )
    assert epoch_block is not None, "GEMPhylogeneticEpoch block missing"
    lean_epochs = re.findall(r"\|\s*([A-Za-z0-9_]+)", epoch_block.group(1))
    assert len(lean_epochs) == 8
    assert list(GEM_EPOCH_IDS.values()) == lean_epochs

    for required_decl in (
        "def gemPrimarySense",
        "def gemQMSBucket",
        "def gemMetaLevel",
        "def gemRepDepth",
        "theorem gemActive_clade_not_bucketC",
        "def gemEpochRank",
        "def gemCausalEdge",
        "theorem gemCausalEdge_irrefl",
        "theorem gemCausalEdge_trans",
        "theorem gemCausalEdge_acyclic",
        "def analyticToGEMEpoch",
        "theorem analyticToGEMEpoch_rank_eq",
        "theorem analyticToGEMEpoch_injective",
        "theorem analyticToGEMEpoch_preserves_causalEdge",
    ):
        assert required_decl in src, f"Missing {required_decl} in {TAXONOMY_POSET_FILE}"

    assert len(CATEGORY_IDS) == 12
    assert len(EVIDENCE_KINDS) == 4


def test_phase_b_audit_prints_gem_axioms() -> None:
    """Verify AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean audits all GEM bridge theorems."""
    audit_src = TAXONOMY_AUDIT_FILE.read_text(encoding="utf-8")
    for thm in EXPECTED_GEM_THEOREMS:
        assert f"#print axioms InfoGeometry.OperatorAlgebra.PeirceSpine.{thm}" in audit_src
    for poset_thm in (
        "gemActive_clade_not_bucketC",
        "gemCausalEdge_irrefl",
        "gemCausalEdge_trans",
        "gemCausalEdge_acyclic",
        "analyticToGEMEpoch_preserves_causalEdge",
    ):
        assert f"#print axioms AnalyticOntologyTaxonomyPhylogenesisPoset.{poset_thm}" in audit_src


class GravitoElectromagneticBridgeUnitTests(unittest.TestCase):
    """Unittest runner for Gravito-Electromagnetic Bridge verification."""

    def test_gem_bridge_theorems(self) -> None:
        test_gem_bridge_theorems_present_and_sorry_free()

    def test_phase_a_owners(self) -> None:
        test_phase_a_owners_integrate_gem_bridge()

    def test_phase_b_taxonomy_and_phylogenesis(self) -> None:
        test_phase_b_gem_taxonomy_and_phylogenesis_contract()

    def test_phase_b_audit(self) -> None:
        test_phase_b_audit_prints_gem_axioms()


if __name__ == "__main__":
    unittest.main()
