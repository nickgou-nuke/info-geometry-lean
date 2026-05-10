from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
DRAZIN = REPO / "lean" / "InfoGeometry" / "Canonical" / "Drazin.lean"
CIK = REPO / "lean" / "InfoGeometry" / "Canonical" / "CertifiedInverseKernel.lean"
INVERSE_ALG = REPO / "lean" / "InfoGeometry" / "Canonical" / "InverseKernelAlgebra.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    starts = list(re.finditer(rf"(?m)^\s*(?:@[^[\n]+\]\s*)*{kind}\s+{re.escape(name)}(?:\s|:|\().*$", text))
    assert starts, f"missing {kind} {name}"
    start = starts[0].start()
    line_end = text.find("\n", starts[0].end())
    search_from = line_end + 1 if line_end != -1 else starts[0].end()
    nxt = re.search(
        r"(?m)^\s*(?:/-!|section|end|namespace|@[^[\n]+\]\s*)*(?:lemma|theorem|def|noncomputable def|abbrev|noncomputable abbrev)\s+",
        text[search_from:],
    )
    end = search_from + nxt.start() if nxt else len(text)
    return text[start:end]


def test_drazin_star_transport_root_uses_star_equations_and_uniqueness():
    text = DRAZIN.read_text()
    transport = decl_block(text, "theorem", "star_isDrazinInverse_of_selfAdjoint")
    assert "congrArg star h.comm" in transport
    assert "congrArg star h.idempotent" in transport
    assert "congrArg star h.power" in transport
    assert "Commute a (star b)" in transport
    derived = decl_block(text, "theorem", "star_eq_self_of_selfAdjoint")
    assert "star_isDrazinInverse_of_selfAdjoint h ha" in derived
    assert "unique h hstar" in derived


def test_certified_inverse_kernel_derives_had_from_ha_not_as_hypothesis():
    text = CIK.read_text()
    a_d = decl_block(text, "theorem", "A_D_star_of_selfAdjoint")
    assert "IsDrazinInverse.star_eq_self_of_selfAdjoint" in a_d
    assert "CIK.hDrazin" in a_d
    spectral = decl_block(text, "theorem", "spectralProjector_star_of_A_selfAdjoint")
    assert "CIK.A_D_star_of_selfAdjoint hA" in spectral
    header = spectral.split(":=", 1)[0]
    assert "hAD" not in header


def test_inverse_kernel_algebra_complement_uses_base_selfadjoint_only():
    text = INVERSE_ALG.read_text()
    block = decl_block(text, "theorem", "spectralComplementaryProjector_star_of_selfAdjoint")
    header = block.split(":=", 1)[0]
    assert "hAD" not in header
    assert "drazinInverse_star_of_selfAdjoint" in block or "spectralProjector_star_of_A_selfAdjoint" in block


def test_cik_projector_star_projection_adapters_are_lean_rooted():
    text = CIK.read_text()
    mp_range = decl_block(text, "theorem", "mpRangeProjector_isStarProjection")
    assert "mpRangeProjector_idempotent" in mp_range
    assert "mpRangeProjector_star" in mp_range
    metric = decl_block(text, "theorem", "metricProjector_isStarProjection")
    assert "metricProjector_idempotent" in metric
    assert "metricProjector_star" in metric
    mp_range_readback = decl_block(text, "theorem", "mpRangeProjector_eq_ownRange_starProjection")
    assert "isStarProjection_iff_eq_starProjection_range.mp" in mp_range_readback
    assert "mpRangeProjector_isStarProjection" in mp_range_readback
    spectral = decl_block(text, "theorem", "spectralProjector_isStarProjection_of_A_selfAdjoint")
    header = spectral.split(":=", 1)[0]
    assert "hAD" not in header
    assert "spectralProjector_idempotent" in spectral
    assert "spectralProjector_star_of_A_selfAdjoint hA" in spectral
    spectral_readback = decl_block(
        text, "theorem", "spectralProjector_eq_ownRange_starProjection_of_A_selfAdjoint"
    )
    assert "isStarProjection_iff_eq_starProjection_range.mp" in spectral_readback
    assert "spectralProjector_isStarProjection_of_A_selfAdjoint hA" in spectral_readback
