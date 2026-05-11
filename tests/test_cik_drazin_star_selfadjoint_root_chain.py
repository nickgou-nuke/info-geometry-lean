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


def test_drazin_star_transport_root_uses_star_equations_and_owner_adapter() -> None:
    text = DRAZIN.read_text()
    transport = decl_block(text, "theorem", "star_isDrazinInverse_of_selfAdjoint")
    assert "congrArg star h.comm" in transport
    assert "congrArg star h.idempotent" in transport
    assert "congrArg star h.power" in transport
    assert "Commute a (star b)" in transport

    derived = decl_block(text, "theorem", "star_eq_self_of_selfAdjoint")
    assert "InfoGeometry.Singular.Drazin.Drazin_star_eq_self_of_selfAdjoint" in derived


def test_certified_inverse_kernel_spectral_star_tracks_both_selfadjoint_inputs() -> None:
    text = CIK.read_text()
    spectral = decl_block(text, "theorem", "spectralProjector_star_of_selfAdjoint")
    header = spectral.split(":=", 1)[0]
    assert "hA" in header
    assert "hAD" in header
    assert "unfold IsDrazinInverse.projection" in spectral
    assert "CIK.hDrazin.comm.symm" in spectral


def test_inverse_kernel_algebra_complements_inherit_mp_stars() -> None:
    text = INVERSE_ALG.read_text()
    mp_block = decl_block(text, "theorem", "mpRangeComplementaryProjector_star")
    assert "CIK.mpRangeProjector_star" in mp_block

    metric_block = decl_block(text, "theorem", "metricComplementaryProjector_star")
    assert "CIK.metricProjector_star" in metric_block


def test_cik_projector_star_lemmas_are_rooted_in_mp_and_drazin_theorems() -> None:
    text = CIK.read_text()

    mp_range = decl_block(text, "theorem", "mpRangeProjector_star")
    assert "IsMoorePenroseInverse.rightProjector_star CIK.hMoorePenrose" in mp_range

    metric = decl_block(text, "theorem", "metricProjector_star")
    assert "IsMoorePenroseInverse.leftProjector_star CIK.hMoorePenrose" in metric

    spectral_selfadj = decl_block(text, "theorem", "spectralProjector_isSelfAdjoint_of_selfAdjoint")
    assert "CIK.spectralProjector_star_of_selfAdjoint hA hAD" in spectral_selfadj

    spectral_from_is = decl_block(text, "theorem", "spectralProjector_star_of_isSelfAdjoint")
    assert "hA.star_eq" in spectral_from_is
    assert "hAD.star_eq" in spectral_from_is
