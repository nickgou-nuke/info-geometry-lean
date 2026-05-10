from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
OWNER = REPO / "lean" / "InfoGeometry" / "ExponentialFamily" / "Analytic" / "LogSumExp.lean"
CONSUMER = REPO / "lean" / "InfoGeometry" / "ExponentialFamily" / "Analytic" / "Softmax.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    starts = list(re.finditer(rf"(?m)^\s*{kind}\s+{re.escape(name)}(?:\s|:|\().*$", text))
    assert starts, f"missing {kind} {name}"
    start = starts[0].start()
    line_end = text.find("\n", starts[0].end())
    search_from = line_end + 1 if line_end != -1 else starts[0].end()
    nxt = re.search(
        r"(?m)^\s*(?:lemma|theorem|def|noncomputable def|abbrev|noncomputable abbrev)\s+",
        text[search_from:],
    )
    end = search_from + nxt.start() if nxt else len(text)
    return text[start:end]


def test_logsumexp_derivative_root_is_hasderivat_chain():
    text = OWNER.read_text()
    root = decl_block(text, "lemma", "hasDerivAt_logSumExp")
    assert "hasDerivAt_logSumExpPartition" in root
    assert "Real.hasDerivAt_log" in root
    assert ".comp" in root
    assert "logSumExp_sum_pos" in root
    exported = decl_block(text, "lemma", "logSumExp_deriv_eq_ratio")
    assert "hasDerivAt_logSumExp" in exported
    assert ".deriv" in exported
    assert "deriv.log" not in exported
    assert "DifferentiableAt" not in exported


def test_softmax_consumes_logsumexp_derivative_export_not_chain_root():
    text = CONSUMER.read_text()
    block = decl_block(text, "lemma", "deriv_logSumExp_eq_firstMoment_div_partition")
    assert "logSumExp_deriv_eq_ratio" in block
    assert "hasDerivAt_logSumExp" not in block
