"""Known-answer tests for igf.graph.decl_schema (mirrors tests/TermDigestTests.lean)."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from igf.graph.decl_schema import decl_key, edge_key, term_digest  # noqa: E402

PROP = ("sort", ("zero",))


def test_keys_match_lean_and_live_rows() -> None:
    assert decl_key("InfoGeometry.AQFT.Pin55Pullback.bladeMatrixEquiv") == "d_f7bec2f5913b1e7a496a4a2aced3f82318f04198"
    assert edge_key("A.b", "type", "C.d") == "e_09abd75daf5e87ea802f2fe7bec241b73bc56c5a"


def test_alpha_and_mdata_invariance() -> None:
    ident = ("lam", PROP, ("bvar", 0))
    assert term_digest(ident) == term_digest(("mdata", ("lam", PROP, ("mdata", ("bvar", 0)))))
    assert term_digest(ident).digest != term_digest(("lam", PROP, ("bvar", 1))).digest


def test_cross_implementation_vectors() -> None:
    vectors = {
        ("lam", PROP, ("bvar", 0)): "51b33626ac2f34eee2d5780e6bda57c03a3dcb09881c177df6b0f8dfde28907f",
        ("const", "Nat", ()): "b9bd90cef763e5b28ff9b3fd950f99027a88b3fbf56353c85f33620c88fb7605",
        ("app", ("const", "Nat.succ", ()), ("litnat", 42)): "f64a8926c3126d626032db8569d478625d5e281c9db6bf5d3373cf102e60eaec",
        ("forall", ("sort", ("succ", ("param", "u"))), ("bvar", 0)): "2e345e048fb3480fe8e6a9e18235a8091b1088266bb559901607bc924a23e893",
        ("proj", "Prod", 0, ("bvar", 0)): "1ec33bbcf0f94981c2781059587ea018e38cfc00ae42f2515120365ff2d32bcd",
    }
    for term, expected in vectors.items():
        assert term_digest(term).digest == expected


def test_open_terms_flagged_and_ids_erased() -> None:
    a = term_digest(("app", ("fvar",), ("bvar", 0)))
    assert a.open_term
    assert a.digest == "d25df22c974adbeab5281386b58b18b8a921b5afab7fbb020ea9692d81204eee"
