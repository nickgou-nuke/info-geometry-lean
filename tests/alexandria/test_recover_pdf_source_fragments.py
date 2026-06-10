from pathlib import Path

from tools.alexandria.recover_pdf_source_fragments import (
    load_xml,
    recover_code_blocks,
    recover_lines,
)


def test_recover_pdf_source_fragments_splits_columns_and_classifies_code(tmp_path: Path) -> None:
    xml = tmp_path / "paper.xml"
    xml.write_text(
        """<?xml version="1.0" encoding="UTF-8"?>
<pdf2xml>
  <page number="1" width="900" height="1100">
    <fontspec id="1" size="10" family="WDMFDK+JuliaMono" color="#000000"/>
    <fontspec id="2" size="12" family="NimbusRoman" color="#000000"/>
    <text top="100" left="50" width="18" height="10" font="1"><b>def</b></text>
    <text top="100" left="74" width="30" height="10" font="1">left</text>
    <text top="100" left="104" width="30" height="10" font="1">(x):</text>
    <text top="115" left="74" width="36" height="10" font="1"><b>return</b></text>
    <text top="115" left="116" width="30" height="10" font="1">x + 1</text>
    <text top="100" left="430" width="18" height="10" font="1"><b>def</b></text>
    <text top="100" left="454" width="36" height="10" font="1">right</text>
    <text top="100" left="490" width="30" height="10" font="1">(y):</text>
    <text top="115" left="454" width="36" height="10" font="1"><b>return</b></text>
    <text top="115" left="496" width="30" height="10" font="1">y + 2</text>
    <text top="180" left="50" width="42" height="10" font="1">theorem</text>
    <text top="180" left="98" width="120" height="10" font="1">candidate_truth</text>
    <text top="180" left="224" width="72" height="10" font="1">: True :=</text>
    <text top="195" left="74" width="12" height="10" font="1">by</text>
    <text top="210" left="98" width="42" height="10" font="1">trivial</text>
    <text top="260" left="50" width="120" height="12" font="2">ordinary prose</text>
  </page>
</pdf2xml>
""",
        encoding="utf-8",
    )

    _, spans = load_xml(xml)
    lines, code_lines = recover_lines(
        spans,
        code_font_substrings=("JuliaMono",),
        y_tolerance=2.0,
        column_gap=80.0,
    )
    blocks = recover_code_blocks(
        code_lines,
        column_tolerance=120.0,
        vertical_gap=28.0,
        drop_line_numbers=True,
        check_lean=False,
        lean_preamble="",
        lean_timeout=5,
        check_python=True,
    )

    texts = [block.text for block in blocks]
    languages = [block.language for block in blocks]
    statuses = {(block.language, block.validationStatus) for block in blocks}

    assert len(lines) >= 5
    assert any("def left" in text for text in texts)
    assert any("def right" in text for text in texts)
    assert not any("def left" in text and "def right" in text for text in texts)
    assert "lean4" in languages
    assert ("python", "passed") in statuses
    assert ("lean4", "not_checked") in statuses
