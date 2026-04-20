from pathlib import Path

from tools.alexandria.semantic_ingest import digest_document


def test_digest_document_extracts_sections_chunks_and_entities(tmp_path: Path) -> None:
    source = tmp_path / "blackbook.md"
    source.write_text(
        "# Constructive Drazin\n\nTheorem. A local Weyl symmetry statement.\n\nProof. Assume the candidate commutes.\n",
        encoding="utf-8",
    )

    document, sections, chunks, entities, adjacent = digest_document(source)

    assert document["title"] == "blackbook"
    assert sections
    assert len(chunks) == 2
    assert chunks[0].chunkKind == "theorem"
    assert chunks[1].chunkKind == "proof"
    assert any(entity.entityType == "theorem" for entity in entities)
    assert any(entity.entityType == "proof" for entity in entities)
    assert len(adjacent) == 1
