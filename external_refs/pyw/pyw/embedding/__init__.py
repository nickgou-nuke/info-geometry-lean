"""
Embedding module - Lie algebra embeddings, sl2-triples, and Levi subalgebras.
"""

from .sl2_triple import (
    SL2Triple,
    RootSpaceGrading,
    weighted_dynkin_diagram,
    root_space_grading,
    compute_sl2_triple,
)

__all__ = [
    "SL2Triple",
    "RootSpaceGrading",
    "weighted_dynkin_diagram",
    "root_space_grading",
    "compute_sl2_triple",
]
