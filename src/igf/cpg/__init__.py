"""Code Property Graph (CPG) and AST AQL Analysis utilities for IGF."""

from igf.cpg.dedup import ArangoCPGDeduplicator, EquivalenceCluster
from igf.cpg.self_compact import LosslessSelfCompactor, CompactStepResult

__all__ = [
    "ArangoCPGDeduplicator",
    "EquivalenceCluster",
    "LosslessSelfCompactor",
    "CompactStepResult",
]
