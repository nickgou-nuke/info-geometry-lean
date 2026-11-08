# QMS package — Quality Management System per docs/ALCHEMICAL_QMS_SOP.md
#
# Implements the controlled confabulation-to-Lean transmutation procedure:
# Stage 0-7 process map with role separation (G-A, A-A, QA-A, Orchestrator),
# Gate 0-5 (intake, owner search, generation controls, semantic audit, CAPA,
# acceptance), formal intent envelopes, audit telemetry, QA acceptance records,
# and CAPA tracking.
#
# Central control principle: generation is not audit; audit is not acceptance;
# acceptance is not promotion authority unless backed by kernel/build/audit output.

from __future__ import annotations

__all__ = [
    "intent_envelope",
    "roles",
    "gates",
    "audit_report",
    "qa_record",
    "capa",
    "qms_runner",
]

__version__ = "4.1"
__sop_id__ = "QMS-SOP-ALC-001"
