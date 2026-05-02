from __future__ import annotations

DEFAULT_AUTHORITY_LEVEL = "derived"
DEFAULT_CLAIM_SCOPE = "derived_spectral_neighborhood_sidecar"
DEFAULT_NON_OVERCLAIM = True

ALLOWED_AUTHORITY_LEVELS = {
    "heuristic",
    "derived",
    "formal-adjacent",
    "formal",
}


def apply_default_claim_policy(doc: dict) -> dict:
    doc.setdefault("authority_level", DEFAULT_AUTHORITY_LEVEL)
    doc.setdefault("claim_scope", DEFAULT_CLAIM_SCOPE)
    doc.setdefault("non_overclaim", DEFAULT_NON_OVERCLAIM)
    return doc


def validate_claim_policy(doc: dict) -> list[str]:
    errors: list[str] = []

    if doc.get("non_overclaim") is not True:
        errors.append("non_overclaim must be true")

    if not doc.get("claim_scope"):
        errors.append("claim_scope is required")

    level = doc.get("authority_level")
    if level not in ALLOWED_AUTHORITY_LEVELS:
        errors.append(f"invalid authority_level: {level}")

    if level == "formal" and not doc.get("proof_link"):
        errors.append("formal authority requires proof_link")

    return errors
