#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal


BRIDGE_METHOD_CHOICES = (
    "getGoalTargets",
    "getProofState",
    "checkSnippet",
    "getDeclValue",
    "validateDecl",
    "getEnvFingerprint",
)

SESSION_METHOD_CHOICES = BRIDGE_METHOD_CHOICES + (
    "didChange",
    "reloadFromDisk",
)

PROOF_PRINT_MODE_CHOICES = (
    "goal-target",
    "proof-state",
    "decl-value",
)

ProofPrintMode = Literal["goal-target", "proof-state", "decl-value"]


@dataclass(frozen=True)
class BridgeCallSpec:
    method: str
    decl_name: str | None = None
    pretty_print_type: bool = False
    pretty_print_value: bool = False


def call_spec_for_print_mode(mode: ProofPrintMode, decl_name: str | None) -> BridgeCallSpec:
    if mode == "decl-value":
        if not decl_name:
            raise ValueError("--decl-name is required for --mode decl-value")
        return BridgeCallSpec(
            method="getDeclValue",
            decl_name=decl_name,
        )
    if mode == "proof-state":
        return BridgeCallSpec(method="getProofState")
    return BridgeCallSpec(method="getGoalTargets")


def extract_print_text(result: dict[str, Any], mode: ProofPrintMode) -> str:
    if mode == "decl-value":
        text = result.get("declarationValue", "")
    else:
        goals = result.get("goals", [])
        if mode == "proof-state":
            text = goals[0]["pretty"] if goals else ""
        else:
            text = goals[0]["target"] if goals else ""
    return text if isinstance(text, str) else ""


def build_prewarm_request(
    *,
    method: str | None,
    decl_name: str | None,
    line: int | None,
    character: int,
    pretty_print_type: bool,
    pretty_print_value: bool,
) -> dict[str, Any] | None:
    if method is None and decl_name is None and line is None:
        return None
    resolved_method = method
    if resolved_method is None:
        if decl_name and pretty_print_value and not pretty_print_type:
            resolved_method = "getDeclValue"
        else:
            resolved_method = "validateDecl" if decl_name else "getProofState"
    return {
        "id": "prewarm",
        "method": resolved_method,
        "declName": decl_name,
        "line": line,
        "character": character,
        "prettyPrintType": pretty_print_type,
        "prettyPrintValue": pretty_print_value,
    }


def summarize_bridge_response(response: dict[str, Any]) -> dict[str, Any]:
    summary = {
        "id": response.get("id"),
        "ok": response.get("ok"),
        "method": response.get("method"),
        "line": response.get("line"),
        "character": response.get("character"),
        "version": response.get("version"),
        "timingsMs": response.get("timingsMs"),
    }
    if response.get("ok") is False:
        summary["error"] = response.get("error")
        return summary
    result = response.get("result")
    if not isinstance(result, dict):
        return summary
    if "declFound" in result:
        summary["declFound"] = result.get("declFound")
    if "hasSorry" in result:
        summary["hasSorry"] = result.get("hasSorry")
    declaration_value = result.get("declarationValue")
    if isinstance(declaration_value, str):
        summary["declarationValueLength"] = len(declaration_value)
    goals = result.get("goals")
    if isinstance(goals, list):
        summary["goalCount"] = len(goals)
        if goals and isinstance(goals[0], dict):
            first_target = goals[0].get("target")
            if isinstance(first_target, str):
                summary["firstGoalTarget"] = first_target
    return summary
