#!/usr/bin/env python3
"""Apply a provenance-aware latent projector and mixture-of-experts taxonomy.

This is inference only. It consumes an explicitly versioned parameter packet;
it does not train on weak labels or promote predictions to reviewed taxonomy.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
from collections import Counter
from pathlib import Path
import sys
from typing import Any

# Keep the documented ``python tools/repository_evolution/latent_taxonomy.py``
# entry point usable as well as ``python -m``. When a file is executed by path,
# Python places this module's directory, rather than the repository root, on
# ``sys.path``.
_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.repository_evolution.git_fossil_overlay import _generation_id


FEATURE_VERSION = "repository_taxonomy_features.v4"
MODEL_SCHEMA = "info_geometry.latent_expert_model.v3"
MAP_SCHEMA = "info_geometry.refactoring_map.v1"
ENCODER_PACKET_SCHEMA = "info_geometry.repository_encoder_embeddings.v2"


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _softmax(logits: dict[str, float]) -> dict[str, float]:
    if not logits:
        return {}
    if any(not math.isfinite(value) for value in logits.values()):
        raise ValueError("model produced a non-finite logit")
    maximum = max(logits.values())
    exps = {key: math.exp(value - maximum) for key, value in logits.items()}
    total = sum(exps.values())
    return {key: value / total for key, value in exps.items()}


def _sigmoid_score(logit: float) -> float:
    """Map one multi-label logit to an independent, uncalibrated score."""
    if not math.isfinite(logit):
        raise ValueError("model produced a non-finite label logit")
    if logit >= 0:
        return 1.0 / (1.0 + math.exp(-logit))
    exp_logit = math.exp(logit)
    return exp_logit / (1.0 + exp_logit)


def _bucket_size(value: Any) -> str:
    try:
        size = max(0, int(value))
    except (TypeError, ValueError):
        return "unknown"
    if size == 0:
        return "0"
    if size < 1024:
        return "1-1023"
    if size < 16384:
        return "1k-16k"
    if size < 262144:
        return "16k-256k"
    return "256k+"


def _bucket_fraction(value: float) -> str:
    if value <= 0:
        return "0"
    if value < 0.25:
        return "0-25%"
    if value < 0.5:
        return "25-50%"
    if value < 0.75:
        return "50-75%"
    if value < 1:
        return "75-100%"
    return "100%"


def _verified_source_lineage_features(
    report: dict[str, Any], dna_records: list[dict[str, Any]] | None,
    overlay: dict[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    if overlay is None:
        return {}
    if not dna_records:
        raise ValueError("Git line-origin features require their source-bound InfoTree DNA records")
    snapshot = report.get("sourceSnapshot") or {}
    provenance = report.get("analysisProvenance") or {}
    if (overlay.get("schema") != "info_geometry.git_fossil_overlay_manifest.v1"
            or overlay.get("gitHead") != snapshot.get("gitHead")
            or overlay.get("pathContentManifestSha256")
            != snapshot.get("pathContentManifestSha256")):
        raise ValueError("Git line-origin manifest belongs to another source-map generation")
    if (provenance.get("analysisInputsConsistentDuringScan") is not True
            or snapshot.get("worktreeConsistentDuringScan") is not True):
        raise ValueError("Git line-origin features require a consistent source-map generation")
    expected_generation = _generation_id(snapshot, provenance)
    if overlay.get("generationId") != expected_generation:
        raise ValueError("Git line-origin generation id does not match the source map")
    features_by_path = overlay.get("sourceLineageFeaturesByPath")
    if not isinstance(features_by_path, dict):
        raise ValueError("Git line-origin manifest lacks per-source features")
    feature_digest = hashlib.sha256(json.dumps(
        features_by_path, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")).hexdigest()
    if feature_digest != overlay.get("sourceLineageFeaturesSha256"):
        raise ValueError("Git line-origin feature digest mismatch")
    files = {row.get("path"): row for row in report.get("files", [])
             if isinstance(row, dict) and isinstance(row.get("path"), str)}
    dna_by_path = {row.get("artifactId"): row for row in dna_records
                   if isinstance(row, dict) and isinstance(row.get("artifactId"), str)}
    if len(dna_by_path) != len(dna_records):
        raise ValueError("duplicate or malformed InfoTree DNA records")
    if set(features_by_path) != set(dna_by_path):
        raise ValueError("Git line-origin features do not cover exactly the captured DNA sources")
    integer_fields = (
        "lineCount", "attributedLineCount", "committedLineCount",
        "currentContentLineCount", "distinctCommitCount", "distinctOriginPathCount",
        "declarationLinkCount", "declarationWithLineOriginCount", "distinctDeclarationCount",
    )
    for path, features in features_by_path.items():
        source_row = files.get(path)
        if (not isinstance(features, dict)
                or features.get("schema") != "info_geometry.source_lineage_features.v1"
                or features.get("generationId") != expected_generation
                or features.get("historyRevision") != snapshot.get("gitHead")
                or features.get("sourcePath") != path
                or features.get("sourceSha256") != dna_by_path[path].get("sourceSha256")
                or source_row is None
                or source_row.get("contentSha256") != features.get("sourceSha256")):
            raise ValueError(f"Git line-origin feature provenance differs for {path}")
        for field in integer_fields:
            value = features.get(field)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"Git line-origin feature {field} is invalid for {path}")
        if (features["attributedLineCount"] > features["lineCount"]
                or features["committedLineCount"] + features["currentContentLineCount"]
                > features["attributedLineCount"]
                or features["declarationWithLineOriginCount"] > features["declarationLinkCount"]
                or features["distinctDeclarationCount"] > features["declarationLinkCount"]):
            raise ValueError(f"Git line-origin feature counts are inconsistent for {path}")
    return features_by_path


def _features_for_map(report: dict[str, Any], dna_records: list[dict[str, Any]] | None = None,
                      git_fossil_overlay_manifest: dict[str, Any] | None = None
                      ) -> tuple[dict[str, Counter[str]], dict[str, list[dict[str, str]]]]:
    files = report.get("files")
    edges = report.get("dependencyEdges")
    declarations = report.get("leanDeclarationCandidates")
    if not isinstance(files, list) or not isinstance(edges, list) or not isinstance(declarations, list):
        raise ValueError("map requires files, dependencyEdges, and leanDeclarationCandidates")
    vectors: dict[str, Counter[str]] = {row["path"]: Counter() for row in files
                                        if isinstance(row, dict) and isinstance(row.get("path"), str)}
    evidence: dict[str, list[dict[str, str]]] = {path: [] for path in vectors}
    walk_adjacency: dict[str, list[tuple[str, str, str]]] = {}
    compiler_evidence = report.get("compilerArtifactEvidence") or {}
    fingerprint_integration = compiler_evidence.get("fingerprintIntegration") or {}
    source_snapshot = report.get("sourceSnapshot") or {}
    analysis_provenance = report.get("analysisProvenance") or {}
    compiler_fingerprints_verified = (
        fingerprint_integration.get("status") == "source_olean_and_export_hashes_verified"
        and compiler_evidence.get("joinStatus")
        == "verified_fingerprint_rows_joined_by_source_file"
        and source_snapshot.get("worktreeConsistentDuringScan") is True
        and analysis_provenance.get("analysisInputsConsistentDuringScan") is True
    )

    def add(path: str, feature: str, amount: float = 1.0) -> None:
        if path in vectors and math.isfinite(float(amount)) and amount > 0:
            vectors[path][feature] += float(amount)

    for row in files:
        path = row.get("path")
        if path not in vectors:
            continue
        for field in ("role", "ownerStatus", "pythonCpgRole"):
            if row.get(field):
                add(path, f"artifact.{field}={row[field]}")
        for target in row.get("buildTargets", []) if isinstance(row.get("buildTargets"), list) else []:
            add(path, f"build.target_count", 1)
        if row.get("buildTargets") or row.get("owner"):
            evidence[path].append({"kind": "build_ownership_candidate", "ref": path})
        add(path, f"artifact.size_bucket={_bucket_size(row.get('sizeBytes'))}")
        history = row.get("gitPathHistory")
        if isinstance(history, dict):
            add(path, f"git.touch_count", history.get("touchCount", 0))
            for change_type, count in (history.get("changeTypes") or {}).items():
                add(path, f"git.change_type={change_type}", count)
            evidence[path].append({"kind": "git_path_history_candidate", "ref": path})
        fingerprints = row.get("compilerFingerprints")
        if fingerprints is not None:
            if not compiler_fingerprints_verified:
                raise ValueError(f"compiler fingerprint summary is not provenance-verified for {path}")
            if (not isinstance(fingerprints, dict)
                    or fingerprints.get("typeDigestAlgorithm") != "lean-expr-debruijn-v4"):
                raise ValueError(f"unsupported compiler fingerprint summary for {path}")
            def fingerprint_count(field: str) -> int:
                value = fingerprints.get(field, 0)
                if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                    raise ValueError(f"invalid compiler fingerprint count {field} for {path}")
                return value

            declaration_count = fingerprint_count("declarationCount")
            unique_types = fingerprint_count("uniqueTypeDigestCount")
            unique_values = fingerprint_count("uniqueValueDigestCount")
            open_types = fingerprint_count("openTypeDigestCount")
            open_values = fingerprint_count("openValueDigestCount")
            if (unique_types > declaration_count or unique_values > declaration_count
                    or open_types > declaration_count or open_values > declaration_count):
                raise ValueError(f"invalid compiler fingerprint counts for {path}")
            add(path, "compiler.type_digest_algorithm=lean-expr-debruijn-v4")
            add(path, f"compiler.declaration_count_bucket={_bucket_size(declaration_count)}")
            add(path, "compiler.unique_type_digest_count", unique_types)
            add(path, "compiler.unique_value_digest_count", unique_values)
            add(path, "compiler.open_type_digest_count", open_types)
            add(path, "compiler.open_value_digest_count", open_values)
            if declaration_count:
                add(path, "compiler.type_digest_reuse_ratio",
                    (declaration_count - unique_types) / declaration_count)
            evidence[path].append({"kind": "compiler_type_fingerprint_summary",
                                   "ref": f"{path}:lean-expr-debruijn-v4"})
        evidence[path].append({"kind": "source_artifact", "ref": path})

    for edge in edges:
        if not isinstance(edge, dict):
            continue
        source, target, kind = edge.get("from"), edge.get("to"), edge.get("kind", "unknown")
        if source in vectors:
            add(source, f"dependency.out={kind}")
            evidence[source].append({"kind": "dependency_edge", "ref": f"{source}->{target}:{kind}"})
            walk_adjacency.setdefault(source, []).append((target, "out", str(kind)))
        if target in vectors:
            add(target, f"dependency.in={kind}")
            evidence[target].append({"kind": "dependency_edge",
                                     "ref": f"{source}->{target}:{kind}"})
            walk_adjacency.setdefault(target, []).append((source, "in", str(kind)))
    # Direction- and type-aware length-two walks add local topology to the
    # structural view without replacing or densifying the witnessed graph.
    # log1p dampens high-degree hubs; only observed edge pairs contribute.
    # The endpoint of the second edge is not part of this feature. Aggregate
    # its multiplicity once per middle vertex instead of enumerating O(deg²)
    # walks at hubs. Preserve parallel edges, backtracking, and self-loops.
    step_counts = {
        middle: Counter((direction, kind) for _, direction, kind in steps)
        for middle, steps in walk_adjacency.items()
    }
    for start, first_steps in walk_adjacency.items():
        counts: Counter[str] = Counter()
        for middle, first_direction, first_kind in first_steps:
            for (second_direction, second_kind), multiplicity in step_counts.get(middle, {}).items():
                feature = (
                    f"dependency.walk2={first_direction}:{first_kind}"
                    f">{second_direction}:{second_kind}"
                )
                counts[feature] += multiplicity
        for feature, count in counts.items():
            add(start, feature, math.log1p(count))
    for declaration in declarations:
        if not isinstance(declaration, dict):
            continue
        path, kind = declaration.get("sourcePath"), declaration.get("kind", "unknown")
        if path in vectors:
            add(path, f"declaration.kind={kind}")
            evidence[path].append({"kind": "lexical_declaration_candidate",
                                   "ref": f"{path}:{declaration.get('line', '?')}"})

    dna_by_path: dict[str, dict[str, Any]] = {}
    for record in dna_records or []:
        path = record.get("artifactId")
        if path in dna_by_path:
            raise ValueError(f"duplicate InfoTree DNA record for {path}")
        dna_by_path[path] = record
    for path, record in dna_by_path.items():
        if path not in vectors:
            continue
        if record.get("sourceSha256") != next(
                (row.get("contentSha256") for row in files if row.get("path") == path), None):
            raise ValueError(f"InfoTree DNA source hash does not match map artifact {path}")
        for feature, count in (record.get("features") or {}).items():
            add(path, f"infotree.{feature}", count)
        evidence[path].append({"kind": "infotree_dna", "ref": str(record.get("dnaFingerprint", ""))})
    lineage_features = _verified_source_lineage_features(
        report, dna_records, git_fossil_overlay_manifest
    )
    for path, features in lineage_features.items():
        add(path, f"git.lineage.attribution_status={features['lineAttributionStatus']}")
        for field in ("lineCount", "distinctCommitCount", "distinctOriginPathCount",
                      "declarationLinkCount", "distinctDeclarationCount"):
            add(path, f"git.lineage.{field}_bucket={_bucket_size(features[field])}")
        line_count = features["lineCount"]
        declaration_count = features["declarationLinkCount"]
        if line_count:
            for field, numerator in (
                ("attributedFraction", features["attributedLineCount"]),
                ("committedFraction", features["committedLineCount"]),
                ("currentContentFraction", features["currentContentLineCount"]),
            ):
                add(path, f"git.lineage.{field}={_bucket_fraction(numerator / line_count)}")
        if declaration_count:
            add(path, "git.lineage.declarationAttributionFraction=" + _bucket_fraction(
                features["declarationWithLineOriginCount"] / declaration_count
            ))
        evidence[path].append({
            "kind": "git_line_origin_summary",
            "ref": f"{features['generationId']}:{features['sourceSha256']}",
        })
    return vectors, evidence


def _dot(weights: dict[str, Any], vector: dict[str, float]) -> float:
    total = 0.0
    for feature, raw_weight in weights.items():
        weight = float(raw_weight)
        value = vector.get(feature, 0.0)
        if not math.isfinite(weight):
            raise ValueError("model contains a non-finite parameter")
        total += weight * value
    return total


def _canonical_embedding_packet_digest(packet: dict[str, Any]) -> str:
    fields = {
        key: packet[key]
        for key in ("schema", "sourceSnapshotSha256", "encoderVersion",
                    "embeddingDimension", "encoderTraining", "embeddings")
    }
    encoded = json.dumps(fields, sort_keys=True, ensure_ascii=False,
                         separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def build_encoder_embedding_packet(report: dict[str, Any], encoder_version: str,
                                   embeddings: list[dict[str, Any]], *,
                                   encoder_training: dict[str, Any] | None = None
                                   ) -> dict[str, Any]:
    """Bind externally computed encoder vectors to every current map artifact."""
    if report.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    snapshot = report.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing a mixed or inconsistent source snapshot")
    if not isinstance(encoder_version, str) or not encoder_version.strip():
        raise ValueError("encoder_version must be a non-empty string")
    if not isinstance(embeddings, list):
        raise ValueError("embeddings must be a list")
    if encoder_training is None:
        encoder_training = {"method": "unspecified", "dataScope": "unknown"}
    if (not isinstance(encoder_training, dict)
            or not isinstance(encoder_training.get("method"), str)
            or not encoder_training["method"].strip()
            or encoder_training.get("dataScope") not in {
                "unknown", "deterministic_no_training", "external_pretrained",
                "repository_train_split", "repository_all_source",
            }):
        raise ValueError("encoderTraining needs a method and a recognized dataScope")
    if encoder_training["dataScope"] == "repository_train_split":
        if (not isinstance(encoder_training.get("sourceSnapshotSha256"), str)
                or not isinstance(encoder_training.get("trainingSplitGroupsSha256"), str)):
            raise ValueError("train-split encoder provenance needs snapshot and group digests")
    source_hashes = {
        row["path"]: row.get("contentSha256")
        for row in report.get("files", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }
    normalized: dict[str, list[float]] = {}
    dimension = None
    for row in embeddings:
        if not isinstance(row, dict):
            raise ValueError("each encoder embedding must be an object")
        artifact = row.get("artifactId")
        if not isinstance(artifact, str) or artifact not in source_hashes:
            raise ValueError(f"encoder embedding references unknown artifact {artifact!r}")
        if artifact in normalized:
            raise ValueError(f"duplicate encoder embedding for {artifact}")
        if row.get("sourceSha256") != source_hashes[artifact]:
            raise ValueError(f"encoder embedding source hash does not match map artifact {artifact}")
        vector = row.get("vector")
        if not isinstance(vector, list) or not vector:
            raise ValueError(f"encoder embedding for {artifact} must have a non-empty vector")
        if dimension is None:
            dimension = len(vector)
        if len(vector) != dimension:
            raise ValueError("encoder embedding dimensions differ across artifacts")
        converted = []
        for value in vector:
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError(f"encoder embedding for {artifact} contains a non-numeric value")
            value = float(value)
            if not math.isfinite(value):
                raise ValueError(f"encoder embedding for {artifact} contains a non-finite value")
            converted.append(value)
        normalized[artifact] = converted
    if not normalized:
        raise ValueError("encoder embedding packet needs at least one current artifact vector")
    packet = {
        "schema": ENCODER_PACKET_SCHEMA,
        "sourceSnapshotSha256": snapshot.get("pathContentManifestSha256"),
        "encoderVersion": encoder_version,
        "embeddingDimension": dimension,
        "encoderTraining": encoder_training,
        "embeddings": [
            {"artifactId": artifact, "sourceSha256": source_hashes[artifact],
             "vector": normalized[artifact]}
            for artifact in sorted(normalized)
        ],
    }
    packet["packetSha256"] = _canonical_embedding_packet_digest(packet)
    return packet


def _validate_encoder_packet(report: dict[str, Any], model: dict[str, Any],
                             packet: dict[str, Any] | None
                             ) -> tuple[dict[str, list[float]], str | None]:
    spec = model.get("encoderSpec")
    if spec is None:
        if packet is not None:
            raise ValueError("model has no encoderSpec for supplied encoder embeddings")
        return {}, None
    if not isinstance(spec, dict):
        raise ValueError("encoderSpec must be an object")
    version, dimension = spec.get("version"), spec.get("dimension")
    if (not isinstance(version, str) or not version.strip()
            or isinstance(dimension, bool) or not isinstance(dimension, int) or dimension < 1):
        raise ValueError("encoderSpec needs a non-empty version and positive dimension")
    if not isinstance(packet, dict) or packet.get("schema") != ENCODER_PACKET_SCHEMA:
        raise ValueError(f"model requires an encoder packet with schema {ENCODER_PACKET_SCHEMA}")
    if packet.get("sourceSnapshotSha256") != (report.get("sourceSnapshot") or {}).get(
            "pathContentManifestSha256"):
        raise ValueError("encoder packet source snapshot does not match refactoring map")
    rebuilt = build_encoder_embedding_packet(report, packet.get("encoderVersion"),
                                              packet.get("embeddings"),
                                              encoder_training=packet.get("encoderTraining"))
    if packet != rebuilt or packet.get("packetSha256") != _canonical_embedding_packet_digest(packet):
        raise ValueError("encoder embedding packet digest or normalized contents do not match")
    if packet.get("encoderVersion") != version:
        raise ValueError("encoder packet version does not match model encoderSpec")
    if packet.get("embeddingDimension") != dimension:
        raise ValueError("encoder packet dimension does not match model encoderSpec")
    return ({row["artifactId"]: row["vector"] for row in packet["embeddings"]},
            packet["packetSha256"])


def apply_latent_expert_model(report: dict[str, Any], model: dict[str, Any],
                              dna_records: list[dict[str, Any]] | None = None,
                              encoder_packet: dict[str, Any] | None = None,
                              git_fossil_overlay_manifest: dict[str, Any] | None = None
                              ) -> dict[str, Any]:
    """Project artifact features and produce evidence-linked expert proposals."""
    if report.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    snapshot = report.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing a mixed or inconsistent source snapshot")
    if model.get("schema") != MODEL_SCHEMA:
        raise ValueError(f"expected model schema {MODEL_SCHEMA}")
    if model.get("featureVersion") != FEATURE_VERSION:
        raise ValueError("model feature version does not match this extractor")
    vocabulary = model.get("featureVocabulary")
    projection = model.get("projection")
    experts = model.get("experts")
    encoder_spec = model.get("encoderSpec")
    if (not isinstance(vocabulary, list) or len(set(vocabulary)) != len(vocabulary)
            or (not vocabulary and encoder_spec is None)):
        raise ValueError("model needs a unique featureVocabulary or a declared encoderSpec")
    if any(isinstance(feature, str) and feature.startswith("git.lineage.")
           for feature in vocabulary) and git_fossil_overlay_manifest is None:
        raise ValueError("model uses Git line-origin features; provide its generation-bound overlay")
    if not isinstance(projection, list) or not projection or not isinstance(experts, list) or not experts:
        raise ValueError("model needs projection rows and at least one expert")
    facet_vocabularies = []
    for expert in experts:
        heads_by_facet = expert.get("labelHeadsByFacet")
        if not isinstance(heads_by_facet, dict) or not heads_by_facet:
            raise ValueError("every expert needs non-empty labelHeadsByFacet")
        facet_vocabularies.append({
            facet: set(heads.keys()) if isinstance(heads, dict) else set()
            for facet, heads in heads_by_facet.items()
        })
    expected_facets = set(facet_vocabularies[0])
    if (not expected_facets
            or any(set(vocabularies) != expected_facets for vocabularies in facet_vocabularies[1:])):
        raise ValueError("every expert must define the same non-empty reviewed-label facets")
    for facet in sorted(expected_facets):
        labels = [vocabularies[facet] for vocabularies in facet_vocabularies]
        if not labels[0] or any(values != labels[0] for values in labels[1:]):
            raise ValueError(f"every expert must share one non-empty label vocabulary for {facet}")
    router = model.get("router")
    if isinstance(router, dict) and router.get("learnsInputConditionalWeights") is True:
        expert_order = router.get("expertOrder")
        feature_mean = router.get("featureMean")
        feature_scale = router.get("featureScale")
        expected_router_dimension = sum(
            len(expert.get("viewProjection", {}).get("projection", projection))
            for expert in experts
        )
        if (not isinstance(expert_order, list)
                or expert_order != [str(expert.get("id", "")) for expert in experts]
                or not isinstance(feature_mean, list)
                or not isinstance(feature_scale, list)
                or len(feature_mean) != expected_router_dimension
                or len(feature_scale) != expected_router_dimension):
            raise ValueError("input router order or feature normalization has invalid dimensions")
        for key, values in (("featureMean", feature_mean), ("featureScale", feature_scale)):
            if any(isinstance(value, bool) or not isinstance(value, (int, float))
                   or not math.isfinite(float(value))
                   or (key == "featureScale" and float(value) <= 0)
                   for value in values):
                raise ValueError(f"input router {key} must contain finite valid numbers")
        weights_by_expert = router.get("weightsByExpert")
        biases_by_expert = router.get("biasByExpert")
        if not isinstance(weights_by_expert, dict) or not isinstance(biases_by_expert, dict):
            raise ValueError("input router needs weightsByExpert and biasByExpert maps")
        for expert_id in expert_order:
            weights = weights_by_expert.get(expert_id)
            bias = biases_by_expert.get(expert_id)
            if (not isinstance(weights, list) or len(weights) != expected_router_dimension
                    or any(isinstance(value, bool) or not isinstance(value, (int, float))
                           or not math.isfinite(float(value)) for value in weights)
                    or isinstance(bias, bool) or not isinstance(bias, (int, float))
                    or not math.isfinite(float(bias))):
                raise ValueError(f"input router parameters are invalid for {expert_id}")
    vectors, evidence = _features_for_map(report, dna_records, git_fossil_overlay_manifest)
    encoder_vectors, encoder_packet_sha256 = _validate_encoder_packet(
        report, model, encoder_packet
    )
    encoder_projection = model.get("encoderProjection")
    if encoder_spec is not None:
        if (not isinstance(encoder_projection, list)
                or len(encoder_projection) != len(projection)
                or any(not isinstance(row, list)
                       or len(row) != encoder_spec["dimension"]
                       for row in encoder_projection)):
            raise ValueError("encoderProjection must match projection rows and encoder dimension")
        for row in encoder_projection:
            if any(isinstance(weight, bool) or not isinstance(weight, (int, float))
                   or not math.isfinite(float(weight)) for weight in row):
                raise ValueError("encoderProjection contains a non-finite or non-numeric weight")
        encoder_normalization = model.get("encoderNormalization")
        if encoder_normalization is not None:
            if not isinstance(encoder_normalization, dict):
                raise ValueError("encoderNormalization must be an object")
            mean, scale = encoder_normalization.get("mean"), encoder_normalization.get("scale")
            if (not isinstance(mean, list) or not isinstance(scale, list)
                    or len(mean) != encoder_spec["dimension"]
                    or len(scale) != encoder_spec["dimension"]):
                raise ValueError("encoderNormalization dimensions must match encoderSpec")
            if any(isinstance(value, bool) or not isinstance(value, (int, float))
                   or not math.isfinite(float(value)) for value in mean):
                raise ValueError("encoderNormalization mean must contain finite numbers")
            if any(isinstance(value, bool) or not isinstance(value, (int, float))
                   or not math.isfinite(float(value)) or float(value) <= 0
                   for value in scale):
                raise ValueError("encoderNormalization scale must contain positive finite numbers")
            normalized_encoder_vectors = {
                path: [(value - float(center)) / float(unit_scale)
                       for value, center, unit_scale in zip(
                           vector, mean, scale
                       )]
                for path, vector in encoder_vectors.items()
            }
        else:
            normalized_encoder_vectors = encoder_vectors
    elif encoder_projection is not None:
        raise ValueError("encoderProjection requires encoderSpec")
    else:
        normalized_encoder_vectors = {}
    min_gate = float(model.get("minimumGate", 0.0))
    min_label = float(model.get("minimumLabelProbability", 0.0))
    min_margin = float(model.get("minimumLabelMargin", 0.0))
    if (any(not math.isfinite(x) or x < 0 for x in (min_gate, min_label, min_margin))
            or min_gate > 1 or min_label > 1 or min_margin > 1):
        raise ValueError("abstention thresholds must be finite and in [0, 1]")
    vocabulary_set = set(vocabulary)
    projection_bias = model.get("projectionBias", [0.0] * len(projection))
    if (not isinstance(projection_bias, list) or len(projection_bias) != len(projection)
            or any(isinstance(value, bool) or not isinstance(value, (int, float))
                   or not math.isfinite(float(value)) for value in projection_bias)):
        raise ValueError("projectionBias must have one finite number per projection row")
    outputs = []
    for path, raw_vector in sorted(vectors.items()):
        if (encoder_spec is not None and path not in encoder_vectors
                and all(expert.get("viewProjection") is None for expert in experts)):
            abstain = {facet: ["encoder_embedding_missing"] for facet in sorted(expected_facets)}
            outputs.append({
                "artifactId": path, "latentCoordinates": [], "expertGates": {},
                "expertProposals": [],
                "combinedLabelProposalsByFacet": {
                    facet: [] for facet in sorted(expected_facets)
                },
                "abstainReasonsByFacet": abstain, "status": "abstain",
            })
            continue
        vector = {feature: math.log1p(value) for feature, value in raw_vector.items()
                  if feature in vocabulary_set and value > 0}
        latent = []
        for index, row in enumerate(projection):
            if not isinstance(row, dict):
                raise ValueError("each projection row must map input features to weights")
            projected = float(projection_bias[index]) + _dot(row, vector)
            if encoder_spec is not None and path in normalized_encoder_vectors:
                projected += sum(weight * value for weight, value in zip(
                    encoder_projection[index], normalized_encoder_vectors[path]
                ))
            latent.append(projected)
        gate_logits: dict[str, float] = {}
        latent_by_expert: dict[str, list[float]] = {}
        expert_logits: dict[str, dict[str, dict[str, float]]] = {}
        expert_evidence: dict[str, list[dict[str, str]]] = {}
        for expert in experts:
            expert_id = str(expert.get("id", ""))
            if not expert_id or expert_id in gate_logits:
                raise ValueError("experts need unique non-empty ids")
            evidence_kinds = expert.get("evidenceKinds")
            if not isinstance(evidence_kinds, list) or not evidence_kinds:
                raise ValueError(f"expert {expert_id} must declare evidenceKinds")
            expert_evidence[expert_id] = [item for item in evidence[path]
                                          if item["kind"] in evidence_kinds]
            view = expert.get("viewProjection")
            if view is None:
                expert_latent = latent
            else:
                view_projection = view.get("projection")
                view_bias = view.get("projectionBias")
                view_encoder_projection = view.get("encoderProjection")
                if (not isinstance(view_projection, list) or not view_projection
                        or not isinstance(view_bias, list)
                        or len(view_bias) != len(view_projection)):
                    raise ValueError(f"expert {expert_id} has an invalid viewProjection")
                expert_latent = []
                view_encoder_values = None
                if view_encoder_projection is not None:
                    if path not in normalized_encoder_vectors:
                        expert_evidence[expert_id] = []
                    else:
                        view_normalization = view.get("encoderNormalization")
                        if view_normalization is None:
                            view_encoder_values = encoder_vectors[path]
                        else:
                            centers = view_normalization.get("mean")
                            scales = view_normalization.get("scale")
                            if (not isinstance(centers, list) or not isinstance(scales, list)
                                    or len(centers) != len(encoder_vectors[path])
                                    or len(scales) != len(encoder_vectors[path])
                                    or any(float(scale) <= 0 for scale in scales)):
                                raise ValueError(
                                    f"expert {expert_id} encoder normalization dimensions differ"
                                )
                            view_encoder_values = [
                                (value - float(center)) / float(scale)
                                for value, center, scale in zip(
                                    encoder_vectors[path], centers, scales
                                )
                            ]
                for index, row in enumerate(view_projection):
                    if not isinstance(row, dict):
                        raise ValueError(f"expert {expert_id} projection rows must be objects")
                    value = float(view_bias[index]) + _dot(row, vector)
                    if view_encoder_projection is not None and view_encoder_values is not None:
                        if (not isinstance(view_encoder_projection, list)
                                or len(view_encoder_projection) != len(view_projection)
                                or len(view_encoder_projection[index]) != len(view_encoder_values)):
                            raise ValueError(f"expert {expert_id} encoder projection dimensions differ")
                        value += sum(float(weight) * item for weight, item in zip(
                            view_encoder_projection[index], view_encoder_values
                        ))
                    expert_latent.append(value)
            latent_by_expert[expert_id] = expert_latent
            gate_weights = expert.get("gateWeights") or []
            if len(gate_weights) != len(expert_latent):
                raise ValueError(f"expert {expert_id} gate dimension differs from its projection")
            if expert_evidence[expert_id]:
                gate_logits[expert_id] = float(expert.get("gateBias", 0.0)) + sum(
                    float(weight) * value for weight, value in zip(gate_weights, expert_latent)
                )
            expert_logits[expert_id] = {}
            for facet, heads in expert["labelHeadsByFacet"].items():
                label_logits = {}
                for label, head in heads.items():
                    weights = head.get("weights") or []
                    if len(weights) != len(expert_latent):
                        raise ValueError(
                            f"expert {expert_id} label head {facet}/{label} has wrong dimension"
                        )
                    label_logits[label] = float(head.get("bias", 0.0)) + sum(
                        float(weight) * value for weight, value in zip(weights, expert_latent)
                    )
                expert_logits[expert_id][facet] = label_logits
        if isinstance(router, dict) and router.get("learnsInputConditionalWeights") is True:
            router_features = []
            for expert_id in router["expertOrder"]:
                expert_values = (latent_by_expert[expert_id]
                                 if expert_evidence[expert_id]
                                 else [0.0] * len(latent_by_expert[expert_id]))
                router_features.extend(expert_values)
            normalized_router_features = [
                (value - float(center)) / float(scale)
                for value, center, scale in zip(
                    router_features, router["featureMean"], router["featureScale"]
                )
            ]
            routed_logits = {
                expert_id: float(router["biasByExpert"][expert_id]) + sum(
                    float(weight) * value for weight, value in zip(
                        router["weightsByExpert"][expert_id], normalized_router_features
                    )
                )
                for expert_id in router["expertOrder"] if expert_evidence[expert_id]
            }
            gates = _softmax(routed_logits)
        else:
            gates = _softmax({expert_id: score for expert_id, score in gate_logits.items()
                              if expert_evidence[expert_id]})
        combined_by_facet: dict[str, Counter[str]] = {
            facet: Counter() for facet in sorted(expected_facets)
        }
        expert_proposals = []
        for expert in experts:
            expert_id = str(expert["id"])
            if expert_id not in gates:
                expert_proposals.append({
                    "expert": expert_id, "gate": 0.0, "labelProposalsByFacet": {},
                    "evidence": [], "status": "abstain_no_declared_evidence",
                })
                continue
            proposals_by_facet = {}
            for facet in sorted(expected_facets):
                scores = {label: _sigmoid_score(logit)
                          for label, logit in expert_logits[expert_id][facet].items()}
                for label, probability in scores.items():
                    combined_by_facet[facet][label] += gates[expert_id] * probability
                top = sorted(scores.items(), key=lambda pair: (-pair[1], pair[0]))[:3]
                proposals_by_facet[facet] = [
                    {"label": label, "probability": score} for label, score in top
                ]
            expert_proposals.append({
                "expert": expert_id,
                "gate": gates[expert_id],
                "labelProposalsByFacet": proposals_by_facet,
                "evidence": expert_evidence[expert_id],
                "status": "expert_proposal_not_reviewed",
                "scoreSemantics": "uncalibrated_sigmoid_score",
                "expertVersion": expert.get("version", "unspecified"),
            })
        ranked_by_facet = {}
        abstain_by_facet = {}
        for facet, combined in combined_by_facet.items():
            ranked = sorted(combined.items(), key=lambda pair: (-pair[1], pair[0]))
            best = ranked[0] if ranked else (None, 0.0)
            margin = best[1] - (ranked[1][1] if len(ranked) > 1 else 0.0)
            reasons = []
            if not ranked:
                reasons.append("model_has_no_label_heads")
            has_input_features = bool(gates)
            if not has_input_features:
                reasons.append("no_model_features_observed")
            if ranked and best[1] < min_label:
                reasons.append("label_probability_below_threshold")
            if ranked and margin < min_margin:
                reasons.append("label_margin_below_threshold")
            if not gates or max(gates.values(), default=0.0) < min_gate:
                reasons.append("expert_gate_below_threshold")
            ranked_by_facet[facet] = [
                {"label": label, "probability": score} for label, score in ranked
            ]
            abstain_by_facet[facet] = sorted(set(reasons))
        ready_facets = sum(not reasons for reasons in abstain_by_facet.values())
        if ready_facets == 0:
            status = "abstain"
        elif ready_facets < len(abstain_by_facet):
            status = "partial_abstention"
        else:
            status = "unreviewed_taxonomy_proposal"
        outputs.append({
            "artifactId": path,
            "latentCoordinates": latent,
            "expertLatentCoordinates": latent_by_expert,
            "expertGates": gates,
            "expertProposals": expert_proposals,
            "combinedLabelProposalsByFacet": ranked_by_facet,
            "abstainReasonsByFacet": abstain_by_facet,
            "status": status,
        })
    return {
        "schema": "info_geometry.latent_taxonomy_proposals.v3",
        "featureVersion": FEATURE_VERSION,
        "modelVersion": model.get("modelVersion"),
        "encoderVersion": encoder_spec.get("version") if encoder_spec else None,
        "encoderEmbeddingPacketSha256": encoder_packet_sha256,
        "encoderCoverage": {
            "embeddedArtifactCount": len(encoder_vectors),
            "targetArtifactCount": len(vectors),
            "missingArtifactCount": len(vectors) - len(encoder_vectors),
        } if encoder_spec else None,
        "sourceSnapshotSha256": snapshot.get("pathContentManifestSha256"),
        "gitLineageFeatureGenerationId": (
            git_fossil_overlay_manifest.get("generationId")
            if git_fossil_overlay_manifest else None
        ),
        "gitLineageFeatureSourceCount": len(
            git_fossil_overlay_manifest.get("sourceLineageFeaturesByPath", {})
            if git_fossil_overlay_manifest else {}
        ),
        "trainingDataSnapshotRefs": model.get("trainingDataSnapshotRefs", []),
        "projectionDimension": len(projection),
        "expertIds": [str(expert["id"]) for expert in experts],
        "labelFacets": sorted(expected_facets),
        "labelPredictionSemantics": "independent_sigmoid_scores_per_facet",
        "artifactCount": len(outputs),
        "reviewedLabelCount": 0,
        "authority": "model proposals only; no semantic or owner label is promoted without review",
        "artifacts": outputs,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("model", type=Path)
    parser.add_argument("--infotree-dna", type=Path)
    parser.add_argument("--git-fossil-overlay-manifest", type=Path,
                        help="optional generation-bound current line-origin feature summary")
    parser.add_argument("--encoder-embeddings", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = _read_json(args.refactoring_map)
    model = _read_json(args.model)
    encoder_packet = _read_json(args.encoder_embeddings) if args.encoder_embeddings else None
    dna = None
    if args.infotree_dna:
        with args.infotree_dna.open("r", encoding="utf-8") as stream:
            dna = [json.loads(line) for line in stream if line.strip()]
    fossil_overlay = (_read_json(args.git_fossil_overlay_manifest)
                      if args.git_fossil_overlay_manifest else None)
    result = apply_latent_expert_model(
        report, model, dna, encoder_packet, fossil_overlay
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    print(json.dumps({"schema": result["schema"], "artifactCount": result["artifactCount"],
                      "abstentionCount": sum(x["status"] == "abstain" for x in result["artifacts"]),
                      "output": str(args.out)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
