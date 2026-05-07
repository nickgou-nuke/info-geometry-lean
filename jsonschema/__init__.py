from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from datetime import datetime
from typing import Any

from .exceptions import ValidationError


__all__ = [
    "Draft202012Validator",
    "RefResolver",
    "FormatChecker",
    "ValidationError",
]


def _looks_like_ref(schema: Mapping[str, Any], ref: str) -> Mapping[str, Any] | None:
    if isinstance(schema.get("$ref"), str):
        return {"$ref": schema["$ref"]}
    return None


def _iter_errors(schema: Mapping[str, Any], instance: Any, path: list[str | int], resolver: "RefResolver | None") -> list[ValidationError]:
    errors: list[ValidationError] = []

    if "$ref" in schema:
        ref = str(schema["$ref"])
        target = None
        if resolver is not None and isinstance(resolver.store, dict):
            target = resolver.store.get(ref)
            if target is None and "#" in ref:
                base_ref, fragment = ref.split("#", 1)
                target = resolver.store.get(base_ref)
                if isinstance(target, Mapping) and fragment.startswith("/"):
                    for part in fragment.lstrip("/").split("/"):
                        part = part.replace("~1", "/").replace("~0", "~")
                        if isinstance(target, Mapping) and part in target:
                            target = target[part]
                        else:
                            target = None
                            break
        if target is None:
            errors.append(
                ValidationError(
                    f"unresolved $ref: {ref}",
                    path=tuple(path),
                )
            )
        elif isinstance(target, Mapping):
            errors.extend(_iter_errors(target, instance, path, resolver))
        return errors

    schema_type = schema.get("type")
    if schema_type is not None:
        expected_types: tuple[type, ...]
        if schema_type == "string":
            expected_types = (str,)
        elif schema_type == "number":
            expected_types = (int, float)
        elif schema_type == "integer":
            expected_types = (int,)
        elif schema_type == "object":
            expected_types = (dict,)
        elif schema_type == "array":
            expected_types = (list,)
        elif schema_type == "boolean":
            expected_types = (bool,)
        elif schema_type == "null":
            expected_types = (type(None),)
        else:
            expected_types = ()

        if expected_types and not isinstance(instance, expected_types):
            errors.append(
                ValidationError(
                    f"should be of type {schema_type}",
                    path=tuple(path),
                )
            )
            return errors
        if schema_type == "integer" and isinstance(instance, bool):
            errors.append(ValidationError("should be integer, not bool", path=tuple(path)))

    if schema_type in {"object", "array"}:
        if isinstance(schema_type, str) and not isinstance(instance, {"object": dict, "array": list}[schema_type]):
            return errors

    if isinstance(instance, Mapping):
        required = schema.get("required", [])
        if isinstance(required, Sequence):
            for key in required:
                if isinstance(key, str) and key not in instance:
                    errors.append(ValidationError(f"missing required property '{key}'", path=tuple(path + [key])))

        properties = schema.get("properties")
        if isinstance(properties, Mapping):
            for key, subschema in properties.items():
                if key in instance and isinstance(subschema, Mapping):
                    child_path = path + [key]
                    errors.extend(_iter_errors(subschema, instance[key], child_path, resolver))

        if schema.get("additionalProperties") is False:
            if properties is not None and isinstance(properties, Mapping):
                extras = set(instance.keys()) - set(properties.keys())
                for extra in sorted(extras):
                    errors.append(ValidationError(f"additional property '{extra}' not allowed", path=tuple(path + [str(extra)])))

        min_props = schema.get("minProperties")
        if isinstance(min_props, int) and len(instance) < min_props:
            errors.append(ValidationError(f"should have at least {min_props} properties", path=tuple(path)))

    if isinstance(instance, Sequence) and not isinstance(instance, (str, bytes, bytearray)):
        items_schema = schema.get("items")
        if isinstance(items_schema, Mapping):
            for i, child in enumerate(instance):
                errors.extend(_iter_errors(items_schema, child, path + [i], resolver))

        min_items = schema.get("minItems")
        if isinstance(min_items, int) and len(instance) < min_items:
            errors.append(ValidationError(f"should have at least {min_items} items", path=tuple(path)))

        contains_schema = schema.get("contains")
        if isinstance(contains_schema, Mapping):
            if not any(not _iter_errors(contains_schema, child, path, resolver) for child in instance):
                errors.append(ValidationError("does not contain items matching the given schema", path=tuple(path)))

    enum_vals = schema.get("enum")
    if enum_vals is not None:
        try:
            if instance not in enum_vals:
                errors.append(ValidationError(f"should be one of {list(enum_vals)}", path=tuple(path)))
        except TypeError:
            # Unhashable instance values are effectively "not equal" to enum entries.
            pass

    if "const" in schema and instance != schema["const"]:
        errors.append(ValidationError(f"{schema['const']!r} was expected", path=tuple(path)))

    min_length = schema.get("minLength")
    if min_length is not None and isinstance(instance, str):
        if len(instance) < int(min_length):
            errors.append(ValidationError(f"should have at least {min_length} characters", path=tuple(path)))

    pattern = schema.get("pattern")
    if pattern is not None and isinstance(instance, str):
        import re

        if re.search(str(pattern), instance) is None:
            errors.append(ValidationError(f"should match pattern {pattern}", path=tuple(path)))

    if "format" in schema and isinstance(instance, str) and schema["format"] == "date-time":
        try:
            datetime.fromisoformat(instance.replace("Z", "+00:00"))
        except Exception:
            errors.append(ValidationError(f"should match format date-time: {instance!r}", path=tuple(path)))

    one_of = schema.get("oneOf")
    if isinstance(one_of, Sequence):
        matched = 0
        for branch in one_of:
            if not isinstance(branch, Mapping):
                continue
            if not _iter_errors(branch, instance, path, resolver):
                matched += 1
        if matched != 1:
            errors.append(ValidationError("should validate against exactly one schema in oneOf", path=tuple(path)))

    any_of = schema.get("anyOf")
    if isinstance(any_of, Sequence):
        if not any(not _iter_errors(branch, instance, path, resolver) for branch in any_of if isinstance(branch, Mapping)):
            errors.append(ValidationError("should validate against at least one schema in anyOf", path=tuple(path)))

    all_of = schema.get("allOf")
    if isinstance(all_of, Sequence):
        for branch in all_of:
            if isinstance(branch, Mapping):
                errors.extend(_iter_errors(branch, instance, path, resolver))

    return errors


class Draft202012Validator:
    def __init__(self, schema: Mapping[str, Any], format_checker: Any | None = None, resolver: "RefResolver | None" = None) -> None:
        self.schema = dict(schema)
        self.resolver = resolver

    @classmethod
    def check_schema(cls, schema: Mapping[str, Any]) -> None:
        if not isinstance(schema, Mapping):
            raise ValidationError("schema must be a mapping")

    def iter_errors(self, instance: Any, *, _schema: Mapping[str, Any] | None = None):
        schema = dict(self.schema if _schema is None else _schema)
        return list(_iter_errors(schema, instance, [], resolver=self.resolver))

    def is_valid(self, instance: Any) -> bool:
        return not self.iter_errors(instance)


def validate(instance: Any, schema: Mapping[str, Any], cls: type[Draft202012Validator] | None = None) -> None:
    validator_cls = cls or Draft202012Validator
    validator = validator_cls(schema)
    errors = list(validator.iter_errors(instance))
    if errors:
        raise errors[0]


class FormatChecker:
    def __init__(self) -> None:
        pass


class RefResolver:
    def __init__(self, base_uri: str | None = None, referrer: Any | None = None, store: Mapping[str, Any] | None = None) -> None:
        self.base_uri = base_uri
        self.referrer = referrer
        self.store = dict(store or {})

    @classmethod
    def from_schema(cls, schema: Mapping[str, Any] | None = None, store: Mapping[str, Any] | None = None) -> "RefResolver":
        return cls(store=store)

