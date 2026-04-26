from __future__ import annotations


class ValidationError(ValueError):
    def __init__(self, message: str, *, path: tuple[str | int, ...] = (), absolute_path: tuple[str | int, ...] | None = None) -> None:
        super().__init__(message)
        self.message = message
        self.path = tuple(path)
        self.absolute_path = tuple(absolute_path) if absolute_path is not None else tuple(path)
        self.validator = None
        self.schema_path: tuple[str, ...] = ()

