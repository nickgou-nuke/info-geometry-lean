#!/usr/bin/env python3
"""Exhaustive physical-folder entrypoint for the lexical Lean inventory.

Includes ignored and hidden directories, dependencies, and external references.
Git metadata and symlinks are reported as omissions. This does not establish
semantic completeness: each candidate still needs Lean owner/dependent review.
The bounded entrypoint remains useful for routine repository-source checks.
"""

import counterexample_inventory as scanner


def main() -> None:
    # The scanner's single-process traversal reports these exclusions. Keep
    # provenance classification intact for dependencies and external sources.
    scanner.SKIP_DIRECTORIES = {".git"}
    scanner.main()


if __name__ == "__main__":
    main()
