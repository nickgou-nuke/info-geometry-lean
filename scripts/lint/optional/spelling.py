#!/usr/bin/env python3
"""Optional spelling linter for Lean 4 docstrings and comments (PhysLean model).

Uses the custom exemption word list at ``scripts/lint/exemptions/spellingWords.txt``.
Extracts prose from ``/-! ... -/``, ``/-- ... -/``, and ``-- ...`` comments, stripping
inline code backticks, fenced code blocks, LaTeX math, and camelCase/snake_case
identifiers.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_WORD_LIST = REPO_ROOT / "scripts" / "lint" / "exemptions" / "spellingWords.txt"
SYSTEM_WORDS_PATH = Path("/usr/share/dict/words")

# Curated high-signal technical & mathematical misspelling dictionary
COMMON_MISSPELLINGS: dict[str, str] = {
    "abelianess": "abelianness",
    "absorbtion": "absorption",
    "accomodate": "accommodate",
    "acheive": "achieve",
    "additonal": "additional",
    "algberaic": "algebraic",
    "algebar": "algebra",
    "algebraicaly": "algebraically",
    "algoritm": "algorithm",
    "analagous": "analogous",
    "annhilate": "annihilate",
    "annhilation": "annihilation",
    "antimmomutator": "anticommutator",
    "approxmation": "approximation",
    "arbitary": "arbitrary",
    "archimedean": "Archimedean",
    "asociative": "associative",
    "assocaited": "associated",
    "associativty": "associativity",
    "assumtpion": "assumption",
    "asymetric": "asymmetric",
    "asyptotic": "asymptotic",
    "bijectve": "bijective",
    "boundry": "boundary",
    "caluclate": "calculate",
    "canoncical": "canonical",
    "canoncial": "canonical",
    "catgeory": "category",
    "cauchys": "Cauchy's",
    "characeristic": "characteristic",
    "cohomolgy": "cohomology",
    "colimt": "colimit",
    "commuatative": "commutative",
    "commuatator": "commutator",
    "commutativty": "commutativity",
    "compability": "compatibility",
    "complemnt": "complement",
    "componet": "component",
    "conection": "connection",
    "conjuagte": "conjugate",
    "conseqeunce": "consequence",
    "consturct": "construct",
    "consturction": "construction",
    "contian": "contain",
    "contunuous": "continuous",
    "contradiciton": "contradiction",
    "convergnece": "convergence",
    "coordinat": "coordinate",
    "corrolary": "corollary",
    "correspondance": "correspondence",
    "covaraint": "covariant",
    "cylinderical": "cylindrical",
    "decompostion": "decomposition",
    "defintion": "definition",
    "degenrate": "degenerate",
    "dependancy": "dependency",
    "deriviative": "derivative",
    "deterimant": "determinant",
    "diagnoal": "diagonal",
    "differentiabilty": "differentiability",
    "dimenison": "dimension",
    "dimensionnal": "dimensional",
    "discontinous": "discontinuous",
    "distribitive": "distributive",
    "eigenvaule": "eigenvalue",
    "elemnt": "element",
    "embeding": "embedding",
    "equivalance": "equivalence",
    "equivlaent": "equivalent",
    "existance": "existence",
    "explicilty": "explicitly",
    "extenison": "extension",
    "familiy": "family",
    "finitness": "finiteness",
    "formual": "formula",
    "foundamental": "fundamental",
    "fucntion": "function",
    "functorality": "functoriality",
    "genearl": "general",
    "geometery": "geometry",
    "globualr": "globular",
    "grothendeick": "Grothendieck",
    "hamiltionian": "Hamiltonian",
    "heisenburg": "Heisenberg",
    "hermetian": "Hermitian",
    "hilber": "Hilbert",
    "homeomoprhism": "homeomorphism",
    "homogeneuos": "homogeneous",
    "homomoprhism": "homomorphism",
    "homotopoy": "homotopy",
    "hypotheis": "hypothesis",
    "idempotnet": "idempotent",
    "identiy": "identity",
    "immediatly": "immediately",
    "implicaiton": "implication",
    "indepedent": "independent",
    "induciton": "induction",
    "inequalty": "inequality",
    "infinitesmal": "infinitesimal",
    "informaiton": "information",
    "injectve": "injective",
    "integable": "integrable",
    "interseciton": "intersection",
    "invaraint": "invariant",
    "invertable": "invertible",
    "isomoprhic": "isomorphic",
    "isomoprhism": "isomorphism",
    "isomorpic": "isomorphic",
    "isomorpism": "isomorphism",
    "lagrangain": "Lagrangian",
    "laplacain": "Laplacian",
    "linera": "linear",
    "localizaiton": "localization",
    "manfifold": "manifold",
    "mathmematical": "mathematical",
    "matirx": "matrix",
    "measruable": "measurable",
    "moniod": "monoid",
    "monomoprhism": "monomorphism",
    "morhpism": "morphism",
    "multiplcation": "multiplication",
    "multiplicaitve": "multiplicative",
    "neccessary": "necessary",
    "nilpotnet": "nilpotent",
    "noncommuatative": "noncommutative",
    "normalizaiton": "normalization",
    "notaiton": "notation",
    "observabel": "observable",
    "occurence": "occurrence",
    "operater": "operator",
    "orthognal": "orthogonal",
    "orthonomal": "orthonormal",
    "paramter": "parameter",
    "partiton": "partition",
    "permuation": "permutation",
    "pierce": "Peirce",
    "pluecker": "Plücker",
    "polynomail": "polynomial",
    "positve": "positive",
    "preshef": "presheaf",
    "probabilty": "probability",
    "projecter": "projector",
    "propostion": "proposition",
    "pushot": "pushout",
    "quadraitc": "quadratic",
    "quantizaiton": "quantization",
    "quaterion": "quaternion",
    "quotinet": "quotient",
    "reciprocl": "reciprocal",
    "realtion": "relation",
    "relativstic": "relativistic",
    "renormalizaiton": "renormalization",
    "represenation": "representation",
    "residuum": "residue",
    "retracion": "retraction",
    "riemannain": "Riemannian",
    "satisfes": "satisfies",
    "semigruop": "semigroup",
    "seperable": "separable",
    "sequnce": "sequence",
    "simplicialy": "simplicially",
    "simultaneuos": "simultaneous",
    "singularty": "singularity",
    "spactime": "spacetime",
    "stablizer": "stabilizer",
    "statment": "statement",
    "structre": "structure",
    "subalgbera": "subalgebra",
    "subgruop": "subgroup",
    "submoduel": "submodule",
    "subpsace": "subspace",
    "substituion": "substitution",
    "sufficent": "sufficient",
    "surjectve": "surjective",
    "symetric": "symmetric",
    "symmetery": "symmetry",
    "symplecitc": "symplectic",
    "tautolgy": "tautology",
    "teh": "the",
    "theorm": "theorem",
    "theroem": "theorem",
    "topolgical": "topological",
    "topolgy": "topology",
    "transforamtion": "transformation",
    "transitve": "transitive",
    "triangluar": "triangular",
    "trivally": "trivially",
    "twister": "twistor",
    "ultafilter": "ultrafilter",
    "unqiue": "unique",
    "uniquness": "uniqueness",
    "unitray": "unitary",
    "vacous": "vacuous",
    "vanishs": "vanishes",
    "variaiton": "variation",
    "vecter": "vector",
    "vorticty": "vorticity",
}

COMMENT_BLOCK_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")
FENCED_CODE_RE = re.compile(r"```.*?```", re.DOTALL)
INLINE_CODE_RE = re.compile(r"`[^`]*`")
MATH_BLOCK_RE = re.compile(r"\$\$.*?\$\$|\$[^$\n]+\$", re.DOTALL)
LATEX_CMD_RE = re.compile(r"\\[A-Za-z]+")
URL_RE = re.compile(r"https?://\S+|file://\S+")
WORD_RE = re.compile(r"\b[A-Za-z]{3,}\b")


def rel_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def load_word_list(path: Path) -> set[str]:
    if not path.exists():
        return set()
    words: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        w = raw.split("#", 1)[0].strip().lower()
        if w:
            words.add(w)
    return words


def collect_lean_files(paths: list[str]) -> list[Path]:
    collected: list[Path] = []
    for raw in paths:
        p = Path(raw)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if p.is_file() and p.suffix == ".lean":
            collected.append(p)
        elif p.is_dir():
            for child in sorted(p.rglob("*.lean")):
                if any(part.startswith(".") or part == "lake-packages" for part in child.parts):
                    continue
                collected.append(child)
    return sorted(set(collected))


def is_identifier_like(token: str) -> bool:
    """Return True if token is camelCase / PascalCase / acronym rather than plain prose."""
    if "_" in token or any(ch.isdigit() for ch in token):
        return True
    # Internal uppercase letters indicate camelCase / PascalCase Lean names
    if any(ch.isupper() for ch in token[1:]):
        return True
    return False


def scrub_comment(text: str) -> str:
    text = FENCED_CODE_RE.sub(" ", text)
    text = INLINE_CODE_RE.sub(" ", text)
    text = MATH_BLOCK_RE.sub(" ", text)
    text = URL_RE.sub(" ", text)
    text = LATEX_CMD_RE.sub(" ", text)
    return text


def scan_file(
    path: Path,
    allowed_words: set[str],
    system_words: set[str] | None,
) -> list[tuple[int, str, str]]:
    """Return list of (line_no, bad_word, suggestion) in `path`."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []

    findings: list[tuple[int, str, str]] = []
    spans: list[tuple[int, str]] = []

    for m in COMMENT_BLOCK_RE.finditer(text):
        line_no = text.count("\n", 0, m.start()) + 1
        spans.append((line_no, m.group(0)))

    # Mask block comments before scanning line comments
    masked = COMMENT_BLOCK_RE.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    for m in LINE_COMMENT_RE.finditer(masked):
        line_no = masked.count("\n", 0, m.start()) + 1
        spans.append((line_no, m.group(0)))

    for base_line, raw_comment in spans:
        cleaned = scrub_comment(raw_comment)
        for offset, line in enumerate(cleaned.splitlines()):
            for wm in WORD_RE.finditer(line):
                word = wm.group(0)
                if is_identifier_like(word):
                    continue
                lower = word.lower()
                if lower in allowed_words:
                    continue
                if lower in COMMON_MISSPELLINGS:
                    findings.append((base_line + offset, word, COMMON_MISSPELLINGS[lower]))
                elif system_words is not None and lower not in system_words:
                    findings.append((base_line + offset, word, "not in dictionary / spellingWords.txt"))

    return findings


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check spelling in Lean comments/docstrings using scripts/lint/exemptions/spellingWords.txt."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        default=["lean/InfoGeometry"],
        help="Lean files or directories to check (default: lean/InfoGeometry).",
    )
    parser.add_argument(
        "--words",
        type=Path,
        default=DEFAULT_WORD_LIST,
        help="Path to exemption word list (default: scripts/lint/exemptions/spellingWords.txt).",
    )
    parser.add_argument(
        "--system-dict",
        action="store_true",
        help="Also flag words absent from /usr/share/dict/words and spellingWords.txt.",
    )
    args = parser.parse_args()

    allowed_words = load_word_list(args.words)
    system_words: set[str] | None = None
    if args.system_dict and SYSTEM_WORDS_PATH.exists():
        system_words = {
            w.strip().lower()
            for w in SYSTEM_WORDS_PATH.read_text(encoding="utf-8", errors="ignore").splitlines()
            if w.strip()
        }

    files = collect_lean_files(args.paths)
    all_findings: list[str] = []

    for path in files:
        rel = rel_path(path)
        for line_no, bad_word, suggestion in scan_file(path, allowed_words, system_words):
            all_findings.append(f"{rel}:{line_no}: `{bad_word}` -> {suggestion}")

    if all_findings:
        print(f"[spelling] FAILED ({len(all_findings)} potential misspelling(s)):")
        for item in all_findings[:100]:
            print(f"  - {item}")
        if len(all_findings) > 100:
            print(f"  ... and {len(all_findings) - 100} more")
        return 1

    print(
        f"[spelling] PASSED ({len(files)} file(s) checked, {len(allowed_words)} exempted domain words loaded)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
