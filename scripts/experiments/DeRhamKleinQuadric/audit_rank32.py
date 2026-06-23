#!/usr/bin/env python3
"""Rank-32 de Rham audit harness for the Klein-quadric-like polynomial.

Target polynomial (default `D=4`):

  f = q(a) * q(b) * q(a - b)

with

  q(x) = x0^2 + x1^2 + x2^2 + x3^2.

This tool runs available CAS backends and records structured diagnostics. It does
not assume any backend is installed; missing binaries are reported as such.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Tuple

ROOT = Path(__file__).resolve().parents[3]
ARTIFACT_DIR = ROOT / "artifacts" / "de_rham_klein_quadric"


def vars_for_dim(dim: int) -> Tuple[str, ...]:
    if dim < 1:
        raise ValueError("dim must be >= 1")
    a = [f"a{i}" for i in range(dim)]
    b = [f"b{i}" for i in range(dim)]
    return tuple(a + b)


def q_expr(vars_block: Tuple[str, ...], signature: str) -> str:
    if signature == "euclidean":
        return " + ".join(f"({v})^2" for v in vars_block)
    if signature == "minkowski":
        # one time-like and the rest space-like convention.
        return " + ".join(f"({v})^2" for v in vars_block[:1]) + (
            " - " + " - ".join(f"({v})^2" for v in vars_block[1:])
            if len(vars_block) > 1
            else ""
        )
    raise ValueError(f"unknown signature: {signature}")


def q_numeric(block: Tuple[int, ...], signature: str, p: int) -> int:
    if signature == "euclidean":
        return sum((x * x) % p for x in block) % p
    if signature == "minkowski":
        return (block[0] * block[0] - sum((x * x) for x in block[1:])) % p
    raise ValueError(f"unknown signature: {signature}")


def quadratic_coefficients(dim: int, signature: str) -> Tuple[int, ...]:
    if signature == "euclidean":
        return tuple(1 for _ in range(dim))
    if signature == "minkowski":
        return (1,) + tuple(-1 for _ in range(dim - 1))
    raise ValueError(f"unknown signature: {signature}")


def legendre_symbol(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    val = pow(a, (p - 1) // 2, p)
    return 1 if val == 1 else -1


def quadratic_zero_count_even(dim: int, signature: str, p: int) -> Tuple[int, int]:
    """Return (# isotropic vectors, split sign) for an even-dimensional form.

    For nondegenerate q over F_p and dim = 2m:
      # {x | q(x)=0} = p^(dim-1) + eps * (p-1) * p^(m-1)
    where eps = chi((-1)^m det(q)).
    """
    if dim <= 0 or dim % 2 != 0:
        raise ValueError("closed-form zero count currently expects positive even dimension")
    coeffs = quadratic_coefficients(dim, signature)
    det = 1
    for c in coeffs:
        det = (det * c) % p
    m = dim // 2
    eps = legendre_symbol(((-1) ** m) * det, p)
    return quadratic_zero_count_even_with_sign(dim, eps, p), eps


def quadratic_zero_count_even_with_sign(dim: int, eps: int, p: int) -> int:
    if dim <= 0 or dim % 2 != 0:
        raise ValueError("zero count by split sign expects positive even dimension")
    m = dim // 2
    return pow(p, dim - 1) + eps * (p - 1) * pow(p, m - 1)


def finite_field_count_closed_form(dim: int, signature: str, p: int) -> dict:
    """Exact complement count for odd p and even dim.

    The complement is `{(a,b) | q(a) q(b) q(a-b) != 0}`.  Inclusion-exclusion
    reduces the only nontrivial term to isotropic orthogonal pairs
    `q(a)=q(b)=B(a,b)=0`.  For a nonzero isotropic `a`, `a^perp/<a>` has the
    same split sign and dimension `dim-2`.
    """
    if p == 2:
        return {
            "status": "skipped",
            "message": "p=2 is characteristic-degenerate for this quadratic-form formula",
        }
    if dim < 2 or dim % 2 != 0:
        return {
            "status": "skipped",
            "message": "closed-form count currently implemented for even dim >= 2",
        }

    n0, eps = quadratic_zero_count_even(dim, signature, p)
    if dim == 2:
        quotient_zero = 1
    else:
        quotient_zero = quadratic_zero_count_even_with_sign(dim - 2, eps, p)
    triple = n0 + (n0 - 1) * p * quotient_zero

    total = pow(p, 2 * dim)
    nonzero = total - 3 * n0 * pow(p, dim) + 3 * n0 * n0 - triple
    zeros = total - nonzero
    return {
        "status": "ok",
        "method": "quadratic_inclusion_exclusion",
        "p": p,
        "total": total,
        "quadric_zero_vectors": n0,
        "split_sign": eps,
        "isotropic_orthogonal_pairs": triple,
        "nonzero": nonzero,
        "f_zero": zeros,
        "ratio_nonzero": nonzero / total,
    }


def finite_field_symbolic_formula(dim: int, signature: str) -> dict | None:
    if dim == 4 and signature == "euclidean":
        return {
            "status": "ok",
            "variable": "p",
            "assumptions": "odd prime; q is split over F_p for D=4 euclidean because eps=1",
            "quadric_zero_vectors": "p^3 + p^2 - p",
            "isotropic_orthogonal_pairs": "2*p^5 + p^4 - 2*p^3",
            "complement_count_expanded": "p^8 - 3*p^7 + 7*p^5 - 4*p^4 - 4*p^3 + 3*p^2",
            "complement_count_factored": "p^2*(p - 1)^2*(p + 1)*(p^3 - 2*p^2 - p + 3)",
            "zero_locus_count_factored": "p^2*(3*p^5 - 7*p^3 + 4*p^2 + 4*p - 3)",
            "candidate_euler_characteristic_from_count_at_1": 0,
            "rank32_euler_check": "not_disproved; an even total Betti rank can have Euler characteristic 0",
            "warning": "This is a finite-field point-count formula, not a de Rham Betti-rank certificate.",
        }
    if dim == 4 and signature == "minkowski":
        return {
            "status": "conditional",
            "variable": "p",
            "assumptions": "odd prime; split sign eps = chi(-1), so the formula depends on p mod 4",
            "warning": "Use sampled counts until a piecewise symbolic formula is recorded.",
        }
    return None


def q_zero_from_vec(x: Tuple[int, ...], y: Tuple[int, ...], signature: str, p: int) -> int:
    return (
        q_numeric(x, signature, p)
        * q_numeric(y, signature, p)
        * q_numeric(tuple(a - b for a, b in zip(x, y)), signature, p)
    ) % p


def finite_field_count_bruteforce(dim: int, signature: str, p: int) -> int:
    comp = 0
    for vec in itertools.product(range(p), repeat=2 * dim):
        a = vec[:dim]
        b = vec[dim:]
        if q_zero_from_vec(tuple(a), tuple(b), signature, p) != 0:
            comp += 1
    return comp


def singular_script(dim: int, signature: str) -> str:
    vars_total = vars_for_dim(dim)
    avars = vars_total[:dim]
    bvars = vars_total[dim:]
    qA = q_expr(avars, signature)
    qB = q_expr(bvars, signature)
    qC = q_expr(tuple(f"{a}-{b}" for a, b in zip(avars, bvars)), signature)
    diffs = [f"poly d{v} = diff(f,{v});" for v in vars_total]

    var_decl = ",".join(vars_total)
    derivative_ideals = ", ".join(f"d{v}" for v in vars_total)

    return f"""ring R = 0,({var_decl}),dp;

poly qA = {qA};
poly qB = {qB};
poly qC = {qC};
poly f = qA*qB*qC;

{chr(10).join(diffs)}

ideal J = f, {derivative_ideals};
ideal sJ = std(J);
ideal Iab = std(ideal(qA, qB));
ideal Iac = std(ideal(qA, qC));
ideal Ibc = std(ideal(qB, qC));
ideal Iabc = std(ideal(qA, qB, qC));

print(\"SINGULAR:dim_singular_locus=\" + string(dim(sJ)));
print(\"SINGULAR:dim_pair_qA_qB=\" + string(dim(Iab)));
print(\"SINGULAR:dim_pair_qA_qC=\" + string(dim(Iac)));
print(\"SINGULAR:dim_pair_qB_qC=\" + string(dim(Ibc)));
print(\"SINGULAR:dim_triple_qA_qB_qC=\" + string(dim(Iabc)));
print(\"SINGULAR:degree_f=\" + string(deg(f)));
print(\"SINGULAR:term_count=\" + string(size(J)));
print(\"SINGULAR:FQ=done\");
quit;
"""


def run_command(cmd, cwd: Path, *, input_text: str | None = None, timeout: int = 120):
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def parse_kv(output: str, prefix: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for line in output.splitlines():
        if not line.startswith(prefix):
            continue
        body = line[len(prefix):].strip()
        if "=" in body:
            k, v = body.split("=", 1)
            out[k] = v
    return out


def run_singular(dim: int, signature: str, cwd: Path) -> dict:
    exe = shutil.which("Singular") or shutil.which("singular")
    if exe is None:
        return {"status": "missing", "stderr": "singular binary not found"}

    script = singular_script(dim, signature)
    try:
        proc = run_command([exe, "-q"], cwd=cwd, input_text=script)
    except subprocess.TimeoutExpired as exc:
        return {"status": "timeout", "stderr": str(exc)}

    payload = parse_kv(proc.stdout, "SINGULAR:")
    return {
        "status": "ok" if proc.returncode == 0 else "error",
        "returncode": proc.returncode,
        "payload": payload,
        "output_tail": "\n".join(proc.stdout.splitlines()[-8:]),
    }


def mac2_dlocalize_ext_script(dim: int, signature: str) -> str:
    vars_total = vars_for_dim(dim)
    dvars = tuple(f"d{v}" for v in vars_total)
    avars = vars_total[:dim]
    bvars = vars_total[dim:]
    var_decl = ",".join(vars_total + dvars)
    weyl_pairs = ", ".join(f"{v} => d{v}" for v in vars_total)
    diff_ideal = ",".join(dvars)

    return f"""needsPackage "BernsteinSato";
needsPackage "Dmodules";

W = QQ[{var_decl}, WeylAlgebra => {{{weyl_pairs}}}];
qA = {q_expr(avars, signature)};
qB = {q_expr(bvars, signature)};
qC = {q_expr(tuple(f"({a}-{b})" for a, b in zip(avars, bvars)), signature)};
f = qA*qB*qC;
Ivars = ideal({diff_ideal});

print ("MACAULAY2:fDegree=" | toString(degree f));
print ("MACAULAY2:ambientVars={2 * dim}");
print ("MACAULAY2:weylVars={4 * dim}");
print ("MACAULAY2:method=dlocalize-ext");
try (
  M = Dlocalize(Ivars, f);
  print ("MACAULAY2:dlocalize_module_class=" | toString(class M));
  E = rationalFunctionExt(M);
  print ("MACAULAY2:dlocalize_ext_table=" | toString(E));
) else (
  print ("MACAULAY2:dlocalize_ext_error=true");
);
"""


def mac2_script(
    dim: int,
    signature: str,
    *,
    attempt_derham: bool,
    derham_degree: int | None,
    derham_method: str,
) -> str:
    if attempt_derham and derham_method == "dlocalize-ext":
        return mac2_dlocalize_ext_script(dim, signature)

    vars_total = vars_for_dim(dim)
    avars = vars_total[:dim]
    bvars = vars_total[dim:]
    var_decl = ",".join(vars_total)

    derham_block = ""
    if attempt_derham:
        if derham_degree is None:
            derham_body = """
  H = deRham f;
  bettiRanks = apply(toList(0..numgens R), k -> try rank(H#k) else 0);
  print ("MACAULAY2:deRham_betti=" | toString(bettiRanks));
  print ("MACAULAY2:deRham_total_rank=" | toString(sum bettiRanks));
"""
        else:
            derham_body = f"""
  Hk = deRham({derham_degree}, f);
  print ("MACAULAY2:deRham_degree={derham_degree}");
  print ("MACAULAY2:deRham_rank=" | toString(rank Hk));
  print ("MACAULAY2:deRham_module=" | toString(Hk));
"""
        derham_block = f"""
needsPackage "Dmodules";
print ("MACAULAY2:Dmodules=loaded");
try (
{derham_body}
) else (
  print ("MACAULAY2:deRham_error=true");
);
"""

    return f"""R = QQ[{var_decl}];
qA = {q_expr(avars, signature)};
qB = {q_expr(bvars, signature)};
qC = {q_expr(tuple(f"({a}-{b})" for a, b in zip(avars, bvars)), signature)};
f = qA*qB*qC;

print ("MACAULAY2:fDegree=" | toString(degree f));
print ("MACAULAY2:vars=" | toString(numgens R));
{derham_block}
"""


def run_macaulay2(
    dim: int,
    signature: str,
    cwd: Path,
    *,
    attempt_derham: bool,
    derham_degree: int | None,
    derham_method: str,
    timeout: int,
) -> dict:
    exe = shutil.which("M2") or shutil.which("Macaulay2") or shutil.which("m2")
    if exe is None:
        return {"status": "missing", "stderr": "macaulay2 binary not found"}

    script = mac2_script(
        dim,
        signature,
        attempt_derham=attempt_derham,
        derham_degree=derham_degree,
        derham_method=derham_method,
    )
    try:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "_klein_quadric_rank32.m2"
            path.write_text(script)
            proc = run_command([exe, "--script", str(path)], cwd=cwd, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        return {
            "status": "timeout",
            "attempted_de_rham": attempt_derham,
            "de_rham_method": derham_method if attempt_derham else None,
            "de_rham_degree": derham_degree,
            "stderr": str(exc),
        }

    payload = parse_kv(proc.stdout, "MACAULAY2:")
    return {
        "status": "ok" if proc.returncode == 0 else "error",
        "returncode": proc.returncode,
        "attempted_de_rham": attempt_derham,
        "de_rham_method": derham_method if attempt_derham else None,
        "de_rham_degree": derham_degree,
        "payload": payload,
        "output_tail": "\n".join(proc.stdout.splitlines()[-8:]),
    }


def run_sage(dim: int, signature: str, fields: Tuple[int, ...], cwd: Path) -> dict:
    exe = shutil.which("sage")
    if exe is None:
        return {"status": "missing", "stderr": "sage binary not found"}

    coeffs = quadratic_coefficients(dim, signature)
    fields_literal = ", ".join(str(p) for p in fields)
    coeffs_literal = ", ".join(str(c) for c in coeffs)
    script = f"""
def legendre_symbol_local(a, p):
    a = ZZ(a) % p
    if a == 0:
        return 0
    return 1 if power_mod(a, (p - 1) // 2, p) == 1 else -1

def zero_count_even(dim, eps, p):
    m = dim // 2
    return p**(dim - 1) + eps * (p - 1) * p**(m - 1)

def complement_count(dim, coeffs, p):
    if p == 2 or dim % 2 != 0:
        return None
    det = prod([ZZ(c) for c in coeffs]) % p
    eps = legendre_symbol_local(((-1)**(dim // 2)) * det, p)
    n0 = zero_count_even(dim, eps, p)
    quotient_zero = 1 if dim == 2 else zero_count_even(dim - 2, eps, p)
    triple = n0 + (n0 - 1) * p * quotient_zero
    nonzero = p**(2 * dim) - 3 * n0 * p**dim + 3 * n0**2 - triple
    return (eps, n0, triple, nonzero)

fields = [{fields_literal}]
coeffs = [{coeffs_literal}]
print("SAGE:status=ok")
for p in fields:
    row = complement_count({dim}, coeffs, p)
    if row is None:
        print("SAGE:p_%s=skipped" % p)
    else:
        eps, n0, triple, nonzero = row
        print("SAGE:p_%s_eps=%s" % (p, eps))
        print("SAGE:p_%s_quadric_zero=%s" % (p, n0))
        print("SAGE:p_%s_isotropic_orthogonal_pairs=%s" % (p, triple))
        print("SAGE:p_%s_complement_count=%s" % (p, nonzero))
"""
    try:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "_klein_quadric_rank32.sage"
            path.write_text(script)
            proc = run_command([exe, str(path)], cwd=cwd)
    except subprocess.TimeoutExpired as exc:
        return {"status": "timeout", "stderr": str(exc)}

    payload = parse_kv(proc.stdout, "SAGE:")
    return {
        "status": "ok" if proc.returncode == 0 else "error",
        "returncode": proc.returncode,
        "payload": payload,
        "output_tail": "\n".join(proc.stdout.splitlines()[-8:]),
    }


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    limit = int(math.isqrt(n))
    d = 3
    while d <= limit:
        if n % d == 0:
            return False
        d += 2
    return True


def run_finite_field_sweep(dim: int, signature: str, fields: Tuple[int, ...]) -> dict:
    out: Dict[str, dict] = {}
    for p in fields:
        if not is_prime(p):
            out[str(p)] = {
                "status": "error",
                "message": "non-prime field order supplied",
            }
            continue

    for p in fields:
        if str(p) in out:
            continue
        out[str(p)] = finite_field_count_closed_form(dim, signature, p)

    result = {"status": "ok", "payload": out}
    symbolic = finite_field_symbolic_formula(dim, signature)
    if symbolic is not None:
        result["symbolic"] = symbolic
    return result


def parse_fields(raw: str) -> Tuple[int, ...]:
    vals = tuple(int(item.strip()) for item in raw.split(",") if item.strip())
    if not vals:
        raise argparse.ArgumentTypeError("--fields requires at least one comma-separated prime, e.g. 2,3,5")
    for p in vals:
        if p < 2:
            raise argparse.ArgumentTypeError("fields must be integers >=2")
    return vals


def main() -> None:
    parser = argparse.ArgumentParser(description="Run a de Rham-style Klein quadric audit")
    parser.add_argument("--dim", type=int, default=4)
    parser.add_argument("--signature", choices=["euclidean", "minkowski"], default="euclidean")
    parser.add_argument(
        "--run",
        nargs="*",
        choices=["singular", "macaulay2", "sage", "finite_field"],
        default=["singular", "macaulay2", "sage", "finite_field"],
        help="Which engines to run",
    )
    parser.add_argument(
        "--fields",
        type=parse_fields,
        default=(3, 5, 7),
        help="Comma-separated finite fields for point-count diagnostics, e.g. --fields 2,3,5",
    )
    parser.add_argument(
        "--out",
        default=str(ARTIFACT_DIR / "rank32_audit.json"),
    )
    parser.add_argument(
        "--m2-derham",
        action="store_true",
        help="Ask Macaulay2/Dmodules to compute de Rham cohomology of the complement.",
    )
    parser.add_argument(
        "--m2-timeout",
        type=int,
        default=120,
        help="Seconds before terminating the Macaulay2 subprocess.",
    )
    parser.add_argument(
        "--m2-degree",
        type=int,
        default=None,
        help="With --m2-derham, compute only H^k_dR via deRham(k, f).",
    )
    parser.add_argument(
        "--m2-method",
        choices=["derham", "dlocalize-ext"],
        default="derham",
        help="With --m2-derham, choose deRham f or Dlocalize plus rationalFunctionExt.",
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="For tiny fields, compare closed-form finite-field counts against brute force.",
    )
    args = parser.parse_args()
    if args.m2_degree is not None and args.m2_method != "derham":
        parser.error("--m2-degree is only valid with --m2-method derham")

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    results = {
        "dimension": args.dim,
        "signature": args.signature,
        "engines": {},
    }

    if "finite_field" in args.run:
        results["engines"]["finite_field"] = run_finite_field_sweep(args.dim, args.signature, args.fields)
        if args.self_check and args.dim <= 4:
            checks = {}
            for p in args.fields:
                if is_prime(p) and p <= 5:
                    brute = finite_field_count_bruteforce(args.dim, args.signature, p)
                    closed = results["engines"]["finite_field"]["payload"][str(p)].get("nonzero")
                    checks[str(p)] = {
                        "bruteforce_nonzero": brute,
                        "closed_form_nonzero": closed,
                        "matches": brute == closed,
                    }
            results["engines"]["finite_field"]["self_check"] = checks
    if "singular" in args.run:
        results["engines"]["singular"] = run_singular(args.dim, args.signature, ROOT)
    if "macaulay2" in args.run:
        results["engines"]["macaulay2"] = run_macaulay2(
            args.dim,
            args.signature,
            ROOT,
            attempt_derham=args.m2_derham,
            derham_degree=args.m2_degree,
            derham_method=args.m2_method,
            timeout=args.m2_timeout,
        )
    if "sage" in args.run:
        results["engines"]["sage"] = run_sage(args.dim, args.signature, args.fields, ROOT)

    results["summary"] = {
        "completed": [k for k, v in results["engines"].items() if v.get("status") in {"ok", "error", "timeout", "missing"}],
        "available": [k for k, v in results["engines"].items() if v.get("status") == "ok"],
        "missing": [k for k, v in results["engines"].items() if v.get("status") == "missing"],
        "rank32_status": "not_assumed",
    }

    out.write_text(json.dumps(results, indent=2))
    print(out)
    print(json.dumps(results["summary"]))


if __name__ == "__main__":
    main()
