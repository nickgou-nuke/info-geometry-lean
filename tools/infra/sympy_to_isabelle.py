#!/usr/bin/env python3
"""SymPy to Isabelle/HOL automated translator and Sledgehammer runner."""

import argparse
import subprocess
import os
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr

def sympy_to_isabelle(expr) -> str:
    """Recursively translates a SymPy expression to Isabelle/HOL syntax."""
    if isinstance(expr, sp.Symbol):
        return str(expr)
    elif isinstance(expr, sp.Integer):
        return str(expr)
    elif isinstance(expr, sp.Rational):
        p, q = expr.p, expr.q
        return f"({p} / {q})"
    elif isinstance(expr, sp.Float):
        return str(expr)
    
    if expr == sp.pi:
        return "pi"
    elif expr == sp.E:
        return "exp 1"
    
    func = expr.func
    args = expr.args
    
    if func == sp.Add:
        return "(" + " + ".join(sympy_to_isabelle(arg) for arg in args) + ")"
    elif func == sp.Mul:
        return "(" + " * ".join(sympy_to_isabelle(arg) for arg in args) + ")"
    elif func == sp.Pow:
        base, exp = args
        return f"({sympy_to_isabelle(base)} ^ {sympy_to_isabelle(exp)})"
    elif func == sp.Equality:
        lhs, rhs = args
        return f"{sympy_to_isabelle(lhs)} = {sympy_to_isabelle(rhs)}"
    elif func == sp.sin:
        return f"(sin {sympy_to_isabelle(args[0])})"
    elif func == sp.cos:
        return f"(cos {sympy_to_isabelle(args[0])})"
    elif func == sp.exp:
        return f"(exp {sympy_to_isabelle(args[0])})"
    elif func == sp.log:
        return f"(ln {sympy_to_isabelle(args[0])})"
    elif func == sp.sinh:
        return f"(sinh {sympy_to_isabelle(args[0])})"
    elif func == sp.cosh:
        return f"(cosh {sympy_to_isabelle(args[0])})"
    else:
        name = func.__name__
        arg_str = " ".join(sympy_to_isabelle(arg) for arg in args)
        return f"({name} {arg_str})"

def main():
    parser = argparse.ArgumentParser(
        description="Translate SymPy relation to Isabelle/HOL and run verification."
    )
    parser.add_argument(
        "--expr",
        required=True,
        help="SymPy expression string, e.g. 'Eq(sin(x - t) + cos(x + t), y)'"
    )
    parser.add_argument(
        "--vars",
        nargs="+",
        default=[],
        help="Variables with type real, e.g. x t"
    )
    parser.add_argument(
        "--theory",
        default="SymPy_Import",
        help="Name of the generated theory"
    )
    args = parser.parse_args()

    # Parse SymPy expression
    local_dict = {v: sp.Symbol(v) for v in args.vars}
    try:
        expr = parse_expr(args.expr, local_dict=local_dict)
    except Exception as e:
        print(f"Error parsing SymPy expression: {e}")
        return

    # Translate to Isabelle term
    try:
        isabelle_term = sympy_to_isabelle(expr)
    except Exception as e:
        print(f"Error translating SymPy expression to Isabelle: {e}")
        return

    print(f"Parsed SymPy Expression: {expr}")
    print(f"Translated Isabelle Term: {isabelle_term}")

    # Generate the theory file content
    vars_decl = " and ".join(f"{v} :: real" for v in args.vars)
    theory_content = f"""theory {args.theory}
  imports Complex_Main
begin

lemma sympy_identity:
  fixes {vars_decl}
  shows "{isabelle_term}"
  apply -
  sorry

end
"""

    thy_path = f"isabelle/InfoGeometry/Canonical/{args.theory}.thy"
    root_path = "isabelle/ROOT"

    print(f"Writing theory file to {thy_path}...")
    with open(thy_path, "w", encoding="utf-8") as f:
        f.write(theory_content)

    # Read original ROOT
    with open(root_path, "r", encoding="utf-8") as f:
        original_root = f.read()

    # Register in ROOT temporarily
    theory_entry = f'    "InfoGeometry/Canonical/{args.theory}"'
    if theory_entry not in original_root:
        lines = original_root.splitlines()
        insert_idx = len(lines)
        for idx, line in enumerate(lines):
            if "InfoGeometry/Canonical/" in line:
                insert_idx = idx + 1
        lines.insert(insert_idx, theory_entry)
        new_root = "\n".join(lines) + "\n"
        with open(root_path, "w", encoding="utf-8") as f:
            f.write(new_root)
        root_modified = True
    else:
        root_modified = False

    try:
        print("Invoking Isabelle Mirabelle with Sledgehammer...")
        if os.path.exists("mirabelle"):
            subprocess.run(["rm", "-rf", "mirabelle"])
            
        cmd = [
            "/home/goutev/Isabelle2025-2/bin/isabelle", "mirabelle",
            "-o", "quick_and_dirty",
            "-A", "sledgehammer",
            "-d", "isabelle",
            "-T", f"InfoGeometry.{args.theory}",
            "InfoGeometry"
        ]
        res = subprocess.run(cmd, capture_output=True, text=True)
        
        # Read mirabelle.log
        log_path = "mirabelle/mirabelle.log"
        if os.path.exists(log_path):
            print("\n=== Mirabelle Sledgehammer Results ===")
            with open(log_path, "r", encoding="utf-8") as f:
                log_lines = f.readlines()
            found_proof = False
            for line in log_lines:
                if f"InfoGeometry.{args.theory}" in line and "Try this:" in line:
                    print(line.strip())
                    found_proof = True
            if not found_proof:
                print("Sledgehammer was unable to find a proof or it timed out.")
        else:
            print("Error: mirabelle.log was not generated.")
            print(f"Stdout:\n{res.stdout}")
            print(f"Stderr:\n{res.stderr}")

    finally:
        # Clean up
        print("\nCleaning up temporary theory files...")
        if os.path.exists(thy_path):
            os.remove(thy_path)
        if root_modified:
            with open(root_path, "w", encoding="utf-8") as f:
                f.write(original_root)
        print("Cleanup complete.")

if __name__ == "__main__":
    main()
