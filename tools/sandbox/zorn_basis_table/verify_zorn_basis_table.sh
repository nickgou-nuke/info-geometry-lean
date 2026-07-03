#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 generate_zorn_basis_table.py >/dev/null
(cd ../../.. && lake env lean lean_sandbox/ZornBasisTableSandbox.lean)
python3 zorn_basis_table_sympy.py
/home/goutev/miniforge3/envs/sage/bin/sage zorn_basis_table.sage.py
/home/goutev/miniforge3/envs/sage/bin/gap -q zorn_basis_table.g
/home/goutev/miniforge3/envs/sage/bin/Singular -q zorn_basis_table.sing
M2 --script zorn_basis_table.m2
/home/goutev/.opam/rocq-9.2/bin/coqc coq/ZornBasisTable.v
/usr/local/bin/isabelle build -D isabelle
printf 'ZORN_BASIS_TABLE_MULTIENGINE_OK entries=64 engines=lean,sympy,sage,gap,singular,macaulay2,coq,isabelle\n'
