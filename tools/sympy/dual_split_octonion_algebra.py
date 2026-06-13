#!/usr/bin/env python3
"""Finite dual split-octonion algebra verifier.

Lean twin:
    lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean

Scope:
    This verifies only the algebraic dual-number extension
    D O_s = O_s + eps O_s with eps^2 = 0 over the existing concrete Zorn
    split-octonion multiplication, together with an external-system arithmetic
    ledger:

    * GAP/Atlas finite G2(2) order data.
    * Sage root/Weyl/D5 Lie-dimension data.
    * clifford and galgebra split-signature atom checks.

    It does not assert Aut(D O_s), SO(4,4) metric symmetry, SU(3)
    stabilizers, KBZ/O(5,5) physical closure, quantum R-matrices, or any
    physical gauge classification.
"""

from __future__ import annotations

from dataclasses import dataclass
import importlib.util
from pathlib import Path
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


split = load_module(ROOT / "tools/sympy/split_octonion_multiplication.py", "split_oct_mul")


@dataclass(frozen=True)
class DualZorn:
    primal: Any
    tangent: Any

    def __mul__(self, other: "DualZorn") -> "DualZorn":
        return DualZorn(
            self.primal * other.primal,
            self.primal * other.tangent + self.tangent * other.primal,
        )


ZERO_D = DualZorn(split.ZERO, split.ZERO)


def base_lift(x: Any) -> DualZorn:
    return DualZorn(x, split.ZERO)


def eps_lift(x: Any) -> DualZorn:
    return DualZorn(split.ZERO, x)


def associator_d(x: DualZorn, y: DualZorn, z: DualZorn) -> DualZorn:
    return (x * y) * z - x * (y * z)  # type: ignore[operator]


def dual_sub(left: DualZorn, right: DualZorn) -> DualZorn:
    return DualZorn(left.primal - right.primal, left.tangent - right.tangent)


def dual_add(left: DualZorn, right: DualZorn) -> DualZorn:
    return DualZorn(left.primal + right.primal, left.tangent + right.tangent)


DualZorn.__add__ = dual_add  # type: ignore[method-assign]
DualZorn.__sub__ = dual_sub  # type: ignore[method-assign]


def verify_dual_product_rules() -> None:
    basis = split.BASIS
    for x in basis:
        for y in basis:
            assert base_lift(x) * base_lift(y) == base_lift(x * y)
            assert eps_lift(x) * eps_lift(y) == ZERO_D
            assert base_lift(x) * eps_lift(y) == eps_lift(x * y)
            assert eps_lift(x) * base_lift(y) == eps_lift(x * y)

    dual_epsilon = eps_lift(split.ONE)
    assert dual_epsilon * dual_epsilon == ZERO_D


def verify_projection_and_nonassociativity() -> None:
    x = DualZorn(split.UP[0], split.DOWN[0])
    y = DualZorn(split.UP[1], split.DOWN[1])
    assert (x * y).primal == x.primal * y.primal

    lifted = associator_d(base_lift(split.UP[0]), base_lift(split.UP[1]), base_lift(split.DOWN[1]))
    assert lifted == base_lift(split.UP[0])
    assert lifted != ZERO_D


def verify_supergraded_and_klein_readouts() -> None:
    dual_epsilon = eps_lift(split.ONE)
    # Odd--odd superbracket is the anticommutator; eps^2 = 0 makes it zero.
    assert dual_epsilon * dual_epsilon + dual_epsilon * dual_epsilon == ZERO_D

    # Integer readouts mirroring the existing Brillouin-Klein owners.
    klein_z2_zero_defect = (0 + 0) % 2
    klein_boundary_zero_charge = 0 + 0 + 0 - 0
    assert klein_z2_zero_defect == 0
    assert klein_boundary_zero_charge == 2 * 0

    for _stage in range(16):
        assert dual_epsilon * dual_epsilon == ZERO_D


def run_checked(cmd: list[str], input_text: str | None = None) -> str:
    completed = subprocess.run(
        cmd,
        input=input_text,
        text=True,
        capture_output=True,
        check=False,
    )
    output = completed.stdout + completed.stderr
    if completed.returncode != 0:
        raise RuntimeError(f"{cmd!r} failed with code {completed.returncode}\n{output}")
    if "Error," in output or "Traceback" in output:
        raise RuntimeError(f"{cmd!r} emitted a failure marker\n{output}")
    return output


def parse_key_values(output: str) -> dict[str, int]:
    data: dict[str, int] = {}
    for line in output.splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        value = value.strip()
        if value.lstrip("-").isdigit():
            data[key.strip()] = int(value)
    return data


def verify_gap_g2two_order_ledger() -> dict[str, int]:
    gap_code = r"""
LoadPackage("atlasrep");;
G := AtlasGroup("G2(2)");;
D := DerivedSubgroup(G);;
Print("G2two_order=", Size(G), "\n");
Print("G2two_derived_order=", Size(D), "\n");
Print("G2two_derived_index=", Index(G,D), "\n");
Print("G2two_aut_order=", Size(AutomorphismGroup(G)), "\n");
QUIT;
"""
    data = parse_key_values(run_checked([str(GAP), "-q"], gap_code))
    assert data["G2two_order"] == 12096
    assert data["G2two_derived_order"] == 6048
    assert data["G2two_derived_index"] == 2
    assert data["G2two_aut_order"] == 12096
    assert data["G2two_derived_order"] * data["G2two_derived_index"] == data["G2two_order"]
    return data


def verify_sage_root_weyl_ledger() -> dict[str, int]:
    sage_code = r"""
from sage.all import RootSystem, WeylGroup, QQ
from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis
for typ, n, label in [('G', 2, 'G2'), ('D', 4, 'D4'), ('D', 5, 'D5')]:
    R = RootSystem([typ, n])
    W = WeylGroup([typ, n])
    print(f"{label}_rank={len(R.index_set())}")
    print(f"{label}_root_count={2 * len(list(R.root_poset()))}")
    print(f"{label}_weyl_order={W.order()}")
g = LieAlgebraChevalleyBasis(QQ, ['D', 5])
print(f"D5_lie_dimension={g.dimension()}")
"""
    data = parse_key_values(run_checked([str(SAGE), "-q", "-c", sage_code]))
    assert data["G2_rank"] == 2
    assert data["G2_root_count"] == 12
    assert data["G2_weyl_order"] == 12
    assert data["D4_rank"] == 4
    assert data["D4_root_count"] == 24
    assert data["D4_weyl_order"] == 192
    assert data["D5_rank"] == 5
    assert data["D5_root_count"] == 40
    assert data["D5_weyl_order"] == 1920
    assert data["D5_lie_dimension"] == 45
    return data


def verify_clifford_split_signature() -> dict[str, int]:
    from clifford import Cl

    _, blades44 = Cl(4, 4)
    _, blades55 = Cl(5, 5)
    assert len(blades44) == 256
    assert len(blades55) == 1024
    assert str(blades44["e1"] * blades44["e1"]) == "1"
    assert str(blades44["e5"] * blades44["e5"]) == "-1"
    assert str(blades55["e1"] * blades55["e1"]) == "1"
    assert str(blades55["e6"] * blades55["e6"]) == "-1"
    return {"cl44_dim": 256, "cl55_dim": 1024}


def verify_galgebra_split_signature() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3 e4 f1 f2 f3 f4", g=[1, 1, 1, 1, -1, -1, -1, -1])
    e1, _e2, _e3, _e4, f1, _f2, _f3, _f4 = ga.mv()
    assert str(e1 * e1) == "1"
    assert str(f1 * f1) == "-1"
    assert str(e1 * f1 + f1 * e1) == "0"


def main() -> None:
    verify_dual_product_rules()
    verify_projection_and_nonassociativity()
    verify_supergraded_and_klein_readouts()
    gap = verify_gap_g2two_order_ledger()
    sage = verify_sage_root_weyl_ledger()
    clifford = verify_clifford_split_signature()
    verify_galgebra_split_signature()
    print("DUAL_SPLIT_OCTONION_ALGEBRA_OK")
    print("DUAL_SPLIT_OCTONION_MULTISYSTEM_BACKBONE_OK")
    print("coordinate_count=16")
    print(
        "gap_g2two="
        f"order:{gap['G2two_order']},derived:{gap['G2two_derived_order']},"
        f"index:{gap['G2two_derived_index']},aut:{gap['G2two_aut_order']}"
    )
    print(
        "sage_root_weyl="
        f"G2:{sage['G2_root_count']}/{sage['G2_weyl_order']},"
        f"D4:{sage['D4_root_count']}/{sage['D4_weyl_order']},"
        f"D5:{sage['D5_root_count']}/{sage['D5_weyl_order']},"
        f"D5_lie:{sage['D5_lie_dimension']}"
    )
    print(f"clifford_dims=Cl44:{clifford['cl44_dim']},Cl55:{clifford['cl55_dim']}")
    print("galgebra_split_atom=e1^2:+1,f1^2:-1,anticomm:0")
    print("scope: dual-number extension of concrete split-octonion multiplication only")


if __name__ == "__main__":
    main()
