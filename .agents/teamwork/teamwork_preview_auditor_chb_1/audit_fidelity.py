#!/usr/bin/env python3
import sys

live_path = "lean/DAG/ConnesHodgeBridge.lean"
sandbox_path = ".agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean"

with open(live_path) as f:
    live_content = f.read()

with open(sandbox_path) as f:
    sandbox_content = f.read()

# Check structure ConnesCorrespondence
print("=== Checking structure ConnesCorrespondence ===")
structure_header = "structure ConnesCorrespondence (α : Type) [BEq α] [Hashable α] where"
assert structure_header in live_content, "Structure header missing from live!"
assert structure_header in sandbox_content, "Structure header missing from sandbox!"

fields = [
    "complex : TwoComplex α",
    "edgeCount : Nat",
    "harmonicDim : Nat",
    "cocycleDimUpperBound : Nat",
    "eulerChar : Int",
    "deriving Repr"
]

for fld in fields:
    assert fld in live_content, f"Field '{fld}' missing from live!"
    assert fld in sandbox_content, f"Field '{fld}' missing from sandbox!"
    print(f"  Field preserved: {fld}")

# Check def fromTwoComplex signature
print("\n=== Checking def fromTwoComplex ===")
def_from_two_complex = "def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :"
assert def_from_two_complex in live_content, "fromTwoComplex missing from live!"
assert def_from_two_complex in sandbox_content, "fromTwoComplex missing from sandbox!"
print(f"  Signature preserved: {def_from_two_complex}")

# Check def fromHodgeData signature
print("\n=== Checking def fromHodgeData ===")
def_from_hodge_data = "def fromHodgeData {α : Type} [BEq α] [Hashable α]\n    (hd : DAG.CocycleBridge.HodgeCocycleData α) : ConnesCorrespondence α :="
assert def_from_hodge_data in live_content, "fromHodgeData missing from live!"
assert def_from_hodge_data in sandbox_content, "fromHodgeData missing from sandbox!"
print(f"  Signature preserved: {def_from_hodge_data.replace(chr(10), ' ')}")

# Check namespaces
print("\n=== Checking namespace and open statements ===")
assert "open DAG" in sandbox_content
assert "namespace DAG.ConnesHodgeBridge" in sandbox_content
assert "end DAG.ConnesHodgeBridge" in sandbox_content
print("  Namespaces correctly preserved.")

print("\n=== Declaration Fidelity: 100% PRESERVED ===")
