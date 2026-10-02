#!/usr/bin/env python3
import os, sys, subprocess, pathlib, re, json
from fractions import Fraction
import random

sys.path.insert(0, "/home/goutev/info-geometry-lean")
from tools.build_lock import acquire_build_lock

results = {}

print("=== Step 1: Token Cleanliness Scan ===")
candidate_file = pathlib.Path("/home/goutev/info-geometry-lean/.agents/sandbox_bott/BottPeriodicityReconciliation.lean")
content = candidate_file.read_text()
banned_patterns = [
    r"\\bsorry\\b",
    r"\\badmit\\b",
    r"\\boops\\b",
    r"\\btrustMe\\b",
    r"\\baxiom\\b",
    r"\\bunsafe\\b",
    r"\\bpartial\\b",
    r"\\bFalse\\b",
    r"\\bexfalso\\b",
    r"\\bcontradiction\\b"
]
tokens_clean = True
for pat in banned_patterns:
    m = re.findall(pat, content)
    if m:
        print(f"FAILED token scan: {pat} found {len(m)} times")
        tokens_clean = False
if tokens_clean:
    print("PASS: Zero cheating or escape tokens found.")
results["token_scan"] = tokens_clean

print("\\n=== Step 2: Docstring Truthfulness Audit ===")
rhetoric_patterns = [
    r"thermodynamic",
    r"hodge-dirac",
    r"cpt",
    r"spacetime",
    r"quantum field",
    r"infinite inductive colimit",
    r"sphere bundle",
    r"topological k-theory",
    r"homotopy group",
    r"pi_k"
]
docstring_clean = True
for pat in rhetoric_patterns:
    m = re.findall(pat, content, re.IGNORECASE)
    if m:
        print(f"FAILED docstring scan: rhetoric pattern {pat} found")
        docstring_clean = False
if docstring_clean:
    print("PASS: Docstrings are strictly dry mathematical statements.")
results["docstring_audit"] = docstring_clean

print("\\n=== Step 3: Mathematical Correctness (Exact Rational Verification) ===")
I2 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
s1 = [[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]
s3 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(-1)]]
eps = [[Fraction(0), Fraction(1)], [Fraction(-1), Fraction(0)]]

def mmul(A, B):
    return [
        [A[0][0]*B[0][0] + A[0][1]*B[1][0], A[0][0]*B[0][1] + A[0][1]*B[1][1]],
        [A[1][0]*B[0][0] + A[1][1]*B[1][0], A[1][0]*B[0][1] + A[1][1]*B[1][1]]
    ]

def madd(A, B):
    return [
        [A[0][0] + B[0][0], A[0][1] + B[0][1]],
        [A[1][0] + B[1][0], A[1][1] + B[1][1]]
    ]

def smul(c, A):
    return [
        [c * A[0][0], c * A[0][1]],
        [c * A[1][0], c * A[1][1]]
    ]

# Check relations:
# 1. s1 * s1 == I2
r1 = mmul(s1, s1) == I2
# 2. eps * eps == -I2
neg_I2 = smul(Fraction(-1), I2)
r2 = mmul(eps, eps) == neg_I2
# 3. s1 * eps + eps * s1 == 0
zero_mat = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(0)]]
r3 = madd(mmul(s1, eps), mmul(eps, s1)) == zero_mat

relations_pass = r1 and r2 and r3
print(f"Relations: s1^2=I2: {r1}, eps^2=-I2: {r2}, anticommutator=0: {r3}")

# Spanning tests over 10,000 random rational matrices
spanning_pass = True
for _ in range(10000):
    A = [
        [Fraction(random.randint(-1000, 1000), random.randint(1, 100)), Fraction(random.randint(-1000, 1000), random.randint(1, 100))],
        [Fraction(random.randint(-1000, 1000), random.randint(1, 100)), Fraction(random.randint(-1000, 1000), random.randint(1, 100))]
    ]
    a = (A[0][0] + A[1][1]) / 2
    b = (A[0][1] + A[1][0]) / 2
    c = (A[0][1] - A[1][0]) / 2
    d = (A[0][0] - A[1][1]) / 2
    rec = madd(madd(smul(a, I2), smul(b, s1)), madd(smul(c, eps), smul(d, s3)))
    if rec != A:
        spanning_pass = False
        break

print(f"Spanning reconstruction 10,000 trials: {PASS if spanning_pass else FAIL}")
results["math_relations"] = relations_pass
results["math_spanning"] = spanning_pass

print("\\n=== Step 4: Compiling under Repository Build Lock ===")
owner = f"reviewer1_verify:{os.getpid()}"
print(f"Acquiring build lock for {owner}...")
with acquire_build_lock(None, owner, block=True):
    print("Lock acquired.")
    cmd1 = ["lake", "env", "lean", str(candidate_file)]
    print("Running:", " ".join(cmd1))
    res1 = subprocess.run(cmd1, capture_output=True, text=True, cwd="/home/goutev/info-geometry-lean")
    print(f"Exit code: {res1.returncode}")
    print(f"STDOUT: {res1.stdout}")
    print(f"STDERR: {res1.stderr}")
    results["candidate_compile_exit"] = res1.returncode
    results["candidate_compile_stdout"] = res1.stdout
    results["candidate_compile_stderr"] = res1.stderr

    axiom_file = pathlib.Path("/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_reviewer_bott_1/AxiomCheck.lean")
    cmd2 = ["lake", "env", "lean", str(axiom_file)]
    print("\\nRunning axiom check:", " ".join(cmd2))
    res2 = subprocess.run(cmd2, capture_output=True, text=True, cwd="/home/goutev/info-geometry-lean")
    print(f"Axiom exit code: {res2.returncode}")
    print(f"Axiom STDOUT:\\n{res2.stdout}")
    print(f"Axiom STDERR:\\n{res2.stderr}")
    results["axiom_compile_exit"] = res2.returncode
    results["axiom_compile_stdout"] = res2.stdout
    results["axiom_compile_stderr"] = res2.stderr

out_json = pathlib.Path("/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_reviewer_bott_1/verification_results.json")
out_json.write_text(json.dumps(results, indent=2))
print("\\nVerification suite finished.")
