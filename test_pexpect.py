import pexpect
import sys

child = pexpect.spawn("lake env lean --server", cwd="/home/goutev/repos/info-geometry-lean", encoding="utf-8")

# This is an LSP server, not an interactive shell!
