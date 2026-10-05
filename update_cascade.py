import re

with open('lean/InfoGeometry/Meta/ArchetypeDischarge.lean', 'r') as f:
    content = f.read()

new_cascade = """/-- Execute a tactic block with an isolated heartbeat budget. -/
def runWithHeartbeats (mvarId : MVarId) (maxHB : Nat) (tac : Syntax) : TermElabM (List MVarId) := do
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := maxHB * 1000 }) do
    Tactic.run mvarId (evalTactic tac)

/-- Hardened cascade that isolates solver stages and handles resource limits cleanly. -/
def autoDischargeCascade (mvarId : MVarId) : TermElabM Unit := do
  let solvers : List (String × Syntax) ← [
    ("rfl",      (← `(tactic| intros; rfl)).raw),
    ("decide",   (← `(tactic| intros; decide)).raw),
    ("simp_all", (← `(tactic| intros; simp_all)).raw),
    ("omega",    (← `(tactic| intros; omega)).raw)
  ].mapM fun (n, t) => pure (n, t)

  for (name, tac) in solvers do
    try
      let remaining ← runWithHeartbeats mvarId 20 tac
      if remaining.isEmpty then
        return ()
    catch _ =>
      continue

  throwError "Automated discharge cascade exhausted portfolio [rfl, decide, simp_all, omega] without closing goal."
"""

content = re.sub(r'/-- Execute a tactic block.*?without closing goal."\n', new_cascade, content, flags=re.DOTALL)

with open('lean/InfoGeometry/Meta/ArchetypeDischarge.lean', 'w') as f:
    f.write(content)
