import InfoGeometry.FormalAgentLib.QmsAgentOS

namespace FormalAgentLib

@[simp] theorem scratch_eq_of_pending_length_eq {s : WorkflowSessionState}
    (h : WorkflowSessionRun QmsAgentOSAst.compactionQmsAgentOS.sessionState s) (hs : s.pending.length = 4) :
    s = QmsAgentOSAst.compactionQmsAgentOS.sessionState := by
  generalize hinit : QmsAgentOSAst.compactionQmsAgentOS.sessionState = init at h
  induction h with
  | refl =>
      sorry
  | step hstep hrun ih =>
      sorry

end FormalAgentLib
