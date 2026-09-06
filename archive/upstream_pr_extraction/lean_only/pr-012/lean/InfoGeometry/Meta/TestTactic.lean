import InfoGeometry.Meta.DvorakTactics

namespace InfoGeometry.Meta

theorem test_aeply : True → True := by
  intro h
  aeply h
  exact h

end InfoGeometry.Meta
