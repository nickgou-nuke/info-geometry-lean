import InfoGeometry.Physics.BogoliubovWeylChemicalPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Physics.ColorCARStandardModel

/-!
# Bogoliubov Weyl gauge → SU(3) color → BdG parafermion weld

The finite theorem-honest content is:

* the Bogoliubov frame determines the q/affine deformation parameter through
  `frameWeylQ = qRapidity frameWeylLogClock`;
* the affine superbracket is undeformed on even-even/color sectors, hence
  reduces to the ordinary Lie commutator for the Gell-Mann generators;
* concrete SU(3) commutator identities from `GellMannSU3` are reused;
* four BdG/Majorana generators are packaged as a finite parafermion spinor lane;
* the SU(3)-on-parafermion and braiding maps below are finite scalar actions
  on the BdG lane.
-/

noncomputable section

namespace InfoGeometry.Physics.BogoliubovSU3ParafermionWeld

open BogoliubovWeylChemicalPotential
open SupergradedCuntzBdG
open GellMannSU3
open ColorCARStandardModel
open InfoGeometry.Topology.AlgebraicCuntzQuotient

abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev ParafermionStage4 := CuntzAlg ℂ (Fin 4)

/-- Four-component BdG/Majorana `+` spinor lane. -/
def bdgParafermionPlus4 (i : Fin 4) : ParafermionStage4 :=
  bdgMajoranaPlus i

/-- Four-component BdG/Majorana `-` spinor lane. -/
def bdgParafermionMinus4 (i : Fin 4) : ParafermionStage4 :=
  bdgMajoranaMinus i

/-- The Bogoliubov frame supplies exactly the affine q-parameter. -/
theorem frame_affine_parameter (F : BogoliubovInertialFrame) :
    frameWeylQ F = qRapidity (frameWeylLogClock F) :=
  frameWeylQ_eq_qRapidity_logClock F

/-- Unruh temperature is the acceleration divided by `2π`, equivalently
`2πT_U=a` in the units used by `SupergradedCuntzBdG`. -/
theorem unruh_temperature_clock (a : ℝ) :
    (2 * Real.pi) * unruhTemperature a = a :=
  two_pi_mul_unruhTemperature a

/-- In the even/color sector, the Bogoliubov q-deformed affine bracket is just
the ordinary Lie commutator.  Thus the vacuum deformation does not deform the
SU(3) color Lie algebra itself. -/
theorem frame_affine_even_even_lie (F : BogoliubovInertialFrame) (X Y : M3C) :
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even X Y =
      lieBracket X Y := by
  exact affineSuperBracket_even_left (frameWeylQ F) Z2Parity.even X Y

/-- The same statement with the q-parameter displayed as an exponential
log-clock. -/
theorem frame_logclock_affine_even_even_lie (F : BogoliubovInertialFrame) (X Y : M3C) :
    affineSuperBracket (qRapidity (frameWeylLogClock F))
      Z2Parity.even Z2Parity.even X Y = lieBracket X Y := by
  exact affineSuperBracket_even_left (qRapidity (frameWeylLogClock F)) Z2Parity.even X Y

/-- Concrete SU(3) color identity: the affine even-even bracket recovers the
Gell-Mann commutator `[λ₁,λ₂]=2iλ₃`. -/
theorem frame_affine_gl1_gl2 (F : BogoliubovInertialFrame) :
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl2 =
      (2 * Complex.I) • gl3 := by
  rw [frame_affine_even_even_lie]
  simpa [lieBracket] using gl1_comm_gl2

/-- Concrete SU(3) color identity: `[λ₁,λ₃]=-2iλ₂`. -/
theorem frame_affine_gl1_gl3 (F : BogoliubovInertialFrame) :
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl3 =
      (-2 * Complex.I) • gl2 := by
  rw [frame_affine_even_even_lie]
  simpa [lieBracket] using gl1_comm_gl3

/-- The Gell-Mann diagonal Cartan pair remains commuting in every Bogoliubov
frame. -/
theorem frame_affine_gl3_gl8_commutes (F : BogoliubovInertialFrame) :
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl3 gl8 = 0 := by
  rw [frame_affine_even_even_lie]
  simp [lieBracket, gl3_comm_gl8]

/-- The q-braiding phase assigned by a Bogoliubov frame. -/
def frameBraidingPhase (F : BogoliubovInertialFrame) : ℂ :=
  qRapidity (frameWeylLogClock F)

/-- The braiding phase is the same scalar as the frame Weyl gauge. -/
theorem frameBraidingPhase_eq_frameWeylQ (F : BogoliubovInertialFrame) :
    frameBraidingPhase F = frameWeylQ F := by
  rw [frame_affine_parameter]
  rfl

/-- Chemical potential shifts the parafermion braiding phase by the exponential
of `β δμ Q`. -/
theorem frameBraidingPhase_mu_shift (F : BogoliubovInertialFrame) (δμ : ℝ) :
    frameBraidingPhase { F with μ := F.μ + δμ } =
      qRapidity (F.β * δμ * F.Q) * frameBraidingPhase F := by
  unfold frameBraidingPhase
  rw [frameWeylLogClock_mu_shift]
  rw [qRapidity_add]
  ring

/-- Basic BdG/Majorana square identity for the four-component parafermion `+` lane. -/
theorem bdgParafermionPlus4_sq (i : Fin 4) :
    bdgParafermionPlus4 i * bdgParafermionPlus4 i = hamiltonianAtom i := by
  simpa [bdgParafermionPlus4] using bdgMajoranaPlus_sq_eq_hamiltonianAtom i

/-- Finite scalar action of an SU(3) color matrix on the BdG parafermion spinor lane.
Acts by scalar multiplication of the matrix trace. -/
def su3ColorAction (X : M3C) (lane : Fin 4 → ParafermionStage4) : Fin 4 → ParafermionStage4 :=
  fun i => X.trace • lane i

/-- Finite braiding map acting on the BdG parafermion spinor lane
by scalar multiplication. -/
def parafermionBraid (z : ℂ) (lane : Fin 4 → ParafermionStage4) : Fin 4 → ParafermionStage4 :=
  fun i => z • lane i

/-- The braiding action with phase 1 is the identity. -/
theorem parafermionBraid_one (lane : Fin 4 → ParafermionStage4) :
    parafermionBraid 1 lane = lane := by
  ext i
  simp [parafermionBraid]

/-- Synthesis: Unruh/Bogoliubov q-clock controls the braiding phase; the even
vacuum-deformed bracket recovers the SU(3) Gell-Mann commutator; the
parafermion/color action data is explicitly defined. -/
theorem bogoliubov_su3_parafermion_synthesis
    (F : BogoliubovInertialFrame) (δμ a : ℝ) :
    (2 * Real.pi) * unruhTemperature a = a ∧
    frameWeylQ F = qRapidity (frameWeylLogClock F) ∧
    frameBraidingPhase F = frameWeylQ F ∧
    frameBraidingPhase { F with μ := F.μ + δμ } =
      qRapidity (F.β * δμ * F.Q) * frameBraidingPhase F ∧
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl2 =
      (2 * Complex.I) • gl3 ∧
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl3 =
      (-2 * Complex.I) • gl2 ∧
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl3 gl8 = 0 ∧
    (∀ i : Fin 4, bdgParafermionPlus4 i * bdgParafermionPlus4 i = hamiltonianAtom i) ∧
    (∀ lane, parafermionBraid 1 lane = lane) := by
  constructor
  · exact unruh_temperature_clock a
  constructor
  · exact frame_affine_parameter F
  constructor
  · exact frameBraidingPhase_eq_frameWeylQ F
  constructor
  · exact frameBraidingPhase_mu_shift F δμ
  constructor
  · exact frame_affine_gl1_gl2 F
  constructor
  · exact frame_affine_gl1_gl3 F
  constructor
  · exact frame_affine_gl3_gl8_commutes F
  constructor
  · exact bdgParafermionPlus4_sq
  · exact parafermionBraid_one

end InfoGeometry.Physics.BogoliubovSU3ParafermionWeld

end noncomputable section
