import InfoGeometry.Canonical.InverseKernelAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

/-!
# EP And Group Inverse

This file isolates the EP corridor of the certified inverse-kernel package.
Here the Moore-Penrose range and domain projectors agree, the dilation gap
collapses, and the Moore-Penrose inverse itself satisfies the Drazin laws with
index `1`.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InverseKernel

variable (IK : InverseKernel E)

/-- EP condition: the Moore-Penrose range and domain projectors agree. -/
def IsEP : Prop :=
  IK.mpRangeProjector = IK.metricProjector

/-- The EP condition is exactly the commutation of `A` and its Moore-Penrose inverse. -/
theorem isEP_iff_comm :
    IK.IsEP ↔ IK.A * IK.A_MP = IK.A_MP * IK.A := by
  unfold InverseKernel.IsEP InverseKernel.mpRangeProjector InverseKernel.metricProjector
  rfl

/-- Under EP, the Moore-Penrose range and domain projectors coincide. -/
theorem mpRangeProjector_eq_metricProjector_of_isEP
    (hEP : IK.IsEP) :
    IK.mpRangeProjector = IK.metricProjector :=
  hEP

/-- Under EP, the left/right mismatch operators coincide. -/
theorem rightProjectorMismatch_eq_projectorMismatch_of_isEP
    (hEP : IK.IsEP) :
    IK.rightProjectorMismatch = IK.projectorMismatch := by
  unfold InverseKernel.rightProjectorMismatch InverseKernel.projectorMismatch
  rw [hEP]

/-- Under EP, the dilation gap vanishes. -/
theorem dilationGap_eq_zero_of_isEP
    (hEP : IK.IsEP) :
    IK.dilationGap = 0 := by
  unfold InverseKernel.dilationGap
  rw [hEP]
  simp

/--
Concrete Moore-Penrose commutation is a constructive route to gap collapse;
callers need not first package the definitional EP predicate.
-/
theorem dilationGap_eq_zero_of_comm
    (hComm : IK.A * IK.A_MP = IK.A_MP * IK.A) :
    IK.dilationGap = 0 :=
  IK.dilationGap_eq_zero_of_isEP (IK.isEP_iff_comm.2 hComm)

/--
Concrete Moore-Penrose commutation is also a direct constructive route to
left/right mismatch agreement; callers with the operator equality no longer
need to package a separate `IK.IsEP` hypothesis.
-/
theorem rightProjectorMismatch_eq_projectorMismatch_of_comm
    (hComm : IK.A * IK.A_MP = IK.A_MP * IK.A) :
    IK.rightProjectorMismatch = IK.projectorMismatch :=
  IK.rightProjectorMismatch_eq_projectorMismatch_of_isEP (IK.isEP_iff_comm.2 hComm)

/-- Vanishing dilation gap forces the EP condition. -/
theorem isEP_of_dilationGap_eq_zero
    (hGap : IK.dilationGap = 0) :
    IK.IsEP := by
  have hSmul :
      ((2 : ℝ)⁻¹) • (IK.mpRangeProjector - IK.metricProjector) = 0 := by
    simpa [InverseKernel.dilationGap] using hGap
  have hDiff : IK.mpRangeProjector - IK.metricProjector = 0 := by
    exact (smul_eq_zero.mp hSmul).resolve_left (by norm_num)
  exact sub_eq_zero.mp hDiff

/--
Vanishing dilation gap is a smaller constructive route to projector agreement:
the EP packet is recovered internally from the gap collapse.
-/
theorem mpRangeProjector_eq_metricProjector_of_dilationGap_eq_zero
    (hGap : IK.dilationGap = 0) :
    IK.mpRangeProjector = IK.metricProjector :=
  IK.mpRangeProjector_eq_metricProjector_of_isEP (IK.isEP_of_dilationGap_eq_zero hGap)

/--
Vanishing dilation gap is also a constructive route back to concrete
Moore-Penrose commutation, so callers with the collapsed gap need not supply a
separate commutation equality.
-/
theorem comm_of_dilationGap_eq_zero
    (hGap : IK.dilationGap = 0) :
    IK.A * IK.A_MP = IK.A_MP * IK.A :=
  IK.isEP_iff_comm.1 (IK.isEP_of_dilationGap_eq_zero hGap)

/-- Concrete Moore-Penrose commutation is equivalent to vanishing dilation gap. -/
theorem comm_iff_dilationGap_eq_zero :
    IK.A * IK.A_MP = IK.A_MP * IK.A ↔ IK.dilationGap = 0 := by
  constructor
  · exact IK.dilationGap_eq_zero_of_comm
  · exact IK.comm_of_dilationGap_eq_zero

/--
Vanishing dilation gap is a smaller constructive route to mismatch agreement:
the EP packet is recovered internally from the gap collapse.
-/
theorem rightProjectorMismatch_eq_projectorMismatch_of_dilationGap_eq_zero
    (hGap : IK.dilationGap = 0) :
    IK.rightProjectorMismatch = IK.projectorMismatch :=
  IK.rightProjectorMismatch_eq_projectorMismatch_of_isEP (IK.isEP_of_dilationGap_eq_zero hGap)

/-- EP is equivalent to vanishing dilation gap. -/
theorem isEP_iff_dilationGap_eq_zero :
    IK.IsEP ↔ IK.dilationGap = 0 := by
  constructor
  · exact IK.dilationGap_eq_zero_of_isEP
  · exact IK.isEP_of_dilationGap_eq_zero

/-- Under EP, the right and left anomaly conventions agree. -/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_isEP
    (hEP : IK.IsEP) :
    IK.rightChiralAnomaly = IK.chiralAnomaly :=
  IK.rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement hEP

/--
Vanishing dilation gap is a smaller constructive route to the anomaly-agreement
surface: the EP packet is recovered internally from the gap collapse.
-/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_dilationGap_eq_zero
    (hGap : IK.dilationGap = 0) :
    IK.rightChiralAnomaly = IK.chiralAnomaly :=
  IK.rightChiralAnomaly_eq_chiralAnomaly_of_isEP (IK.isEP_of_dilationGap_eq_zero hGap)

/--
Concrete Moore-Penrose commutation is a constructive route to anomaly-agreement:
callers with the operator equality no longer need to package either `IK.IsEP`
or the intermediate dilation-gap collapse.
-/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_comm
    (hComm : IK.A * IK.A_MP = IK.A_MP * IK.A) :
    IK.rightChiralAnomaly = IK.chiralAnomaly :=
  IK.rightChiralAnomaly_eq_chiralAnomaly_of_isEP (IK.isEP_iff_comm.2 hComm)

/--
In the EP corridor, the Moore-Penrose inverse satisfies the Drazin laws with
index `1`, so it is a group inverse witness.
-/
theorem moorePenrose_isDrazinInverse_one_of_isEP
    (hMP : IsMoorePenroseInverse IK.A IK.A_MP)
    (hEP : IK.IsEP) :
    IsDrazinInverse IK.A IK.A_MP 1 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simpa [InverseKernel.IsEP, InverseKernel.mpRangeProjector, InverseKernel.metricProjector] using hEP
  · exact hMP.bab_eq_b
  · have hComm : IK.A * IK.A_MP = IK.A_MP * IK.A := by
      simpa [InverseKernel.IsEP, InverseKernel.mpRangeProjector, InverseKernel.metricProjector] using hEP
    calc
      IK.A ^ (1 + 1) * IK.A_MP = IK.A * IK.A * IK.A_MP := by
        simp [pow_two, mul_assoc]
      _ = IK.A * (IK.A * IK.A_MP) := by
        simp [mul_assoc]
      _ = IK.A * (IK.A_MP * IK.A) := by
        rw [hComm]
      _ = IK.A * IK.A_MP * IK.A := by
        simp [mul_assoc]
      _ = IK.A := hMP.aba_eq_a
      _ = IK.A ^ 1 := by simp

/--
Vanishing dilation gap is a smaller constructive route to the group-inverse
Drazin witness: the EP packet is recovered internally from the gap collapse.
-/
theorem moorePenrose_isDrazinInverse_one_of_dilationGap_eq_zero
    (hMP : IsMoorePenroseInverse IK.A IK.A_MP)
    (hGap : IK.dilationGap = 0) :
    IsDrazinInverse IK.A IK.A_MP 1 :=
  IK.moorePenrose_isDrazinInverse_one_of_isEP hMP (IK.isEP_of_dilationGap_eq_zero hGap)

/--
Direct commutation route to the group-inverse Drazin witness.  This avoids
requiring callers to package the definitional EP predicate when they already
own the concrete Moore-Penrose commutation equality.
-/
theorem moorePenrose_isDrazinInverse_one_of_comm
    (hMP : IsMoorePenroseInverse IK.A IK.A_MP)
    (hComm : IK.A * IK.A_MP = IK.A_MP * IK.A) :
    IsDrazinInverse IK.A IK.A_MP 1 :=
  IK.moorePenrose_isDrazinInverse_one_of_isEP hMP (IK.isEP_iff_comm.2 hComm)

end InverseKernel

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Certified EP condition. -/
def IsEP : Prop :=
  CIK.toInverseKernel'.IsEP

/-- Certified EP is exactly commutation of `A` and `A_MP`. -/
theorem isEP_iff_comm :
    CIK.IsEP ↔ CIK.A * CIK.A_MP = CIK.A_MP * CIK.A := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.isEP_iff_comm

/-- Under certified EP, the Moore-Penrose range and domain projectors agree. -/
theorem mpRangeProjector_eq_metricProjector_of_isEP
    (hEP : CIK.IsEP) :
    CIK.mpRangeProjector = CIK.metricProjector :=
  hEP

/-- Under certified EP, the left/right mismatch operators agree. -/
theorem rightProjectorMismatch_eq_projectorMismatch_of_isEP
    (hEP : CIK.IsEP) :
    CIK.rightProjectorMismatch = CIK.projectorMismatch := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.rightProjectorMismatch,
    CertifiedInverseKernel.projectorMismatch, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightProjectorMismatch_eq_projectorMismatch_of_isEP hEP

/-- Under certified EP, the dilation gap vanishes. -/
theorem dilationGap_eq_zero_of_isEP
    (hEP : CIK.IsEP) :
    CIK.dilationGap = 0 := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.dilationGap,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.dilationGap_eq_zero_of_isEP hEP

/--
Certified concrete Moore-Penrose commutation is a constructive route to gap
collapse, avoiding a separately supplied `CIK.IsEP` packet.
-/
theorem dilationGap_eq_zero_of_comm
    (hComm : CIK.A * CIK.A_MP = CIK.A_MP * CIK.A) :
    CIK.dilationGap = 0 := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.dilationGap_eq_zero_of_comm hComm

/--
Certified concrete Moore-Penrose commutation is a direct constructive route to
left/right mismatch agreement, avoiding a separately supplied `CIK.IsEP` packet.
-/
theorem rightProjectorMismatch_eq_projectorMismatch_of_comm
    (hComm : CIK.A * CIK.A_MP = CIK.A_MP * CIK.A) :
    CIK.rightProjectorMismatch = CIK.projectorMismatch := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.rightProjectorMismatch,
    CertifiedInverseKernel.projectorMismatch, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightProjectorMismatch_eq_projectorMismatch_of_comm hComm

/-- Certified vanishing dilation gap forces EP. -/
theorem isEP_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    CIK.IsEP := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.dilationGap,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.isEP_of_dilationGap_eq_zero hGap

/--
Certified gap-collapse route to projector agreement: callers that already own
`dilationGap = 0` do not need to provide a separate `CIK.IsEP` packet.
-/
theorem mpRangeProjector_eq_metricProjector_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    CIK.mpRangeProjector = CIK.metricProjector :=
  CIK.mpRangeProjector_eq_metricProjector_of_isEP (CIK.isEP_of_dilationGap_eq_zero hGap)

/--
Certified gap-collapse route back to concrete Moore-Penrose commutation: callers
that already own `dilationGap = 0` do not need to supply a separate commutation
equality.
-/
theorem comm_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    CIK.A * CIK.A_MP = CIK.A_MP * CIK.A :=
  CIK.isEP_iff_comm.1 (CIK.isEP_of_dilationGap_eq_zero hGap)

/-- Certified concrete commutation is equivalent to vanishing dilation gap. -/
theorem comm_iff_dilationGap_eq_zero :
    CIK.A * CIK.A_MP = CIK.A_MP * CIK.A ↔ CIK.dilationGap = 0 := by
  constructor
  · exact CIK.dilationGap_eq_zero_of_comm
  · exact CIK.comm_of_dilationGap_eq_zero

/--
Certified gap-collapse route to mismatch agreement: callers that already own
`dilationGap = 0` do not need to provide a separate `CIK.IsEP` packet.
-/
theorem rightProjectorMismatch_eq_projectorMismatch_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    CIK.rightProjectorMismatch = CIK.projectorMismatch :=
  CIK.rightProjectorMismatch_eq_projectorMismatch_of_isEP (CIK.isEP_of_dilationGap_eq_zero hGap)

/-- Certified EP is equivalent to vanishing dilation gap. -/
theorem isEP_iff_dilationGap_eq_zero :
    CIK.IsEP ↔ CIK.dilationGap = 0 := by
  constructor
  · exact CIK.dilationGap_eq_zero_of_isEP
  · exact CIK.isEP_of_dilationGap_eq_zero

/-- Under certified EP, the right and left anomaly conventions agree. -/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_isEP
    (hEP : CIK.IsEP) :
    CIK.rightChiralAnomaly = CIK.chiralAnomaly := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.rightChiralAnomaly,
    CertifiedInverseKernel.chiralAnomaly, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightChiralAnomaly_eq_chiralAnomaly_of_isEP hEP

/--
Certified gap-collapse route to anomaly agreement: callers that already own
`dilationGap = 0` do not need to provide a separate `CIK.IsEP` packet.
-/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    CIK.rightChiralAnomaly = CIK.chiralAnomaly := by
  simpa [CertifiedInverseKernel.dilationGap, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightChiralAnomaly_eq_chiralAnomaly_of_dilationGap_eq_zero hGap

/--
Certified concrete Moore-Penrose commutation is a constructive route to anomaly
agreement, avoiding both a separately supplied `CIK.IsEP` packet and a separately
supplied dilation-gap collapse witness.
-/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_comm
    (hComm : CIK.A * CIK.A_MP = CIK.A_MP * CIK.A) :
    CIK.rightChiralAnomaly = CIK.chiralAnomaly := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.rightChiralAnomaly,
    CertifiedInverseKernel.chiralAnomaly, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightChiralAnomaly_eq_chiralAnomaly_of_comm hComm

/-- Under certified EP, the spectral/dilation commutator vanishes trivially. -/
theorem spectralProjector_commutator_dilationGap_eq_zero_of_isEP
    (hEP : CIK.IsEP) :
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector = 0 := by
  have hGap : CIK.dilationGap = 0 := CIK.dilationGap_eq_zero_of_isEP hEP
  simp [hGap]

/--
Certified commutation route to the spectral/dilation commutator collapse.  This
removes the explicit EP-packet hypothesis from callers that already own the
concrete Moore-Penrose commutation equality.
-/
theorem spectralProjector_commutator_dilationGap_eq_zero_of_comm
    (hComm : CIK.A * CIK.A_MP = CIK.A_MP * CIK.A) :
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector = 0 := by
  have hGap : CIK.dilationGap = 0 := CIK.dilationGap_eq_zero_of_comm hComm
  simp [hGap]

/--
Certified gap-collapse route to the spectral/dilation commutator collapse:
callers that already own `dilationGap = 0` do not need to provide a separate
`CIK.IsEP` packet.
-/
theorem spectralProjector_commutator_dilationGap_eq_zero_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector = 0 := by
  simp [hGap]

/--
In the certified EP corridor, the Moore-Penrose inverse is a Drazin inverse of
index `1`.
-/
theorem moorePenrose_isDrazinInverse_one_of_isEP
    (hEP : CIK.IsEP) :
    IsDrazinInverse CIK.A CIK.A_MP 1 := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.moorePenrose_isDrazinInverse_one_of_isEP CIK.hMoorePenrose hEP

/--
Certified gap-collapse route to the group-inverse Drazin witness.  This keeps
legacy EP-based theorem names, while callers that already own `dilationGap = 0`
do not need to provide a separate `CIK.IsEP` packet.
-/
theorem moorePenrose_isDrazinInverse_one_of_dilationGap_eq_zero
    (hGap : CIK.dilationGap = 0) :
    IsDrazinInverse CIK.A CIK.A_MP 1 := by
  simpa [CertifiedInverseKernel.dilationGap, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.moorePenrose_isDrazinInverse_one_of_dilationGap_eq_zero
      CIK.hMoorePenrose hGap

/--
Certified direct commutation route to the group-inverse Drazin witness.  This
keeps the legacy EP route available while allowing callers with the concrete
operator commutation equality to avoid constructing a separate `CIK.IsEP`
packet.
-/
theorem moorePenrose_isDrazinInverse_one_of_comm
    (hComm : CIK.A * CIK.A_MP = CIK.A_MP * CIK.A) :
    IsDrazinInverse CIK.A CIK.A_MP 1 := by
  simpa [CertifiedInverseKernel.IsEP, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.moorePenrose_isDrazinInverse_one_of_comm
      CIK.hMoorePenrose hComm

end CertifiedInverseKernel

end InfoGeometry.Canonical
