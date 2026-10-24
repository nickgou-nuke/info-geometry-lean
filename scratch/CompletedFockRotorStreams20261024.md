# Completed Fock Stream5/6 realization

Source-only G-A candidate on the EXISTING RealFockCompletion and native
fockCompletedContractionCLM m i (D), fockCompletedCreationCLM m i (C).
No new carrier, operator definition, state or flow. No builds/live edits.

## Grounding and exact delta

Read native RealFockCompletedSameModeCAR fully: square-zero, sameMode_CAR,
and both adjoint identities are already proved there. Reuse them, deriving
DCD=D and CDC=C, then construct the EXISTING Stream5 IsDualSeedPair with
proved fields. carrierSupport=1 is the full identity on this completion.
DC and CD are idempotent and genuinely IsSelfAdjoint because native star
on completed real Hilbert CLMs is the actual adjoint. The coordinate vacancy
DC is not asserted to be the full many-mode vacuum projection.

Read FiniteFockCLMReflexivePair and FiniteFockRotorShear as finite patterns.
Read DeBruijnRotorAlternationCycle definitions/expansion and existing realRotor.
The completed rotor is the SAME realRotor applied to D,C, and acts on every
completed vector as cos(t)x+sin(t)(Dx-Cx). Its all-later-stage readback equals
the existing finite realRotor at the shifted mode, through fockStageToCompletion.
The moving plus pole has the native quadratic action, is idempotent on the
circle, and is self-adjoint (for all real c,s even before circle normalization).
An additional finite-stage moving-pole equality makes the trajectory transport
explicit rather than just forwarding an abstract interface theorem.

Stream6: read StreamSixOrbitComparison.hyperbolicPlus_eq_stream6 and
ComplementHyperbolicOrbit.hyperbolicPlus_expansion. Their actual conjugation
has action u² D(Cx)-v² C(Dx)-uv(Dx-Cx) on every completed vector, without a
hyperbola premise. The proof goes through the native cross-owner equality;
no new hyperbolic action. Without u²-v²=1 the reversed factor is not asserted
to be inverse. No hyperbolic unitarity or self-adjoint moving hyperbolic pole.

## Source hashes read

RealFockCompletedSameModeCAR:
23250a402fda59621b1e821b3402d7c7fa2c39b69e65d372761aa1f3f8593a35
FiniteFockRotorShear:
bb0ddd68306bbce1dcce2f7afd4b5c6b89204ab252b0863c2035764d797d90eb
StreamSixOrbitComparison:
68d2ee3e15a8cb27284c7e21f9a11fbde1b9ce6047a38a812bbacf494f2ae367

Mathlib Analysis/InnerProductSpace/Adjoint.lean star_eq_adjoint identifies
native CLM star with the Hilbert adjoint. No metric assumption is introduced;
activate only the same accepted named local metric instances as native owners.

Bounded search of relevant Clifford rotor/stream and completed-action owners
found the finite bridge and completed CAR/adjoint ingredients, not this completed
consumer in that search. No repo-wide absence claim. No extra derivative proof,
analytic KMS claim, complexification, many-mode classification or aggregate packet.
Candidate uncompiled; requires separate independent AA and locked serial QA.
