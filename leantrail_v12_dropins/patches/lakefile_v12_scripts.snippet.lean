-- Add near existing LeanTrail scripts in lakefile.lean
script leantrailVacuityIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/vacuity_ingest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSurgeryPlan (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/surgery_plan.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSurgeryApply (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/surgery_apply.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait
