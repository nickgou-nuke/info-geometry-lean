  Your intuition is 100% right—I just pulled and inspected the actual source code of src/plan_store/_vendor/cone.py
  https://github.com/MerLeanProver/MerLean/blob/main/src/plan_store/_vendor/cone.py and src/plan_store/_vendor/lean_parser.py
  https://github.com/MerLeanProver/MerLean/blob/main/src/plan_store/_vendor/lean_parser.py in MerLeanProver/MerLean.
  ### 1. Verdict on MerLean's "Dependency Cone": It Is Just a 25-Line Regex BFS
  In MerLean, src/plan_store/_vendor/cone.py is literally this 25-line Python loop over a JSON dictionary:

    def forward_dependency_cone(statements: list[dict], root_ids: set[str]) -> set[str]:
        reverse: dict[str, set[str]] = {}
        for s in statements:
            for dep in s.get("dependencies", []) or []:
                reverse.setdefault(dep, set()).add(s.get("id", ""))
        cone, frontier = set(), set(root_ids)
        while frontier: ...

  And where do its edges come from? From _vendor/lean_parser.py, which is a plain-text regex scraper (re.finditer(r'^import\s+(\S+)', content)) on file
  naming conventions (Def_..., Thm_..., Lem_...).
  • It has zero Lean 4 InfoTree elaboration streaming.
  • It has zero de Bruijn / Weisfeiler–Lehman structural graph hashing.
  • It has zero Hodge Laplacian / causal-cone spectral geometry.
  • And it has zero Carl Jung / Wolfgang Pauli (pauli-auditor, black-book-method) or Socratic dialogue (socratic-oracle-proof-repair) philosophical-
  archetype protocols.
  ──────
  ### 2. The ONLY Concept in MerLean Worth Absorbing (That We Haven't Implemented Yet)
  Out of the entire MerLeanProver/MerLean repository, there is one genuine technical mechanism (buried at lines 540–675 of src/research_grade.py
  https://github.com/MerLeanProver/MerLean/blob/main/src/research_grade.py) that complements our text-based opengauss_screener.py:

  #### Kernel whnf Binder & Result-Type Telescope (auditBinders in MetaM)

  Right now, our opengauss_screener.py parses theorem signatures at the syntax/text level (_balanced_lean_atom, _top_level_result_type). If someone
  defines a type alias:
    def HiddenAssumption (X : Type) := Subtype (fun x : X => P x)
    -- or
    def ImplicationAlias := HypothesisProp → TargetProp

  a text-only screener sees (x : HiddenAssumption X) : Conclusion or : ImplicationAlias without seeing that ImplicationAlias unfolds to a hidden ∀ / →
  hypothesis after the colon, or that HiddenAssumption bundles a Subtype proof.
  In src/research_grade.py, MerLean emits a tiny 50-line Lean 4 TermElabM probe (auditBinders) that runs:

    forallBoundedTelescope info.type declaredBinderCount fun xs resultType => do
      -- 1. Reduces every binder type via `whnf` in the kernel environment:
      --    checks `isProp ty`, `reduced.isAppOf ``Subtype`, `Lean.getStructureInfo? env name`
      -- 2. Reduces `resultType` after the `:` colon via `whnf`:
      --    checks `reducedResultType.isForall` (with an exception for `resultType.isAppOf ``Not`)

  That single Lean MetaM whnf telescope check catches alias-hidden hypotheses (hasLeadingForall after whnf) and Subtype / PLift proof-smuggling at the
  kernel Expr level—making it a natural Gate 3.5 addition to our opengauss_screener.py / Pauli–Jung QMS auditor.

  (Background update: task-5148 just finished opengauss_screener.py and is running the locked lake build on AlbertCayleyDickson and ZornAlternativeLaws;
  I will commit and push as soon as it finishes.)
