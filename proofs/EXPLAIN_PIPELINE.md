  I have launched the exact streaming mode extraction pipeline following the rigorous ArangoDB architecture rules!

  It's currently running the  DumpLeanGraph.lean  syntax dump across all files in streaming JSONL mode, and will then run  ExtractGraph.lean  and join the syntax and environment in the bridge (
  join_syntax_env.py ) before importing it into the  LeanUniverseGraph  collection via  import_arango.py .

  Once the pipeline completes, the  LeanUniverseGraph  in ArangoDB will reflect the absolute truth of the compiled theory AST and dependencies without relying on text heuristics! I will notify you as
 ┃     cd /home/goutev/auto/proofs
 ┃     source /home/goutev/.config/arango/env.sh
 ┃
 ┃   ### 2. Layer 1: Syntax Extraction (Streaming Mode)
 ┃
 ┃   We use a streaming JSONL dump to parse the syntax AST of all  .lean  files. This avoids memory exhaustion and ensures every file's syntactic structure is captured exactly as the Lean parser sees
 ┃   it.
 ┃
 ┃     lake env lean --run tools/lean_graph/DumpLeanGraph.lean *.lean > /tmp/syntax.jsonl
 ┃
 ┃   ### 3. Layer 2: Environment Extraction
 ┃
 ┃   We execute a metaprogramming script that queries the Lean  Environment  and  ConstantInfo . This uses  getUsedConstants  over the elaborated proofs to extract the exact dependency graph.
 ┃
 ┃     # This outputs the dependencies to proof_graph.json
 ┃     lake env lean tools/ExtractGraph.lean
 ┃
 ┃   ### 4. Graph Analysis & SCC Enforcement
 ┃
 ┃   To ensure there are no cyclic logic traps and to enforce Strongly Connected Component (SCC) rules on the graph, run the graph analysis suite:
 ┃
 ┃     # Canonicalize the graph and check for cycles or topological inconsistencies
 ┃     python3 tools/lean_graph/canonicalize_proof_graph.py proof_graph.json
 ┃     python3 tools/lean_graph/find_scc.py proof_graph.json
 ┃
 ┃   ### 5. Bridge: Syntax-Environment Join
 ┃
 ┃   We bridge the syntax ranges with the elaborated environment dependencies, matching the records and embedding the full AST into a unified JSONL stream.
 ┃
 ┃     python3 tools/lean_graph/join_syntax_env.py \
 ┃       --syntax-jsonl /tmp/syntax.jsonl \
 ┃       --env-json proof_graph.json \
 ┃       --include-syntax-tree \
 ┃       > /tmp/bridge.jsonl
 ┃
 ┃   ### 6. ArangoDB Ingestion
 ┃
 ┃   Finally, we push the unified streaming records into the  LeanUniverseGraph  collections ( lean_decls ,  syntax_nodes ,  references ,  ast_child ,  has_syntax ) in ArangoDB.
 ┃
 ┃     python3 tools/lean_graph/import_arango.py /tmp/bridge.jsonl --execute
 ┃
 ┃   ## Schema Enforced
 ┃
 ┃   By running this exact pipeline, we guarantee that the  agent_brain  and  LeanUniverseGraph  are populated strictly with validated, type-checked theorems.
 ┃
 ┃   •  lean_decls : Only contains elaborated Lean declarations.
 ┃   •  references : Only contains mathematically verified dependency edges, excluding heuristic regex false-positives.
