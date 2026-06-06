import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";

const registerLegacyTool = (pi: ExtensionAPI, tool: unknown) => (pi.registerTool as any)(tool);
const AICLAW_ARANGO_URL = process.env.AICLAW_ARANGO_URL || "http://127.0.0.1:8540";
const AICLAW_ARANGO_DB = process.env.AICLAW_ARANGO_DB || "aiclaw_auto_rag";
const AICLAW_ARANGO_USER = process.env.AICLAW_ARANGO_USER || "root";
const AICLAW_ARANGO_PASSWORD = process.env.AICLAW_ARANGO_PASSWORD || "password";
const AICLAW_KNOWLEDGE_BASE = process.env.AICLAW_KNOWLEDGE_BASE || "knowledge_base.json";

function assertSeparateBrain() {
  if (process.env.AICLAW_ALLOW_SHARED_ARANGO === "1") return;
  if (AICLAW_ARANGO_URL.includes(":8530") || AICLAW_ARANGO_DB === "infogeometry") {
    throw new Error(
      "Refusing to commit aiClaw proof memory into the repo DAG brain. Set " +
        "AICLAW_ARANGO_URL/AICLAW_ARANGO_DB to the isolated proof-memory brain."
    );
  }
}

/**
 * Verify & Store Conscious Knowledge
 *
 * A Pi extension that permanently saves verified mathematical truths
 * (both Lean 4 formal logic and SymPy algebraic witnesses) to the
 * ArangoDB knowledge graph. This closes the epistemic loop:
 *
 * 1. Query unconscious literature (query_graph_rag)
 * 2. Ground in algebra (verify_sympy_witness)
 * 3. Formalize in logic (verify_lean_proof)
 * 4. Persist as conscious truth (this tool)
 *
 * The tool stores the verified theorem with its algebraic witness,
 * embedding, and links back to the source literature that inspired it.
 */

export default function (pi: ExtensionAPI) {
  registerLegacyTool(pi, {
    name: "commit_conscious_knowledge",
    label: "Verify & Store Conscious Knowledge",
    description:
      "USE THIS TOOL ONLY AFTER both verification steps pass successfully: " +
      "the Lean 4 proof compiles AND the SymPy algebraic witness computes. " +
      "It saves the unified mathematical truth to the knowledge database " +
      "with links back to the source literature that inspired it.",
    promptSnippet: "Commit verified multimodal knowledge to the persistent knowledge graph",
    promptGuidelines: [
      "Only use commit_conscious_knowledge AFTER verify_lean_proof succeeds AND verify_sympy_witness succeeds.",
      "Include the inspiring node titles from query_graph_rag results.",
    ],
    parameters: Type.Object({
      theoremName: Type.String({
        description: "The name of the newly proven theorem or system architecture.",
      }),
      formalLogic: Type.String({
        description: "The exact, compiler-verified Lean 4 code or formal specification.",
      }),
      sympyWitnessCode: Type.String({
        description: "The Python SymPy script used to ground the proof.",
      }),
      algebraicOutput: Type.String({
        description:
          "The resulting closed-form mathematical output computed by SymPy.",
      }),
      inspiringNodes: Type.Array(Type.String(), {
        description:
          "An array of the original knowledge-base node titles that inspired this discovery.",
      }),
      tags: Type.Optional(
        Type.Array(Type.String(), {
          description: "Optional tags for categorizing this knowledge.",
        })
      ),
    }),
    required: [
      "theoremName",
      "formalLogic",
      "sympyWitnessCode",
      "algebraicOutput",
      "inspiringNodes",
    ],

    async execute(
      _toolCallId: string,
      params: {
        theoremName: string;
        formalLogic: string;
        sympyWitnessCode: string;
        algebraicOutput: string;
        inspiringNodes: string[];
        tags?: string[];
      },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      onUpdate?.({
        content: [
          {
            type: "text" as const,
            text: `Ascending '${params.theoremName}' into Conscious Knowledge Layer...`,
          },
        ],
      });

      // Build the embedding prompt for combined logic + algebra
      const vectorPrompt = `Theorem: ${params.theoremName}\nLogic: ${params.formalLogic.substring(0, 500)}\nAlgebra: ${params.algebraicOutput}`;

      let vector: number[] | null = null;
      try {
        const { pipeline } = await import("@xenova/transformers");
        const embedder = await pipeline(
          "feature-extraction",
          "Xenova/all-MiniLM-L6-v2"
        );
        const output = await embedder(vectorPrompt, {
          pooling: "mean",
          normalize: true,
        });
        vector = Array.from(output.data as Float32Array);
      } catch {
        // Embedding generation is optional for persistence
      }

      const now = new Date().toISOString();
      const entry = {
        title: params.theoremName,
        content: params.formalLogic,
        sympy_code: params.sympyWitnessCode,
        algebraic_state: params.algebraicOutput,
        embedding: vector,
        source: "Pi_Agent_Multimodal_Derived",
        status: "verified_conscious_truth",
        inspiring_nodes: params.inspiringNodes,
        tags: params.tags || ["verified", "formal", "algebraic"],
        created_at: now,
        updated_at: now,
      };

      // Try ArangoDB first
      try {
        assertSeparateBrain();
        const { Database } = await import("arangojs");
        const rootDb = new Database({ url: AICLAW_ARANGO_URL });
        rootDb.useBasicAuth(AICLAW_ARANGO_USER, AICLAW_ARANGO_PASSWORD);
        const db = rootDb.database(AICLAW_ARANGO_DB);

        const nodesColl = db.collection("literature_nodes");
        const edgesColl = db.collection("citation_edges");
        const safeKey = params.theoremName.replace(/[^a-zA-Z0-9]/g, "_");

        const nodeExists = await nodesColl.documentExists(safeKey);
        if (nodeExists) {
          await nodesColl.update(safeKey, {
            ...entry,
            _key: safeKey,
          });
        } else {
          await nodesColl.save({
            ...entry,
            _key: safeKey,
          });
        }

        // Create edge links back to inspiring nodes
        for (const inspiration of params.inspiringNodes) {
          const inspKey = inspiration.replace(/[^a-zA-Z0-9]/g, "_");
          const edge = {
            _from: `literature_nodes/${safeKey}`,
            _to: `literature_nodes/${inspKey}`,
            type: "derived_from_unconscious_literature",
            created_at: now,
          };
          try {
            await edgesColl.save(edge);
          } catch {
            // Edge may already exist - ignore
          }
        }

        return {
          content: [
            {
              type: "text" as const,
              text:
                `[SYSTEM] Multimodal commitment complete for '${params.theoremName}'.\n` +
                `Logic and Algebra are locked in sync in isolated aiClaw ArangoDB.\n` +
                `Inspiring nodes: ${params.inspiringNodes.join(", ")}`,
            },
          ],
        };
      } catch (dbError: any) {
        // ArangoDB not available - save to local JSON file
        try {
          const fs = await import("fs");
          const path = await import("path");
          const knowledgePath = path.default.resolve(process.cwd(), AICLAW_KNOWLEDGE_BASE);

          let knowledgeBase: any[] = [];
          if (fs.existsSync(knowledgePath)) {
            const raw = fs.readFileSync(knowledgePath, "utf-8");
            try {
              knowledgeBase = JSON.parse(raw);
              if (!Array.isArray(knowledgeBase)) {
                knowledgeBase = [knowledgeBase];
              }
            } catch {
              knowledgeBase = [];
            }
          }

          // Check if theorem already exists
          const existingIdx = knowledgeBase.findIndex(
            (k: any) => k.title === params.theoremName
          );
          if (existingIdx >= 0) {
            knowledgeBase[existingIdx] = {
              ...knowledgeBase[existingIdx],
              ...entry,
              version: (knowledgeBase[existingIdx].version || 1) + 1,
              updated_at: now,
            };
          } else {
            knowledgeBase.push({
              ...entry,
              version: 1,
              id: `conscious_${params.theoremName.replace(/[^a-zA-Z0-9]/g, "_")}`,
            });
          }

          fs.writeFileSync(knowledgePath, JSON.stringify(knowledgeBase, null, 2));

          return {
            content: [
              {
                type: "text" as const,
                text:
                  `[SYSTEM] Multimodal commitment complete for '${params.theoremName}'.\n` +
                  `Saved to local knowledge_base.json (ArangoDB unavailable).\n` +
                  `Inspiring nodes: ${params.inspiringNodes.join(", ")}\n` +
                  `File: ${knowledgePath}`,
              },
            ],
          };
        } catch (fsError: any) {
          // Last resort: return the knowledge as text
          return {
            content: [
              {
                type: "text" as const,
                text:
                  `[SYSTEM] Knowledge committed (in-memory only - no database available).\n` +
                  `Theorem: ${params.theoremName}\n` +
                  `Algebraic Result: ${params.algebraicOutput}\n` +
                  `Inspiring Nodes: ${params.inspiringNodes.join(", ")}\n\n` +
                  `To persist: install ArangoDB or ensure write access to the working directory.\n` +
                  `Error: ${fsError.message}`,
              },
            ],
          };
        }
      }
    },
  });
}
