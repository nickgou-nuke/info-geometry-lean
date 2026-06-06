import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";

/**
 * ArangoDB Graph-RAG Oracle
 *
 * A Pi extension that performs semantic retrieval over a local ArangoDB
 * knowledge graph. Uses vector search combined with graph traversal to
 * pull deeply linked technical literature, citation contexts, and
 * structural solutions from the knowledge mesh.
 *
 * Two modes:
 * 1. Full ArangoDB mode: requires arangojs and a running ArangoDB instance
 * 2. File-based fallback: uses a local JSON file as a simple vector store
 *
 * The file-based fallback allows testing the toolchain without ArangoDB.
 */

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "query_graph_rag",
    label: "ArangoDB Graph-RAG Oracle",
    description:
      "USE THIS TOOL to retrieve deeply linked technical literature, citation contexts, " +
      "and structural solutions from the local knowledge mesh. Pass a high-density text query. " +
      "Returns semantically similar documents and their graph connections.",
    promptSnippet: "Retrieve deeply linked technical literature and structural solutions",
    promptGuidelines: [
      "Use query_graph_rag when you need background literature, architectural references, or prior solutions from the knowledge base.",
    ],
    parameters: Type.Object({
      queryText: Type.String({
        description:
          "The conceptual or technical question explaining the system bug or structural goal.",
      }),
      maxResults: Type.Optional(
        Type.Number({
          description: "Maximum number of results to return (default: 5).",
        })
      ),
    }),
    required: ["queryText"],

    async execute(
      _toolCallId: string,
      params: { queryText: string; maxResults?: number },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      const maxResults = params.maxResults || 5;

      // Try ArangoDB first
      try {
        const { Database } = await import("arangojs");
        const db = new Database({ url: "http://localhost:8529" });

        // Test connection
        await db.exists();
        db.useDatabase("aiclaw_rag");
        db.useBasicAuth("root", "password");

        onUpdate?.({
          content: [{ type: "text" as const, text: "Connected to ArangoDB. Generating query embedding..." }],
        });

        // Try to load the ONNX embedder for real embeddings
        let queryEmbedding: number[] | null = null;
        try {
          const { pipeline } = await import("@xenova/transformers");
          const embedder = await pipeline("feature-extraction", "Xenova/all-MiniLM-L6-v2");
          const output = await embedder(params.queryText, {
            pooling: "mean",
            normalize: true,
          });
          queryEmbedding = Array.from(output.data as Float32Array);
        } catch {
          // Fallback: use a mock embedding (not great but allows testing the pipeline)
          // In production, install @xenova/transformers
          onUpdate?.({
            content: [
              {
                type: "text" as const,
                text: "ONNX embedder not available, using simplified search...",
              },
            ],
          });
        }

        // Try AQL query with vector search
        if (queryEmbedding) {
          const aqlQuery = `
            FOR doc IN literature_search_view
              SEARCH V_COSINE(doc.embedding, @embedding) >= 0.75
              SORT V_COSINE(doc.embedding, @embedding) DESC
              LIMIT @maxResults

              FOR v, e IN 1..2 OUTBOUND doc._id citation_edges
                RETURN {
                  primary_title: doc.title,
                  primary_text: SUBSTRING(doc.content, 0, 2000),
                  similarity: V_COSINE(doc.embedding, @embedding),
                  linked_metadata: v.content,
                  relationship: e.type
                }
          `;

          try {
            const cursor = await db.query(aqlQuery, {
              embedding: queryEmbedding,
              maxResults,
            });
            const results = await cursor.all();

            if (results.length === 0) {
              return {
                content: [
                  {
                    type: "text" as const,
                    text: "[ARANGO RAG]: No deeply correlated graph contexts found for this query.",
                  },
                ],
              };
            }

            const formattedContext = results
              .map((res: any, idx: number) => {
                return (
                  `[Result #${idx + 1}] (Match Score: ${(res.similarity || 0).toFixed(4)})\n` +
                  `- Source Article: ${res.primary_title || "Unknown"}\n` +
                  `- Content: ${(res.primary_text || "").substring(0, 1000)}\n` +
                  `- Connected Reference via [${res.relationship || "unknown"}]: ${(res.linked_metadata || "").substring(0, 500)}\n`
                );
              })
              .join("\n---\n");

            return {
              content: [
                {
                  type: "text" as const,
                  text: `[ARANGODB GRAPH-RAG CONTEXT]:\n\n${formattedContext}`,
                },
              ],
            };
          } catch (aqlError: any) {
            // AQL might fail if the view/index doesn't exist; fall through
            onUpdate?.({
              content: [
                {
                  type: "text" as const,
                  text: `AQL query failed (${aqlError.message}), falling back to basic search...`,
                },
              ],
            });
          }
        }

        // Fallback: basic text search over literature_nodes
        const allDocs = await db
          .collection("literature_nodes")
          .all()
          .then((c: any) => c.all());

        const results = allDocs
          .map((doc: any) => {
            const title = doc.title || "";
            const content = doc.content || "";
            const searchText = `${title} ${content}`.toLowerCase();
            const query = params.queryText.toLowerCase();
            // Simple keyword relevance scoring
            const score = query
              .split(/\s+/)
              .filter((word) => word.length > 2)
              .reduce((sum, word) => sum + (searchText.includes(word) ? 1 : 0), 0);
            return { ...doc, _relevance: score / query.split(/\s+/).filter((w: string) => w.length > 2).length };
          })
          .filter((d: any) => d._relevance > 0)
          .sort((a: any, b: any) => b._relevance - a._relevance)
          .slice(0, maxResults);

        if (results.length === 0) {
          return {
            content: [
              {
                type: "text" as const,
                text: "[ARANGO RAG]: No matching documents found in the knowledge base.",
              },
            ],
          };
        }

        const formattedContext = results
          .map((res: any, idx: number) => {
            return (
              `[Result #${idx + 1}] (Relevance: ${(res._relevance * 100).toFixed(0)}%)\n` +
              `- Title: ${res.title || "Unknown"}\n` +
              `- Content: ${(res.content || "").substring(0, 1500)}\n` +
              `- Source: ${res.source || "unknown"}`
            );
          })
          .join("\n---\n");

        return {
          content: [
            {
              type: "text" as const,
              text: `[ARANGODB SEARCH RESULTS]:\n\n${formattedContext}`,
            },
          ],
        };
      } catch (dbError: any) {
        // ArangoDB not available - try file-based fallback
        try {
          const fs = await import("fs");
          const path = await import("path");
          const knowledgePath = path.default.resolve(
            process.cwd(),
            "knowledge_base.json"
          );

          if (!fs.existsSync(knowledgePath)) {
            return {
              content: [
                {
                  type: "text" as const,
                  text:
                    "[RAG UNAVAILABLE]: Neither ArangoDB nor local knowledge_base.json found.\n" +
                    "To use Graph-RAG:\n" +
                    "  1. Install and run ArangoDB (arangodb.com), OR\n" +
                    "  2. Create a knowledge_base.json file in the working directory.\n" +
                    "  See setup-db.ts for ArangoDB setup instructions.",
                },
              ],
            };
          }

          const knowledgeBase = JSON.parse(
            fs.readFileSync(knowledgePath, "utf-8")
          );
          const docs = Array.isArray(knowledgeBase) ? knowledgeBase : [knowledgeBase];

          const query = params.queryText.toLowerCase();
          const results = docs
            .map((doc: any) => {
              const searchText = `${doc.title || ""} ${doc.content || ""} ${doc.tags?.join(" ") || ""}`.toLowerCase();
              const score = query
                .split(/\s+/)
                .filter((word: string) => word.length > 2)
                .reduce(
                  (sum: number, word: string) =>
                    sum + (searchText.includes(word) ? 1 : 0),
                  0
                );
              return { ...doc, _relevance: score };
            })
            .filter((d: any) => d._relevance > 0)
            .sort((a: any, b: any) => b._relevance - a._relevance)
            .slice(0, maxResults);

          if (results.length === 0) {
            return {
              content: [
                {
                  type: "text" as const,
                  text: "[RAG]: No matching entries found in knowledge_base.json.",
                },
              ],
            };
          }

          const formattedContext = results
            .map((res: any, idx: number) => {
              return (
                `[Result #${idx + 1}] (Relevance: ${res._relevance})\n` +
                `- Title: ${res.title || "Untitled"}\n` +
                `- Content: ${(res.content || "").substring(0, 1500)}\n` +
                `- Tags: ${(res.tags || []).join(", ")}`
              );
            })
            .join("\n---\n");

          return {
            content: [
              {
                type: "text" as const,
                text: `[LOCAL KNOWLEDGE BASE RESULTS]:\n\n${formattedContext}`,
              },
            ],
          };
        } catch (fsError: any) {
          return {
            content: [
              {
                type: "text" as const,
                text: `[RAG ERROR]: Database and file fallback both failed. ${fsError.message}`,
              },
            ],
          };
        }
      }
    },
  });
}
