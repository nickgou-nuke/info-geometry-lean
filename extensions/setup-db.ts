/**
 * ArangoDB Vector-Graph Synchronization Script
 *
 * Run this once to prime your ArangoDB instance for the aiClaw RAG pipeline.
 * It creates the required collections, analyzers, and ArangoSearch views.
 *
 * Usage: npx ts-node setup-db.ts
 *
 * Requirements:
 *   - Isolated aiClaw ArangoDB running on AICLAW_ARANGO_URL
 *   - arangojs installed (npm install arangojs)
 */

const AICLAW_ARANGO_URL = process.env.AICLAW_ARANGO_URL || "http://127.0.0.1:8540";
const AICLAW_ARANGO_DB = process.env.AICLAW_ARANGO_DB || "aiclaw_auto_rag";
const AICLAW_ARANGO_USER = process.env.AICLAW_ARANGO_USER || "root";
const AICLAW_ARANGO_PASSWORD = process.env.AICLAW_ARANGO_PASSWORD || "password";

function assertSeparateBrain() {
  if (process.env.AICLAW_ALLOW_SHARED_ARANGO === "1") return;
  if (AICLAW_ARANGO_URL.includes(":8530") || AICLAW_ARANGO_DB === "infogeometry") {
    throw new Error(
      "Refusing to initialize the repo DAG brain. Set AICLAW_ARANGO_URL to a separate " +
        "port/database, or set AICLAW_ALLOW_SHARED_ARANGO=1 if this is intentional."
    );
  }
}

async function main() {
  console.log("🔄 ArangoDB Graph-RAG Setup Starting...");
  assertSeparateBrain();

  try {
    const { Database } = await import("arangojs");
    const db = new Database({ url: AICLAW_ARANGO_URL });
    db.useBasicAuth(AICLAW_ARANGO_USER, AICLAW_ARANGO_PASSWORD);

    // First, check if we can connect (with timeout)
    const version = await Promise.race([
      db.version(),
      new Promise((_, reject) => setTimeout(() => reject(new Error("Connection timeout")), 5000)),
    ]);
    console.log(`✅ Connected to ArangoDB v${version}`);

    // Create or use the isolated aiClaw database
    try {
      await db.createDatabase(AICLAW_ARANGO_DB);
      console.log(`✅ Created database '${AICLAW_ARANGO_DB}'.`);
    } catch {
      console.log(`⚡ Database '${AICLAW_ARANGO_DB}' already exists.`);
    }

    const aiclawDb = db.database(AICLAW_ARANGO_DB);

    // 1. Create Document Collection (Literature Nodes)
    const literatureNodes = aiclawDb.collection("literature_nodes");
    if (!(await literatureNodes.exists())) {
      await literatureNodes.create();
      console.log("✅ Created 'literature_nodes' document collection.");
    } else {
      console.log("⚡ 'literature_nodes' collection already exists.");
    }

    // 2. Create Edge Collection (Citation Graph)
    const citationEdges = aiclawDb.collection("citation_edges");
    if (!(await citationEdges.exists())) {
      await citationEdges.create({ type: 3 }); // 3 = Edge collection
      console.log("✅ Created 'citation_edges' edge collection.");
    } else {
      console.log("⚡ 'citation_edges' collection already exists.");
    }

    // 3. Try to create ArangoSearch View
    try {
      const existingViews = await aiclawDb.views();
      const viewExists = existingViews.some(
        (v: any) => v.name === "literature_search_view"
      );

      if (!viewExists) {
        await aiclawDb.createView("literature_search_view", {
          type: "arangosearch",
          links: {
            literature_nodes: {
              includeAllFields: true,
              fields: {
                embedding: {
                  analyzers: ["identity"],
                },
                title: {
                  analyzers: ["text_en"],
                },
                content: {
                  analyzers: ["text_en"],
                },
              },
            },
          },
          primarySort: [],
        });
        console.log(
          "✅ Created ArangoSearch View: 'literature_search_view'"
        );
      } else {
        console.log(
          "⚡ 'literature_search_view' already exists. Updating properties..."
        );
        const view = aiclawDb.view("literature_search_view");
        await view.updateProperties({
          links: {
            literature_nodes: {
              includeAllFields: true,
              fields: {
                embedding: { analyzers: ["identity"] },
                title: { analyzers: ["text_en"] },
                content: { analyzers: ["text_en"] },
              },
            },
          },
        });
        console.log("✅ Updated 'literature_search_view' properties.");
      }
    } catch (viewError: any) {
      console.log(
        `⚠️  Could not create/update view (may need ArangoDB 3.10+): ${viewError.message}`
      );
      console.log(
        "  The system will work with basic keyword search as fallback."
      );
    }

    // 4. Create indexes for faster lookups
    try {
      await literatureNodes.ensureIndex({
        type: "persistent",
        fields: ["title"],
      });
      await literatureNodes.ensureIndex({
        type: "persistent",
        fields: ["source"],
      });
      await literatureNodes.ensureIndex({
        type: "persistent",
        fields: ["status"],
      });
      console.log("✅ Created persistent indexes on title, source, status.");
    } catch (idxError: any) {
      console.log(`⚠️  Index creation note: ${idxError.message}`);
    }

    // 5. Insert sample seed data if the collection is empty
    const countResult = await literatureNodes.count();
    if (countResult.count === 0) {
      console.log("📝 Inserting seed literature entries...");
      const seedData = [
        {
          _key: "Cooley_Tukey_1965_Base",
          title: "Cooley-Tukey FFT Algorithm",
          content:
            "The Cooley-Tukey algorithm, named after J.W. Cooley and John Tukey, is the most common fast Fourier transform algorithm. It re-expresses the discrete Fourier transform (DFT) of an arbitrary composite size N = N1N2 in terms of N1 smaller DFTs of size N2, recursively, to reduce the computational complexity to O(N log N).",
          source: "aiClaw_google_ai",
          tags: ["FFT", "signal-processing", "algorithm"],
          status: "literature",
        },
        {
          _key: "DFT_Algebraic_Rings",
          title: "DFT over Algebraic Rings",
          content:
            "The discrete Fourier transform can be generalized to arbitrary rings. For a commutative ring R, the DFT of a sequence of length N is defined using a primitive Nth root of unity in R. The matrix representation involves the Vandermonde matrix with entries ω^k where ω is the primitive root.",
          source: "aiClaw_google_ai",
          tags: ["FFT", "abstract-algebra", "rings"],
          status: "literature",
        },
        {
          _key: "Lean4_Mathlib_Overview",
          title: "Lean 4 Mathlib: Analysis and Algebra",
          content:
            "Mathlib is the mathematical library for Lean 4. It contains formalizations of algebra, analysis, number theory, and more. The Complex module provides definitions for complex numbers, exponentials, and trigonometric functions needed for FFT formalization.",
          source: "aiClaw_google_ai",
          tags: ["lean4", "mathlib", "formal-verification"],
          status: "literature",
        },
      ];

      for (const doc of seedData) {
        try {
          await literatureNodes.save(doc);
          console.log(`  ✅ Seeded: ${doc.title}`);
        } catch (e) {
          console.log(`  ⚡ Already exists: ${doc.title}`);
        }
      }

      // Create citation edges between seed documents
      const edges = [
        {
          _from: "literature_nodes/Lean4_Mathlib_Overview",
          _to: "literature_nodes/DFT_Algebraic_Rings",
          type: "provides_framework_for",
        },
        {
          _from: "literature_nodes/DFT_Algebraic_Rings",
          _to: "literature_nodes/Cooley_Tukey_1965_Base",
          type: "generalizes",
        },
      ];

      for (const edge of edges) {
        try {
          await citationEdges.save(edge);
          console.log(`  ✅ Edge: ${edge.type} (${edge._from} -> ${edge._to})`);
        } catch (e) {
          console.log(`  ⚡ Edge already exists.`);
        }
      }
    } else {
      console.log(`📊 Collection already has ${countResult.count} documents.`);
    }

    console.log("\n🚀 ArangoDB Vector-Graph Setup Complete!");
    console.log(`   Endpoint: ${AICLAW_ARANGO_URL}`);
    console.log(`   Database: ${AICLAW_ARANGO_DB}`);
    console.log("   Collections: literature_nodes, citation_edges");
    console.log("   To insert more data, run the aiClaw ingestion pipeline.");
  } catch (error: any) {
    console.error("\n❌ Setup failed:", error.message);
    console.log("\n📋 Prerequisites:");
    console.log("  1. Install ArangoDB: https://arangodb.com/downloads/");
    console.log(
      "  2. Start ArangoDB: systemctl start arangodb3 (or arangod &)"
    );
    console.log("  3. Install npm deps: npm install arangojs");
    console.log("\n   Or alternatively:");
    console.log(
      "  4. Use the file-based fallback: create a knowledge_base.json file"
    );
  }
}

main();
