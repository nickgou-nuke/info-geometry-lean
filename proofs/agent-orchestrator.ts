import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import * as fs from "fs";
import * as path from "path";

/**
 * Agent Orchestrator — Multi-agent theorem proving pipeline
 *
 * Manages a queue of theorems, each processed by:
 *   Researcher → Algebraist (SymPy) → Formalist (Lean) → Critic → Archivist
 *
 * Queue: task_queue.json
 * Agents: orchestrator, algebraist, formalist, critic, archivist, researcher
 */

interface Task {
  id: string;
  title: string;
  status: "pending" | "running" | "done" | "failed";
  sympy_witness: boolean;
  lean_proof: boolean;
  external_ref: string | null;
}

interface Queue {
  orchestrator: string;
  queue: Task[];
  agents: Record<string, { role: string; tool: string; status: string }>;
}

const QUEUE_PATH = path.join(process.cwd(), "task_queue.json");

function loadQueue(): Queue {
  try {
    return JSON.parse(fs.readFileSync(QUEUE_PATH, "utf-8"));
  } catch {
    return {
      orchestrator: "deepseek/deepseek-v4-flash",
      queue: [],
      agents: {},
    };
  }
}

function saveQueue(q: Queue) {
  fs.writeFileSync(QUEUE_PATH, JSON.stringify(q, null, 2));
}

export default function (pi: ExtensionAPI) {
  // ── Tool 1: Show queue status ──
  pi.registerTool({
    name: "queue_status",
    label: "Task Queue Status",
    description:
      "Show the current state of the theorem proving task queue: " +
      "which theorems are pending, running, or done, and which agents are available.",
    promptSnippet: "Show the theorem proving task queue status",
    parameters: Type.Object({}),

    async execute() {
      const q = loadQueue();
      const tasks = q.queue;
      const pending = tasks.filter((t) => t.status === "pending").length;
      const running = tasks.filter((t) => t.status === "running").length;
      const done = tasks.filter((t) => t.status === "done").length;
      const agents = Object.entries(q.agents).map(
        ([name, a]) => `  • ${name}: ${a.role} (${a.status})`
      );

      let report = `Task Queue: ${tasks.length} total\n`;
      report += `  Pending: ${pending}\n  Running: ${running}\n  Done: ${done}\n\n`;
      report += `Theorems:\n`;

      for (const t of tasks) {
        const icon =
          t.status === "done"
            ? "✅"
            : t.status === "running"
            ? "🔄"
            : "⏳";
        const sympy = t.sympy_witness ? "✓" : " ";
        const lean = t.lean_proof ? "✓" : " ";
        report += `  ${icon} [${sympy}|${lean}] ${t.id}: ${t.title.substring(0, 60)}\n`;
      }

      report += `\nAgents:\n${agents.join("\n")}\n`;

      return {
        content: [{ type: "text" as const, text: report }],
      };
    },
  });

  // ── Tool 2: Add theorem to queue ──
  pi.registerTool({
    name: "queue_add_theorem",
    label: "Add Theorem to Queue",
    description:
      "Add a new theorem to the proving pipeline. " +
      "The orchestrator will assign it to the researcher, algebraist, formalist, critic, and archivist.",
    promptSnippet: "Add a theorem to the proving queue",
    parameters: Type.Object({
      theoremId: Type.String({
        description: "Unique ID like 'theorem-009'",
      }),
      title: Type.String({
        description: "Descriptive name of the theorem",
      }),
      sympyCode: Type.Optional(
        Type.String({
          description: "Optional SymPy Python code to verify",
        })
      ),
      leanCode: Type.Optional(
        Type.String({
          description: "Optional Lean 4 code for the theorem",
        })
      ),
    }),
    required: ["theoremId", "title"],

    async execute(
      _toolCallId: string,
      params: { theoremId: string; title: string; sympyCode?: string; leanCode?: string }
    ) {
      const q = loadQueue();

      // Check for duplicate
      if (q.queue.some((t) => t.id === params.theoremId)) {
        return {
          content: [
            {
              type: "text" as const,
              text: `[ERROR]: Theorem ${params.theoremId} already exists in queue.`,
            },
          ],
        };
      }

      q.queue.push({
        id: params.theoremId,
        title: params.title,
        status: "pending",
        sympy_witness: !!params.sympyCode,
        lean_proof: !!params.leanCode,
        external_ref: null,
      });

      saveQueue(q);

      // If SymPy code provided, create a witness file
      if (params.sympyCode) {
        const witnessDir = path.join(process.cwd(), "witnesses");
        if (!fs.existsSync(witnessDir)) fs.mkdirSync(witnessDir);
        fs.writeFileSync(
          path.join(witnessDir, `${params.theoremId}_sympy.py`),
          params.sympyCode
        );
      }

      // If Lean code provided, create a proof file
      if (params.leanCode) {
        const proofDir = path.join(process.cwd(), "proofs");
        if (!fs.existsSync(proofDir)) fs.mkdirSync(proofDir);
        fs.writeFileSync(
          path.join(proofDir, `${params.theoremId}.lean`),
          params.leanCode
        );
      }

      return {
        content: [
          {
            type: "text" as const,
            text:
              `[QUEUE]: Added ${params.theoremId} — "${params.title}"\n` +
              `Status: pending\n` +
              `Queue: ${q.queue.length} total, ` +
              `${q.queue.filter((t) => t.status === "pending").length} pending\n` +
              (params.sympyCode
                ? `SymPy witness: witnesses/${params.theoremId}_sympy.py\n`
                : "") +
              (params.leanCode
                ? `Lean proof: proofs/${params.theoremId}.lean\n`
                : ""),
          },
        ],
      };
    },
  });

  // ── Tool 3: Run next pending theorem ──
  pi.registerTool({
    name: "queue_run_next",
    label: "Run Next Theorem",
    description:
      "Take the next pending theorem from the queue and run it through the pipeline: " +
      "Researcher → Algebraist (SymPy) → Formalist (Lean) → Critic → Archivist.",
    promptSnippet: "Run the next pending theorem through the proving pipeline",
    parameters: Type.Object({}),

    async execute() {
      const q = loadQueue();
      const next = q.queue.find((t) => t.status === "pending");

      if (!next) {
        return {
          content: [
            {
              type: "text" as const,
              text: "[QUEUE]: No pending theorems. Add one with queue_add_theorem.",
            },
          ],
        };
      }

      next.status = "running";
      saveQueue(q);

      return {
        content: [
          {
            type: "text" as const,
            text:
              `[QUEUE]: Running ${next.id} — "${next.title}"\n` +
              `\nPipeline:\n` +
              `  1. 🔍 Researcher — gather context from Wikipedia + repos\n` +
              `  2. 🧮 Algebraist — verify with verify_sympy_witness\n` +
              `  3. 📐 Formalist — prove with verify_lean_proof\n` +
              `  4. 🔎 Critic — check with vacuity-linter\n` +
              `  5. 💾 Archivist — commit with commit_conscious_knowledge\n` +
              `\nThe orchestrator will now process each step.`,
          },
        ],
      };
    },
  });
}
