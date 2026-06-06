import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { execFile } from "child_process";
import * as fs from "fs";
import * as path from "path";
import * as util from "util";

const registerLegacyTool = (pi: ExtensionAPI, tool: unknown) => (pi.registerTool as any)(tool);
const execFilePromise = util.promisify(execFile);

/**
 * Agent Orchestrator - concrete local theorem proving pipeline.
 *
 * Queue: task_queue.json
 * Persistent task files:
 *   proofs/<task-id>.lean
 *   proofs/<task-id>.sp
 *
 * Execution model:
 *   Researcher and Algebraist run concurrently for context grounding.
 *   Formalist runs Lean after grounding.
 *   Critic runs the vacuity linter after Lean.
 *   Archivist writes a JSON run report under artifacts/agent_orchestrator/.
 */

type TaskStatus = "pending" | "running" | "done" | "failed";
type StageName = "researcher" | "algebraist" | "formalist" | "critic" | "archivist";

interface Task {
  id: string;
  title: string;
  status: TaskStatus;
  sympy_witness: boolean;
  lean_proof: boolean;
  external_ref: string | null;
  sympy_path?: string;
  lean_path?: string;
  last_report?: string;
}

interface Queue {
  orchestrator: string;
  queue: Task[];
  agents: Record<string, { role: string; tool: string; status: string }>;
}

interface StageResult {
  stage: StageName;
  ok: boolean;
  skipped?: boolean;
  path?: string;
  command?: string[];
  elapsed_ms: number;
  stdout?: string;
  stderr?: string;
  error?: string;
}

interface RunReport {
  task_id: string;
  title: string;
  status: TaskStatus;
  started_at: string;
  finished_at: string;
  stages: StageResult[];
}

const CWD = process.cwd();
const QUEUE_PATH = path.join(CWD, "task_queue.json");
const PROOF_DIR = path.join(CWD, "proofs");
const ARTIFACT_DIR = path.join(CWD, "artifacts", "agent_orchestrator");

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

function ensureDir(dir: string) {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

function safeId(id: string): string {
  return id.replace(/[^a-zA-Z0-9_.-]/g, "_");
}

function rel(p: string): string {
  return path.relative(CWD, p) || ".";
}

function clip(text: string | undefined, limit = 4000): string {
  if (!text) return "";
  if (text.length <= limit) return text;
  return text.slice(0, limit) + `\n...[truncated ${text.length - limit} chars]`;
}

function taskLeanPath(task: Task): string {
  if (task.lean_path) return path.resolve(CWD, task.lean_path);
  return path.join(PROOF_DIR, `${safeId(task.id)}.lean`);
}

function taskSympyPath(task: Task): string {
  if (task.sympy_path) return path.resolve(CWD, task.sympy_path);
  const sideBySide = path.join(PROOF_DIR, `${safeId(task.id)}.sp`);
  if (fs.existsSync(sideBySide)) return sideBySide;
  return path.join(CWD, "witnesses", `${safeId(task.id)}_sympy.py`);
}

function stageSkip(stage: StageName, reason: string): StageResult {
  return {
    stage,
    ok: true,
    skipped: true,
    elapsed_ms: 0,
    stdout: reason,
  };
}

async function runExec(
  stage: StageName,
  command: string,
  args: string[],
  options: { cwd?: string; timeout?: number; allowExitOne?: boolean; pathForReport?: string } = {}
): Promise<StageResult> {
  const started = Date.now();
  try {
    const result = await execFilePromise(command, args, {
      cwd: options.cwd ?? CWD,
      timeout: options.timeout ?? 60000,
      maxBuffer: 1024 * 1024 * 8,
    });
    return {
      stage,
      ok: true,
      path: options.pathForReport,
      command: [command, ...args],
      elapsed_ms: Date.now() - started,
      stdout: result.stdout,
      stderr: result.stderr,
    };
  } catch (error: any) {
    if (options.allowExitOne && error?.code === 1) {
      return {
        stage,
        ok: true,
        path: options.pathForReport,
        command: [command, ...args],
        elapsed_ms: Date.now() - started,
        stdout: error.stdout || "No local matches.",
        stderr: error.stderr,
      };
    }

    return {
      stage,
      ok: false,
      path: options.pathForReport,
      command: [command, ...args],
      elapsed_ms: Date.now() - started,
      stdout: error?.stdout,
      stderr: error?.stderr,
      error: error?.message ?? String(error),
    };
  }
}

async function findPythonWithSympy(): Promise<string | null> {
  const candidates = [
    path.join(CWD, ".venv", "bin", "python3"),
    path.join(CWD, ".venv", "bin", "python"),
    "python3",
    "python",
  ];

  for (const candidate of candidates) {
    if (candidate.includes(path.sep) && !fs.existsSync(candidate)) continue;
    try {
      await execFilePromise(candidate, ["-c", "import sympy"], { timeout: 5000 });
      return candidate;
    } catch {
      // Try the next candidate.
    }
  }
  return null;
}

async function runResearcher(task: Task): Promise<StageResult> {
  const searchRoots = ["lean", "docs", "tools"].filter((p) => fs.existsSync(path.join(CWD, p)));
  if (searchRoots.length === 0) return stageSkip("researcher", "No local search roots found.");

  return runExec(
    "researcher",
    "rg",
    ["-n", "--fixed-strings", "--ignore-case", "--max-count", "12", task.title, ...searchRoots],
    { timeout: 15000, allowExitOne: true }
  );
}

async function runAlgebraist(task: Task): Promise<StageResult> {
  const sympyPath = taskSympyPath(task);
  if (!fs.existsSync(sympyPath)) {
    return task.sympy_witness
      ? {
          stage: "algebraist",
          ok: false,
          path: rel(sympyPath),
          elapsed_ms: 0,
          error: `SymPy witness missing: ${rel(sympyPath)}`,
        }
      : stageSkip("algebraist", "No SymPy witness requested.");
  }

  const python = await findPythonWithSympy();
  if (!python) {
    return {
      stage: "algebraist",
      ok: false,
      path: rel(sympyPath),
      elapsed_ms: 0,
      error: "No Python executable with SymPy is available.",
    };
  }

  return runExec("algebraist", python, [sympyPath], {
    timeout: 30000,
    pathForReport: rel(sympyPath),
  });
}

async function runFormalist(task: Task): Promise<StageResult> {
  const leanPath = taskLeanPath(task);
  if (!fs.existsSync(leanPath)) {
    return task.lean_proof
      ? {
          stage: "formalist",
          ok: false,
          path: rel(leanPath),
          elapsed_ms: 0,
          error: `Lean proof missing: ${rel(leanPath)}`,
        }
      : stageSkip("formalist", "No Lean proof requested.");
  }

  return runExec("formalist", "lake", ["env", "lean", leanPath], {
    timeout: 120000,
    pathForReport: rel(leanPath),
  });
}

async function runCritic(task: Task): Promise<StageResult> {
  const leanPath = taskLeanPath(task);
  if (!fs.existsSync(leanPath)) return stageSkip("critic", "No Lean file to lint.");

  const linter = fs.existsSync(path.join(CWD, "tools", "scripts", "vacuity-linter.py"))
    ? path.join(CWD, "tools", "scripts", "vacuity-linter.py")
    : path.join(CWD, "scripts", "vacuity-linter.py");

  if (!fs.existsSync(linter)) return stageSkip("critic", "No vacuity linter found.");

  return runExec("critic", "python3", [linter, "--json", leanPath], {
    timeout: 30000,
    pathForReport: rel(leanPath),
  });
}

function writeReport(report: RunReport): string {
  ensureDir(ARTIFACT_DIR);
  const stamp = new Date().toISOString().replace(/[-:]/g, "").replace(/\..+/, "Z");
  const reportPath = path.join(ARTIFACT_DIR, `${stamp}_${safeId(report.task_id)}.json`);
  fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));
  return reportPath;
}

function summarizeReport(report: RunReport, reportPath: string): string {
  const lines = [
    `[QUEUE]: ${report.status === "done" ? "completed" : "failed"} ${report.task_id} - "${report.title}"`,
    `Report: ${rel(reportPath)}`,
    "",
    "Executed workers:",
  ];

  for (const stage of report.stages) {
    const mark = stage.ok ? (stage.skipped ? "SKIP" : "OK") : "FAIL";
    lines.push(
      `  ${mark} ${stage.stage}` +
        (stage.path ? ` (${stage.path})` : "") +
        ` in ${stage.elapsed_ms}ms`
    );
    const detail = clip(stage.error || stage.stderr || stage.stdout, 900).trim();
    if (detail) lines.push(`    ${detail.replace(/\n/g, "\n    ")}`);
  }

  return lines.join("\n");
}

export default function (pi: ExtensionAPI) {
  registerLegacyTool(pi, {
    name: "queue_status",
    label: "Task Queue Status",
    description:
      "Show the current state of the theorem proving task queue: " +
      "which theorems are pending, running, failed, or done, and which agents are available.",
    promptSnippet: "Show the theorem proving task queue status",
    parameters: Type.Object({}),

    async execute() {
      const q = loadQueue();
      const tasks = q.queue;
      const pending = tasks.filter((t) => t.status === "pending").length;
      const running = tasks.filter((t) => t.status === "running").length;
      const done = tasks.filter((t) => t.status === "done").length;
      const failed = tasks.filter((t) => t.status === "failed").length;
      const agents = Object.entries(q.agents).map(
        ([name, a]) => `  - ${name}: ${a.role} (${a.status})`
      );

      let report = `Task Queue: ${tasks.length} total\n`;
      report += `  Pending: ${pending}\n  Running: ${running}\n  Done: ${done}\n  Failed: ${failed}\n\n`;
      report += "Theorems:\n";

      for (const t of tasks) {
        const icon =
          t.status === "done" ? "OK" : t.status === "running" ? "RUN" : t.status === "failed" ? "FAIL" : "WAIT";
        const sympy = t.sympy_witness ? "sp" : "  ";
        const lean = t.lean_proof ? "ln" : "  ";
        report += `  ${icon} [${sympy}|${lean}] ${t.id}: ${t.title.substring(0, 80)}\n`;
      }

      report += `\nAgents:\n${agents.join("\n")}\n`;

      return {
        content: [{ type: "text" as const, text: report }],
      };
    },
  });

  registerLegacyTool(pi, {
    name: "queue_add_theorem",
    label: "Add Theorem to Queue",
    description:
      "Add a theorem to the concrete local proving pipeline. " +
      "SymPy and Lean source are persisted side-by-side as proofs/<id>.sp and proofs/<id>.lean.",
    promptSnippet: "Add a theorem to the proving queue",
    parameters: Type.Object({
      theoremId: Type.String({
        description: "Unique ID like 'lemma_name' or 'theorem-009'",
      }),
      title: Type.String({
        description: "Descriptive name of the theorem",
      }),
      sympyCode: Type.Optional(
        Type.String({
          description: "Optional SymPy Python code to persist as proofs/<id>.sp",
        })
      ),
      leanCode: Type.Optional(
        Type.String({
          description: "Optional Lean 4 code to persist as proofs/<id>.lean",
        })
      ),
    }),
    required: ["theoremId", "title"],

    async execute(
      _toolCallId: string,
      params: { theoremId: string; title: string; sympyCode?: string; leanCode?: string }
    ) {
      const q = loadQueue();

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

      ensureDir(PROOF_DIR);
      const id = safeId(params.theoremId);
      const leanPath = path.join(PROOF_DIR, `${id}.lean`);
      const sympyPath = path.join(PROOF_DIR, `${id}.sp`);

      if (params.sympyCode) fs.writeFileSync(sympyPath, params.sympyCode);
      if (params.leanCode) fs.writeFileSync(leanPath, params.leanCode);

      q.queue.push({
        id: params.theoremId,
        title: params.title,
        status: "pending",
        sympy_witness: !!params.sympyCode,
        lean_proof: !!params.leanCode,
        external_ref: null,
        sympy_path: params.sympyCode ? rel(sympyPath) : undefined,
        lean_path: params.leanCode ? rel(leanPath) : undefined,
      });

      saveQueue(q);

      return {
        content: [
          {
            type: "text" as const,
            text:
              `[QUEUE]: Added ${params.theoremId} - "${params.title}"\n` +
              "Status: pending\n" +
              `Queue: ${q.queue.length} total, ` +
              `${q.queue.filter((t) => t.status === "pending").length} pending\n` +
              (params.sympyCode ? `SymPy witness: ${rel(sympyPath)}\n` : "") +
              (params.leanCode ? `Lean proof: ${rel(leanPath)}\n` : ""),
          },
        ],
      };
    },
  });

  registerLegacyTool(pi, {
    name: "queue_run_next",
    label: "Run Next Theorem",
    description:
      "Run the next pending theorem through concrete local workers: " +
      "Researcher + Algebraist in parallel, then Formalist, Critic, and Archivist.",
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

      const startedAt = new Date().toISOString();
      next.status = "running";
      saveQueue(q);

      const grounding = await Promise.all([runResearcher(next), runAlgebraist(next)]);
      const formalist = await runFormalist(next);
      const critic = await runCritic(next);
      const stages = [...grounding, formalist, critic];
      const ok = stages.every((s) => s.ok);

      next.status = ok ? "done" : "failed";

      const reportWithoutPath: RunReport = {
        task_id: next.id,
        title: next.title,
        status: next.status,
        started_at: startedAt,
        finished_at: new Date().toISOString(),
        stages,
      };
      const reportPath = writeReport(reportWithoutPath);

      const archivist: StageResult = {
        stage: "archivist",
        ok: true,
        path: rel(reportPath),
        elapsed_ms: 0,
        stdout: `Wrote ${rel(reportPath)}`,
      };
      reportWithoutPath.stages.push(archivist);
      fs.writeFileSync(reportPath, JSON.stringify(reportWithoutPath, null, 2));

      next.last_report = rel(reportPath);
      saveQueue(q);

      return {
        content: [
          {
            type: "text" as const,
            text: summarizeReport(reportWithoutPath, reportPath),
          },
        ],
      };
    },
  });
}
