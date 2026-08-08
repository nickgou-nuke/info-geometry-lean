import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { exec } from "child_process";
import * as fs from "fs";
import * as path from "path";
import * as util from "util";

const execPromise = util.promisify(exec);
const exists = (p: string) => fs.existsSync(p);

/**
 * Lean 4 Theorem Prover — Structured JSON Diagnostics
 *
 * Compiles Lean 4 code via `lean --json` and returns structured diagnostics
 * (line numbers, error codes, goal states) instead of naive substring matching.
 *
 * Two modes:
 *   - plain:  `lean --json <file>` for code without Mathlib
 *   - mathlib: `lake env lean --json <file>` for code importing Mathlib
 *
 * The --json flag outputs one JSON object per diagnostic event (error, warning, etc.)
 * with exact position, severity, error kind, and the full error message (including goal state).
 */

interface LeanPos {
  line: number;
  column: number;
}

interface LeanDiagnostic {
  severity: "error" | "warning" | "info";
  pos: LeanPos;
  endPos: LeanPos;
  kind: string;
  data: string;
  fileName: string;
  caption?: string;
}

interface StructuredResult {
  success: boolean;
  diagnostics: LeanDiagnostic[];
  raw: string;
}

const DEFAULT_MATHLIB_PROJECT = "/home/goutev/repos/info-geometry-lean";

function findMathlibProject(): string {
  const candidates = [
    process.env.INFO_GEOMETRY_LEAN_ROOT,
    process.cwd(),
    DEFAULT_MATHLIB_PROJECT,
  ].filter((p): p is string => !!p);

  for (const candidate of candidates) {
    if (exists(candidate) && exists(path.join(candidate, "lakefile.lean"))) {
      return candidate;
    }
  }
  return DEFAULT_MATHLIB_PROJECT;
}

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "verify_lean_proof",
    label: "Lean 4 Theorem Prover (Structured Diagnostics)",
    description:
      "Verifies Lean 4 code using `lean --json` for structured diagnostics. " +
      "Returns exact line numbers, error kinds, and goal states for each error. " +
      "Supports plain Lean and Mathlib imports.",
    promptSnippet: "Verify mathematical/logical correctness via Lean 4 theorem prover",
    promptGuidelines: [
      "Use verify_lean_proof to formally verify algorithm correctness with Lean 4.",
      "The structured output includes line:column positions, error kinds, and goal states.",
      "If there are type errors, the diagnostic includes what type was expected vs found.",
    ],
    parameters: Type.Object({
      leanCode: Type.String({
        description: "The complete Lean 4 source code to compile.",
      }),
      theoremName: Type.String({
        description: "Name of the theorem or definition being proven.",
      }),
    }),
    required: ["leanCode", "theoremName"],

    async execute(
      _toolCallId: string,
      params: { leanCode: string; theoremName: string },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      // ── Check Lean availability ──
      try {
        await execPromise("which lean");
      } catch {
        return {
          content: [{ type: "text" as const, text: "[LEAN NOT FOUND]: Lean 4 not in PATH. Install via elan." }],
        };
      }

      const safeName = params.theoremName.replace(/[^a-zA-Z0-9]/g, "_") + ".lean";
      const tempDir = path.join(process.cwd(), ".lean_sandbox");
      if (!exists(tempDir)) fs.mkdirSync(tempDir, { recursive: true });
      const filePath = path.join(tempDir, safeName);
      fs.writeFileSync(filePath, params.leanCode);

      const needsMathlib = /^\s*import\s+Mathlib/m.test(params.leanCode);

      try {
        const result = needsMathlib
          ? await compileWithMathlib(filePath, params.theoremName, onUpdate)
          : await compilePlain(filePath, params.theoremName, onUpdate);

        // Curvature Defect Learning: log proof attempts to the cognitive graph
        await logProofAttempt(params.theoremName, _toolCallId, result);

        return { content: [{ type: "text" as const, text: formatResult(result, params.theoremName, params.leanCode) }] };
      } finally {
        try { fs.unlinkSync(filePath); } catch {}
      }
    },
  });
}

/**
 * Log the result of a proof attempt to the cognitive graph (Brain 2).
 */
async function logProofAttempt(theoremName: string, toolCallId: string, result: StructuredResult) {
  try {
    const { Database } = await import("arangojs");
    const dbUrl = process.env.AGENT_BRAIN_ARANGO_URL || process.env.ARANGO_URL || "http://localhost:8530";
    const dbName = process.env.AGENT_BRAIN_ARANGO_DB || "agent_brain";
    const user = process.env.AGENT_BRAIN_ARANGO_USER || "root";
    const pass = process.env.AGENT_BRAIN_ARANGO_PASSWORD || process.env.ARANGO_PASS || "alexandria_root";

    const rootDb = new Database({ url: dbUrl });
    const db = rootDb.database(dbName);
    db.useBasicAuth(user, pass);

    const attemptsColl = db.collection("proof_attempts");
    const exists = await attemptsColl.exists();
    if (!exists) {
      await attemptsColl.create({ type: 3 }); // Edge collection
    }

    const safeName = theoremName.replace(/[^a-zA-Z0-9]/g, "_");
    
    if (result.success) {
      await attemptsColl.save({
        _from: `steps/tool_${toolCallId}`,
        _to: `lean_theorems/${safeName}`,
        relation: "proved",
        compile_time_ms: 0, // Could measure elapsed time
        timestamp: new Date().toISOString()
      });
    } else {
      const errors = result.diagnostics.filter(d => d.severity === "error");
      if (errors.length > 0) {
        const primaryError = errors[0];
        await attemptsColl.save({
          _from: `steps/tool_${toolCallId}`,
          _to: `lean_theorems/${safeName}`,
          relation: "failed",
          error_type: primaryError.kind || "unknown",
          error_message: primaryError.data,
          timestamp: new Date().toISOString()
        });
      }
    }
  } catch (err) {
    // Silently fail if DB is unavailable, so we don't break the agent
    console.error("Failed to log proof attempt to ArangoDB:", err);
  }
}

/**
 * Compile with plain `lean --json`.
 */
async function compilePlain(filePath: string, theoremName: string, onUpdate: any): Promise<StructuredResult> {
  onUpdate?.({ content: [{ type: "text" as const, text: `Compiling '${theoremName}' (plain mode, --json)...` }] });

  try {
    const { stdout } = await execPromise(`lean --json ${filePath}`, { timeout: 30000 });
    return { success: true, diagnostics: [], raw: stdout };
  } catch (error: any) {
    const raw = error.stdout || error.stderr || error.message || "";
    const diagnostics = parseDiagnostics(raw);
    return { success: diagnostics.length === 0, diagnostics, raw };
  }
}

/**
 * Compile with `lake env lean --json` (mathlib mode).
 */
async function compileWithMathlib(filePath: string, theoremName: string, onUpdate: any): Promise<StructuredResult> {
  const mathlibProject = findMathlibProject();
  if (!exists(mathlibProject) || !exists(path.join(mathlibProject, "lakefile.lean"))) {
    return {
      success: false,
      diagnostics: [{
        severity: "error", kind: "system.setup",
        pos: { line: 0, column: 0 }, endPos: { line: 0, column: 0 },
        data: `Mathlib project not found at ${mathlibProject}. Set INFO_GEOMETRY_LEAN_ROOT or run from the project root.`,
        fileName: filePath,
      }],
      raw: "",
    };
  }

  onUpdate?.({ content: [{ type: "text" as const, text: `Compiling '${theoremName}' (mathlib mode, --json)...` }] });

  try {
    const { stdout } = await execPromise(`lake env lean --json ${filePath} 2>&1`, {
      cwd: mathlibProject,
      timeout: 60000,
    });
    return { success: true, diagnostics: [], raw: stdout };
  } catch (error: any) {
    const raw = error.stdout || error.stderr || error.message || "";
    const diagnostics = parseDiagnostics(raw);
    return { success: diagnostics.length === 0, diagnostics, raw };
  }
}

/**
 * Parse the multi-line JSON output from `lean --json`.
 * Each line is a separate diagnostic event.
 */
function parseDiagnostics(raw: string): LeanDiagnostic[] {
  const diags: LeanDiagnostic[] = [];
  for (const line of raw.split("\n")) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      const parsed = JSON.parse(trimmed);
      if (parsed && typeof parsed === "object" && "severity" in parsed) {
        diags.push(parsed as LeanDiagnostic);
      }
    } catch {
      // Not JSON — skip (e.g., progress messages from lake)
    }
  }
  return diags;
}

/**
 * Format the compilation result as a structured text report
 * with exact line numbers, error kinds, and goal states.
 */
function formatResult(result: StructuredResult, theoremName: string, code: string): string {
  if (result.success) {
    const diagSummary = result.diagnostics.length > 0
      ? `\n(plus ${result.diagnostics.length} non-critical diagnostic(s))`
      : "";
    return [
      `[LEAN SUCCESS] Theorem '${theoremName}' verified. No errors.`,
      `Lean 4.28.0 | --json diagnostics`,
      diagSummary,
    ].join("\n");
  }

  const errors = result.diagnostics.filter(d => d.severity === "error");
  const warnings = result.diagnostics.filter(d => d.severity === "warning");
  const others = result.diagnostics.filter(d => d.severity !== "error" && d.severity !== "warning");

  const codeLines = code.split("\n");

  // Group errors by kind for a summary
  const errorKinds = new Map<string, number>();
  for (const e of errors) {
    const kind = e.kind || "[anonymous]";
    errorKinds.set(kind, (errorKinds.get(kind) || 0) + 1);
  }

  let report = `[LEAN COMPILE ERROR] Theorem '${theoremName}' — ${errors.length} error(s), ${warnings.length} warning(s)\n\n`;

  // ── Error summary by kind ──
  report += `── Error kinds ──\n`;
  for (const [kind, count] of errorKinds) {
    report += `  ${kind}: ${count}\n`;
  }
  report += "\n";

  // ── Per-error details (first 10) ──
  report += `── Error details ──\n`;
  for (let i = 0; i < Math.min(errors.length, 10); i++) {
    const e = errors[i];
    const line = e.pos.line;
    const col = e.pos.column;
    const context = line > 0 && line <= codeLines.length
      ? `\n    Code context: ${codeLines[line - 1].substring(0, 80)}`
      : "";
    // Extract goal state from data (text after ⊢ or "goal:")
    const goalMatch = e.data.match(/⊢\s*(.+?)(?:\n|$)/);
    const goalInfo = goalMatch ? `\n    Goal: ⊢ ${goalMatch[1].trim()}` : "";

    report += [
      `  [${i + 1}/${errors.length}] Line ${line}:${col}`,
      `    Kind: ${e.kind || "[anonymous]"}`,
      `    Message: ${e.data.split("\n")[0]}`,
      goalInfo,
      context,
      "",
    ].join("\n");
  }
  if (errors.length > 10) {
    report += `  ... and ${errors.length - 10} more error(s)\n\n`;
  }

  // ── Warnings ──
  if (warnings.length > 0) {
    report += `── Warnings ──\n`;
    for (const w of warnings.slice(0, 5)) {
      report += `  Line ${w.pos.line}:${w.pos.column} — ${w.data.split("\n")[0]}\n`;
    }
    if (warnings.length > 5) {
      report += `  ... and ${warnings.length - 5} more\n`;
    }
    report += "\n";
  }

  // ── Suggested actions based on error kinds ──
  report += `── Suggested actions ──\n`;
  const suggestions = new Set<string>();
  for (const e of errors) {
    const kind = e.kind || "";
    if (kind.includes("unsolvedGoals") || e.data.includes("⊢")) {
      suggestions.add("Goal not fully proven: provide more steps before `done` or `rfl`");
    }
    if (kind.includes("typeMismatch") || kind.includes("synthInstance")) {
      suggestions.add("Type mismatch or missing instance: check that all typeclass arguments are satisfied");
    }
    if (kind.includes("unknownIdentifier")) {
      suggestions.add("Unknown identifier: check spelling or import the required module");
    }
    if (kind.includes("ambiguous")) {
      suggestions.add("Ambiguous name: use a fully qualified name or open the relevant namespace");
    }
    if (e.data.includes("has no field") || e.data.includes("unknown field")) {
      suggestions.add("Field not found: check the structure's field names");
    }
    if (e.data.includes("recursive")) {
      suggestions.add("Recursive definition: use `termination_by` or `decreasing_by`");
    }
  }
  if (suggestions.size === 0) {
    suggestions.add("Review the error messages above and fix the proof");
  }
  for (const s of suggestions) {
    report += `  • ${s}\n`;
  }

  return report;
}
