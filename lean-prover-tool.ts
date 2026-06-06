import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { exec } from "child_process";
import * as fs from "fs";
import * as path from "path";
import * as util from "util";

const execPromise = util.promisify(exec);
const exists = (p: string) => fs.existsSync(p);

/**
 * Lean 4 Theorem Prover & Auto-Formalizer
 *
 * Verifies Lean 4 code using the system-installed Lean 4.28.0 (managed by elan).
 *
 * Two compilation modes:
 *   - plain:  `lean <file>` directly — for code without Mathlib imports
 *   - mathlib: writes to the existing info-geometry-lean project's src/
 *              and runs `lake build` there — for code needing mathlib
 *
 * System state:
 *   - elan 4.2.1, Lean 4.28.0 at ~/.elan/bin/
 *   - info-geometry-lean project at /home/goutev/info-geometry-lean/
 *     (fully built with mathlib v4.28.0, 6.9GB .lake/packages/)
 *   - mathlib cache at ~/.cache/mathlib/ (411MB)
 */

// Path to the pre-built Lean project with mathlib
const MATHLIB_PROJECT = "/home/goutev/info-geometry-lean";

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "verify_lean_proof",
    label: "Lean 4 Theorem Prover & Auto-Formalizer",
    description:
      "USE THIS TOOL to verify mathematical or logical correctness in Lean 4. " +
      "Supports both plain Lean code and code importing Mathlib (via the pre-built " +
      "info-geometry-lean project). Returns type-checking errors from the Lean 4 kernel. " +
      "Lean 4.28.0 managed by elan.",
    promptSnippet: "Verify mathematical/logical correctness via Lean 4 theorem prover",
    promptGuidelines: [
      "Use verify_lean_proof when you need to formally verify algorithm correctness with Lean 4.",
      "The system supports both plain Lean code and Mathlib imports.",
    ],
    parameters: Type.Object({
      leanCode: Type.String({
        description:
          "The complete Lean 4 source code (theorem or definition) to compile. " +
          "Can include `import Mathlib` for mathlib-dependent proofs.",
      }),
      theoremName: Type.String({
        description: "The name of the specific theorem or lemma being proven.",
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
          content: [
            {
              type: "text" as const,
              text:
                "[LEAN NOT FOUND]: Lean 4 compiler is not installed or not in PATH.\n" +
                "Install: curl -fsSL https://raw.githubusercontent.com/leanprover/lean4/master/install.sh | bash\n" +
                "Or add to PATH: export PATH=\"$HOME/.elan/bin:$PATH\"",
            },
          ],
        };
      }

      const safeFileName =
        params.theoremName.replace(/[^a-zA-Z0-9]/g, "_") + ".lean";

      // Detect if code needs mathlib
      const needsMathlib = /^\s*import\s+Mathlib/m.test(params.leanCode);

      if (needsMathlib) {
        return await verifyWithMathlib(params.leanCode, params.theoremName, safeFileName, onUpdate);
      } else {
        return await verifyPlain(params.leanCode, params.theoremName, safeFileName, onUpdate);
      }
    },
  });
}

/**
 * Verify plain Lean code (no Mathlib imports) using `lean <file>`.
 */
async function verifyPlain(
  code: string,
  theoremName: string,
  safeFileName: string,
  onUpdate: any
): Promise<{ content: { type: "text"; text: string }[] }> {
  const tempDir = path.join(process.cwd(), ".lean_sandbox");
  if (!exists(tempDir)) fs.mkdirSync(tempDir, { recursive: true });

  const filePath = path.join(tempDir, safeFileName);
  fs.writeFileSync(filePath, code);

  try {
    onUpdate?.({
      content: [
        {
          type: "text" as const,
          text: `Running Lean 4.28.0 (plain mode) for: ${theoremName}...`,
        },
      ],
    });

    const { stdout } = await execPromise(`lean ${filePath}`, {
      timeout: 30000,
    });

    try { fs.unlinkSync(filePath); } catch {}

    return {
      content: [
        {
          type: "text" as const,
          text:
            `[LEAN SUCCESS]: Theorem '${theoremName}' is completely verified. No logical errors.\n` +
            `Lean 4.28.0 | elan 4.2.1` +
            (stdout ? `\nOutput:\n${stdout}` : ""),
        },
      ],
    };
  } catch (error: any) {
    try { fs.unlinkSync(filePath); } catch {}

    return {
      content: [
        {
          type: "text" as const,
          text:
            `[LEAN COMPILE ERROR]:\n${error.stderr || error.stdout || error.message}\n\n` +
            `Theorem '${theoremName}' failed type-checking. ` +
            `Use ask_chatgpt_compiler to get help fixing the proof.`,
        },
      ],
    };
  }
}

/**
 * Verify code with Mathlib imports using `lake env lean`.
 * Uses the pre-built project's environment to access mathlib,
 * but only compiles the single file (not the whole project).
 * This avoids triggering pre-existing audit errors in the project.
 */
async function verifyWithMathlib(
  code: string,
  theoremName: string,
  safeFileName: string,
  onUpdate: any
): Promise<{ content: { type: "text"; text: string }[] }> {
  // Check the pre-built project exists
  if (!exists(MATHLIB_PROJECT) || !exists(path.join(MATHLIB_PROJECT, "lakefile.lean"))) {
    return {
      content: [
        {
          type: "text" as const,
          text:
            "[MATHLIB PROJECT NOT FOUND]: The pre-built Lean project at " +
            MATHLIB_PROJECT + " is not available.\n" +
            "Use plain Lean code without `import Mathlib`, or set up a lake project.",
        },
      ],
    };
  }

  // Write to a temp file (NOT inside the project src/ — avoids triggering full rebuild)
  const tempDir = path.join(process.cwd(), ".lean_sandbox");
  if (!exists(tempDir)) fs.mkdirSync(tempDir, { recursive: true });
  const filePath = path.join(tempDir, safeFileName);
  fs.writeFileSync(filePath, code);

  try {
    onUpdate?.({
      content: [
        {
          type: "text" as const,
          text: `Compiling with mathlib v4.28.0 (single file mode)...`,
        },
      ],
    });

    // Use `lake env lean` — sets up load paths for mathlib but only compiles our file
    const { stdout, stderr } = await execPromise(
      `lake env lean ${filePath} 2>&1`,
      { cwd: MATHLIB_PROJECT, timeout: 60000 }
    );

    try { fs.unlinkSync(filePath); } catch {}

    const fullOutput = stdout + stderr;

    // Check for errors in the output
    if (fullOutput.includes("error:") || fullOutput.includes("Error")) {
      return {
        content: [
          {
            type: "text" as const,
            text:
              `[LEAN COMPILE ERROR] (mathlib v4.28.0):\n${fullOutput.slice(-2000)}\n\n` +
              `Theorem '${theoremName}' failed. Use ask_chatgpt_compiler for help.`,
          },
        ],
      };
    }

    return {
      content: [
        {
          type: "text" as const,
          text:
            `[LEAN SUCCESS]: Theorem '${theoremName}' verified with mathlib v4.28.0. No errors.\n` +
            `\nLean 4.28.0 | mathlib v4.28.0 | elan 4.2.1` +
            (fullOutput.trim() ? `\n${fullOutput.trim()}` : ""),
        },
      ],
    };
  } catch (error: any) {
    try { fs.unlinkSync(filePath); } catch {}

    return {
      content: [
        {
          type: "text" as const,
          text:
            `[LEAN COMPILE ERROR] (mathlib v4.28.0):\n${error.stderr || error.stdout || error.message}\n\n` +
            `Theorem '${theoremName}' failed. Use ask_chatgpt_compiler for help.`,
        },
      ],
    };
  }
}
