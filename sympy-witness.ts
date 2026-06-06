import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { execFile } from "child_process";
import * as fs from "fs";
import * as path from "path";
import * as util from "util";

const registerLegacyTool = (pi: ExtensionAPI, tool: unknown) => (pi.registerTool as any)(tool);
const execFilePromise = util.promisify(execFile);

function safeName(name: string): string {
  return name.replace(/[^a-zA-Z0-9_.-]/g, "_");
}

function ensureDir(dir: string) {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

function rel(p: string): string {
  return path.relative(process.cwd(), p) || ".";
}

/**
 * SymPy Algebraic Witness
 *
 * A Pi extension that computes the algebraic representation of a
 * theorem or proof. Runs Python/SymPy code to calculate closed-form
 * mathematical witnesses, providing the "right hemisphere" ground truth
 * that can then be formally verified with Lean 4.
 *
 * Requirements:
 *   - Python 3 installed
 *   - sympy library installed (`pip install sympy`)
 */

export default function (pi: ExtensionAPI) {
  registerLegacyTool(pi, {
    name: "verify_sympy_witness",
    label: "SymPy Algebraic Witness",
    description:
      "USE THIS TOOL to calculate the algebraic representation of a theorem or proof. " +
      "Provide Python code using the 'sympy' library to compute and output the closed-form " +
      "mathematical witness. This grounds abstract logic in computable algebra. " +
      "Requires Python 3 and sympy (`pip install sympy`).",
    promptSnippet: "Compute algebraic witness via SymPy for mathematical grounding",
    promptGuidelines: [
      "Use verify_sympy_witness BEFORE verify_lean_proof to establish algebraic ground truth first.",
      "The SymPy witness acts as the 'right hemisphere' grounding for the 'left hemisphere' Lean 4 formalization.",
    ],
    parameters: Type.Object({
      pythonCode: Type.String({
        description:
          "The complete Python script using sympy to compute the algebraic representation. Must print the result to stdout.",
      }),
      witnessName: Type.String({
        description:
          "A descriptive name for this algebraic witness (e.g., 'FFT_Matrix_Roots').",
      }),
    }),
    required: ["pythonCode", "witnessName"],

    async execute(
      _toolCallId: string,
      params: { pythonCode: string; witnessName: string },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      // Discover Python executable — prefer local venv, then system
      const pythonCandidates = [
        path.join(process.cwd(), ".venv", "bin", "python3"),
        path.join(process.cwd(), ".venv", "bin", "python"),
        "python3",
        "python",
      ];

      let pythonBin = "python3";
      for (const candidate of pythonCandidates) {
        if (candidate.includes(path.sep) && !fs.existsSync(candidate)) continue;
        try {
          await execFilePromise(candidate, ["-c", "import sympy; print(sympy.__version__)"]);
          pythonBin = candidate;
          break;
        } catch {
          // Try next candidate
        }
      }

      // If none found, check without sympy (maybe user will install it)
      try {
        await execFilePromise(pythonBin, ["--version"]);
      } catch {
        return {
          content: [
            {
              type: "text" as const,
              text:
                "[SYMPY NOT FOUND]: Python is not available.\n" +
                "Install Python 3 with: apt install python3 python3-pip\n" +
                "Then: pip install sympy",
            },
          ],
        };
      }

      onUpdate?.({
        content: [
          {
            type: "text" as const,
            text: `Computing algebraic witness '${params.witnessName}' via SymPy...`,
          },
        ],
      });

      const proofDir = path.join(process.cwd(), "proofs");
      ensureDir(proofDir);
      const witnessPath = path.join(proofDir, `${safeName(params.witnessName)}.sp`);
      fs.writeFileSync(witnessPath, params.pythonCode);

      try {
        const result = await execFilePromise(pythonBin, [witnessPath], {
          timeout: 30000,
          maxBuffer: 1024 * 1024 * 4,
        });
        const stdout = result.stdout;
        const stderr = result.stderr;

        if (stderr && !stdout) {
          return {
            content: [
              {
                type: "text" as const,
                text:
                  `[SYMPY WARNING]: Witness produced stderr:\n${stderr}\n\n` +
                  `Persisted witness: ${rel(witnessPath)}`,
              },
            ],
          };
        }

        return {
          content: [
            {
              type: "text" as const,
              text:
                `[SYMPY ALGEBRAIC WITNESS RESULT]:\n` +
                `Witness: ${params.witnessName}\n\n` +
                `Persisted witness: ${rel(witnessPath)}\n\n` +
                `${stdout.trim()}` +
                (stderr ? `\n\n[stderr]:\n${stderr}` : ""),
            },
          ],
        };
      } catch (error: any) {
        return {
          content: [
            {
              type: "text" as const,
              text:
                `[SYMPY ERROR]: Algebraic witness calculation failed.\n` +
                `Error: ${error.stderr || error.stdout || error.message}\n\n` +
                `Persisted failing witness for repair: ${rel(witnessPath)}\n\n` +
                `Fix the Python/SymPy code and try again.`,
            },
          ],
        };
      }
    },
  });
}
