import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { exec } from "child_process";
import * as fs from "fs";
import * as path from "path";
import * as util from "util";

const execPromise = util.promisify(exec);

/**
 * SymPy Algebraic Witness
 *
 * A Pi extension that runs Python/SymPy code for computable algebraic
 * witnesses.  These witnesses are useful audit evidence, but they are not
 * proof authority and must not be treated as a substitute for Lean kernel
 * verification or explicit mathematical assumptions.
 *
 * Requirements:
 *   - Python 3 installed
 *   - sympy library installed (`pip install sympy`)
 */

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "verify_sympy_witness",
    label: "SymPy Algebraic Witness",
    description:
      "USE THIS TOOL to calculate a computable algebraic witness for a theorem-shaped claim. " +
      "Provide Python code using the 'sympy' library to compute and assert the relevant " +
      "closed-form identities. Treat the result as audit evidence, not as a proof. " +
      "Requires Python 3 and sympy (`pip install sympy`).",
    promptSnippet: "Compute an asserted algebraic witness via SymPy for audit",
    promptGuidelines: [
      "Use verify_sympy_witness to test executable algebra before Lean formalization.",
      "Do not accept printed success text as proof; include explicit assertions in the witness code.",
      "Use verify_lean_proof or repo Lean audit tools for kernel-checked proof claims.",
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
        try {
          await execPromise(`${candidate} -c 'import sympy; print(sympy.__version__)'`);
          pythonBin = candidate;
          break;
        } catch {
          // Try next candidate
        }
      }

      // If none found, check without sympy (maybe user will install it)
      try {
        await execPromise(`${pythonBin} --version`);
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

      const tempFilePath = path.join(process.cwd(), ".temp_witness.py");
      fs.writeFileSync(tempFilePath, params.pythonCode);

      try {
        let stdout: string, stderr: string;
        try {
          const result = await execPromise(`${pythonBin} ${tempFilePath}`, {
            timeout: 30000,
          });
          stdout = result.stdout;
          stderr = result.stderr;
        } catch {
          // Final fallback: just try python
          const result = await execPromise(`python ${tempFilePath}`, {
            timeout: 30000,
          });
          stdout = result.stdout;
          stderr = result.stderr;
        }

        // Clean up
        try {
          fs.unlinkSync(tempFilePath);
        } catch {}

        if (stderr && !stdout) {
          return {
            content: [
              {
                type: "text" as const,
                text: `[SYMPY WARNING]: Witness produced stderr:\n${stderr}`,
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
                `${stdout.trim()}` +
                (stderr ? `\n\n[stderr]:\n${stderr}` : ""),
            },
          ],
        };
      } catch (error: any) {
        // Clean up
        try {
          fs.unlinkSync(tempFilePath);
        } catch {}

        return {
          content: [
            {
              type: "text" as const,
              text:
                `[SYMPY ERROR]: Algebraic witness calculation failed.\n` +
                `Error: ${error.stderr || error.stdout || error.message}\n\n` +
                `Fix the Python/SymPy code and try again.`,
            },
          ],
        };
      }
    },
  });
}
