import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { spawn } from "node:child_process";

const registerLegacyTool = (pi: ExtensionAPI, tool: unknown) => (pi.registerTool as any)(tool);

/**
 * ChatGPT Oracle Bridge
 *
 * Dual-mode consultant LLM tool:
 *   1. Queued aiClaw bridge — routes through tools/infra/aiclaw_chat.py and
 *      the shared per-platform single-flight lane.
 *   2. API fallback — uses DeepSeek/OpenAI API directly
 *
 * The bridge mode is token-free — it uses your browser's ChatGPT session, but
 * only through the repo queue. Do not use the legacy port-1956 direct bridge.
 * The API mode always works (requires DEEPSEEK_API_KEY).
 */

export default function (pi: ExtensionAPI) {
  registerLegacyTool(pi, {
    name: "ask_chatgpt_compiler",
    label: "ChatGPT Oracle Bridge",
    description:
      "USE THIS TOOL ONLY FOR COMPLEX BUGS, ARCHITECTURAL ISSUES, OR COMPILATION ERRORS. " +
      "Sends code and logs to a consultant LLM for expert evaluation. " +
      "Use when you've exhausted local debugging and need a fresh perspective.",
    promptSnippet: "Consult an expert LLM for complex debugging or architectural review",
    promptGuidelines: [
      "Use ask_chatgpt_compiler when you encounter complex bugs, architectural issues, or compilation errors that local debugging cannot resolve.",
    ],
    parameters: Type.Object({
      code: Type.String({
        description: "The problematic source code that needs review or correction.",
      }),
      context: Type.String({
        description:
          "Terminal output, compiler error traceback, or specific question for the Oracle.",
      }),
      systemRole: Type.Optional(
        Type.String({
          description:
            "Optional: Override the consultant's system role. Default: expert code reviewer.",
        })
      ),
    }),
    required: ["code", "context"],

    async execute(
      _toolCallId: string,
      params: { code: string; context: string; systemRole?: string },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      const prompt = `--- ORCHESTRATOR CONTEXT/ERROR ---\n${params.context}\n\n--- CODE TO REVIEW ---\n${params.code}\n\nPlease provide direct fixes, optimized code blocks, or explain the error clearly.`;

      // ── Try queued aiClaw bridge (browser ChatGPT) first ──
      try {
        const bridgeResult = await tryQueuedAiClaw(prompt, onUpdate);
        if (bridgeResult) return bridgeResult;
      } catch {
        // Bridge failed silently, fall through to API
      }

      // ── Fall back to DeepSeek API ──
      return await tryApiFallback(prompt, params.systemRole, onUpdate);
    },
  });
}

/**
 * Try to send the prompt via the queued aiClaw adapter to browser ChatGPT.
 * Returns a result if successful, or null if the bridge is unavailable.
 */
async function tryQueuedAiClaw(
  prompt: string,
  onUpdate: any
): Promise<{ content: { type: "text"; text: string }[] } | null> {
  return new Promise((resolve) => {
    onUpdate?.({
      content: [{ type: "text" as const, text: "Consulting ChatGPT via queued aiClaw lane..." }],
    });
    const child = spawn(
      "python3",
      [
        "tools/infra/aiclaw_chat.py",
        "ask",
        "--wait",
        "--new",
        "--json",
        "--quiet",
        "--timeout",
        process.env.AICLAW_TIMEOUT || "600",
        "--queue-timeout",
        process.env.AICLAW_QUEUE_TIMEOUT || "900",
      ],
      { cwd: process.cwd(), env: process.env, stdio: ["pipe", "pipe", "pipe"] }
    );
    let stdout = "";
    let stderr = "";
    let settled = false;
    const finish = (value: { content: { type: "text"; text: string }[] } | null) => {
      if (!settled) {
        settled = true;
        resolve(value);
      }
    };

    child.stdout.on("data", (chunk) => {
      stdout += chunk.toString();
    });
    child.stderr.on("data", (chunk) => {
      stderr += chunk.toString();
    });
    child.on("error", () => finish(null));
    child.on("close", (code) => {
      const combined = `${stdout}\n${stderr}`.trim();
      if (code !== 0) {
        if (/queue|lane|busy/i.test(combined)) {
          finish({
            content: [
              {
                type: "text" as const,
                text: `[CHATGPT ORACLE BUSY]: queued aiClaw refused to send.\n${combined}`,
              },
            ],
          });
          return;
        }
        finish(null);
        return;
      }
      try {
        const res = JSON.parse(stdout);
        const content = String(res.content || "").trim();
        if (res.suspect_intermediate || res.queue?.held || /^thinking\.?$/i.test(content)) {
          finish({
            content: [
              {
                type: "text" as const,
                text:
                  "[CHATGPT ORACLE NEEDS READBACK]: aiClaw returned a suspect/intermediate result. " +
                  "The ChatGPT lane is held; recover the final visible answer read-only before sending again.",
              },
            ],
          });
          return;
        }
        if (!res.success || !content) {
          finish(null);
          return;
        }
        finish({
          content: [{ type: "text" as const, text: `[CHATGPT ORACLE RESPONSE (queued aiClaw)]:\n${content}` }],
        });
      } catch {
        finish(null);
      }
    });
    child.stdin.end(prompt);
  });
}

/**
 * Fallback: send the prompt via the DeepSeek/OpenAI API.
 */
async function tryApiFallback(
  prompt: string,
  systemRole: string | undefined,
  onUpdate: any
): Promise<{ content: { type: "text"; text: string }[] }> {
  const systemPrompt =
    systemRole ||
    "You are the Oracle/Compiler in a hybrid AI system. " +
      "The Orchestrator (the primary coding agent) has encountered a complex bug or error " +
      "and needs your expert review. Provide direct fixes, optimized code blocks, " +
      "or explain the error clearly. Be concise and specific.";

  const apiKey =
    process.env.DEEPSEEK_API_KEY ||
    process.env.OPENAI_API_KEY ||
    process.env.ANTHROPIC_API_KEY ||
    "";
  const baseUrl =
    process.env.OPENAI_BASE_URL?.replace(/\/+$/, "") ||
    process.env.DEEPSEEK_BASE_URL?.replace(/\/+$/, "") ||
    "https://api.deepseek.com/v1";
  const model =
    process.env.ORACLE_MODEL || process.env.CONSULTANT_MODEL || "deepseek-chat";

  if (!apiKey) {
    return {
      content: [
        {
          type: "text" as const,
          text: "[ORACLE UNAVAILABLE]: queued aiClaw lane and API fallback are unavailable. Check `python3 tools/infra/aiclaw_chat.py status` or set DEEPSEEK_API_KEY.",
        },
      ],
    };
  }

  try {
    onUpdate?.({
      content: [
        {
          type: "text" as const,
          text: `Consulting ${model} via API (bridge unavailable)...`,
        },
      ],
    });

    const response = await fetch(`${baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Authorization: `Bearer ${apiKey}`,
      },
      body: JSON.stringify({
        model: model,
        messages: [
          { role: "system", content: systemPrompt },
          { role: "user", content: prompt },
        ],
        max_tokens: 4096,
        temperature: 0.3,
      }),
    });

    if (!response.ok) {
      const errorText = await response.text();
      return {
        content: [
          {
            type: "text" as const,
            text: `[ORACLE ERROR]: API returned ${response.status}: ${errorText}`,
          },
        ],
      };
    }

    const data = (await response.json()) as any;
    const oracleResponse =
      data.choices?.[0]?.message?.content || "[ORACLE: No response content]";

    return {
      content: [
        {
          type: "text" as const,
          text: `[CHATGPT ORACLE RESPONSE]:\n${oracleResponse}`,
        },
      ],
    };
  } catch (error: any) {
    return {
      content: [
        {
          type: "text" as const,
          text: `[ORACLE ERROR]: Connection failed. Error: ${error.message}`,
        },
      ],
    };
  }
}
