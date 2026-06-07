import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { spawn } from "node:child_process";
import * as crypto from "node:crypto";
import * as fs from "node:fs";
import * as path from "node:path";

const registerLegacyTool = (pi: ExtensionAPI, tool: unknown) => (pi.registerTool as any)(tool);

const MAX_LEDGER_TEXT = Number(process.env.AGENT_MESSAGE_LEDGER_MAX_TEXT_CHARS || "20000");

function sha256(text: string): string {
  return crypto.createHash("sha256").update(text).digest("hex");
}

function redactText(text: string): { text: string; matches: string[] } {
  const patterns: [string, RegExp][] = [
    ["openai_key", /\bsk-[A-Za-z0-9_-]{20,}\b/g],
    ["github_token", /\bgh[pousr]_[A-Za-z0-9_]{20,}\b/g],
    ["aws_access_key", /\bAKIA[0-9A-Z]{16}\b/g],
    ["bearer_token", /\bBearer\s+[A-Za-z0-9._~+/=-]{20,}\b/gi],
    ["secret_assignment", /\b(password|passwd|secret|token|api[_-]?key)\s*[:=]\s*['"]?[^'"\s]+/gi],
  ];
  let out = text;
  const matches: string[] = [];
  for (const [name, pattern] of patterns) {
    if (pattern.test(out)) {
      matches.push(name);
      out = out.replace(pattern, `[REDACTED:${name}]`);
    }
  }
  return { text: out, matches: [...new Set(matches)].sort() };
}

function clipText(text: string): { text: string; truncated: boolean } {
  if (MAX_LEDGER_TEXT <= 0) return { text: "", truncated: text.length > 0 };
  if (text.length <= MAX_LEDGER_TEXT) return { text, truncated: false };
  const half = Math.floor(MAX_LEDGER_TEXT / 2);
  return {
    text:
      text.slice(0, half) +
      `\n\n[... clipped ${text.length - MAX_LEDGER_TEXT} chars ...]\n\n` +
      text.slice(-(MAX_LEDGER_TEXT - half)),
    truncated: true,
  };
}

function recordAgentMessage(event: {
  sourceTool: string;
  channel: string;
  provider: string;
  model: string;
  platform?: string;
  promptText: string;
  responseText: string;
  success: boolean;
  latencyMs?: number;
  metadata?: Record<string, unknown>;
}) {
  try {
    const repo = process.cwd();
    const dir = path.join(repo, "artifacts", "agent_messages");
    fs.mkdirSync(dir, { recursive: true });
    const day = new Date().toISOString().slice(0, 10).replace(/-/g, "");
    const file = path.join(dir, `${day}_agent_messages.jsonl`);
    const prompt = redactText(event.promptText || "");
    const response = redactText(event.responseText || "");
    const promptClip = clipText(prompt.text);
    const responseClip = clipText(response.text);
    const payload = {
      schema: "agent-message-ledger/v1",
      event_id: crypto.randomUUID(),
      ts: new Date().toISOString(),
      source_tool: event.sourceTool,
      source_file: "chatgpt-oracle.ts",
      channel: event.channel,
      direction: "agent_to_model",
      provider: event.provider,
      model: event.model,
      platform: event.platform || "",
      correlation_id: sha256(event.promptText || "").slice(0, 16),
      prompt_sha256: sha256(event.promptText || ""),
      prompt_chars: (event.promptText || "").length,
      prompt_text: promptClip.text,
      prompt_truncated: promptClip.truncated,
      prompt_sensitive_matches: prompt.matches,
      response_sha256: sha256(event.responseText || ""),
      response_chars: (event.responseText || "").length,
      response_text: responseClip.text,
      response_truncated: responseClip.truncated,
      response_sensitive_matches: response.matches,
      success: event.success,
      latency_ms: event.latencyMs ?? null,
      metadata: event.metadata || {},
      authority: "observation_only_not_proof",
    };
    fs.appendFileSync(file, JSON.stringify(payload) + "\n", "utf8");
  } catch {
    // Observation must never block the oracle.
  }
}

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
  const modelPrompt = JSON.stringify({
    messages: [
      { role: "system", content: systemPrompt },
      { role: "user", content: prompt },
    ],
  });

  if (!apiKey) {
    const text = "[ORACLE UNAVAILABLE]: queued aiClaw lane and API fallback are unavailable. Check `python3 tools/infra/aiclaw_chat.py status` or set DEEPSEEK_API_KEY.";
    recordAgentMessage({
      sourceTool: "ask_chatgpt_compiler",
      channel: "chatgpt_oracle_api_fallback",
      provider: "api-fallback",
      model,
      promptText: modelPrompt,
      responseText: text,
      success: false,
      metadata: { failure_pattern: "missing_api_key" },
    });
    return {
      content: [
        {
          type: "text" as const,
          text,
        },
      ],
    };
  }

  const started = Date.now();
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
      const text = `[ORACLE ERROR]: API returned ${response.status}: ${errorText}`;
      recordAgentMessage({
        sourceTool: "ask_chatgpt_compiler",
        channel: "chatgpt_oracle_api_fallback",
        provider: "api-fallback",
        model,
        promptText: modelPrompt,
        responseText: text,
        success: false,
        latencyMs: Date.now() - started,
        metadata: { status: response.status, failure_pattern: "api_error_status" },
      });
      return {
        content: [
          {
            type: "text" as const,
            text,
          },
        ],
      };
    }

    const data = (await response.json()) as any;
    const oracleResponse =
      data.choices?.[0]?.message?.content || "[ORACLE: No response content]";
    recordAgentMessage({
      sourceTool: "ask_chatgpt_compiler",
      channel: "chatgpt_oracle_api_fallback",
      provider: "api-fallback",
      model,
      promptText: modelPrompt,
      responseText: oracleResponse,
      success: true,
      latencyMs: Date.now() - started,
      metadata: { base_url: baseUrl.replace(/\/\/.*@/, "//[redacted]@") },
    });

    return {
      content: [
        {
          type: "text" as const,
          text: `[CHATGPT ORACLE RESPONSE]:\n${oracleResponse}`,
        },
      ],
    };
  } catch (error: any) {
    const text = `[ORACLE ERROR]: Connection failed. Error: ${error.message}`;
    recordAgentMessage({
      sourceTool: "ask_chatgpt_compiler",
      channel: "chatgpt_oracle_api_fallback",
      provider: "api-fallback",
      model,
      promptText: modelPrompt,
      responseText: text,
      success: false,
      latencyMs: Date.now() - started,
      metadata: { failure_pattern: "api_connection_error" },
    });
    return {
      content: [
        {
          type: "text" as const,
          text,
        },
      ],
    };
  }
}
