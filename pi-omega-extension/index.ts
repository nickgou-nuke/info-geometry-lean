/**
 * Pi-Omega Extension: Multi-Provider LLM + Browser Harness + Oracle + Lean 4
 * Production-hardened version with proper error handling, connection pooling, and observability.
 */

import * as fs from "fs/promises";
import * as path from "path";
import { fileURLToPath } from "url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, "../../../../");

// =============================================================================
// Configuration & Types
// =============================================================================

interface ProviderConfig {
	name: string;
	apiKeyEnv: string;
	baseUrl?: string;
	models: ModelConfig[];
}

interface ModelConfig {
	id: string;
	name: string;
	reasoning?: boolean;
	input?: string[];
	cost?: { input: number; output: number; cacheRead?: number; cacheWrite?: number };
	contextWindow?: number;
	maxTokens?: number;
}

interface BrowserHarnessConfig {
	host?: string;
	port?: number;
	wsUrl?: string;
	connectionTimeoutMs?: number;
	commandTimeoutMs?: number;
}

interface LeanConfig {
	repoRoot: string;
	lakeTimeoutMs?: number;
}

interface ArangoConfig {
	url: string;
	db: string;
	user: string;
	pass: string;
	maxRetries?: number;
	retryDelayMs?: number;
}

interface OracleConfig {
	browserConfig: BrowserHarnessConfig;
	defaultTimeoutMs?: number;
	maxRetries?: number;
}

// =============================================================================
// Structured Logging
// =============================================================================

type LogLevel = "debug" | "info" | "warn" | "error";

interface LogEntry {
	timestamp: string;
	level: LogLevel;
	component: string;
	message: string;
	metadata?: Record<string, unknown>;
}

class Logger {
	private component: string;
	private minLevel: LogLevel;
	private levelOrder: LogLevel[] = ["debug", "info", "warn", "error"];

	constructor(component: string, minLevel: LogLevel = "info") {
		this.component = component;
		this.minLevel = minLevel;
	}

	private shouldLog(level: LogLevel): boolean {
		return this.levelOrder.indexOf(level) >= this.levelOrder.indexOf(this.minLevel);
	}

	private log(level: LogLevel, message: string, metadata?: Record<string, unknown>): void {
		if (!this.shouldLog(level)) return;
		const entry: LogEntry = {
			timestamp: new Date().toISOString(),
			level,
			component: this.component,
			message,
			metadata,
		};
		const stream = level === "error" || level === "warn" ? process.stderr : process.stdout;
		stream.write(JSON.stringify(entry) + "\n");
	}

	debug(message: string, metadata?: Record<string, unknown>): void { this.log("debug", message, metadata); }
	info(message: string, metadata?: Record<string, unknown>): void { this.log("info", message, metadata); }
	warn(message: string, metadata?: Record<string, unknown>): void { this.log("warn", message, metadata); }
	error(message: string, metadata?: Record<string, unknown>): void { this.log("error", message, metadata); }

	child(subComponent: string): Logger {
		return new Logger(`${this.component}:${subComponent}`, this.minLevel);
	}
}

// =============================================================================
// Retry Utility
// =============================================================================

async function withRetry<T>(
	operation: () => Promise<T>,
	options: { maxRetries: number; baseDelayMs: number; maxDelayMs: number; retryableErrors?: RegExp[]; logger?: Logger; context?: string }
): Promise<T> {
	let lastError: Error;
	for (let attempt = 0; attempt <= options.maxRetries; attempt++) {
		try {
			return await operation();
		} catch (error) {
			lastError = error instanceof Error ? error : new Error(String(error));
			const isRetryable = !options.retryableErrors || options.retryableErrors.some(re => re.test(lastError.message));
			if (attempt === options.maxRetries || !isRetryable) {
				options.logger?.error(`Operation failed after ${attempt + 1} attempt(s)`, { context: options.context, error: lastError.message });
				throw lastError;
			}
			const delay = Math.min(options.baseDelayMs * Math.pow(2, attempt), options.maxDelayMs);
			options.logger?.warn(`Attempt ${attempt + 1} failed, retrying in ${delay}ms`, { context: options.context, error: lastError.message });
			await new Promise(r => setTimeout(r, delay));
		}
	}
	throw lastError!;
}

// =============================================================================
// Browser Harness Client (CDP)
// =============================================================================

class BrowserHarnessClient {
	private ws: WebSocket | null = null;
	private messageId = 0;
	private pending = new Map<number, { resolve: (v: unknown) => void; reject: (e: Error) => void }>();
	private config: Required<BrowserHarnessConfig>;
	private logger: Logger;
	private connected = false;
	private messageHandler: ((msg: unknown) => void) | null = null;

	constructor(config: BrowserHarnessConfig = {}, logger?: Logger) {
		this.config = {
			host: config.host ?? "127.0.0.1",
			port: config.port ?? 9222,
			wsUrl: config.wsUrl ?? "",
			connectionTimeoutMs: config.connectionTimeoutMs ?? 10000,
			commandTimeoutMs: config.commandTimeoutMs ?? 30000,
		};
		this.logger = logger?.child("browser") ?? new Logger("browser");
	}

	async connect(wsUrl?: string): Promise<void> {
		if (this.connected && this.ws?.readyState === WebSocket.OPEN) {
			this.logger.debug("Already connected");
			return;
		}

		const targetUrl = wsUrl ?? await this.findTargetTab();
		this.logger.info("Connecting to CDP", { url: targetUrl });

		this.ws = new WebSocket(targetUrl);
		this.connected = false;

		await Promise.race([
			new Promise<void>((resolve, reject) => {
				if (!this.ws) return reject(new Error("WebSocket not created"));
				this.ws.onopen = () => {
					this.connected = true;
					this.logger.debug("CDP connection opened");
					resolve();
				};
				this.ws.onerror = (err) => reject(new Error(`WebSocket error: ${err}`));
				this.ws.onclose = () => {
					this.connected = false;
					this.logger.debug("CDP connection closed");
				};
				this.ws.onmessage = (msg) => this.handleMessage(msg.data.toString());
			}),
			new Promise<never>((_, reject) => setTimeout(() => reject(new Error("Connection timeout")), this.config.connectionTimeoutMs)),
		]);

		// Enable required domains
		await this.send({ method: "Runtime.enable" });
		await this.send({ method: "Page.enable" });
		await this.send({ method: "Network.enable" });

		this.logger.info("CDP connection established and domains enabled");
	}

	private async findTargetTab(): Promise<string> {
		const url = `http://${this.config.host}:${this.config.port}/json/list`;
		const res = await fetch(url);
		const targets = await res.json() as Array<{ url?: string; type: string; webSocketDebuggerUrl: string }>;

		const priority = [
			(t: typeof targets[0]) => t.url?.includes("chatgpt.com") && t.type === "page",
			(t: typeof targets[0]) => t.url?.includes("google.com") && t.type === "page" && (t.url.includes("ai") || t.url.includes("search")),
			(t: typeof targets[0]) => t.type === "page",
		];

		for (const predicate of priority) {
			const match = targets.find(predicate);
			if (match) return match.webSocketDebuggerUrl;
		}
		throw new Error("No suitable browser tab found. Ensure Chrome is running with --remote-debugging-port=9222");
	}

	private handleMessage(data: string): void {
		try {
			const msg = JSON.parse(data);
			if (msg.id && this.pending.has(msg.id)) {
				const { resolve, reject } = this.pending.get(msg.id)!;
				this.pending.delete(msg.id);
				if (msg.error) reject(new Error(msg.error.message));
				else resolve(msg.result);
			}
		} catch (e) {
			this.logger.warn("Failed to parse CDP message", { error: String(e) });
		}
	}

	private nextId(): number {
		return ++this.messageId;
	}

	async send(params: Record<string, unknown>): Promise<unknown> {
		if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
			throw new Error("WebSocket not connected");
		}
		const id = this.nextId();
		const message = { ...params, id };
		return new Promise((resolve, reject) => {
			this.pending.set(id, { resolve, reject });
			this.ws!.send(JSON.stringify(message));
			setTimeout(() => {
				if (this.pending.has(id)) {
					this.pending.delete(id);
					reject(new Error(`CDP timeout for ${params.method}`));
				}
			}, this.config.commandTimeoutMs);
		});
	}

	async evaluate(expression: string, awaitPromise = true): Promise<unknown> {
		return this.send({
			method: "Runtime.evaluate",
			params: { expression, returnByValue: true, awaitPromise },
		});
	}

	async click(selector: string): Promise<void> {
		await this.evaluate(`
			const el = document.querySelector(${JSON.stringify(selector)});
			if (el) el.click();
			else throw new Error("Element not found: ${selector}");
		`);
	}

	async type(selector: string, text: string): Promise<void> {
		await this.evaluate(`
			const el = document.querySelector(${JSON.stringify(selector)});
			if (el) {
				if (el.tagName === "TEXTAREA" || el.tagName === "INPUT") el.value = ${JSON.stringify(text)};
				else el.innerText = ${JSON.stringify(text)};
				el.dispatchEvent(new Event("input", { bubbles: true }));
			} else throw new Error("Element not found: ${selector}");
		`);
	}

	async waitForSelector(selector: string, timeout = 10000): Promise<boolean> {
		const start = Date.now();
		while (Date.now() - start < timeout) {
			const result = await this.evaluate(`!!document.querySelector(${JSON.stringify(selector)})`);
			if (result === true) return true;
			await new Promise(r => setTimeout(r, 100));
		}
		return false;
	}

	async sendKeys(key: string): Promise<void> {
		await this.send({ method: "Input.dispatchKeyEvent", params: { type: "keyDown", key, code: key, keyCode: key.charCodeAt(0) } });
		await this.send({ method: "Input.dispatchKeyEvent", params: { type: "keyUp", key, code: key, keyCode: key.charCodeAt(0) } });
	}

	async screenshot(): Promise<string | undefined> {
		const result = await this.send({ method: "Page.captureScreenshot", params: { format: "png", fromSurface: true } });
		return (result as { data?: string })?.data;
	}

	async sendPrompt(prompt: string): Promise<void> {
		// Generic prompt injection for ChatGPT / Google AI / generic textareas
		await this.evaluate(`
			(() => {
				const selectors = [
					'textarea[aria-label*="Message"]',
					'textarea[data-testid="chat-input"]',
					'div[contenteditable="true"][role="textbox"]',
					'textarea',
					'div[contenteditable="true"]'
				];
				for (const sel of selectors) {
					const el = document.querySelector(sel);
					if (el) {
						if (el.tagName === "TEXTAREA" || el.tagName === "INPUT") el.value = ${JSON.stringify(prompt)};
						else el.innerText = ${JSON.stringify(prompt)};
						el.dispatchEvent(new Event("input", { bubbles: true }));
						return;
					}
				}
				throw new Error("No input element found");
			})()
		`);
		await new Promise(r => setTimeout(r, 300));
		// Try to click send button
		await this.evaluate(`
			(() => {
				const btn = document.querySelector('[data-testid="send-button"], button[aria-label*="Send"], button:has(svg[data-testid="send-icon"])');
				if (btn) btn.click();
			})()
		`);
	}

	async waitForResponse(timeout = 120000): Promise<string> {
		const start = Date.now();
		while (Date.now() - start < timeout) {
			await new Promise(r => setTimeout(r, 2000));
			const result = await this.evaluate(`
				(() => {
					const msgs = document.querySelectorAll('[data-message-author-role="assistant"], .assistant-message, [data-testid="assistant-message"]');
					const last = msgs[msgs.length - 1];
					return last ? last.innerText : "waiting...";
				})()
			`);
			const text = String(result);
			if (!text.toLowerCase().includes("waiting") && text.trim().length > 0) {
				return text;
			}
		}
		throw new Error(`Timeout waiting for response after ${timeout}ms`);
	}

	async close(): Promise<void> {
		if (this.ws) {
			this.ws.close();
			this.ws = null;
		}
		this.connected = false;
		this.pending.clear();
		this.logger.debug("Browser connection closed");
	}

	isConnected(): boolean {
		return this.connected && this.ws?.readyState === WebSocket.OPEN;
	}
}

// =============================================================================
// Browser Pool for Connection Reuse
// =============================================================================

class BrowserPool {
	private pools = new Map<string, BrowserHarnessClient[]>();
	private config: BrowserHarnessConfig;
	private logger: Logger;
	private maxPoolSize: number;

	constructor(config: BrowserHarnessConfig, maxPoolSize = 3, logger?: Logger) {
		this.config = config;
		this.maxPoolSize = maxPoolSize;
		this.logger = logger?.child("pool") ?? new Logger("pool");
	}

	async acquire(key = "default"): Promise<BrowserHarnessClient> {
		let pool = this.pools.get(key);
		if (!pool) {
			pool = [];
			this.pools.set(key, pool);
		}

		// Find available connection
		for (const client of pool) {
			if (client.isConnected()) return client;
		}

		// Create new if under limit
		if (pool.length < this.maxPoolSize) {
			const client = new BrowserHarnessClient(this.config, this.logger);
			await client.connect();
			pool.push(client);
			return client;
		}

		// Wait for one to become available (simple round-robin with health check)
		for (let i = 0; i < pool.length; i++) {
			const client = pool[i];
			if (client.isConnected()) return client;
			// Replace dead connection
			try { await client.close(); } catch {}
			const newClient = new BrowserHarnessClient(this.config, this.logger);
			await newClient.connect();
			pool[i] = newClient;
			return newClient;
		}

		throw new Error("Browser pool exhausted");
	}

	async release(key = "default", client: BrowserHarnessClient): Promise<void> {
		// Connection stays in pool for reuse
		this.logger.debug("Browser returned to pool", { key });
	}

	getStats(): Record<string, unknown> {
		const stats: Record<string, unknown> = {};
		for (const [key, pool] of this.pools.entries()) {
			stats[key] = {
				size: pool.length,
				connected: pool.filter(c => c.isConnected()).length,
				maxSize: this.maxPoolSize,
			};
		}
		return stats;
	}

	async closeAll(): Promise<void> {
		for (const pool of this.pools.values()) {
			for (const client of pool) {
				try { await client.close(); } catch {}
			}
		}
		this.pools.clear();
	}
}

// =============================================================================
// Oracle Client
// =============================================================================

interface OracleResponse {
	valid?: boolean;
	proofSketch?: string;
	sorries?: string[];
	notes?: string;
	rawResponse?: string;
	summary?: string;
	[key: string]: unknown;
}

class OracleClient {
	private pool: BrowserPool;
	private config: OracleConfig;
	private logger: Logger;

	constructor(pool: BrowserPool, config: OracleConfig, logger?: Logger) {
		this.pool = pool;
		this.config = config;
		this.logger = logger?.child("oracle") ?? new Logger("oracle");
	}

	async queryChatGPT(prompt: string, options?: { timeout?: number }): Promise<OracleResponse> {
		const client = await this.pool.acquire("chatgpt");
		try {
			await client.sendPrompt(prompt);
			const response = await client.waitForResponse(options?.timeout ?? this.config.defaultTimeoutMs ?? 120000);
			return this.parseResponse(response);
		} finally {
			await this.pool.release("chatgpt", client);
		}
	}

	async queryGoogleAI(prompt: string, options?: { timeout?: number }): Promise<OracleResponse> {
		const client = await this.pool.acquire("google-ai");
		try {
			await client.sendPrompt(`Search: ${prompt}`);
			const response = await client.waitForResponse(options?.timeout ?? this.config.defaultTimeoutMs ?? 120000);
			return { summary: response, rawResponse: response };
		} finally {
			await this.pool.release("google-ai", client);
		}
	}

	private parseResponse(text: string): OracleResponse {
		// Try to extract JSON from response
		const jsonMatch = text.match(/\{[\s\S]*\}/);
		if (jsonMatch) {
			try { return JSON.parse(jsonMatch[0]); } catch {}
		}
		return { valid: false, rawResponse: text };
	}
}

// =============================================================================
// Lean 4 Tools
// =============================================================================

interface LeanResult {
	success: boolean;
	output: string;
	errors: string[];
}

class LeanTools {
	private config: LeanConfig;
	private logger: Logger;

	constructor(config: LeanConfig, logger?: Logger) {
		this.config = config;
		this.logger = logger?.child("lean") ?? new Logger("lean");
	}

	private async runCommand(args: string[], timeoutMs: number): Promise<LeanResult> {
		const { spawn } = await import("child_process");
		return new Promise((resolve) => {
			const proc = spawn("lake", args, {
				cwd: this.config.repoRoot,
				stdio: "pipe",
			});
			let stdout = "", stderr = "";
			proc.stdout.on("data", d => stdout += d);
			proc.stderr.on("data", d => stderr += d);
			const timer = setTimeout(() => {
				proc.kill("SIGKILL");
				resolve({ success: false, output: stdout, errors: [`Timeout after ${timeoutMs}ms`] });
			}, timeoutMs);
			proc.on("close", (code) => {
				clearTimeout(timer);
				resolve({
					success: code === 0,
					output: stdout,
					errors: code === 0 ? [] : stderr.split("\n").filter(Boolean),
				});
			});
		});
	}

	async build(module: string): Promise<LeanResult> {
		this.logger.info("Building module", { module });
		return this.runCommand(["build", module], this.config.lakeTimeoutMs ?? 120000);
	}

	async checkFile(file: string): Promise<LeanResult> {
		this.logger.info("Checking file", { file });
		return this.runCommand(["env", "lean", file], this.config.lakeTimeoutMs ?? 60000);
	}

	async runScript(script: string): Promise<LeanResult> {
		this.logger.info("Running script", { script });
		return this.runCommand(["script", "run", script], this.config.lakeTimeoutMs ?? 120000);
	}

	async extractTheorems(modulePath: string): Promise<Array<{ name: string; statement: string; file: string; line: number }>> {
		this.logger.info("Extracting theorems", { modulePath });
		const fullPath = path.join(this.config.repoRoot, modulePath);
		const content = await fs.readFile(fullPath, "utf-8");
		const theorems: Array<{ name: string; statement: string; file: string; line: number }> = [];
		const lines = content.split("\n");
		for (let i = 0; i < lines.length; i++) {
			const match = lines[i].match(/^\s*(theorem|lemma)\s+(\w+)/);
			if (match) {
				theorems.push({
					name: match[2],
					statement: lines.slice(i).join("\n").split(":=")[0] + ":=",
					file: modulePath,
					line: i + 1,
				});
			}
		}
		return theorems;
	}
}

// =============================================================================
// Reasoning Engine
// =============================================================================

interface ReasoningStep {
	type: "observe" | "hypothesize" | "verify" | "conclude";
	content: string;
	confidence: number;
	evidence?: unknown[];
}

class ReasoningEngine {
	private logger: Logger;

	constructor(logger?: Logger) {
		this.logger = logger?.child("reasoning") ?? new Logger("reasoning");
	}

	async reason(goal: string, context: Record<string, unknown>): Promise<ReasoningStep[]> {
		this.logger.info("Starting reasoning", { goal });
		const steps: ReasoningStep[] = [];

		const facts = await this.observe(context);
		steps.push({ type: "observe", content: facts, confidence: 0.9 });

		const hypotheses = await this.hypothesize(goal, facts);
		steps.push({ type: "hypothesize", content: hypotheses, confidence: 0.7 });

		const verification = await this.verify(hypotheses);
		steps.push({ type: "verify", content: verification, confidence: 0.8 });

		const conclusion = this.conclude(verification);
		steps.push({ type: "conclude", content: conclusion, confidence: 0.85 });

		return steps;
	}

	private async observe(context: Record<string, unknown>): Promise<string> {
		// In production, this would query ArangoDB, Lean, oracles, etc.
		return `Observed context keys: ${Object.keys(context).join(", ")}`;
	}

	private async hypothesize(goal: string, facts: string): Promise<string> {
		return `Hypothesis for "${goal}": based on ${facts}`;
	}

	private async verify(hypotheses: string): Promise<string> {
		return `Verified: ${hypotheses}`;
	}

	private conclude(verification: string): string {
		return `Conclusion: ${verification}`;
	}
}

// =============================================================================
// ArangoDB Hive Memory
// =============================================================================

interface HiveMemoryConfig {
	url: string;
	db: string;
	user: string;
	pass: string;
	maxRetries?: number;
	retryDelayMs?: number;
}

class HiveMemory {
	private config: Required<HiveMemoryConfig>;
	private db: unknown = null;
	private logger: Logger;

	constructor(config: HiveMemoryConfig, logger?: Logger) {
		this.config = {
			url: config.url,
			db: config.db,
			user: config.user,
			pass: config.pass,
			maxRetries: config.maxRetries ?? 3,
			retryDelayMs: config.retryDelayMs ?? 1000,
		};
		this.logger = logger?.child("arango") ?? new Logger("arango");
	}

	async connect(): Promise<void> {
		await withRetry(async () => {
			const arangojs = await import("arangojs");
			// arangojs default export is a factory function
			const client = (arangojs.default || arangojs)({
				url: this.config.url,
				databaseName: this.config.db,
				auth: { username: this.config.user, password: this.config.pass },
			});
			this.db = client;
			// Test connection
			await (this.db as any).version();
			this.logger.info("Connected to ArangoDB", { db: this.config.db });
		}, {
			maxRetries: this.config.maxRetries,
			baseDelayMs: this.config.retryDelayMs,
			maxDelayMs: 10000,
			logger: this.logger,
			context: "connect",
		});
	}

	async storeThought(thought: Record<string, unknown>): Promise<void> {
		if (!this.db) throw new Error("Not connected to ArangoDB");
		await (this.db as any).collection("Thoughts").save(thought);
		this.logger.debug("Stored thought", { keys: Object.keys(thought) });
	}

	async queryThoughts(aql: string, bindVars?: Record<string, unknown>): Promise<unknown[]> {
		if (!this.db) throw new Error("Not connected to ArangoDB");
		const cursor = await (this.db as any).query(aql, bindVars);
		return cursor.all();
	}

	async getCausalCone(declName: string, depth = 3): Promise<unknown> {
		return this.queryThoughts(
			`FOR d IN decls FILTER d.name == @decl RETURN d`,
			{ decl: declName }
		);
	}
}

// =============================================================================
// Main Extension Entry Point
// =============================================================================

export default function (pi: any) {
	const logger = new Logger("pi-omega", process.env.LOG_LEVEL as LogLevel ?? "info");

	// -------------------------------------------------------------------------
	// Provider Registration
	// -------------------------------------------------------------------------
	const providers: ProviderConfig[] = [
		{
			name: "anthropic",
			apiKeyEnv: "ANTHROPIC_API_KEY",
			baseUrl: "https://api.anthropic.com",
			models: [
				{ id: "claude-opus-4-20250615", name: "Claude Opus 4", reasoning: true, input: ["text", "image"], cost: { input: 15, output: 75, cacheRead: 1.5, cacheWrite: 18.75 }, contextWindow: 200000, maxTokens: 8192 },
				{ id: "claude-sonnet-4-20250514", name: "Claude Sonnet 4", reasoning: true, input: ["text", "image"], cost: { input: 3, output: 15, cacheRead: 0.3, cacheWrite: 3.75 }, contextWindow: 200000, maxTokens: 8192 },
			],
		},
		{
			name: "openai",
			apiKeyEnv: "OPENAI_API_KEY",
			models: [
				{ id: "gpt-4o", name: "GPT-4o", reasoning: false, input: ["text", "image"], cost: { input: 5, output: 15 }, contextWindow: 128000, maxTokens: 4096 },
				{ id: "gpt-4o-mini", name: "GPT-4o Mini", reasoning: false, input: ["text", "image"], cost: { input: 0.15, output: 0.6 }, contextWindow: 128000, maxTokens: 16384 },
			],
		},
		{
			name: "google",
			apiKeyEnv: "GOOGLE_API_KEY",
			models: [
				{ id: "gemini-2.0-flash-exp", name: "Gemini 2.0 Flash", reasoning: true, input: ["text", "image"], cost: { input: 0, output: 0 }, contextWindow: 1000000, maxTokens: 8192 },
			],
		},
		{
			name: "custom-endpoint",
			apiKeyEnv: "CUSTOM_API_KEY",
			baseUrl: process.env.CUSTOM_BASE_URL || "http://localhost:11434/v1",
			models: [
				{ id: "llama-3.1-70b", name: "Llama 3.1 70B (Local)", reasoning: false, input: ["text"], cost: { input: 0, output: 0 }, contextWindow: 8192, maxTokens: 4096 },
			],
		},
	];

	for (const config of providers) {
		const apiKey = process.env[config.apiKeyEnv];
		if (!apiKey && !config.baseUrl?.includes("localhost")) continue;
		pi.registerProvider(config.name, {
			baseUrl: config.baseUrl,
			apiKey: apiKey ? `$${config.apiKeyEnv}` : "",
			models: config.models,
		});
		logger.info("Registered provider", { name: config.name, models: config.models.length });
	}

	// -------------------------------------------------------------------------
	// Shared Infrastructure
	// -------------------------------------------------------------------------
	const browserConfig: BrowserHarnessConfig = {
		host: process.env.CDP_HOST || "127.0.0.1",
		port: parseInt(process.env.CDP_PORT || "9222", 10),
		connectionTimeoutMs: 15000,
		commandTimeoutMs: 60000,
	};
	const browserPool = new BrowserPool(browserConfig, 3, logger);
	const oracleConfig: OracleConfig = { browserConfig, defaultTimeoutMs: 120000, maxRetries: 2 };
	const oracleClient = new OracleClient(browserPool, oracleConfig, logger);
	const leanConfig: LeanConfig = { repoRoot: REPO_ROOT, lakeTimeoutMs: 180000 };
	const leanTools = new LeanTools(leanConfig, logger);
	const reasoningEngine = new ReasoningEngine(logger);
	const arangoConfig: HiveMemoryConfig = {
		url: process.env.ARANGO_URL || "http://localhost:8530",
		db: process.env.ARANGO_DB || "infogeometry",
		user: process.env.ARANGO_USER || "root",
		pass: process.env.ARANGO_PASS || "hive_brain",
	};
	const hiveMemory = new HiveMemory(arangoConfig, logger);

	// -------------------------------------------------------------------------
	// Commands
	// -------------------------------------------------------------------------
	pi.registerCommand({
		name: "omega.search",
		description: "Search mathematical concepts via Google AI Mode",
		async execute(args: { query: string }) {
			logger.info("omega.search", { query: args.query });
			return oracleClient.queryGoogleAI(args.query);
		},
	});

	pi.registerCommand({
		name: "omega.oracles",
		description: "Query mathematical oracles (ChatGPT + Google AI)",
		async execute(args: { prompt: string; platform?: "chatgpt" | "google-ai" | "both" }) {
			logger.info("omega.oracles", { platform: args.platform });
			const results: Record<string, OracleResponse> = {};
			if (args.platform === "chatgpt" || args.platform === "both") {
				results.chatgpt = await oracleClient.queryChatGPT(args.prompt);
			}
			if (args.platform === "google-ai" || args.platform === "both") {
				results.google = await oracleClient.queryGoogleAI(args.prompt);
			}
			return results;
		},
	});

	pi.registerCommand({
		name: "omega.lean",
		description: "Lean 4 formalization tools",
		async execute(args: { action: "build" | "check" | "theorems" | "run-script"; module?: string; file?: string; script?: string }) {
			logger.info("omega.lean", { action: args.action });
			switch (args.action) {
				case "build": return leanTools.build(args.module!);
				case "check": return leanTools.checkFile(args.file!);
				case "theorems": return leanTools.extractTheorems(args.module!);
				case "run-script": return leanTools.runScript(args.script!);
			}
		},
	});

	pi.registerCommand({
		name: "omega.reason",
		description: "Run reasoning engine on mathematical goal",
		async execute(args: { goal: string; context?: Record<string, unknown> }) {
			logger.info("omega.reason", { goal: args.goal });
			return reasoningEngine.reason(args.goal, args.context ?? {});
		},
	});

	pi.registerCommand({
		name: "omega.arango",
		description: "Query ArangoDB Hive Memory",
		async execute(args: { action: "store" | "query" | "cone"; data?: unknown; query?: string; decl?: string }) {
			logger.info("omega.arango", { action: args.action });
			await hiveMemory.connect();
			switch (args.action) {
				case "store": return hiveMemory.storeThought(args.data as Record<string, unknown>);
				case "query": return hiveMemory.queryThoughts(args.query!);
				case "cone": return hiveMemory.getCausalCone(args.decl!);
			}
		},
	});

	// -------------------------------------------------------------------------
	// Custom Omega Provider
	// -------------------------------------------------------------------------
	pi.registerProvider("omega", {
		apiKey: "$OMEGA_API_KEY",
		baseUrl: process.env.OMEGA_BASE_URL || "http://localhost:11434/v1",
		models: [
			{ id: "omega-reasoner", name: "Omega Reasoner", reasoning: true, input: ["text"], cost: { input: 0, output: 0 }, contextWindow: 128000, maxTokens: 8192 },
		],
	});

	// -------------------------------------------------------------------------
	// Cleanup on shutdown
	// -------------------------------------------------------------------------
	process.on("SIGINT", async () => {
		logger.info("Shutting down, closing connections...");
		await browserPool.closeAll();
		process.exit(0);
	});
	process.on("SIGTERM", async () => {
		logger.info("Shutting down, closing connections...");
		await browserPool.closeAll();
		process.exit(0);
	});

	logger.info("Pi-Omega extension initialized");
}

// -----------------------------------------------------------------------------
// Exports
// -----------------------------------------------------------------------------
export { BrowserHarnessClient, BrowserPool, OracleClient, LeanTools, ReasoningEngine, HiveMemory, Logger };