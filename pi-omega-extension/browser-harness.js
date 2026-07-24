/**
 * Browser Harness CDP Client
 * Low-level Chrome DevTools Protocol client for browser automation
 */

export interface CDPMessage {
	id: number;
	method?: string;
	params?: any;
	result?: any;
	error?: { code: number; message: string };
}

export interface BrowserHarnessConfig {
	wsUrl?: string;
	port?: number;
	host?: string;
}

export class BrowserHarnessClient {
	private ws: WebSocket | null = null;
	private messageId = 0;
	private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
	private config: BrowserHarnessConfig;

	constructor(config: BrowserHarnessConfig = {}) {
		this.config = {
			host: config.host || "127.0.0.1",
			port: config.port || 9222,
			...config,
		};
	}

	async connect(wsUrl?: string): Promise<void> {
		const targetUrl = wsUrl || await this.findTargetTab();
		
		this.ws = new WebSocket(targetUrl);
		
		await new Promise<void>((resolve, reject) => {
			const timeout = setTimeout(() => reject(new Error("Connection timeout")), 10000);
			
			this.ws!.onopen = () => {
				clearTimeout(timeout);
				resolve();
			};
			this.ws!.onerror = (err) => {
				clearTimeout(timeout);
				reject(err);
			};
			this.ws!.onmessage = (msg) => this.handleMessage(JSON.parse(msg.data.toString()));
		});

		// Enable Runtime domain
		await this.send({ id: this.nextId(), method: "Runtime.enable" });
		await this.send({ id: this.nextId(), method: "Page.enable" });
		await this.send({ id: this.nextId(), method: "Network.enable" });
	}

	private async findTargetTab(): Promise<string> {
		const res = await fetch(`http://${this.config.host}:${this.config.port}/json/list`);
		const targets = await res.json();
		
		// Try to find ChatGPT or Google AI tab
		const chatgpt = targets.find((t: any) => 
			t.url?.includes("chatgpt.com") && t.type === "page"
		);
		if (chatgpt) return chatgpt.webSocketDebuggerUrl;
		
		const googleAI = targets.find((t: any) => 
			t.url?.includes("google.com") && t.type === "page" &&
			(t.url.includes("ai") || t.url.includes("search"))
		);
		if (googleAI) return googleAI.webSocketDebuggerUrl;
		
		// Fallback to first page
		const page = targets.find((t: any) => t.type === "page");
		if (page) return page.webSocketDebuggerUrl;
		
		throw new Error("No suitable browser tab found");
	}

	private handleMessage(msg: any): void {
		if (msg.id && this.pending.has(msg.id)) {
			const { resolve, reject } = this.pending.get(msg.id)!;
			this.pending.delete(msg.id);
			
			if (msg.error) {
				reject(new Error(msg.error.message));
			} else {
				resolve(msg.result);
			}
		}
	}

	private nextId(): number {
		return ++this.messageId;
	}

	async send(msg: Omit<CDPMessage, "id">): Promise<any> {
		if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
			throw new Error("WebSocket not connected");
		}

		const id = ++this.messageId;
		const message: CDPMessage = { ...msg, id };

		return new Promise((resolve, reject) => {
			this.pending.set(id, { resolve, reject });
			this.ws!.send(JSON.stringify({ ...msg, id }));
			
			setTimeout(() => {
				if (this.pending.has(id)) {
					this.pending.delete(id);
					reject(new Error(`CDP timeout for ${msg.method}`));
				}
			}, 30000);
		});
	}

	async evaluate(expression: string, awaitPromise = true): Promise<any> {
		return this.send({
			method: "Runtime.evaluate",
			params: { 
				expression, 
				returnByValue: true, 
				awaitPromise,
				userGesture: true,
			},
		});
	}

	async callFunctionOn(objectId: string, functionDeclaration: string, args: any[] = []): Promise<any> {
		return this.send({
			method: "Runtime.callFunctionOn",
			params: {
				objectId,
				functionDeclaration,
				arguments: args.map(v => ({ value: v })),
				returnByValue: true,
				awaitPromise: true,
			},
		});
	}

	async getDocument(): Promise<any> {
		const result = await this.evaluate("document.documentElement.outerHTML");
		return result.result?.value;
	}

	async click(selector: string): Promise<void> {
		await this.evaluate(`
			const el = document.querySelector(${JSON.stringify(selector)});
			if (el) el.click();
		`);
	}

	async type(selector: string, text: string): Promise<void> {
		await this.evaluate(`
			const el = document.querySelector(${JSON.stringify(selector)});
			if (el) {
				el.focus();
				el.value = ${JSON.stringify(text)};
				el.dispatchEvent(new Event('input', {bubbles: true}));
			}
		`);
	}

	async waitForSelector(selector: string, timeout = 10000): Promise<boolean> {
		const start = Date.now();
		while (Date.now() - start < timeout) {
			const exists = await this.evaluate(`!!document.querySelector(${JSON.stringify(selector)})`);
			if (exists.result?.value) return true;
			await new Promise(r => setTimeout(r, 100));
		}
		return false;
	}

	async sendKeys(keys: string): Promise<void> {
		await this.send({
			method: "Input.dispatchKeyEvent",
			params: {
				type: "keyDown",
				key: keys,
				code: keys,
				keyCode: keys.charCodeAt(0),
			},
		});
		await this.send({
			method: "Input.dispatchKeyEvent",
			params: {
				type: "keyUp",
				key: keys,
				code: keys,
				keyCode: keys.charCodeAt(0),
			},
		});
	}

	async screenshot(): Promise<string> {
		const result = await this.send({
			method: "Page.captureScreenshot",
			params: { format: "png", fromSurface: true },
		});
		return result.result?.data;
	}

	async close(): Promise<void> {
		if (this.ws) {
			this.ws.close();
			this.ws = null;
		}
	}
}

// Simple message-based client for Chrome extension communication
export class ChromeExtensionClient {
	private port: chrome.runtime.Port | null = null;

	async connect(extensionId: string): Promise<void> {
		return new Promise((resolve, reject) => {
			this.port = chrome.runtime.connect(extensionId);
			this.port.onDisconnect.addListener(() => reject(new Error("Port disconnected")));
			
			this.port.onMessage.addListener((msg) => {
				if (msg.type === "ready") resolve();
			});
			
			this.port.postMessage({ type: "init" });
			
			setTimeout(() => reject(new Error("Connection timeout")), 5000);
		}
	}

	async send(message: any): Promise<any> {
		if (!this.port) throw new Error("Not connected");
		
		return new Promise((resolve, reject) => {
			const id = Math.random().toString(36).slice(2);
			const listener = (msg: any) => {
				if (msg.id === id) {
					this.port!.onMessage.removeListener(listener);
					if (msg.error) reject(new Error(msg.error));
					else resolve(msg.result);
				}
			};
			this.port!.onMessage.addListener(listener);
			this.port!.postMessage({ ...message, id });
			setTimeout(() => reject(new Error("Timeout")), 30000);
		});
	}

	disconnect(): void {
		this.port?.disconnect();
		this.port = null;
	}
}

// Utility functions
export async function waitForCondition(
	check: () => Promise<boolean>,
	timeout = 10000,
	interval = 200
): Promise<boolean> {
	const start = Date.now();
	while (Date.now() - start < timeout) {
		if (await check()) return true;
		await new Promise(r => setTimeout(r, interval));
	}
	return false;
}

export function createCDPClient(config?: BrowserHarnessConfig): BrowserHarnessClient {
	return new BrowserHarnessClient(config);
}

// Export main class
export { BrowserHarnessClient as default };