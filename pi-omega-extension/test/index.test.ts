import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { BrowserHarnessClient, BrowserPool, LeanTools, ReasoningEngine, Logger } from "../dist/index.js";

describe("BrowserHarnessClient", () => {
	let client: BrowserHarnessClient;

	beforeEach(() => {
		client = new BrowserHarnessClient({ host: "127.0.0.1", port: 9222 });
		vi.clearAllMocks();
	});

	it("constructs with default config", () => {
		expect(client).toBeDefined();
		expect(client.isConnected()).toBe(false);
	});

	it("throws on send when not connected", async () => {
		await expect(client.send({ method: "Test" })).rejects.toThrow("WebSocket not connected");
	});
});

describe("BrowserPool", () => {
	let pool: BrowserPool;

	beforeEach(() => {
		pool = new BrowserPool({ host: "127.0.0.1", port: 9222 }, 2);
	});

	afterEach(async () => {
		await pool.closeAll();
	});

	it("creates pool with max size", () => {
		expect(pool).toBeDefined();
	});

	it("getStats returns pool statistics", () => {
		const stats = pool.getStats();
		expect(stats).toBeDefined();
		expect(typeof stats).toBe("object");
	});
});

describe("LeanTools", () => {
	let leanTools: LeanTools;

	beforeEach(() => {
		leanTools = new LeanTools({ repoRoot: "/tmp/test" });
		vi.clearAllMocks();
	});

	it("constructs with config", () => {
		expect(leanTools).toBeDefined();
	});

	it("has all required methods", () => {
		expect(typeof leanTools.build).toBe("function");
		expect(typeof leanTools.checkFile).toBe("function");
		expect(typeof leanTools.runScript).toBe("function");
		expect(typeof leanTools.extractTheorems).toBe("function");
	});
});

describe("ReasoningEngine", () => {
	let engine: ReasoningEngine;

	beforeEach(() => {
		engine = new ReasoningEngine();
	});

	it("returns 4-step reasoning pipeline", async () => {
		const steps = await engine.reason("test goal", { key: "value" });
		expect(steps).toHaveLength(4);
		expect(steps[0].type).toBe("observe");
		expect(steps[1].type).toBe("hypothesize");
		expect(steps[2].type).toBe("verify");
		expect(steps[3].type).toBe("conclude");
	});

	it("includes confidence scores", async () => {
		const steps = await engine.reason("test goal", {});
		steps.forEach(step => {
			expect(step.confidence).toBeGreaterThan(0);
			expect(step.confidence).toBeLessThanOrEqual(1);
		});
	});
});

describe("Logger", () => {
	let logger: Logger;
	let stdoutSpy: any;
	let stderrSpy: any;

	beforeEach(() => {
		logger = new Logger("test", "debug");
		stdoutSpy = vi.spyOn(process.stdout, "write").mockImplementation(() => true);
		stderrSpy = vi.spyOn(process.stderr, "write").mockImplementation(() => true);
	});

	afterEach(() => {
		stdoutSpy.mockRestore();
		stderrSpy.mockRestore();
	});

	it("logs at different levels", () => {
		logger.debug("debug message");
		logger.info("info message");
		logger.warn("warn message");
		logger.error("error message");

		expect(stdoutSpy).toHaveBeenCalledTimes(2); // debug, info
		expect(stderrSpy).toHaveBeenCalledTimes(2); // warn, error
	});

	it("respects min log level", () => {
		const warnLogger = new Logger("test", "warn");
		warnLogger.debug("should not appear");
		warnLogger.info("should not appear");
		warnLogger.warn("should appear");
		warnLogger.error("should appear");

		const calls = [...stdoutSpy.mock.calls, ...stderrSpy.mock.calls].filter((c: any) => c[0].includes("should appear"));
		expect(calls.length).toBe(2);
	});

	it("creates child loggers", () => {
		const child = logger.child("subcomponent");
		expect(child).toBeDefined();
		child.info("child message");
		expect(stdoutSpy).toHaveBeenCalledWith(expect.stringContaining("test:subcomponent"));
	});
});