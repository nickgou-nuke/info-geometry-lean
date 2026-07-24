#!/usr/bin/env node
/**
 * Pi-Omega Extension Demo
 * Demonstrates multi-provider LLM + Browser Harness + Oracle + Lean 4
 */

import { BrowserHarnessClient } from "./browser-harness.js";
import { LeanTools } from "./index.js";
import { ReasoningEngine } from "./index.js";
import { HiveMemory } from "./index.js";

async function demo() {
	console.log("🚀 Pi-Omega Extension Demo");
	console.log("=".repeat(50));

	// 1. Test Lean 4 build
	console.log("\n📐 Testing Lean 4 build...");
	const lean = new LeanTools();
	const buildResult = await lean.build("InfoGeometry.Algebra.StructureConstants");
	console.log(`   Build: ${buildResult.success ? "✅ PASS" : "❌ FAIL"}`);
	if (!buildResult.success) {
		console.log(`   Errors: ${buildResult.errors.slice(0, 3).join("\n   ")}`);
	}

	// 2. Test Lean file check
	console.log("\n🔍 Checking Lean file...");
	const checkResult = await lean.checkFile("lean/InfoGeometry/Algebra/StructureConstants.lean");
	console.log(`   Check: ${checkResult.success ? "✅ PASS" : "❌ FAIL"}`);

	// 3. Test reasoning engine
	console.log("\n🧠 Running reasoning engine...");
	const engine = new ReasoningEngine();
	const steps = await engine.reason(
		"Prove that f_antisym_ab holds for su(3) structure constants",
		{ module: "InfoGeometry.Algebra.StructureConstants" }
	);
	console.log(`   Reasoning steps: ${steps.length}`);
	for (const step of steps) {
		console.log(`   [${step.type}] ${step.content.slice(0, 80)}...`);
	}

	// 4. Test Browser Harness (if Chrome is running)
	console.log("\n🌐 Testing Browser Harness...");
	try {
		const browser = new BrowserHarnessClient();
		await browser.connect();
		console.log("   ✅ Connected to Chrome CDP");
		
		// Simple test
		const title = await browser.evaluate("document.title");
		console.log(`   Page title: ${title.result?.value}`);
		
		await browser.close();
	} catch (e) {
		console.log(`   ⚠️ Browser not available: ${e.message}`);
	}

	// 5. Test Hive Memory (if ArangoDB is running)
	console.log("\n🧠 Testing Hive Memory...");
	try {
		const hive = new HiveMemory({
			url: process.env.ARANGO_URL || "http://localhost:8530",
			db: process.env.ARANGO_DB || "infogeometry",
			user: process.env.ARANGO_USER || "root",
			pass: process.env.ARANGO_PASS || "hive_brain",
		});
		await hive.connect();
		const result = await hive.getCausalCone("InfoGeometry.Algebra.StructureConstants.f_antisym_ab");
		console.log("   ✅ Connected to Hive Memory");
		console.log(`   Causal cone: ${JSON.stringify(result).slice(0, 100)}...`);
	} catch (e) {
		console.log(`   ⚠️ ArangoDB not available: ${(e as Error).message}`);
	}

	// 6. Test Lean theorem extraction
	console.log("\n📚 Extracting Lean theorems...");
	const lean = new (await import("./index.js")).LeanTools();
	const theorems = await lean.extractTheorems("lean/InfoGeometry/Algebra/StructureConstants.lean");
	console.log(`   Found ${theorems.length} theorems`);
	for (const t of theorems.slice(0, 5)) {
		console.log(`   - ${t.name} (line ${t.line})`);
	}

	console.log("\n✅ Demo complete!");
}

// Run demo
main().catch(console.error);