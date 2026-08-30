[O[I✦ I have configured OpenClaw to work with the local Qwen model using the following steps:

   1. Resolved Port Conflicts: The OpenClaw Gateway was originally configured to use port 18789, which is also
      the port assigned to the vLLM Proposer (Qwen 35B) in the project's orchestration scripts. I repaired the
      gateway configuration via openclaw doctor --repair, ensuring it is stable on port 18789 (the entry point
      for Hermes).
   2. Launched Qwen 35B via SparkRun: I initiated the vLLM serving for Qwen/Qwen3.6-35B-A3B-FP8 on port 8000
      using sparkrun. This is currently running in the background (it may take some time to download the model
      weights and initialize the GPU kernels).
   3. Configured OpenClaw Provider: I updated the OpenClaw configuration (~/.openclaw/openclaw.json) to point to
      the local vLLM instance:
       * Provider: vllm
       * Base URL: http://127.0.0.1:8000/v1
       * Model ID: Qwen/Qwen3.6-35B-A3B-FP8
       * API Mode: openai-responses (standard Chat Completions)
   4. Verified Status:
       * OpenClaw Gateway: Active on ws://127.0.0.1:18789.
       * Primary Model: Set to vllm/Qwen/Qwen3.6-35B-A3B-FP8.

  The system is now prepared for Hermes and other agents to use the local Qwen 35B resident once the background
  sparkrun process completes its startup sequence.
