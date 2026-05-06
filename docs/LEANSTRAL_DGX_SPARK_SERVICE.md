# Leanstral GGUF and Mistral-family DGX Spark resident services

This repo uses local Mistral-family models as proposal engines. They do not
replace Lean, `lake build`, Hive promotion gates, LeanParanoia, SafeVerify, or
multi-checker reports.

## Recommended current default: Leanstral GGUF

The practical quantized Leanstral route is:

```text
jackcloudman/Leanstral-2603-GGUF
mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf
served model name: leanstral-gguf
backend: llama-server / llama.cpp
```

The Hugging Face model card lists Q4_K_M at about 68 GB, Q8_0 at about 118 GB,
and recommends `llama-server` with `-fit on`, flash attention, Jinja chat
template support, and a template that supports `[THINK]` blocks.

## Files

- `tools/infra/leanstral_gguf_llama_service.sh` launches the GGUF Leanstral
  model through `llama-server`.
- `systemd/user/leanstral-gguf-llama.service` is the user-systemd template for
  the GGUF path.
- `tools/infra/leanstral_vllm_service.sh` launches the official Mistral Small 4
  NVFP4 checkpoint through vLLM as a fallback Mistral-family resident.
- `tools/infra/qwen_vllm_service.sh` is a compatibility wrapper that starts the
  vLLM Mistral-family launcher.

## Download GGUF model

```bash
mkdir -p /home/goutev/models/Leanstral-2603-GGUF
hf download jackcloudman/Leanstral-2603-GGUF \
  mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf \
  --local-dir /home/goutev/models/Leanstral-2603-GGUF
```

Download or provide a Leanstral-compatible chat template:

```bash
# Example target path used by the service template:
/home/goutev/models/Leanstral-2603-GGUF/chat_template.jinja
```

If Hugging Face auth is needed, put tokens in the local environment file, never
in repo scripts:

```text
~/.config/info-geometry-lean/leanstral.env
```

Example:

```bash
HF_TOKEN=...
HUGGING_FACE_HUB_TOKEN=...
```

## Install GGUF user service

```bash
mkdir -p ~/.config/systemd/user
cp systemd/user/leanstral-gguf-llama.service ~/.config/systemd/user/leanstral-gguf-llama.service
systemctl --user daemon-reload
systemctl --user enable --now leanstral-gguf-llama.service
```

Inspect logs:

```bash
journalctl --user -u leanstral-gguf-llama.service -f
```

Check OpenAI-compatible endpoint:

```bash
curl http://127.0.0.1:18789/v1/models
```

## GGUF defaults

```text
model path: /home/goutev/models/Leanstral-2603-GGUF/mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf
served model name: leanstral-gguf
port: 18789
context size: 128000
parallel: 1
gpu layers: -1
flash attention: on
fit/offload: on
```

Override in `~/.config/info-geometry-lean/leanstral.env`:

```bash
LEANSTRAL_GGUF_MODEL=/path/to/model.gguf
LEANSTRAL_GGUF_CHAT_TEMPLATE=/path/to/chat_template.jinja
LEANSTRAL_GGUF_CTX_SIZE=65536
LEANSTRAL_GGUF_PORT=18789
```

## vLLM NVFP4 fallback

If the GGUF path is not stable, use the official NVFP4 Mistral-family checkpoint:

```text
mistralai/Mistral-Small-4-119B-2603-NVFP4
served model name: mistral-small-4-nvfp4
backend: vLLM
```

The vLLM fallback launcher encodes the DGX Spark / GB10 quirks reported by
operators running this checkpoint locally:

```text
attention backend: TRITON_MLA
FlashInfer autotune: disabled
CUDA arch list: 12.1a
TRITON_PTXAS_PATH: /usr/local/cuda/bin/ptxas
VLLM_SKIP_P2P_CHECK: 1
CUDA graph capture sizes: 1 2 4 8 16 32 64 128 256
max CUDA graph capture size: 256
```

Why these defaults matter:

- `TRITON_MLA` avoids SM100-only FlashAttention/FlashInfer MLA kernels on the
  GB10's SM121 variant.
- disabling FlashInfer autotune avoids long startup stalls from failed tactics
  on SM121.
- bounded CUDA graph capture sizes reduce startup and memory overhead for
  personal/small-team use.

Install service template:

```bash
cp systemd/user/leanstral-vllm.service ~/.config/systemd/user/leanstral-vllm.service
systemctl --user daemon-reload
systemctl --user enable --now leanstral-vllm.service
```

Do not run both services on port `18789` at the same time.

### Mistral parser compatibility

Mistral-family tool calls and reasoning blocks require a sufficiently recent vLLM
parser surface. The relevant upstream fixes are:

- vLLM PR `38150`: injects Mistral grammar constraints through the structured
  output path for grammar-capable Mistral tokenizers.
- vLLM PR `39217`: fixes the serving layer so grammar-constrained Mistral output
  is parsed by `MistralToolParser`, and so `[TOOL_CALLS]`/reasoning content do
  not fall through the generic parser path.

Before using the vLLM fallback for agent/tool work, run:

```bash
lake script run checkVllmMistralCompat
```

The checker verifies that `vllm serve --help` exposes:

```text
--tool-call-parser
--enable-auto-tool-choice
--reasoning-parser
```

and reports whether the DGX Spark fallback flags are available.

## Authority boundary

```text
Local model proposes.
Hive records provenance.
Lean checks truth.
Audit gates decide promotion.
```
