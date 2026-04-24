# Nemotron Nano 3 via vLLM on DGX Spark / GB10

Status: disabled by default in this workspace.

## Reason

Recent local audit plus linked community reports indicate that the current
`Nemotron-3-Nano-30B` + `vLLM` path on DGX Spark / GB10 is not a reliable default
planner lane here.

Observed locally:
- repo configs expected Nemotron on `127.0.0.1:30000/v1`
- the historical launcher used a different port/model exposure path
- direct startup attempts did not produce a healthy local API endpoint during the
  test window

Community evidence cited by the operator points to a stronger backend diagnosis:
- Nemotron Nano 3 NVFP4 is currently disabled in at least one DGX Spark
  community stack due to incompatibility with the current vLLM build on GB10
- this appears to require proper V1 engine support or updated backend support

## Current local policy

- do not assume Nemotron Nano 3 via vLLM is available on this host
- do not auto-route planner traffic to that lane without an explicit health check
- treat any manual vLLM Nemotron bring-up as experimental

## Launcher behavior

`/home/goutev/bin/start-nemotron3-vllm.sh` now fails closed by default.

To force an experimental launch anyway:

```bash
NEMOTRON_ALLOW_UNSUPPORTED_VLLM=1 /home/goutev/bin/start-nemotron3-vllm.sh
```

## Suggested alternatives

- use the working local proof/audit lanes already running on this host
- use a community DGX Spark stack that carries GB10-specific vLLM patches/tests
- use a non-vLLM Nemotron path only after confirming healthy model load,
  `/health`, `/v1/models`, and a tiny completion request
