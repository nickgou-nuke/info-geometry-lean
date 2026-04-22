# Twin Möbius Tape Transformer Python Prototype

## Status

Prototype note, Python/runtime layer.

This document gives a concrete software skeleton for implementing the Twin
Möbius Tape Transformer as a runtime wrapper around standard frozen transformer
models.

The design goal is to validate the memory geometry before attempting invasive
model changes.

---

## 1. Prototype target

Build a runtime with:

- two equal transformer branches,
- two equal active windows,
- two equal cache-bearing branch states,
- cross-branch transport of expired stream slices,
- branchwise inference,
- fused output,
- optional self-feedback and multimodal extension.

This first prototype should use:

- standard frozen open-weight models,
- prompt/text-level transport between branches,
- minimal cache hacking,
- simple weighted output fusion.

---

## 2. Recommended stack

### Model families

Good initial candidates:

- Mistral-family,
- LLaMA-family,
- Qwen-family.

Prefer models with:

- stable local inference APIs,
- straightforward generation loops,
- manageable KV-cache behavior,
- easy hidden-state/logit access.

### Python libraries

Recommended initial stack:

- `transformers`
- `torch`
- optional serving/runtime wrapper depending on deployment target

Do not begin with highly optimized custom kernels. Start with clarity.

---

## 3. Runtime objects

### 3.1 StreamSlice

A single unit of stream transport.

```python
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

@dataclass
class StreamSlice:
    content: str
    source_tag: str
    branch_tag: str
    timestamp: float
    saliency: float = 1.0
    metadata: Dict[str, Any] = field(default_factory=dict)
```

Typical `source_tag` values:

- `world`
- `self`
- `memory`
- `retrieval`
- `image`
- `audio`

Typical `branch_tag` values:

- `plus`
- `minus`

---

### 3.2 TransportEvent

Represents cross-branch movement.

```python
@dataclass
class TransportEvent:
    source_branch: str
    target_branch: str
    original_slice: StreamSlice
    transported_slice: StreamSlice
    transport_name: str
    timestamp: float
```

---

### 3.3 BranchState

Holds the state of one branch.

```python
@dataclass
class BranchState:
    name: str
    active_window: List[StreamSlice] = field(default_factory=list)
    residual_queue: List[StreamSlice] = field(default_factory=list)
    summary_memory: List[str] = field(default_factory=list)
    kv_cache: Optional[Any] = None
    last_hidden: Optional[Any] = None
    last_logits: Optional[Any] = None
```

Notes:

- `active_window` holds current live slices,
- `residual_queue` can store transported material waiting to be integrated,
- `summary_memory` stores compact stabilized context,
- `kv_cache` is optional in the first prototype.

---

### 3.4 FusionState

Stores output fusion diagnostics.

```python
@dataclass
class FusionState:
    alpha: float = 0.9
    beta: float = 0.1
    last_forward_score: Optional[float] = None
    last_backward_score: Optional[float] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
```

---

## 4. Core runtime class

```python
class TwinMoebiusRuntime:
    def __init__(
        self,
        forward_model,
        backward_model,
        tokenizer,
        window_size: int = 2048,
        alpha: float = 0.9,
        beta: float = 0.1,
    ):
        self.forward_model = forward_model
        self.backward_model = backward_model
        self.tokenizer = tokenizer
        self.window_size = window_size

        self.plus = BranchState(name="plus")
        self.minus = BranchState(name="minus")
        self.fusion = FusionState(alpha=alpha, beta=beta)

        self.transport_log: List[TransportEvent] = []
```

---

## 5. Active window management

### 5.1 Append new slice

```python
def append_to_branch(self, branch: BranchState, slice_: StreamSlice):
    branch.active_window.append(slice_)
```

### 5.2 Window overflow handling

```python
def enforce_window_bound(self, branch: BranchState):
    overflow = []
    while self.window_token_length(branch.active_window) > self.window_size:
        overflow.append(branch.active_window.pop(0))
    return overflow
```

### 5.3 Token-length estimate

```python
def window_token_length(self, slices: List[StreamSlice]) -> int:
    text = self.render_window(slices)
    return len(self.tokenizer.encode(text, add_special_tokens=False))
```

---

## 6. Rendering branch prompts

The first prototype should remain prompt/text based.

```python
def render_window(self, slices: List[StreamSlice]) -> str:
    parts = []
    for s in slices:
        parts.append(f"[{s.source_tag}:{s.branch_tag}] {s.content}")
    return "\n".join(parts)
```

```python
def build_branch_prompt(self, branch: BranchState) -> str:
    summary_block = "\n".join(branch.summary_memory[-8:])
    active_block = self.render_window(branch.active_window)

    return (
        "[SYSTEM] Twin Möbius Tape branch runtime\n"
        f"[BRANCH] {branch.name}\n"
        f"[SUMMARY]\n{summary_block}\n"
        f"[ACTIVE]\n{active_block}\n"
        "[TASK] Continue coherently from this branch state.\n"
    )
```

---

## 7. Cross-branch transport

### 7.1 Minimal transport map

The first version should be simple and stable.

```python
def gamma_plus_minus(self, slice_: StreamSlice) -> StreamSlice:
    return StreamSlice(
        content=slice_.content,
        source_tag=slice_.source_tag,
        branch_tag="minus",
        timestamp=slice_.timestamp,
        saliency=0.8 * slice_.saliency,
        metadata={**slice_.metadata, "transport": "gamma_plus_minus"},
    )
```

```python
def gamma_minus_plus(self, slice_: StreamSlice) -> StreamSlice:
    return StreamSlice(
        content=slice_.content,
        source_tag=slice_.source_tag,
        branch_tag="plus",
        timestamp=slice_.timestamp,
        saliency=0.8 * slice_.saliency,
        metadata={**slice_.metadata, "transport": "gamma_minus_plus"},
    )
```

### 7.2 Logging transport

```python
def transport_slice(self, source: BranchState, target: BranchState, slice_: StreamSlice, transport_fn, name: str):
    transported = transport_fn(slice_)
    target.residual_queue.append(transported)
    self.transport_log.append(
        TransportEvent(
            source_branch=source.name,
            target_branch=target.name,
            original_slice=slice_,
            transported_slice=transported,
            transport_name=name,
            timestamp=slice_.timestamp,
        )
    )
```

---

## 8. Residual integration

The first version should integrate residual slices conservatively.

```python
def integrate_residual_queue(self, branch: BranchState, max_items: int = 2):
    items = branch.residual_queue[:max_items]
    branch.residual_queue = branch.residual_queue[max_items:]
    branch.active_window.extend(items)
```

Later versions may:

- summarize residual slices,
- compress them,
- prioritize by saliency,
- convert them into memory summaries rather than raw active slices.

---

## 9. Branch inference

### 9.1 Forward call

```python
import torch

@torch.no_grad()
def run_branch(self, model, branch: BranchState):
    prompt = self.build_branch_prompt(branch)
    inputs = self.tokenizer(prompt, return_tensors="pt")
    outputs = model(**inputs, output_hidden_states=True, use_cache=True)

    branch.kv_cache = getattr(outputs, "past_key_values", None)
    branch.last_hidden = outputs.hidden_states[-1]
    branch.last_logits = outputs.logits[:, -1, :]
    return outputs
```

This is enough for the first prototype.

---

## 10. Output fusion

### 10.1 Logit fusion

Safest first fusion rule.

```python
def fuse_logits(self):
    lp = self.plus.last_logits
    lm = self.minus.last_logits
    return self.fusion.alpha * lp + self.fusion.beta * lm
```

### 10.2 Token selection

```python
def sample_fused_token(self, fused_logits):
    probs = torch.softmax(fused_logits, dim=-1)
    token_id = torch.argmax(probs, dim=-1)
    return token_id.item()
```

### 10.3 Decode

```python
def decode_token(self, token_id: int) -> str:
    return self.tokenizer.decode([token_id])
```

---

## 11. Main stream step

```python
def step(self, new_content: str, timestamp: float):
    new_slice = StreamSlice(
        content=new_content,
        source_tag="world",
        branch_tag="plus",
        timestamp=timestamp,
    )

    self.append_to_branch(self.plus, new_slice)

    overflow_plus = self.enforce_window_bound(self.plus)
    for s in overflow_plus:
        self.transport_slice(self.plus, self.minus, s, self.gamma_plus_minus, "gamma_plus_minus")

    self.integrate_residual_queue(self.minus, max_items=2)
    overflow_minus = self.enforce_window_bound(self.minus)
    for s in overflow_minus:
        self.transport_slice(self.minus, self.plus, s, self.gamma_minus_plus, "gamma_minus_plus")

    self.run_branch(self.forward_model, self.plus)
    self.run_branch(self.backward_model, self.minus)

    fused_logits = self.fuse_logits()
    token_id = self.sample_fused_token(fused_logits)
    token_text = self.decode_token(token_id)

    emitted = StreamSlice(
        content=token_text,
        source_tag="self",
        branch_tag="plus",
        timestamp=timestamp,
    )

    self.append_to_branch(self.plus, emitted)

    return token_text
```

This is enough to validate the geometry.

---

## 12. Self-feedback policy

Self-feedback should be conservative.

Recommended first rules:

- feed back only emitted summaries or stable chunks,
- do not feed back every token with full weight,
- tag all self-generated slices,
- damp self-generated saliency,
- allow operator-level reset.

A stronger self-loop can be explored only after runtime stability is confirmed.

---

## 13. Two-lane weak-value extension

Once the prototype is stable, add:

- separate branch confidence scores,
- compatibility gating between branch outputs,
- dynamic fusion coefficients,
- optional branch-specific query transformations,
- optional residual memory EMA update.

The prototype should not begin there.

---

## 14. Multimodal extension path

Generalize `StreamSlice.content` into a modality-aware payload.

```python
@dataclass
class StreamSlice:
    content: Any
    modality: str
    source_tag: str
    branch_tag: str
    timestamp: float
    saliency: float = 1.0
    metadata: Dict[str, Any] = field(default_factory=dict)
```

Then provide modality-specific renderers:

- text renderer,
- image-token renderer,
- audio-slice renderer,
- memory-bundle renderer.

The branch logic remains unchanged.

---

## 15. Logging and diagnostics

Track at least:

- branch window lengths,
- residual queue lengths,
- transport events per step,
- fusion coefficients,
- branch agreement score,
- self-generated fraction in each branch,
- repetition and loop indicators.

This is critical for catching resonance failure modes early.

---

## 16. Safety/stability rules

For the first prototype:

- cap active window sizes,
- cap residual queue sizes,
- decay transported saliency,
- limit self-feedback,
- keep branch fusion simple,
- avoid raw cross-branch KV injection,
- prefer transported slices and summaries over direct hidden-state surgery.

The first goal is to prove the runtime geometry is useful, not to maximize
recurrence complexity.

---

## 17. First milestone checklist

A successful first milestone should show:

- both branches stay live,
- expired forward slices reappear meaningfully in the backward branch,
- backward branch contributes nontrivially to fused output,
- the system remains stable across long stream runs,
- the runtime does not collapse into immediate repetition loops.

---

## 18. Summary

The Python prototype should begin as a plain runtime wrapper around two frozen
standard transformers.

The novelty is not in changing the transformer block. It is in:

- twin branch state,
- cross-branch transport,
- recirculating stream geometry,
- and fused present inference.

That is enough to validate the Möbius tape hypothesis before any deeper model
surgery is attempted.
