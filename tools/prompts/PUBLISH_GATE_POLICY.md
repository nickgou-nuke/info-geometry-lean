# Publish Gate Policy Contract

Effective date: **2026-04-12**

Publish capabilities are deny-by-default.

## Gate Rules

1. Two-key approval is mandatory for any outbound internet write.
2. Key 1: human.
3. Key 2: policy_engine.
4. Default policy is deny for publish.

## Outbound Internet Write (Examples)

- Posting comments to external platforms.
- Creating or updating public blog content.
- Any tool action that modifies remote, public-facing state.

## Approval Record

Each publish action must record:
- goal id
- tool id
- human approval token
- policy approval token
- timestamp
