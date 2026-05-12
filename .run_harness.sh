#!/bin/bash
export CHATGPT_PROMPT_FILE=.tmp_chatgpt_prompt.txt
export CHATGPT_RESULT_JSON=.tmp_chatgpt_result.json
browser-harness -c "$(cat tools/infra/chatgpt_browser_harness_driver.py)"
