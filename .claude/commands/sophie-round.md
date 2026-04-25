Run the next round of the current Sophie session.

1. Call `get_round_tasks` with no arguments — the server reads `sessions/current.json` to resolve the session automatically. Only call `list_sessions` if `get_round_tasks` returns an error (no current session found), then ask the user which session to use.
2. If `should_stop=true`, report the final status and stop.
3. If `resumed=true`, note which agents already completed (`agents_completed`) and skip straight to the first name in `agents_pending`.
4. For each agent name in `agents_pending`, work through them one at a time:

   **a. Fetch the task**
   Call `get_agent_task(agent_name)` to get the `system_prompt` and `user_message` for that agent.

   **b. Act as the agent**

   **Researcher tasks (agent = "Researcher"):**
   Before producing any JSON, actively use your WebSearch and WebFetch tools to research
   the conjecture and open subproblems. Issue at least 2–3 distinct search queries and
   fetch at least one promising page. Only after gathering results, compile your findings
   into the required JSON format and output it.

   **All other agent tasks:**
   Output only valid JSON matching the agent's required format. Do not add prose before
   or after the JSON block.

   **c. Submit immediately**
   Call `submit_agent_result(agent_name, response_json)` right away — do not wait until
   all agents are done. The result is persisted immediately so a token-exhaustion restart
   can resume from this point. Check `round_complete` in the response — if `true`, the
   round has been finalized automatically.

5. After all agents have submitted (or `round_complete=true` is returned), call `refresh_viewer` with the session_id.
6. Report a brief summary of what happened this round and suggest running `/sophie-round` again to continue.

**Resuming after token exhaustion:** If a previous run was interrupted mid-round,
`get_round_tasks` will return `resumed=true` with `agents_completed` (already done) and
`agents_pending` (still to go). Simply continue from step 4 with the pending agents —
the KB already contains the completed agents' contributions.
