Run the next round of the current Sophie session.

1. Call `get_round_tasks` with no arguments — the server reads `sessions/current.json` to resolve the session automatically. Only call `list_sessions` if `get_round_tasks` returns an error (no current session found), then ask the user which session to use.
2. If `should_stop=true` or `resolved=true`, report the final status and stop.
3. For each task in the round, read its `system_prompt` and `user_message`, then act as that agent:

   **Researcher tasks (agent = "Researcher"):**
   Before producing any JSON, actively use your WebSearch and WebFetch tools to research
   the conjecture and open subproblems. Issue at least 2–3 distinct search queries and
   fetch at least one promising page. Only after gathering results, compile your findings
   into the required JSON format and output it.

   **All other agent tasks:**
   Output only valid JSON matching the agent's required format. Do not add prose before
   or after the JSON block.

4. Collect all task results into a single results array.
5. Call `submit_round_results` with the session_id, round number, and results JSON.
6. Call `refresh_viewer` with the session_id.
7. Report a brief summary of what happened this round and suggest running `/sophie-round` again to continue.
