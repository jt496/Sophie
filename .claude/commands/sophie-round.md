Run the next round of the current Sophie session.

1. Call `get_round_tasks` with no arguments — the server reads `sessions/current.json` to resolve the session automatically. Only call `list_sessions` if `get_round_tasks` returns an error (no current session found), then ask the user which session to use.
2. Call `get_round_tasks` to get the tasks for the current round
3. If `should_stop=true` or `resolved=true`, report the final status and stop
4. For each task in the round, read its `system_prompt` and `user_message`, then respond AS that agent — output only valid JSON matching the agent's required format
5. Collect all task results into a single results array
6. Call `submit_round_results` with the session_id, round number, and results JSON
7. Call `refresh_viewer` with the session_id
8. Report a brief summary of what happened this round and suggest running `/sophie-round` again to continue
