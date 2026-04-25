Run the next round of the current Sophie session.

If the user provided agent letters after the command (e.g. `/sophie-round CP`), pass
them as the `agents` argument to `get_round_tasks`.  The letters are:
  C=Checker  D=Disprover  E=Experimenter  F=Formalizer  P=Prover  R=Researcher  S=Searcher
If no letters were given, omit the `agents` argument and let the scheduler decide.

1. Call `get_round_tasks` — pass `agents="$ARGUMENTS"` if the user supplied letters, otherwise call with no arguments. The server reads `sessions/current.json` to resolve the session automatically. Only call `list_sessions` if `get_round_tasks` returns an error (no current session found), then ask the user which session to use.
2. If `should_stop=true`, report the final status and stop.
3. If `resumed=true`, note which agents already completed (`agents_completed`) and skip straight to the first name in `agents_pending`.
4. For each agent name in `agents_pending`, work through them one at a time:

   **a. Fetch the task**

   **If the agent is "Formalizer":**
   First call `get_formalization_candidates` to retrieve the list of unformalized proofs
   and subproblems. Present the candidates to the user as a numbered list showing each
   candidate's id, type, status, and excerpt. Ask the user to pick one (by number or ID).
   Wait for the user's reply, then call `get_agent_task("Formalizer", source_id=<chosen_id>)`.

   **For all other agents:**
   Call `get_agent_task(agent_name)` to get the `system_prompt` and `user_message`.

   **b. Act as the agent**

   **Researcher tasks (agent = "Researcher"):**
   Before producing any JSON, actively use your WebSearch and WebFetch tools to research
   the conjecture and open subproblems. Issue at least 2–3 distinct search queries and
   fetch at least one promising page. Only after gathering results, compile your findings
   into the required JSON format and output it.

   **All other agent tasks:**
   Output only valid JSON matching the agent's required format. Do not add prose before
   or after the JSON block.

   **c. Submit immediately, then refresh**
   Call `submit_agent_result(agent_name, response_json)` right away — do not wait until
   all agents are done. The result is persisted immediately so a token-exhaustion restart
   can resume from this point. Check `round_complete` in the response — if `true`, the
   round has been finalized automatically.
   After each `submit_agent_result` call, immediately call `refresh_viewer` with the
   session_id. This updates the viewer with partial round progress so the user can see
   each agent's result as it arrives, not just at the end of the round.

5. After all agents have submitted (or `round_complete=true` is returned), call `refresh_viewer` once more with the session_id to ensure the final round state is displayed.
6. Report a brief summary of what happened this round and suggest running `/sophie-round` again to continue.

**Resuming after token exhaustion:** If a previous run was interrupted mid-round,
`get_round_tasks` will return `resumed=true` with `agents_completed` (already done) and
`agents_pending` (still to go). Simply continue from step 4 with the pending agents —
the KB already contains the completed agents' contributions.
