Run multiple rounds of the current Sophie session automatically.

Usage: `/sophie-rounds N` where N is the number of rounds to run (e.g. `/sophie-rounds 5`).
Optionally append agent letters: `/sophie-rounds 3 CP` to run Checker+Prover each round.

Parse `$ARGUMENTS`: the first token is the count N (default 1 if missing or not a number),
any remaining tokens are agent letters passed to `get_round_tasks`.

Repeat the following loop up to N times, stopping early if `should_stop=true` or `resolved=true`:

---

**Each iteration:**

1. Call `get_round_tasks` — pass `agents=<letters>` if agent letters were supplied, otherwise call with no arguments.
2. If `should_stop=true`, report the final status and stop the loop immediately.
3. If `resumed=true`, note which agents already completed (`agents_completed`) and skip to the first name in `agents_pending`.
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
   Call `submit_agent_result(agent_name, response_json)` right away. Check `round_complete`
   in the response — if `true`, the round has been finalized. If `resolved=true`, stop
   the loop after refreshing.
   After each `submit_agent_result` call, immediately call `refresh_viewer` with the session_id.

5. After all agents in this round have submitted (or `round_complete=true`), call `refresh_viewer` once more.
6. Print a one-line summary of the round (round number, agents run, key outcomes).
7. If `resolved=true` or `should_stop=true`, stop. Otherwise continue to the next iteration.

---

After the loop ends, report:
- How many rounds were completed out of N requested.
- Whether the session is now resolved, should_stop, or still open.
- A brief summary of the most significant developments across the runs.
