Start a new Sophie session for a mathematical conjecture.

Ask the user for the conjecture if not already provided, then:
1. Call `start_session` with the conjecture text to get a session_id
2. Call `get_session_status` to confirm the session was created
3. Tell the user the session_id and conjecture, and suggest running `/sophie-round` to begin the first round
