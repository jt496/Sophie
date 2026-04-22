Formalize a result from the current Sophie session in Lean 4.

1. Call `list_sessions` to find the most recent active session, or ask the user for a session_id if unclear
2. Call `get_formalization_task` to get the formalization task details
3. Work through the Lean 4 formalization — use the lean-lsp MCP tools (lean_goal, lean_diagnostic_messages, lean_multi_attempt, lean_leansearch, lean_loogle, etc.) to develop and verify the proof
4. Once the proof is complete and verified, call `submit_formalization` with the session_id and the Lean code
5. Call `refresh_viewer` with the session_id
6. Report what was formalized and whether it was accepted
