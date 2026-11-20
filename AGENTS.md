# User communication record

The user requests that answers, status updates, and questions be recorded in
`answers.tex`, compiled to `answers.pdf` at every turn in this workspace.

- Overwrite `answers.tex` at the start of each turn so it contains only that
  turn's user-facing status updates, questions (if any), and final answer.
  Add messages before `% END CONVERSATION LOG` during the turn. Record the
  actual messages; do not include internal reasoning, tool dumps, or credentials.
  This follows the user's updated preference of 17 November 2026.
- Compile before ending each turn: `python3 build_answers.py`. Check the PDF
  for layout problems after changes. Keep the final chat answer consistent
  with its entry in the document.
- For LeanCalc turns, also rebuild `LeanCalc.pdf`, as the user requested earlier:
  `python3 lean_calc/build_document.py`. That command now compiles both PDFs.
  Rebuild the app first if Lean source or the C bridge changed. Leave the
  Formal verification section blank until the user asks to begin that work.

These instructions record user preferences; they do not request approvals or
change the scope of a task.
