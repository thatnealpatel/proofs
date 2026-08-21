- You **MUST NOT** manually write or modify files in `./References`.

- You **MUST NOT** truncate shell/bash output; doing so risks missing critical information
  that poisons all downstream reasoning. You SHOULD redirect unfamiliar output into `/tmp/**`
  and probe its shape before reading.

- You **MUST** treat a proof as complete when the file compiles with no `sorry`, no `admit`, and no errors.

- You **MUST** dispatch parallel `vacuity`, `foundations`, and `style` reviewer agents against all uncommitted
  Lean programs before staging or committing.

- You **MUST** use `flock .lake/agent.lock lake build ...` when trying to build proofs to avoid stomping on other agents.

- You **MUST** load `/leandoc` and use `leandoc` for retrieval for Lean semantic search and symbol search before using other tools.

- You SHOULD use `exact?`, `apply?`, `#loogle` and `#leansearch` as documented
  in `/leandoc` for tactic and lemma discovery.

- You **MUST** run `sage` and `python` commands wrapped in `timeout 300` by default.
  Anything that times out **MUST NOT** be retried; it should be escalated to the USER.

- You SHOULD use `.lean` files in `Scratch` for `#check`, `#eval`, or `#example`
  experiments before crystallizing them into non-`Scratch` Lean libraries.

- You SHOULD use reach for `/sage` first when looking for computational algebra
  intuitions; `sage` programs cannot be proofs, but they are useful for pre-proof
  orientation and proof-assisting activities. They can be used to produce counter-
  examples and witnesses.

- You SHOULD use `fetch` for arXiv and academic paper pdf links before `WebFetch`;
  `fetch` auto-canonicalizes into `.tex` or `.txt` for agents.

- You SHOULD use `sage -c "<sage code>"` for short queries or explorations.

- You SHOULD implement directly onto `main` unless told otherwise.
