# Working on this theory library

- Read `THEORY.md` for mathematical scope and unfinished obligations.
- Read `docs/PROOF_WORKFLOW.md` before writing or changing formal proofs.
- Work stays on the current branch unless the user asks otherwise. Do not commit
  or push without authorization for that operation.
- Do not change the kernel or add axioms to make a proof pass.
- Preserve exact-statement checks and transitive admission checks. Kernel
  acceptance alone is insufficient: the kernel deliberately accepts `Sorry`.
- Use `./check algebra` or `./check foundations` during development and
  `./check full` before handing off a broad change. Report skipped tests and
  remaining mathematical obligations explicitly.
- Use `./check index` then `./check search QUERY` to discover checked theorems
  and reachable dependencies. A dependency record is not a directly replayed
  proof; the index covers registered checks, not every upstream theorem.
- `./check collisions` is advisory. Runtime checks remain authoritative.
- The short command output is a summary. Inspect its full log when needed;
  never treat output truncation or a missing success marker as success.
- New theorem families need a runner registered in `check` and `TheoryCheck`,
  a suite using `ProofChecks`, exact public statements, and edge/model tests.
- Infrastructure self-tests: `python3 -m unittest discover -s scripts -p 'test_*.py'`.
