# Proof workflow

## Commands

Requires Python 3 and the existing Java 21/sbt launcher prerequisites.

| Command | Meaning |
| --- | --- |
| `./check algebra` | Fresh Group and Lagrange executable checks |
| `./check foundations` | Fresh Cantor and Bernstein checks |
| `./check all` | All four registered executable checks; updates inventory |
| `./check full` | Those checks plus explicit `lisa-sets/testOnly *` |
| `./check index` | Same proof verification as `all`, plus searchable inventory |
| `./check search 'bijection'` | Search names and formal statements; refuses stale data |
| `./check show lisa.maths.Algebra.Lagrange.bijection` | Exact record, including dependency names |
| `./check collisions` | Advisory source scan for repeated simple DEF names |

Full logs and generated JSON live under ignored `.tools/checks/`. The command
retains sbt's nonzero exit status, requires every requested check's success
marker, and refuses verification if source files change during the run. Full
mode reports ScalaTest's canceled count; optional TPTP corpus tests require
an external dataset. It does not silently fall back to incremental testQuick.
Formatting and lint are separate from proof checking. The known upstream
`LibraryCacheCheck.scala` import-style lint issue is not suppressed.

The inventory is a diagnostic snapshot, not a proof cache. `checked` means
directly replayed by this run's shared harness; `dependency` means discovered
via frontend imports, not independently replayed by the harness. `admitted`
is explicitly distinct. All checked roots must have no transitive admissions.
The index includes reachable theorem/definition/axiom records, not all LISA
source declarations. Source locations are best-effort and left unresolved when
ambiguous. Axioms and definitions have no theorem-proof import list in this
frontend API: an empty list is not an axiom-freedom claim. Inspect the JSON for
complete records. Search displays at most 20 matches.
If an upstream custom printer cannot render a schematic expression, its record
uses explicitly labeled kernel syntax instead; this fallback affects only
display, never proof verification.

## Writing proofs without rediscovering the traps

- **Apply multiplication to a pair:** `m(pair(x)(y))`. `m(x, y)` means
  curried set-function application. See `Algebra/Group.scala`.
- **Definitions have kernel names:** distinct Scala objects do not necessarily
  isolate equal short DEF names. We encountered `Matching.graph` versus a
  constant-function `graph`; use descriptive distinct names. The advisory scan
  does not parse sorts or all Scala syntax, so it can both warn unnecessarily
  and miss declarations. Never use it instead of loading theories together.
- **`have` versus `thenHave`:** an explicitly supplied `Tactic.from(facts...)`
  belongs after `have`. `thenHave` supplies the previous fact implicitly;
  use the tactic's supported previous-step form.
- **Hypotheses are not automatically assumed:** use `assumeAll` or explicit
  `assume(...)` inside a proof before deriving unconditional intermediate facts.
- **Tautology is propositional:** it does not derive equality transitivity or
  instantiate quantified formulas. Derive equalities with `Congruence`, and
  instantiate quantifiers explicitly when necessary.
- **Congruence needs usable facts:** split conjunctions with `Tautology` first.
  Normalize alpha-renamed quantified expressions before equality rewriting.
- **Witness elimination:** combine witness conditions into one conjunction
  using `Restate` before `LeftExists`. See `PartitionProduct.bijection`.
- **Bounded quantifiers:** nested bounded forall includes implications. Introduce
  them one at a time using Restate/RightForall; Generalize handles consecutive
  unbounded quantifiers, not arbitrary quantifier/implication alternation.
- **Extensionality:** give it a pointwise membership equivalence; do not first
  wrap that equivalence in a forall. See `Coset.sameCoset`.
- **Schema substitutions include sorts:** when names collide, specify
  `Variable[Ind >>: Ind >>: Prop]("P")` explicitly.
- **Bound automation:** Superpose produces kernel-checked proofs, but broad
  search can time out or encounter unsupported higher-sort shapes. Prefer
  small helper lemmas and explicit witness/equality reasoning to increasing
  search limits blindly. See the explicit partition-product proof.

## Adding coverage

Call `ProofChecks.requireFresh()` before loading theorems, use
`ProofChecks.expect(theorem, independentlyWrittenExpectedSequent)` for public
contracts, and pass the helper/root theorem list to `ProofChecks.verify`.
The shared harness rejects draft/cache modes, empty checks, admissions,
missing high-level proofs, and invalid kernel proofs. Keep concrete models
and negative edge cases: a proof from an impossible structure definition is
not a useful mathematical result. The admitted fixture in `ProofChecksSuite`
exists solely to verify that admission rejection works.

Keep the kernel unchanged. Do not introduce a macro framework until repeated
proof patterns demonstrate a specific need. No new proof DSL is required for
these commands or guides.
