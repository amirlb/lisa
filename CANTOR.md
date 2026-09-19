# Cantor and Cantor–Schröder–Bernstein in LISA

This checkout starts at upstream LISA revision
`41cd4592f068ed3351ac2287516a96347cdf7664` (version 0.9.4).
The `upstream` remote points to <https://github.com/epfl-lara/lisa>.

## Run

Requirements: Java 21, Bash, curl, and sha256sum. No global Scala or sbt
installation is needed. The launcher downloads sbt 2.0.0 from Maven Central,
checks its pinned SHA-256, and keeps sbt tooling in the ignored `.tools/`
directory. Scala versions come from upstream `build.sbt`.
The first build needs network access for dependencies (including JitPack).

```sh
./sbtw compile
./sbtw 'lisa-sets/Test/runMain lisa.utils.prooflib.CantorCheck'
./sbtw 'lisa-sets/testOnly lisa.utils.prooflib.CantorSuite'
./sbtw 'lisa-sets/Test/runMain lisa.utils.prooflib.CantorBernsteinCheck'
./sbtw 'lisa-sets/testOnly lisa.utils.prooflib.CantorBernsteinSuite'
```

The executable check prints `CANTOR_CHECK PASSED` only after checking the
statements, fresh kernel proofs, and absence of transitive `sorry` dependencies.
It refuses draft mode and theorem-cache mode. Run it in a fresh JVM using the
command above.

For the broader test suites and upstream style checks:

```sh
./sbtw test 'lisa-sets/testOnly *'
./sbtw 'scalafixAll --check' scalafmtCheckAll
```

Validation on Java 21: the fresh Cantor check passed for all eight checked
theorems/instances; the baseline root suite passed 68 tests; the set-theory
suite passed 495 tests with no failures. Another 44 corpus-backed tests were
canceled because the optional TPTP benchmark dataset is not installed.
The root lint and formatting checks passed. In sbt 2, an unchanged `test` run
may use `testQuick` and report zero newly selected tests; use the explicit
Cantor executable above when you want a fresh verification every time.
The additional `lisa-sets/scalafixAll --check` exposes an existing import-style
violation in the unchanged upstream `LibraryCacheCheck.scala`; it is left
untouched rather than mixing an unrelated cleanup into this proof contribution.

## The proof

`lisa-sets/src/main/scala/lisa/maths/SetTheory/Functions/Cantor.scala`
contains the elementary argument, without importing cardinal or ordinal theory:

1. Given a function `f: A -> P(A)`, comprehension gives
   `D = {x in A | x not in f(x)}`. It is a subset of `A`.
2. If `f(a) = D` for any `a in A`, membership gives
   `a in D` if and only if `a not in D`, a contradiction.
3. Consequently `D` is not in the range of `f`; `f` cannot be surjective.
4. Replacement constructs the singleton graph `x -> {x}`. It is a function
   into `P(A)` and is injective because `{x} = {y}` implies `x = y`.

`Cardinal.cantorTheorem` combines these results using the existing definition
of strict cardinal comparison: an injection exists, but no bijection exists.
Its statement remains `forall A, A < P(A)`. No assumption that `A` is nonempty
is needed; the checks include explicit empty-set instances.

The development adds no axioms and does not change the kernel. The proof uses
LISA's existing set-theoretic definitions and kernel-checked tactics. Other
upstream declarations still contain `sorry`, but neither Cantor nor
Cantor–Bernstein depends on them. This is why the regression checks test
`withSorry`, not merely whether the kernel accepts the proof.

## Cantor–Schröder–Bernstein

`Cardinal.cantorBernsteinTheorem` now proves the existing statement
`(A ≲ B, B ≲ A) ⊢ A ≍ B`: mutual injections give a bijection, including
when the sets are empty. The proof is split into three reusable pieces in
`lisa-sets/src/main/scala/lisa/maths/SetTheory/Functions/`:

- `PowerSetFixedPoint.fixedPoint`: a monotone map sending subsets of `A` to
  subsets of `A` has a fixed point. Take the intersection, within `A`, of all
  pre-fixed subsets `S` satisfying `H(S) ⊆ S`. Monotonicity proves both
  inclusions between that intersection and its image.
- `Matching.bijection`: a relation specified by a predicate, total and unique
  in both directions, yields a set-theoretic bijection. Comprehension bounds
  its graph by `A × B`; the proof establishes functionhood, injectivity, and
  surjectivity using the existing definitions.
- `CantorBernstein.bijection`: for injections `f: A → B` and `g: B → A`,
  apply the fixed-point lemma to `H(S) = A \ g[B \ f[S]]`. At a fixed point
  `C`, match `x ∈ C` with `f(x)` and match `x ∈ A \ C` with the unique
  `y ∈ B` for which `g(y) = x`. The fixed-point equation ensures that these
  two parts cover `B` without overlap.

This route needs no ordinal recursion or added choice axiom. The helper
`H` and matching predicate are schematic expressions in LISA's existing
language; no new foundational mechanism or kernel rule is introduced.
The work fills the dependencies needed for this theorem, not unrelated
upstream placeholders.

`CantorBernsteinCheck` verifies the exact public statements, freshly generated
kernel proofs, and absence of transitive admissions for 15 theorems and
instances. Its identity-matching example establishes mutual injections
without assumptions, then exercises Cantor–Bernstein for arbitrary `A` and
specializes to the empty set. It refuses draft mode and theorem-cache mode.

After this addition, the explicit full set-theory suite passed 496 tests
(49 suites, no failures; the same 44 optional TPTP corpus tests canceled).
Both fresh executable checks passed. Formatting is stable; the additional
set-theory lint check still reports only the existing `LibraryCacheCheck.scala`
import-style issue noted above.
