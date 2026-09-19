# Theory map and outstanding obligations

This is a human-maintained mathematical roadmap, not a verification certificate.
`./check all` checks the formal contracts; `./check index` indexes their reachable
dependencies. Upstream files outside that closure can still contain admissions.

| Area | Checked results | Still missing |
| --- | --- | --- |
| Set cardinal comparison | Cantor, Bernstein, singleton injection | A developed finite-cardinality/natural-number API |
| Reusable set constructions | Powerset fixed point, matching bijection, partition product, constant functions | Broader partition/quotient convenience library |
| Groups | Carrier-bounded laws, cancellation, inverse identities, subgroups, explicit trivial group | General structure packaging, homomorphisms, group actions |
| Cosets | Translation bijections, coverage, overlapping cosets equal | Normal-subgroup quotient-group operations |
| Lagrange | `(G/H) × H ≍ G`; existence of a cardinal factor | **Natural-number** statement `|H| divides |G|` and its finite-counting bridge |

The Lagrange construction uses existing Hilbert epsilon to select representatives;
it is choice-based and also applies to infinite groups. The finite theorem can
be proved without that choice-based route. No extra axiom was added. Do not
describe the natural-number formulation as completed merely because the cardinal
identity is checked.

Detailed arguments and commands: `CANTOR.md`, `ALGEBRA.md`, and
`docs/PROOF_WORKFLOW.md`. Infrastructure changes must not silently alter theorem
statements, foundational assumptions, or which checks are executed.
