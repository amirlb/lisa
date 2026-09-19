# Algebra and Lagrange's cardinal theorem

This development belongs to the shared `theory/development` branch.
The target is the finite-group theorem: if H is a subgroup of finite G,
then |G| = [G:H] |H|, hence |H| divides |G|.

## Representation

`lisa.maths.Algebra.Group.group(G)(m)(e)(i)` describes a carrier G,
a set-theoretic multiplication function m: G × G → G, an identity e ∈ G,
and a set-theoretic inverse function i: G → G. Associativity, identity,
and inverse laws are explicitly bounded by G. Multiplication is applied
as `m(pair(x)(y))`; LISA's `m(x, y)` instead means curried application.
The parameters can later be packaged into a set-valued structure without
changing the underlying group laws.

`Subgroup.subgroup(H)(G)(m)(e)(i)` uses the ambient operations: H ⊆ G,
e ∈ H, and H is closed under multiplication and inversion. It includes
the ambient group hypothesis. No normality or finiteness is required.

`Coset.left(G)(H)(m)(a)` is the subset of G consisting of products ah
with h ∈ H. The translation theorem constructs a bijection H → aH
using the generic matching-to-bijection lemma from the set-theory work.

## Milestones

1. Group laws, cancellation, inverse uniqueness and involution;
   subgroup closure; coset membership and translation bijection.
2. Cosets are equal or disjoint and cover the group; generic partition
   and quotient-set lemmas should live in set theory, not only algebra.
3. Natural numbers and finite cardinality, including uniqueness,
   finite subsets/images, and uniform finite-partition counting.
4. Combine the coset partition with counting to prove Lagrange's theorem.

Milestones 1 and the coset-partition part of 2 are implemented. The development
also proves Lagrange directly in bijective/cardinal form, without first building
the natural-number counting API. Milestone 3 and the explicit natural-number
formulation of 4 remain future work; they are not hidden assumptions of the
theorem below.

## Checked cardinal statement

`Lagrange.bijection` has the exact statement

```
subgroup(H)(G)(m)(e)(i)
  ⊢ ∃f. bijective(f)(cosets(G)(H)(m) × H)(G)
```

`cosets` is the replacement set `{aH | a ∈ G}`. No normality assumption
is made; this is a quotient **set**, not a quotient group. `cardinalIdentity`
expresses the same result using the existing `Cardinal.equinumerosity`:
`|G/H| · |H| = |G|`, where multiplication of cardinalities is represented
by Cartesian product. `cardinalDivisibility` concludes that some set Q
satisfies `Q × H ≍ G`. This is cardinal divisibility, not a newly invented
definition of natural-number divisibility.

The proof proceeds as follows:

1. Coset membership is reflexive on G, symmetric, and transitive.
2. Overlapping cosets are equal; every element belongs to a coset.
3. For each coset C, select a representative r(C) and parametrize C
   bijectively by `h ↦ r(C)h`.
4. `PartitionProduct.bijection` assembles the maps into the bijection
   `(C,h) ↦ r(C)h` from the product of the block set and H onto G.

The generic partition-product lemma takes the parametrizations as input;
it does not choose them. The group proof selects representatives with LISA's
existing Hilbert epsilon and uses existing replacement to build sets.
**This is a choice-based proof and works for infinite groups too.** It is a
change from the initially proposed finite-induction route, not a claim that
the finite theorem needs choice. No new choice axiom or kernel rule is added.
In particular, this proof does not use the unfinished ordinal-valued `card`
construction or assume an unproved finite-counting theorem.

For an explicitly numerical statement `|H| divides |G|` in the natural-number
library, the remaining work is to construct finite cardinalities and prove
that their multiplication agrees with Cartesian product. The group-theoretic
and set-bijection content is already proved.

`TrivialGroup.isGroup` constructs a one-element group using set-theoretic
constant functions, rather than assuming a group exists. Regression tests
instantiate Lagrange for it and separately prove that the empty carrier
cannot be a group.

## Verification

```sh
./sbtw 'lisa-sets/Test/runMain lisa.utils.prooflib.GroupCheck'
./sbtw 'lisa-sets/Test/runMain lisa.utils.prooflib.LagrangeCheck'
./sbtw 'lisa-sets/testOnly *'
```

The executable checks the public closure and translation statements,
fresh kernel proofs, and absence of transitive admissions. It refuses draft
and theorem-cache modes. No axioms or kernel rules are added.

Milestone 1 validation: all 26 algebra lemmas passed the fresh proof and
transitive-admission checks. The full set-theory suite passed 497 tests;
44 optional TPTP-corpus tests were canceled because the dataset is absent.

Lagrange validation: the 23 additional lemmas and instances passed the fresh
kernel and transitive-admission checks, including the exact cardinal statements,
the constructed one-element group, and rejection of an empty group carrier.
The full suite now passes 498 tests across 51 suites, with the same 44
optional corpus tests canceled. The set-theory lint check still reports the
pre-existing import-style issue in `LibraryCacheCheck.scala`.
