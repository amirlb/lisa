package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Construct a set-theoretic bijection from a total one-to-one matching.
 */
object Matching extends lisa.Main {
  private val A, B, h, x, y, z, p = variable[Ind]
  private val P = variable[Ind >>: Ind >>: Prop]

  val graph = DEF(λ(A, λ(B, λ(P, { p ∈ (A × B) | P(fst(p))(snd(p)) }))))

  val membership = Theorem((x, y) ∈ graph(A)(B)(P) <=> x ∈ A /\ y ∈ B /\ P(x)(y)) {
    have((x, y) ∈ { p ∈ (A × B) | P(fst(p))(snd(p)) } <=> (x, y) ∈ (A × B) /\ P(fst(x, y))(snd(x, y))) by Comprehension.apply
    thenHave((x, y) ∈ graph(A)(B)(P) <=> (x, y) ∈ (A × B) /\ P(x)(y)) by Substitute(
      graph.definition,
      Pair.pairFst,
      Pair.pairSnd
    )
    thenHave(thesis) by Tautology.fromLastStep(CartesianProduct.pairMembership)
  }

  val bounded = Theorem(relationBetween(graph(A)(B)(P))(A)(B)) {
    have({ p ∈ (A × B) | P(fst(p))(snd(p)) } ⊆ (A × B)) by Restate.from(
      Comprehension.subset of (y := (A × B), φ := λ(p, P(fst(p))(snd(p))))
    )
    thenHave(graph(A)(B)(P) ⊆ (A × B)) by Substitute(graph.definition)
    thenHave(thesis) by Substitute(Relation.relationBetween.definition of (R := graph(A)(B)(P), X := A, Y := B))
  }

  val bijection = Theorem(
    (
      ∀(x, x ∈ A ==> ∃(y, y ∈ B /\ P(x)(y))),
      ∀(y, y ∈ B ==> ∃(x, x ∈ A /\ P(x)(y))),
      ∀(x, ∀(y, ∀(z, (x ∈ A /\ y ∈ B /\ z ∈ B /\ P(x)(y) /\ P(x)(z)) ==> (y === z)))),
      ∀(x, ∀(z, ∀(y, (x ∈ A /\ z ∈ A /\ y ∈ B /\ P(x)(y) /\ P(z)(y)) ==> (x === z))))
    ) |- ∃(h, bijective(h)(A)(B))
  ) {
    val total = assume(∀(x, x ∈ A ==> ∃(y, y ∈ B /\ P(x)(y))))
    val onto = assume(∀(y, y ∈ B ==> ∃(x, x ∈ A /\ P(x)(y))))
    val unique = assume(∀(x, ∀(y, ∀(z, (x ∈ A /\ y ∈ B /\ z ∈ B /\ P(x)(y) /\ P(x)(z)) ==> (y === z)))))
    val reverseUnique = assume(∀(x, ∀(z, ∀(y, (x ∈ A /\ z ∈ A /\ y ∈ B /\ P(x)(y) /\ P(z)(y)) ==> (x === z)))))
    val G = graph(A)(B)(P)
    have(x ∈ A |- ∃(y, (x, y) ∈ G /\ ∀(z, (x, z) ∈ G ==> (z === y)))) subproof {
      assume(x ∈ A)
      have((y ∈ B, P(x)(y)) |- ∃(y, (x, y) ∈ G /\ ∀(z, (x, z) ∈ G ==> (z === y)))) subproof {
        assume(y ∈ B)
        assume(P(x)(y))
        val member = have((x, y) ∈ G) by Tautology.from(membership)
        have((x ∈ A /\ y ∈ B /\ z ∈ B /\ P(x)(y) /\ P(x)(z)) ==> (y === z)) by InstantiateForall(x, y, z)(unique)
        thenHave((x, z) ∈ G ==> (z === y)) by Tautology.fromLastStep(membership of (y := z))
        thenHave(∀(z, (x, z) ∈ G ==> (z === y))) by RightForall
        thenHave((x, y) ∈ G /\ ∀(z, (x, z) ∈ G ==> (z === y))) by Tautology.fromLastStep(member)
        thenHave(thesis) by RightExists
      }
      thenHave(y ∈ B /\ P(x)(y) |- ∃(y, (x, y) ∈ G /\ ∀(z, (x, z) ∈ G ==> (z === y)))) by Restate
      val witness = thenHave(∃(y, y ∈ B /\ P(x)(y)) |- ∃(y, (x, y) ∈ G /\ ∀(z, (x, z) ∈ G ==> (z === y)))) by LeftExists
      have(x ∈ A ==> ∃(y, y ∈ B /\ P(x)(y))) by InstantiateForall(x)(total)
      thenHave(thesis) by Tautology.fromLastStep(witness)
    }
    thenHave(x ∈ A |- ∃!(y, (x, y) ∈ G)) by Substitute(∃!.definition of (Variable[Ind >>: Prop]("P") := λ(y, (x, y) ∈ G)))
    thenHave(x ∈ A ==> ∃!(y, (x, y) ∈ G)) by Restate
    thenHave(∀(x ∈ A, ∃!(y, (x, y) ∈ G))) by RightForall
    val fn = thenHave(functionBetween(G)(A)(B)) by Tautology.fromLastStep(bounded, functionBetween.definition of (f := G))
    val functionFact = have(function(G)) by Tautology.from(fn, BasicTheorems.functionBetweenIsFunction of (f := G))
    val domain = have(dom(G) === A) by Tautology.from(fn, BasicTheorems.functionBetweenDomain of (f := G))

    val application = have(x ∈ A |- G(x) ∈ B /\ P(x)(G(x))) subproof {
      assume(x ∈ A)
      val inDomain = have(x ∈ dom(G)) by Congruence.from(domain)
      have((x, G(x)) ∈ G) by Tautology.from(inDomain, functionFact, BasicTheorems.appDefinition of (f := G, y := G(x)))
      thenHave(thesis) by Tautology.fromLastStep(membership of (y := G(x)))
    }
    val injectivity = have(injective(G)(A)) subproof {
      have((x ∈ A, z ∈ A, G(x) === G(z)) |- x === z) subproof {
        assume(x ∈ A)
        assume(z ∈ A)
        assume(G(x) === G(z))
        val left = have(P(x)(G(x))) by Tautology.from(application)
        val typed = have(G(x) ∈ B) by Tautology.from(application)
        have(P(z)(G(z))) by Tautology.from(application of (x := z))
        val right = thenHave(P(z)(G(x))) by Congruence
        have((x ∈ A /\ z ∈ A /\ G(x) ∈ B /\ P(x)(G(x)) /\ P(z)(G(x))) ==> (x === z)) by InstantiateForall(x, z, G(x))(reverseUnique)
        thenHave(thesis) by Tautology.fromLastStep(left, typed, right)
      }
      thenHave(x ∈ A |- z ∈ A ==> ((G(x) === G(z)) ==> (x === z))) by Restate
      thenHave(x ∈ A |- ∀(z ∈ A, (G(x) === G(z)) ==> (x === z))) by RightForall
      thenHave(x ∈ A ==> ∀(z ∈ A, (G(x) === G(z)) ==> (x === z))) by Restate
      thenHave(∀(x ∈ A, ∀(z ∈ A, (G(x) === G(z)) ==> (x === z)))) by RightForall
      thenHave(thesis) by Substitute(injective.definition of (f := G))
    }

    val ontoSubset = have(B ⊆ range(G)) subproof {
      have(y ∈ B |- y ∈ range(G)) subproof {
        assume(y ∈ B)
        have((x ∈ A, P(x)(y)) |- (x, y) ∈ G) by Tautology.from(membership)
        thenHave((x ∈ A, P(x)(y)) |- y ∈ range(G)) by Tautology.fromLastStep(BasicTheorems.rangeMembership of (f := G))
        thenHave(x ∈ A /\ P(x)(y) |- y ∈ range(G)) by Restate
        val witness = thenHave(∃(x, x ∈ A /\ P(x)(y)) |- y ∈ range(G)) by LeftExists
        have(y ∈ B ==> ∃(x, x ∈ A /\ P(x)(y))) by InstantiateForall(y)(onto)
        thenHave(thesis) by Tautology.fromLastStep(witness)
      }
      thenHave(y ∈ B ==> y ∈ range(G)) by Restate
      thenHave(∀(y, y ∈ B ==> y ∈ range(G))) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := B, y := range(G)))
    }
    have(range(G) ⊆ B) by Tautology.from(fn, BasicTheorems.functionBetweenRange of (f := G))
    thenHave(range(G) === B) by Tautology.fromLastStep(ontoSubset, Subset.doubleInclusion of (x := range(G), y := B))
    val surjectivity = thenHave(surjective(G)(B)) by Substitute(surjective.definition of (f := G))
    have(bijective(G)(A)(B)) by Tautology.from(fn, injectivity, surjectivity, bijective.definition of (f := G))
    thenHave(thesis) by RightExists
  }
}
