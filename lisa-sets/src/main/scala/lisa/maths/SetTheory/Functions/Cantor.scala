package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Cantor's diagonal argument, independent of ordinal/cardinal machinery.
 */
object Cantor extends lisa.Main {
  private val A, f, x, y, z, a, b, c, d = variable[Ind]

  /**
   * No function from a set to its powerset is onto, including when the set is empty.
   */
  val noSurjection = Theorem(
    functionBetween(f)(A)(𝒫(A)) |- ¬(surjective(f)(𝒫(A)))
  ) {
    assume(functionBetween(f)(A)(𝒫(A)))
    val D = { x ∈ A | x ∉ f(x) }
    val isFunction = have(function(f)) by Tautology.from(BasicTheorems.functionBetweenIsFunction of (B := 𝒫(A)))
    val domain = have(dom(f) === A) by Tautology.from(BasicTheorems.functionBetweenDomain of (B := 𝒫(A)))
    val diagonalSubset = have(D ⊆ A) by Tautology.from(Comprehension.subset of (y := A, φ := λ(x, x ∉ f(x))))
    val diagonalInPower = have(D ∈ 𝒫(A)) by Tautology.from(diagonalSubset, PowerSet.membership of (x := D, y := A))

    // No pair in f can have D as its second coordinate.
    have((z ∈ f, snd(z) === D) |- ()) subproof {
      assume(z ∈ f)
      assume(snd(z) === D)
      have(z === (fst(z), snd(z))) by Tautology.from(isFunction, BasicTheorems.inversion)
      val pair = thenHave((fst(z), snd(z)) ∈ f) by Congruence
      val inDomain = have(fst(z) ∈ dom(f)) by Tautology.from(pair, BasicTheorems.domainMembership of (x := fst(z), y := snd(z)))
      val inA = have(fst(z) ∈ A) by Congruence.from(inDomain, domain)
      val image = have(f(fst(z)) === snd(z)) by Tautology.from(
        pair,
        inDomain,
        isFunction,
        BasicTheorems.appDefinition of (x := fst(z), y := snd(z))
      )
      val diagonal = have(fst(z) ∈ D <=> fst(z) ∈ A /\ fst(z) ∉ f(fst(z))) by Comprehension.apply
      val sameMembership = have(fst(z) ∈ D <=> fst(z) ∈ f(fst(z))) by Congruence.from(image)
      have(thesis) by Tautology.from(inA, diagonal, sameMembership)
    }
    thenHave(z ∈ f /\ (snd(z) === D) |- ()) by Restate
    val noPreimage = thenHave(∃(z, z ∈ f /\ (snd(z) === D)) |- ()) by LeftExists
    have(D ∈ { snd(z) | z ∈ f } <=> ∃(z, z ∈ f /\ (snd(z) === D))) by Replacement.apply
    val rangeMembership = thenHave(D ∈ range(f) <=> ∃(z, z ∈ f /\ (snd(z) === D))) by Substitute(Relation.range.definition of (R := f))
    val notInRange = have(D ∉ range(f)) by Tautology.from(noPreimage, rangeMembership)
    have(range(f) === 𝒫(A) |- ()) by Congruence.from(diagonalInPower, notInRange)
    thenHave(¬(range(f) === 𝒫(A))) by Restate
    thenHave(thesis) by Substitute(surjective.definition of (B := 𝒫(A)))
  }

  // The graph of x ↦ {x}; Replacement constructs this as a set.
  private def singletonGraph(A: Expr[Ind]): Expr[Ind] = { (x, singleton(x)) | x ∈ A }

  val singletonGraphMembership = Theorem(
    (x, y) ∈ singletonGraph(A) <=> x ∈ A /\ (y === singleton(x))
  ) {
    val g = singletonGraph(A)
    have((a ∈ A, (a, singleton(a)) === (x, y)) |- x ∈ A /\ (y === singleton(x))) subproof {
      assume(a ∈ A)
      assume((a, singleton(a)) === (x, y))
      val first = have(a === x) by Tautology.from(Pair.extensionality of (b := singleton(a), c := x, d := y))
      val second = have(singleton(a) === y) by Tautology.from(Pair.extensionality of (b := singleton(a), c := x, d := y))
      val member = have(x ∈ A) by Congruence.from(first)
      val value = have(y === singleton(x)) by Congruence.from(first, second)
      have(thesis) by Tautology.from(member, value)
    }
    thenHave(a ∈ A /\ ((a, singleton(a)) === (x, y)) |- x ∈ A /\ (y === singleton(x))) by Restate
    val witness = thenHave(∃(a, a ∈ A /\ ((a, singleton(a)) === (x, y))) |- x ∈ A /\ (y === singleton(x))) by LeftExists
    val membership = have((x, y) ∈ g <=> ∃(a, a ∈ A /\ ((a, singleton(a)) === (x, y)))) by Replacement.apply
    val forward = have((x, y) ∈ g |- x ∈ A /\ (y === singleton(x))) by Tautology.from(witness, membership)
    have((x ∈ A, y === singleton(x)) |- (x, singleton(x)) ∈ g) by Tautology.from(
      Replacement.map of (F := λ(x, (x, singleton(x))))
    )
    val backward = thenHave((x ∈ A, y === singleton(x)) |- (x, y) ∈ g) by Congruence
    have(thesis) by Tautology.from(forward, backward)
  }

  val singletonGraphFunction = Theorem(functionBetween(singletonGraph(A))(A)(𝒫(A))) {
    val g = singletonGraph(A)
    have(x ∈ A |- singleton(x) ∈ 𝒫(A)) by Tautology.from(
      Subset.leftSingleton of (y := A),
      PowerSet.membership of (x := singleton(x), y := A)
    )
    have(x ∈ A ==> (x, singleton(x)) ∈ (A × 𝒫(A))) by Tautology.from(
      lastStep,
      CartesianProduct.pairMembership of (y := singleton(x), B := 𝒫(A))
    )
    val typedPair = thenHave(∀(x, x ∈ A ==> (x, singleton(x)) ∈ (A × 𝒫(A)))) by RightForall
    have((x ∈ A, (x, singleton(x)) === z) |- (x, singleton(x)) ∈ (A × 𝒫(A))) by InstantiateForall(x)(typedPair)
    thenHave((x ∈ A, (x, singleton(x)) === z) |- z ∈ (A × 𝒫(A))) by Congruence
    thenHave(x ∈ A /\ ((x, singleton(x)) === z) |- z ∈ (A × 𝒫(A))) by Restate
    val witness = thenHave(∃(x, x ∈ A /\ ((x, singleton(x)) === z)) |- z ∈ (A × 𝒫(A))) by LeftExists
    have(z ∈ g ==> z ∈ (A × 𝒫(A))) by Tautology.from(witness, Replacement.membership of (y := z, F := λ(x, (x, singleton(x)))))
    thenHave(∀(z, z ∈ g ==> z ∈ (A × 𝒫(A)))) by RightForall
    thenHave(g ⊆ (A × 𝒫(A))) by Substitute(⊆.definition of (x := g, y := (A × 𝒫(A))))
    val relation = thenHave(relationBetween(g)(A)(𝒫(A))) by Substitute(Relation.relationBetween.definition of (R := g, X := A, Y := 𝒫(A)))

    have((x, y) ∈ g <=> x ∈ A /\ (y === singleton(x))) by Restate.from(singletonGraphMembership)
    thenHave((x, y) ∈ g ==> (y === singleton(x))) by Tautology.fromLastStep()
    val unique = thenHave(∀(y, (x, y) ∈ g ==> (y === singleton(x)))) by RightForall
    have(x ∈ A |- (x, singleton(x)) ∈ g /\ ∀(y, (x, y) ∈ g ==> (y === singleton(x)))) by Tautology.from(
      unique,
      singletonGraphMembership of (y := singleton(x))
    )
    thenHave(x ∈ A |- ∃(y, (x, y) ∈ g /\ ∀(z, (x, z) ∈ g ==> (z === y)))) by RightExists
    thenHave(x ∈ A |- ∃!(y, (x, y) ∈ g)) by Substitute(∃!.definition of (P := λ(y, (x, y) ∈ g)))
    thenHave(x ∈ A ==> ∃!(y, (x, y) ∈ g)) by Restate
    thenHave(∀(x ∈ A, ∃!(y, (x, y) ∈ g))) by RightForall
    have(thesis) by Tautology.from(lastStep, relation, functionBetween.definition of (f := g, B := 𝒫(A)))
  }

  val singletonGraphApplication = Theorem(x ∈ A |- singletonGraph(A)(x) === singleton(x)) {
    assume(x ∈ A)
    val g = singletonGraph(A)
    val fn = have(function(g)) by Tautology.from(singletonGraphFunction, BasicTheorems.functionBetweenIsFunction of (f := g, B := 𝒫(A)))
    val domain = have(dom(g) === A) by Tautology.from(singletonGraphFunction, BasicTheorems.functionBetweenDomain of (f := g, B := 𝒫(A)))
    val inDomain = have(x ∈ dom(g)) by Congruence.from(domain)
    have(thesis) by Tautology.from(
      fn,
      inDomain,
      BasicTheorems.appDefinition of (f := g, y := singleton(x)),
      singletonGraphMembership of (y := singleton(x))
    )
  }

  /**
   * The singleton map witnesses |A| ≤ |P(A)| without using Choice.
   */
  val singletonInjection = Theorem(∃(f, functionBetween(f)(A)(𝒫(A)) /\ injective(f)(A))) {
    val g = singletonGraph(A)
    val atX = have(x ∈ A |- g(x) === singleton(x)) by Restate.from(singletonGraphApplication)
    // Restate fixes the bound-variable spelling before congruence closure.
    val atY = have(y ∈ A |- g(y) === singleton(y)) by Restate.from(singletonGraphApplication of (x := y))
    have((x ∈ A, y ∈ A, g(x) === g(y)) |- singleton(x) === singleton(y)) by Congruence.from(
      atX,
      atY
    )
    thenHave((x ∈ A, y ∈ A, g(x) === g(y)) |- x === y) by Tautology.fromLastStep(Singleton.extensionality)
    thenHave(x ∈ A |- y ∈ A ==> ((g(x) === g(y)) ==> (x === y))) by Restate
    thenHave(x ∈ A |- ∀(y ∈ A, (g(x) === g(y)) ==> (x === y))) by RightForall
    thenHave(x ∈ A ==> ∀(y ∈ A, (g(x) === g(y)) ==> (x === y))) by Restate
    thenHave(∀(x ∈ A, ∀(y ∈ A, (g(x) === g(y)) ==> (x === y)))) by RightForall
    thenHave(injective(g)(A)) by Substitute(injective.definition of (f := g))
    thenHave(functionBetween(g)(A)(𝒫(A)) /\ injective(g)(A)) by Tautology.fromLastStep(singletonGraphFunction)
    thenHave(thesis) by RightExists
  }
}
