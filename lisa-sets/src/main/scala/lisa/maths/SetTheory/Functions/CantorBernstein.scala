package lisa.maths.SetTheory.Functions

import lisa.automation.Superpose
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Cantor–Schröder–Bernstein via a monotone map on the powerset of A.
 */
object CantorBernstein extends lisa.Main {
  private val A, B, C, S, T, f, g, h, x, y, z = variable[Ind]

  // A \ g[B \ f[S]], written using bounded quantifiers instead of image operators.
  val step = DEF(λ(A, λ(B, λ(f, λ(g, λ(S, { x ∈ A | ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y))) }))))))

  val stepMembership = Theorem(
    x ∈ step(A)(B)(f)(g)(S) <=> x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y)))
  ) {
    have(
      x ∈ { x ∈ A | ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y))) } <=>
        x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y)))
    ) by Comprehension.apply
    thenHave(thesis) by Substitute(step.definition)
  }

  val stepBounded = Theorem(step(A)(B)(f)(g)(S) ⊆ A) {
    have({ x ∈ A | ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y))) } ⊆ A) by Restate.from(
      Comprehension.subset of (y := A, φ := λ(x, ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y)))))
    )
    thenHave(thesis) by Substitute(step.definition)
  }

  val stepMonotone = Theorem(S ⊆ T |- step(A)(B)(f)(g)(S) ⊆ step(A)(B)(f)(g)(T)) {
    assume(S ⊆ T)
    val inclusion = have(∀(z, z ∈ S ==> z ∈ T)) by Tautology.from(Subset.definition of (x := S, y := T))
    val first = have(x ∈ step(A)(B)(f)(g)(S) <=> x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ S /\ (f(z) === y)))) by Tautology.from(stepMembership)
    val second = have(x ∈ step(A)(B)(f)(g)(T) <=> x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ T /\ (f(z) === y)))) by Tautology.from(stepMembership of (S := T))
    have(x ∈ step(A)(B)(f)(g)(S) ==> x ∈ step(A)(B)(f)(g)(T)) by Superpose.from(inclusion, first, second)
    thenHave(∀(x, x ∈ step(A)(B)(f)(g)(S) ==> x ∈ step(A)(B)(f)(g)(T))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := step(A)(B)(f)(g)(S), y := step(A)(B)(f)(g)(T)))
  }

  val partitionExists = Theorem(∃(C, C ⊆ A /\ (step(A)(B)(f)(g)(C) === C))) {
    have(S ⊆ A ==> step(A)(B)(f)(g)(S) ⊆ A) by Tautology.from(stepBounded)
    val bounded = thenHave(∀(S, S ⊆ A ==> step(A)(B)(f)(g)(S) ⊆ A)) by RightForall
    have((S ⊆ A /\ T ⊆ A /\ S ⊆ T) ==> step(A)(B)(f)(g)(S) ⊆ step(A)(B)(f)(g)(T)) by Tautology.from(stepMonotone)
    val monotone = thenHave(∀(S, ∀(T, (S ⊆ A /\ T ⊆ A /\ S ⊆ T) ==> step(A)(B)(f)(g)(S) ⊆ step(A)(B)(f)(g)(T)))) by Generalize
    have(thesis) by Tautology.from(bounded, monotone, PowerSetFixedPoint.fixedPoint of (Variable[Ind >>: Ind]("H") := λ(S, step(A)(B)(f)(g)(S))))
  }

  val bijectionOfFixedPoint = Theorem(
    (functionBetween(f)(A)(B), injective(f)(A), functionBetween(g)(B)(A), injective(g)(B), C ⊆ A, step(A)(B)(f)(g)(C) === C)
      |- ∃(h, bijective(h)(A)(B))
  ) {
    assumeAll
    have(x ∈ A ==> f(x) ∈ B) by Tautology.from(BasicTheorems.appTyping)
    val fTyped = thenHave(∀(x, x ∈ A ==> f(x) ∈ B)) by RightForall
    have(y ∈ B ==> g(y) ∈ A) by Tautology.from(BasicTheorems.appTyping of (f := g, A := B, B := A, x := y))
    val gTyped = thenHave(∀(y, y ∈ B ==> g(y) ∈ A)) by RightForall
    val fInjective = have(∀(x ∈ A, ∀(z ∈ A, (f(x) === f(z)) ==> (x === z)))) by Substitute(injective.definition)(have(injective(f)(A)) by Hypothesis)
    val gInjective = have(∀(y ∈ B, ∀(z ∈ B, (g(y) === g(z)) ==> (y === z)))) by Substitute(injective.definition of (f := g, A := B))(have(injective(g)(B)) by Hypothesis)
    val cSubset = have(∀(x, x ∈ C ==> x ∈ A)) by Tautology.from(Subset.definition of (x := C, y := A))
    have(x ∈ step(A)(B)(f)(g)(C) <=> x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ C /\ (f(z) === y)))) by Tautology.from(stepMembership of (S := C))
    thenHave(x ∈ C <=> x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ C /\ (f(z) === y)))) by Substitute(step(A)(B)(f)(g)(C) === C)
    val fixed = thenHave(∀(x, x ∈ C <=> x ∈ A /\ ∀(y, (y ∈ B /\ (g(y) === x)) ==> ∃(z, z ∈ C /\ (f(z) === y))))) by RightForall

    // g(y) is in C exactly when y is in f[C].
    have(y ∈ B ==> (g(y) ∈ C <=> ∃(x, x ∈ C /\ (f(x) === y)))) by Superpose.from(fixed, gTyped, gInjective)
    val imageCriterion = thenHave(∀(y, y ∈ B ==> (g(y) ∈ C <=> ∃(x, x ∈ C /\ (f(x) === y))))) by RightForall
    have((x ∈ A /\ x ∉ C) ==> ∃(y, y ∈ B /\ (g(y) === x))) by Superpose.from(fixed)
    val outsidePreimage = thenHave(∀(x, (x ∈ A /\ x ∉ C) ==> ∃(y, y ∈ B /\ (g(y) === x)))) by RightForall

    def link(x: Expr[Ind], y: Expr[Ind]): Expr[Prop] = (x ∈ C /\ (f(x) === y)) \/ (x ∉ C /\ (g(y) === x))
    val total = have(∀(x, x ∈ A ==> ∃(y, y ∈ B /\ link(x, y)))) by Superpose.from(fTyped, outsidePreimage)
    val onto = have(∀(y, y ∈ B ==> ∃(x, x ∈ A /\ link(x, y)))) by Superpose.from(gTyped, cSubset, imageCriterion)
    val unique = have(∀(x, ∀(y, ∀(z, (x ∈ A /\ y ∈ B /\ z ∈ B /\ link(x, y) /\ link(x, z)) ==> (y === z))))) by Superpose.from(gInjective)
    val reverseUnique = have(∀(x, ∀(z, ∀(y, (x ∈ A /\ z ∈ A /\ y ∈ B /\ link(x, y) /\ link(z, y)) ==> (x === z))))) by Superpose.from(fInjective, imageCriterion)
    have(thesis) by Tautology.from(
      total,
      onto,
      unique,
      reverseUnique,
      Matching.bijection of (Variable[Ind >>: Ind >>: Prop]("P") := λ(x, λ(y, link(x, y))))
    )
  }

  /**
   * Mutual injections suffice, with no nonemptiness hypotheses.
   */
  val bijection = Theorem(
    (functionBetween(f)(A)(B), injective(f)(A), functionBetween(g)(B)(A), injective(g)(B)) |- ∃(h, bijective(h)(A)(B))
  ) {
    assumeAll
    have(C ⊆ A /\ (step(A)(B)(f)(g)(C) === C) |- ∃(h, bijective(h)(A)(B))) by Tautology.from(bijectionOfFixedPoint)
    thenHave(∃(C, C ⊆ A /\ (step(A)(B)(f)(g)(C) === C)) |- ∃(h, bijective(h)(A)(B))) by LeftExists
    thenHave(thesis) by Tautology.fromLastStep(partitionExists)
  }
}
