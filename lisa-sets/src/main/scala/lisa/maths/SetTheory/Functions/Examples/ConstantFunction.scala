package lisa.maths.SetTheory.Functions.Examples

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * The constant function with domain A and value c.
 */
object ConstantFunction extends lisa.Main {
  private val A, B, c, x, y, z, f = variable[Ind]

  val constantFunction = DEF(λ(A, λ(c, A × singleton(c))))

  val membership = Theorem(pair(x)(y) ∈ constantFunction(A)(c) <=> x ∈ A /\ (y === c)) {
    have(pair(x)(y) ∈ (A × singleton(c)) <=> x ∈ A /\ (y === c)) by Tautology.from(CartesianProduct.pairMembership of (B := singleton(c)), Singleton.membership of (x := c))
    thenHave(thesis) by Substitute(constantFunction.definition)
  }
  val function = Theorem(functionBetween(constantFunction(A)(c))(A)(singleton(c))) {
    have(constantFunction(A)(c) ⊆ (A × singleton(c))) by Substitute(constantFunction.definition)(Subset.reflexivity of (x := (A × singleton(c))))
    val bounded = thenHave(relationBetween(constantFunction(A)(c))(A)(singleton(c))) by Substitute(Relation.relationBetween.definition of (R := constantFunction(A)(c), X := A, Y := singleton(c)))
    have(x ∈ A |- ∃!(y, pair(x)(y) ∈ constantFunction(A)(c))) subproof {
      assume(x ∈ A)
      val member = have(pair(x)(c) ∈ constantFunction(A)(c)) by Tautology.from(membership of (y := c))
      have(pair(x)(y) ∈ constantFunction(A)(c) ==> (y === c)) by Tautology.from(membership)
      thenHave(∀(y, pair(x)(y) ∈ constantFunction(A)(c) ==> (y === c))) by RightForall
      thenHave(pair(x)(c) ∈ constantFunction(A)(c) /\ ∀(y, pair(x)(y) ∈ constantFunction(A)(c) ==> (y === c))) by Tautology.fromLastStep(member)
      thenHave(∃(z, pair(x)(z) ∈ constantFunction(A)(c) /\ ∀(y, pair(x)(y) ∈ constantFunction(A)(c) ==> (y === z)))) by RightExists
      thenHave(thesis) by Substitute(∃!.definition of (P := λ(y, pair(x)(y) ∈ constantFunction(A)(c))))
    }
    thenHave(x ∈ A ==> ∃!(y, pair(x)(y) ∈ constantFunction(A)(c))) by Restate
    thenHave(∀(x ∈ A, ∃!(y, pair(x)(y) ∈ constantFunction(A)(c)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(bounded, functionBetween.definition of (f := constantFunction(A)(c), B := singleton(c)))
  }
  val application = Theorem(x ∈ A |- constantFunction(A)(c)(x) === c) {
    have(thesis) by Tautology.from(function, BasicTheorems.appTyping of (f := constantFunction(A)(c), B := singleton(c)), Singleton.membership of (x := c, y := constantFunction(A)(c)(x)))
  }
}
