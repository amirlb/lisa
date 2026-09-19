package lisa.maths.Algebra

import lisa.automation.Superpose
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Examples.ConstantFunction
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * An explicit inhabited model, not an assumed group instance.
 */
object TrivialGroup extends lisa.Main {
  private val G, m, e, i, A, c, x, y, z = variable[Ind]
  val multiplication = DEF(λ(e, ConstantFunction.constantFunction(singleton(e) × singleton(e))(e)))
  val inversion = DEF(λ(e, ConstantFunction.constantFunction(singleton(e))(e)))

  val isGroup = Theorem(Group.group(singleton(e))(multiplication(e))(e)(inversion(e))) {
    val S = singleton(e)
    val M = multiplication(e)
    val I = inversion(e)
    val fnM = have(functionBetween(M)(S × S)(S)) by Substitute(multiplication.definition)(ConstantFunction.function of (A := (S × S), c := e))
    val fnI = have(functionBetween(I)(S)(S)) by Substitute(inversion.definition)(ConstantFunction.function of (A := S, c := e))
    val identityMember = have(e ∈ S) by Tautology.from(Singleton.membership of (x := e, y := e))
    val pairMember = have(pair(e)(e) ∈ (S × S)) by Tautology.from(identityMember, CartesianProduct.pairMembership of (A := S, B := S, x := e, y := e))
    have(ConstantFunction.constantFunction(S × S)(e)(pair(e)(e)) === e) by Tautology.from(pairMember, ConstantFunction.application of (A := (S × S), c := e, x := pair(e)(e)))
    val multiply = thenHave(M(pair(e)(e)) === e) by Substitute(multiplication.definition)
    have(ConstantFunction.constantFunction(S)(e)(e) === e) by Tautology.from(identityMember, ConstantFunction.application of (A := S, c := e, x := e))
    val invert = thenHave(I(e) === e) by Substitute(inversion.definition)
    have(x ∈ S <=> (x === e)) by Restate.from(Singleton.membership of (x := e, y := x))
    val members = thenHave(∀(x, x ∈ S <=> (x === e))) by RightForall
    val assoc = have(∀(x, ∀(y, ∀(z, (x ∈ S /\ y ∈ S /\ z ∈ S) ==> (M(pair(M(pair(x)(y)))(z)) === M(pair(x)(M(pair(y)(z))))))))) by Superpose.from(members, multiply)
    val ident = have(∀(x, x ∈ S ==> ((M(pair(e)(x)) === x) /\ (M(pair(x)(e)) === x)))) by Superpose.from(members, multiply)
    val inverse = have(∀(x, x ∈ S ==> ((M(pair(I(x))(x)) === e) /\ (M(pair(x)(I(x))) === e)))) by Superpose.from(members, multiply, invert)
    have(thesis) by Tautology.from(fnM, fnI, identityMember, assoc, ident, inverse, Group.group.definition of (G := S, m := M, i := I))
  }
}
