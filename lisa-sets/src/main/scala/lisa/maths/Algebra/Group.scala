package lisa.maths.Algebra

import lisa.automation.Superpose
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Groups with explicit set-valued operations, ready to be packaged as structures.
 * Multiplication is a function G × G → G, not a curried function on all sets.
 * Every algebraic law is restricted to the carrier.
 */
object Group extends lisa.Main {
  private val G, m, e, i, x, y, z = variable[Ind]
  private def mul(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = m(pair(x)(y))

  val group = DEF(
    λ(
      G,
      λ(
        m,
        λ(
          e,
          λ(
            i,
            functionBetween(m)(G × G)(G) /\ functionBetween(i)(G)(G) /\ e ∈ G /\
              ∀(
                x,
                ∀(
                  y,
                  ∀(
                    z,
                    (x ∈ G /\ y ∈ G /\ z ∈ G) ==>
                      (mul(mul(x, y), z) === mul(x, mul(y, z)))
                  )
                )
              ) /\
              ∀(x, x ∈ G ==> ((mul(e, x) === x) /\ (mul(x, e) === x))) /\
              ∀(x, x ∈ G ==> ((mul(i(x), x) === e) /\ (mul(x, i(x)) === e)))
          )
        )
      )
    )
  )

  val multiplicationFunction = Theorem(group(G)(m)(e)(i) |- functionBetween(m)(G × G)(G)) {
    have(thesis) by Tautology.from(group.definition)
  }
  val inverseFunction = Theorem(group(G)(m)(e)(i) |- functionBetween(i)(G)(G)) {
    have(thesis) by Tautology.from(group.definition)
  }
  val identityMember = Theorem(group(G)(m)(e)(i) |- e ∈ G) {
    have(thesis) by Tautology.from(group.definition)
  }
  val closure = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G) |- mul(x, y) ∈ G) {
    have(thesis) by Tautology.from(multiplicationFunction, CartesianProduct.pairMembership of (A := G, B := G), BasicTheorems.appTyping of (f := m, A := (G × G), B := G, x := (x, y)))
  }
  val inverseMember = Theorem((group(G)(m)(e)(i), x ∈ G) |- i(x) ∈ G) {
    have(thesis) by Tautology.from(inverseFunction, BasicTheorems.appTyping of (f := i, A := G, B := G))
  }
  val associative = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G, z ∈ G) |- mul(mul(x, y), z) === mul(x, mul(y, z))) {
    assume(group(G)(m)(e)(i))
    have(∀(x, ∀(y, ∀(z, (x ∈ G /\ y ∈ G /\ z ∈ G) ==> (mul(mul(x, y), z) === mul(x, mul(y, z))))))) by Tautology.from(group.definition)
    thenHave((x ∈ G /\ y ∈ G /\ z ∈ G) ==> (mul(mul(x, y), z) === mul(x, mul(y, z)))) by InstantiateForall(x, y, z)
    thenHave(thesis) by Restate
  }
  val identity = Theorem((group(G)(m)(e)(i), x ∈ G) |- (mul(e, x) === x) /\ (mul(x, e) === x)) {
    assume(group(G)(m)(e)(i))
    have(∀(x, x ∈ G ==> ((mul(e, x) === x) /\ (mul(x, e) === x)))) by Tautology.from(group.definition)
    thenHave(x ∈ G ==> ((mul(e, x) === x) /\ (mul(x, e) === x))) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }
  val inverse = Theorem((group(G)(m)(e)(i), x ∈ G) |- (mul(i(x), x) === e) /\ (mul(x, i(x)) === e)) {
    assume(group(G)(m)(e)(i))
    have(∀(x, x ∈ G ==> ((mul(i(x), x) === e) /\ (mul(x, i(x)) === e)))) by Tautology.from(group.definition)
    thenHave(x ∈ G ==> ((mul(i(x), x) === e) /\ (mul(x, i(x)) === e))) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  val leftUndo = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G) |- mul(i(x), mul(x, y)) === y) {
    have(thesis) by Superpose.from(inverseMember, associative of (x := i(x), y := x, z := y), inverse, identity of (x := y))
  }
  val rightUndo = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G) |- mul(mul(y, x), i(x)) === y) {
    have(thesis) by Superpose.from(inverseMember, associative of (x := y, y := x, z := i(x)), inverse, identity of (x := y))
  }
  val leftCancellation = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G, z ∈ G, mul(x, y) === mul(x, z)) |- y === z) {
    have(thesis) by Superpose.from(leftUndo, leftUndo of (y := z))
  }
  val rightCancellation = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G, z ∈ G, mul(y, x) === mul(z, x)) |- y === z) {
    have(thesis) by Superpose.from(rightUndo, rightUndo of (y := z))
  }
  val inverseUnique = Theorem((group(G)(m)(e)(i), x ∈ G, y ∈ G, mul(x, y) === e) |- y === i(x)) {
    have(thesis) by Superpose.from(inverseMember, inverse, leftCancellation of (z := i(x)))
  }
  val inverseInvolution = Theorem((group(G)(m)(e)(i), x ∈ G) |- i(i(x)) === x) {
    have(thesis) by Superpose.from(inverseMember, inverse, inverseUnique of (x := i(x), y := x))
  }
  val inverseIdentity = Theorem(group(G)(m)(e)(i) |- i(e) === e) {
    have(thesis) by Superpose.from(identityMember, identity of (x := e), inverseUnique of (x := e, y := e))
  }
}
