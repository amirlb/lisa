package lisa.maths.Algebra

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * A subgroup is a subset closed under the ambient group's operations.
 * Its multiplication need not be stored as a second, restricted graph.
 */
object Subgroup extends lisa.Main {
  private val G, H, m, e, i, x, y = variable[Ind]
  private def mul(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = m(pair(x)(y))

  val subgroup = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          m,
          λ(
            e,
            λ(
              i,
              Group.group(G)(m)(e)(i) /\ H ⊆ G /\ e ∈ H /\
                ∀(x, ∀(y, (x ∈ H /\ y ∈ H) ==> mul(x, y) ∈ H)) /\
                ∀(x, x ∈ H ==> i(x) ∈ H)
            )
          )
        )
      )
    )
  )

  val ambientGroup = Theorem(subgroup(H)(G)(m)(e)(i) |- Group.group(G)(m)(e)(i)) {
    have(thesis) by Tautology.from(subgroup.definition)
  }
  val subset = Theorem(subgroup(H)(G)(m)(e)(i) |- H ⊆ G) {
    have(thesis) by Tautology.from(subgroup.definition)
  }
  val member = Theorem((subgroup(H)(G)(m)(e)(i), x ∈ H) |- x ∈ G) {
    have(thesis) by Tautology.from(subset, Subset.membership of (x := H, y := G, z := x))
  }
  val identityMember = Theorem(subgroup(H)(G)(m)(e)(i) |- e ∈ H) {
    have(thesis) by Tautology.from(subgroup.definition)
  }
  val closure = Theorem((subgroup(H)(G)(m)(e)(i), x ∈ H, y ∈ H) |- mul(x, y) ∈ H) {
    assume(subgroup(H)(G)(m)(e)(i))
    have(∀(x, ∀(y, (x ∈ H /\ y ∈ H) ==> mul(x, y) ∈ H))) by Tautology.from(subgroup.definition)
    thenHave((x ∈ H /\ y ∈ H) ==> mul(x, y) ∈ H) by InstantiateForall(x, y)
    thenHave(thesis) by Restate
  }
  val inverseMember = Theorem((subgroup(H)(G)(m)(e)(i), x ∈ H) |- i(x) ∈ H) {
    assume(subgroup(H)(G)(m)(e)(i))
    have(∀(x, x ∈ H ==> i(x) ∈ H)) by Tautology.from(subgroup.definition)
    thenHave(x ∈ H ==> i(x) ∈ H) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  val self = Theorem(Group.group(G)(m)(e)(i) |- subgroup(G)(G)(m)(e)(i)) {
    assume(Group.group(G)(m)(e)(i))
    have((x ∈ G /\ y ∈ G) ==> mul(x, y) ∈ G) by Tautology.from(Group.closure)
    val closed = thenHave(∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> mul(x, y) ∈ G))) by Generalize
    have(x ∈ G ==> i(x) ∈ G) by Tautology.from(Group.inverseMember)
    val inverses = thenHave(∀(x, x ∈ G ==> i(x) ∈ G)) by RightForall
    have(thesis) by Tautology.from(closed, inverses, Group.identityMember, Subset.reflexivity of (x := G), subgroup.definition of (H := G))
  }
}
