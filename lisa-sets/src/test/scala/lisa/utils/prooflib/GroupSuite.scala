package lisa.utils.prooflib

import lisa.maths.Algebra.Coset
import lisa.maths.Algebra.Group
import lisa.maths.Algebra.Subgroup
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import org.scalatest.funsuite.AnyFunSuite

object GroupCheck extends lisa.Main {
  private val G, H, m, e, i, a, f, x, y = variable[Ind]

  def verify(): Unit = {
    ProofChecks.requireFresh()
    // In particular, multiplication takes an ordered pair, not two curried arguments.
    val expectedClosure = (Group.group(G)(m)(e)(i), x ∈ G, y ∈ G) |- m(pair(x)(y)) ∈ G
    val expectedTranslation = (Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G) |- ∃(f, bijective(f)(H)(Coset.left(G)(H)(m)(a)))
    ProofChecks.expect(Group.closure, expectedClosure)
    ProofChecks.expect(Coset.translationBijection, expectedTranslation)
    val theorems = List(
      Group.multiplicationFunction,
      Group.inverseFunction,
      Group.identityMember,
      Group.closure,
      Group.inverseMember,
      Group.associative,
      Group.identity,
      Group.inverse,
      Group.leftUndo,
      Group.rightUndo,
      Group.leftCancellation,
      Group.rightCancellation,
      Group.inverseUnique,
      Group.inverseInvolution,
      Group.inverseIdentity,
      Subgroup.ambientGroup,
      Subgroup.subset,
      Subgroup.member,
      Subgroup.identityMember,
      Subgroup.closure,
      Subgroup.inverseMember,
      Subgroup.self,
      Coset.membership,
      Coset.subset,
      Coset.representativeMember,
      Coset.translationBijection
    )
    ProofChecks.verify("GROUP_CHECK", theorems)
  }

  override def main(args: Array[String]): Unit = verify()
}

class GroupSuite extends AnyFunSuite {
  test("Group laws and coset translation are freshly checked without admissions") {
    GroupCheck.verify()
  }
}
