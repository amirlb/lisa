package lisa.utils.prooflib

import lisa.SetTheoryLibrary
import lisa.kernel.proof.SCProofChecker
import lisa.maths.Algebra.Coset
import lisa.maths.Algebra.Group
import lisa.maths.Algebra.Subgroup
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import org.scalatest.funsuite.AnyFunSuite

object GroupCheck extends lisa.Main {
  private val G, H, m, e, i, a, f, x, y = variable[Ind]

  def verify(): Unit = {
    require(!SetTheoryLibrary.isDraft, "Group proofs must be checked outside draft mode")
    require(!SetTheoryLibrary._withCache, "This check requires fresh proof generation")
    // In particular, multiplication takes an ordered pair, not two curried arguments.
    val expectedClosure = (Group.group(G)(m)(e)(i), x ∈ G, y ∈ G) |- m(pair(x)(y)) ∈ G
    val expectedTranslation = (Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G) |- ∃(f, bijective(f)(H)(Coset.left(G)(H)(m)(a)))
    require(isSameSequent(Group.closure.statement, expectedClosure))
    require(isSameSequent(Coset.translationBijection.statement, expectedTranslation))
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
    theorems.foreach { theorem =>
      require(!theorem.withSorry, s"Admitted dependency: ${theorem.fullName}")
      require(theorem.highProof.nonEmpty, s"Expected a freshly generated proof: ${theorem.fullName}")
      require(theorem.kernelProof.exists(p => SCProofChecker.checkSCProof(p).isValid), s"Kernel rejected ${theorem.fullName}")
      println(s"GROUP_CHECK ${theorem.fullName}: checked, no admitted dependencies")
    }
    println("GROUP_CHECK PASSED")
  }

  override def main(args: Array[String]): Unit = verify()
}

class GroupSuite extends AnyFunSuite {
  test("Group laws and coset translation are freshly checked without admissions") {
    GroupCheck.verify()
  }
}
