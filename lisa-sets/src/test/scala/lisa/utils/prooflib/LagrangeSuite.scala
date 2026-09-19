package lisa.utils.prooflib

import lisa.SetTheoryLibrary
import lisa.kernel.proof.SCProofChecker
import lisa.maths.Algebra.Coset
import lisa.maths.Algebra.Group
import lisa.maths.Algebra.Lagrange
import lisa.maths.Algebra.Subgroup
import lisa.maths.Algebra.TrivialGroup
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Cardinal.Cardinal
import lisa.maths.SetTheory.Functions.Examples.ConstantFunction
import lisa.maths.SetTheory.Functions.PartitionProduct
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import org.scalatest.funsuite.AnyFunSuite

object LagrangeCheck extends lisa.Main {
  private val G, H, m, e, i, f, Q = variable[Ind]

  def verify(): Unit = {
    require(!SetTheoryLibrary.isDraft, "Lagrange must be checked outside draft mode")
    require(!SetTheoryLibrary._withCache, "This check requires fresh proof generation")
    val expectedBijection = Subgroup.subgroup(H)(G)(m)(e)(i) |- ∃(f, bijective(f)(Lagrange.cosets(G)(H)(m) × H)(G))
    val expectedCardinal = Subgroup.subgroup(H)(G)(m)(e)(i) |- Cardinal.equinumerosity(Lagrange.cosets(G)(H)(m) × H)(G)
    val expectedDivisibility = Subgroup.subgroup(H)(G)(m)(e)(i) |- ∃(Q, Cardinal.equinumerosity(Q × H)(G))
    require(isSameSequent(Lagrange.bijection.statement, expectedBijection))
    require(isSameSequent(Lagrange.cardinalIdentity.statement, expectedCardinal))
    require(isSameSequent(Lagrange.cardinalDivisibility.statement, expectedDivisibility))
    require(TrivialGroup.isGroup.statement.left.isEmpty)
    require(LagrangeExamples.trivial.statement.left.isEmpty)
    val theorems = List(
      Coset.productMember,
      Coset.symmetric,
      Coset.transitive,
      Coset.sameCoset,
      Coset.overlap,
      PartitionProduct.bijection,
      Lagrange.cosetsMembership,
      Lagrange.selection,
      Lagrange.bounded,
      Lagrange.covers,
      Lagrange.disjoint,
      Lagrange.translationTyped,
      Lagrange.translationOnto,
      Lagrange.translationInjective,
      Lagrange.bijection,
      Lagrange.cardinalIdentity,
      Lagrange.cardinalDivisibility,
      ConstantFunction.membership,
      ConstantFunction.function,
      ConstantFunction.application,
      TrivialGroup.isGroup,
      LagrangeExamples.trivial,
      LagrangeExamples.emptyIsNotGroup
    )
    theorems.foreach { theorem =>
      require(!theorem.withSorry, s"Admitted dependency: ${theorem.fullName}")
      require(theorem.highProof.nonEmpty, s"Expected a freshly generated proof: ${theorem.fullName}")
      require(theorem.kernelProof.exists(p => SCProofChecker.checkSCProof(p).isValid), s"Kernel rejected ${theorem.fullName}")
      println(s"LAGRANGE_CHECK ${theorem.fullName}: checked, no admitted dependencies")
    }
    println("LAGRANGE_CHECK PASSED (bijective/cardinal form)")
  }

  override def main(args: Array[String]): Unit = verify()
}

private object LagrangeExamples extends lisa.Main {
  private val G, H, m, e, i = variable[Ind]
  val trivial = Theorem(Cardinal.equinumerosity(Lagrange.cosets(singleton(e))(singleton(e))(TrivialGroup.multiplication(e)) × singleton(e))(singleton(e))) {
    have(Subgroup.subgroup(singleton(e))(singleton(e))(TrivialGroup.multiplication(e))(e)(TrivialGroup.inversion(e))) by Tautology.from(
      TrivialGroup.isGroup,
      Subgroup.self of (G := singleton(e), m := TrivialGroup.multiplication(e), i := TrivialGroup.inversion(e))
    )
    thenHave(thesis) by Tautology.fromLastStep(Lagrange.cardinalIdentity of (G := singleton(e), H := singleton(e), m := TrivialGroup.multiplication(e), i := TrivialGroup.inversion(e)))
  }
  val emptyIsNotGroup = Theorem(¬(Group.group(∅)(m)(e)(i))) {
    have(thesis) by Tautology.from(Group.identityMember of (G := ∅), EmptySet.definition of (x := e))
  }
}

class LagrangeSuite extends AnyFunSuite {
  test("Lagrange's cardinal identity and an explicit group instance have no admissions") {
    LagrangeCheck.verify()
  }
}
