package lisa.utils.prooflib

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
    ProofChecks.requireFresh()
    val expectedBijection = Subgroup.subgroup(H)(G)(m)(e)(i) |- ∃(f, bijective(f)(Lagrange.cosets(G)(H)(m) × H)(G))
    val expectedCardinal = Subgroup.subgroup(H)(G)(m)(e)(i) |- Cardinal.equinumerosity(Lagrange.cosets(G)(H)(m) × H)(G)
    val expectedDivisibility = Subgroup.subgroup(H)(G)(m)(e)(i) |- ∃(Q, Cardinal.equinumerosity(Q × H)(G))
    ProofChecks.expect(Lagrange.bijection, expectedBijection)
    ProofChecks.expect(Lagrange.cardinalIdentity, expectedCardinal)
    ProofChecks.expect(Lagrange.cardinalDivisibility, expectedDivisibility)
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
    ProofChecks.verify("LAGRANGE_CHECK", theorems)
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
