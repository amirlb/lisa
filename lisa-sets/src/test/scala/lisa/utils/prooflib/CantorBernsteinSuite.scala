package lisa.utils.prooflib

import lisa.automation.Superpose
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Cardinal.Cardinal
import lisa.maths.SetTheory.Functions.CantorBernstein
import lisa.maths.SetTheory.Functions.Matching
import lisa.maths.SetTheory.Functions.PowerSetFixedPoint
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import org.scalatest.funsuite.AnyFunSuite

/**
 * Fresh kernel checks, including transitive admission checks and exact public statements.
 */
object CantorBernsteinCheck extends lisa.Main {
  private val A, B, f, g, h, α, β = variable[Ind]

  def verify(): Unit = {
    ProofChecks.requireFresh()
    val expectedBijection = (functionBetween(f)(A)(B), injective(f)(A), functionBetween(g)(B)(A), injective(g)(B)) |- ∃(h, bijective(h)(A)(B))
    val expectedCardinal = (Cardinal.dominates(α)(β), Cardinal.dominates(β)(α)) |- Cardinal.equinumerosity(α)(β)
    ProofChecks.expect(CantorBernstein.bijection, expectedBijection)
    ProofChecks.expect(Cardinal.cantorBernsteinTheorem, expectedCardinal)
    ProofChecks.expect(BernsteinExamples.empty, () |- Cardinal.equinumerosity(∅)(∅))
    val theorems = List(
      PowerSetFixedPoint.fixedPoint,
      Matching.membership,
      Matching.bounded,
      Matching.bijection,
      CantorBernstein.stepMembership,
      CantorBernstein.stepBounded,
      CantorBernstein.stepMonotone,
      CantorBernstein.partitionExists,
      CantorBernstein.bijectionOfFixedPoint,
      CantorBernstein.bijection,
      Cardinal.cantorBernsteinTheorem,
      BernsteinExamples.identityMatching,
      BernsteinExamples.reflexiveDomination,
      BernsteinExamples.reflexiveEquinumerosity,
      BernsteinExamples.empty
    )
    ProofChecks.verify("BERNSTEIN_CHECK", theorems)
  }

  override def main(args: Array[String]): Unit = verify()
}

private object BernsteinExamples extends lisa.Main {
  private val A, B, f, h, x, y, z, α, β = variable[Ind]

  val identityMatching = Theorem(∃(h, bijective(h)(A)(A))) {
    val total = have(∀(x, x ∈ A ==> ∃(y, y ∈ A /\ (x === y)))) by Superpose
    val onto = have(∀(y, y ∈ A ==> ∃(x, x ∈ A /\ (x === y)))) by Superpose
    val unique = have(∀(x, ∀(y, ∀(z, (x ∈ A /\ y ∈ A /\ z ∈ A /\ (x === y) /\ (x === z)) ==> (y === z))))) by Superpose
    val reverseUnique = have(∀(x, ∀(z, ∀(y, (x ∈ A /\ z ∈ A /\ y ∈ A /\ (x === y) /\ (z === y)) ==> (x === z))))) by Superpose
    have(thesis) by Tautology.from(total, onto, unique, reverseUnique, Matching.bijection of (B := A, Variable[Ind >>: Ind >>: Prop]("P") := λ(x, λ(y, x === y))))
  }

  val reflexiveDomination = Theorem(Cardinal.dominates(A)(A)) {
    have(bijective(f)(A)(A) |- functionBetween(f)(A)(A) /\ injective(f)(A)) by Tautology.from(bijective.definition of (B := A))
    thenHave(bijective(f)(A)(A) |- ∃(f, functionBetween(f)(A)(A) /\ injective(f)(A))) by RightExists
    thenHave(∃(f, bijective(f)(A)(A)) |- ∃(f, functionBetween(f)(A)(A) /\ injective(f)(A))) by LeftExists
    thenHave(∃(f, functionBetween(f)(A)(A) /\ injective(f)(A))) by Tautology.fromLastStep(identityMatching)
    thenHave(thesis) by Substitute(Cardinal.dominates.definition of (B := A))
  }

  val reflexiveEquinumerosity = Theorem(Cardinal.equinumerosity(A)(A)) {
    have(thesis) by Tautology.from(reflexiveDomination, Cardinal.cantorBernsteinTheorem of (α := A, β := A))
  }

  val empty = Theorem(Cardinal.equinumerosity(∅)(∅)) {
    have(thesis) by Restate.from(reflexiveEquinumerosity of (A := ∅))
  }
}

class CantorBernsteinSuite extends AnyFunSuite {
  test("Cantor–Bernstein and its supporting lemmas are freshly checked without admissions") {
    CantorBernsteinCheck.verify()
  }
}
