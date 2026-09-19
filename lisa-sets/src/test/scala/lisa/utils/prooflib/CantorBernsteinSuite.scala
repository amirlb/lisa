package lisa.utils.prooflib

import lisa.SetTheoryLibrary
import lisa.automation.Superpose
import lisa.kernel.proof.SCProofChecker
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
    require(!SetTheoryLibrary.isDraft, "Cantor–Bernstein must be checked outside draft mode")
    require(!SetTheoryLibrary._withCache, "This check requires fresh proof generation")
    val expectedBijection = (functionBetween(f)(A)(B), injective(f)(A), functionBetween(g)(B)(A), injective(g)(B)) |- ∃(h, bijective(h)(A)(B))
    val expectedCardinal = (Cardinal.dominates(α)(β), Cardinal.dominates(β)(α)) |- Cardinal.equinumerosity(α)(β)
    require(isSameSequent(CantorBernstein.bijection.statement, expectedBijection))
    require(isSameSequent(Cardinal.cantorBernsteinTheorem.statement, expectedCardinal))
    require(isSameSequent(BernsteinExamples.empty.statement, () |- Cardinal.equinumerosity(∅)(∅)))
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
    theorems.foreach { theorem =>
      require(!theorem.withSorry, s"Admitted dependency: ${theorem.fullName}")
      require(theorem.highProof.nonEmpty, s"Expected a freshly generated proof: ${theorem.fullName}")
      require(theorem.kernelProof.exists(p => SCProofChecker.checkSCProof(p).isValid), s"Kernel rejected ${theorem.fullName}")
      println(s"BERNSTEIN_CHECK ${theorem.fullName}: checked, no admitted dependencies")
    }
    println("BERNSTEIN_CHECK PASSED")
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
