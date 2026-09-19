package lisa.utils.prooflib

import lisa.SetTheoryLibrary
import lisa.kernel.proof.SCProofChecker
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Cardinal.Cardinal
import lisa.maths.SetTheory.Functions.Cantor
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import org.scalatest.funsuite.AnyFunSuite

/**
 * An executable check as well as a regression suite; run in a fresh JVM.
 */
object CantorCheck extends lisa.Main {
  private val A, f, x = variable[Ind]

  def verify(): Unit = {
    require(!SetTheoryLibrary.isDraft, "Cantor must be checked outside draft mode")
    require(!SetTheoryLibrary._withCache, "This check requires fresh proof generation")
    val expectedNoSurjection = functionBetween(f)(A)(𝒫(A)) |- ¬(surjective(f)(𝒫(A)))
    val expectedInjection = () |- ∃(f, functionBetween(f)(A)(𝒫(A)) /\ injective(f)(A))
    val expectedCantor = () |- ∀(x, Cardinal.dominates(x)(𝒫(x)) /\ ¬(Cardinal.equinumerosity(x)(𝒫(x))))
    require(isSameSequent(Cantor.noSurjection.statement, expectedNoSurjection))
    require(isSameSequent(Cantor.singletonInjection.statement, expectedInjection))
    require(isSameSequent(Cardinal.cantorTheorem.statement, expectedCantor))
    val theorems = List(
      Cantor.noSurjection,
      Cantor.singletonGraphMembership,
      Cantor.singletonGraphFunction,
      Cantor.singletonGraphApplication,
      Cantor.singletonInjection,
      Cardinal.cantorTheorem,
      EmptyCantor.noSurjection,
      EmptyCantor.strictCardinality
    )
    theorems.foreach { theorem =>
      require(!theorem.withSorry, s"Admitted dependency: ${theorem.fullName}")
      require(theorem.highProof.nonEmpty, s"Expected a freshly generated proof: ${theorem.fullName}")
      require(theorem.kernelProof.exists(p => SCProofChecker.checkSCProof(p).isValid), s"Kernel rejected ${theorem.fullName}")
      println(s"CANTOR_CHECK ${theorem.fullName}: checked, no admitted dependencies")
    }
    println("CANTOR_CHECK PASSED")
  }

  override def main(args: Array[String]): Unit = verify()
}

private object EmptyCantor extends lisa.Main {
  private val f = variable[Ind]
  val noSurjection = Theorem(functionBetween(f)(∅)(𝒫(∅)) |- ¬(surjective(f)(𝒫(∅)))) {
    have(thesis) by Restate.from(Cantor.noSurjection of (A := ∅))
  }
  val strictCardinality = Theorem(Cardinal.dominates(∅)(𝒫(∅)) /\ ¬(Cardinal.equinumerosity(∅)(𝒫(∅)))) {
    have(thesis) by InstantiateForall(∅)(Cardinal.cantorTheorem)
  }
}

class CantorSuite extends AnyFunSuite {
  test("Cantor, singleton injection, and the empty case are freshly checked without admissions") {
    CantorCheck.verify()
  }
}
