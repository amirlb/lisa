package lisa.utils.prooflib

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
    ProofChecks.requireFresh()
    val expectedNoSurjection = functionBetween(f)(A)(𝒫(A)) |- ¬(surjective(f)(𝒫(A)))
    val expectedInjection = () |- ∃(f, functionBetween(f)(A)(𝒫(A)) /\ injective(f)(A))
    val expectedCantor = () |- ∀(x, Cardinal.dominates(x)(𝒫(x)) /\ ¬(Cardinal.equinumerosity(x)(𝒫(x))))
    ProofChecks.expect(Cantor.noSurjection, expectedNoSurjection)
    ProofChecks.expect(Cantor.singletonInjection, expectedInjection)
    ProofChecks.expect(Cardinal.cantorTheorem, expectedCantor)
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
    ProofChecks.verify("CANTOR_CHECK", theorems)
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
