package lisa.utils.prooflib

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary._
import lisa.kernel.proof.SCProofChecker
import lisa.utils.fol.FOL.Sequent
import lisa.utils.fol.FOL.isSameSequent

/**
 * Shared trust boundary for the project's executable proof checks.
 */
object ProofChecks {
  def requireFresh(): Unit = {
    require(!SetTheoryLibrary.isDraft, "Proof checks refuse draft mode")
    require(!SetTheoryLibrary._withCache, "Proof checks require fresh proof generation")
  }

  def expect(theorem: THM, expected: Sequent): Unit = {
    require(isSameSequent(theorem.statement, expected), s"Statement mismatch: ${theorem.fullName}\nExpected: $expected\nActual: ${theorem.statement}")
  }

  def verify(label: String, theorems: Seq[THM]): Unit = {
    requireFresh()
    require(theorems.nonEmpty, s"Empty proof check: $label")
    theorems.foreach { theorem =>
      require(!theorem.withSorry, s"Admitted dependency: ${theorem.fullName}")
      require(theorem.highProof.nonEmpty, s"Expected a freshly generated proof: ${theorem.fullName}")
      require(theorem.kernelProof.exists(p => SCProofChecker.checkSCProof(p).isValid), s"Kernel rejected ${theorem.fullName}")
    }
    // Inventory is diagnostic output, never a substitute for the checks above.
    val roots = theorems.map(_.fullName).toSet
    val seen = scala.collection.mutable.Set.empty[String]
    def encoded(s: String): String = java.util.Base64.getEncoder.encodeToString(s.getBytes(java.nio.charset.StandardCharsets.UTF_8))
    def visit(j: JUSTIFICATION): Unit = if (seen.add(j.fullName)) {
      val dependencies = j match {
        case t: THM => t.highProof.toList.flatMap(_.justifications)
        case _ => Nil
      }
      val status = if (j.withSorry) "admitted" else if (roots(j.fullName)) "checked" else "dependency"
      val kind = j match {
        case _: THM => "theorem"
        case _: DEFINITION => "definition"
        case _: AXIOM => "axiom"
      }
      val statement =
        try j.statement.toString
        catch { case scala.util.control.NonFatal(_) => s"[kernel syntax] ${j.statement.underlying}" }
      println(s"PROOF_RECORD\t${encoded(j.fullName)}\t${encoded(statement)}\t${encoded(dependencies.map(_.fullName).sorted.mkString("\n"))}\t$status\t$kind")
      dependencies.foreach(visit)
    }
    theorems.foreach(visit)
    println(s"PROOF_CHECK $label PASSED (${theorems.size} fresh kernel proofs; no admitted dependencies)")
  }
}

object TheoryCheck {
  def main(args: Array[String]): Unit = {
    ProofChecks.requireFresh()
    CantorCheck.verify()
    CantorBernsteinCheck.verify()
    GroupCheck.verify()
    LagrangeCheck.verify()
  }
}
