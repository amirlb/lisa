package lisa.utils.prooflib

import lisa.SetTheoryLibrary
import lisa.maths.Algebra.Group
import lisa.utils.fol.FOL._
import org.scalatest.funsuite.AnyFunSuite

/**
 * Negative fixtures must never be included in the verified theorem registry.
 */
private object AdmissionFixture extends lisa.Main {
  val intentionallyAdmitted = Theorem(⊥) { sorry }
}

class ProofChecksSuite extends AnyFunSuite {
  test("reject empty checks") {
    intercept[IllegalArgumentException](ProofChecks.verify("empty", Nil))
  }
  test("reject wrong statements") {
    intercept[IllegalArgumentException](ProofChecks.expect(Group.identityMember, () |- ()))
  }
  test("reject admitted proofs even when the kernel accepts Sorry") {
    val theorem = AdmissionFixture.intentionallyAdmitted
    assert(theorem.withSorry)
    val error = intercept[IllegalArgumentException](ProofChecks.verify("negative-fixture", Seq(theorem)))
    assert(error.getMessage.contains("Admitted dependency"))
  }
  test("refuse cache mode and restore library settings") {
    val old = SetTheoryLibrary._withCache
    try {
      SetTheoryLibrary._withCache = true
      intercept[IllegalArgumentException](ProofChecks.requireFresh())
    } finally SetTheoryLibrary._withCache = old
  }
  test("refuse draft mode and restore library settings") {
    val old = SetTheoryLibrary._draft
    try {
      SetTheoryLibrary._draft = Some(sourcecode.File("negative-fixture"))
      intercept[IllegalArgumentException](ProofChecks.requireFresh())
    } finally SetTheoryLibrary._draft = old
  }
}
