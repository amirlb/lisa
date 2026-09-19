package lisa.maths.SetTheory.Functions

import lisa.automation.Superpose
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Assemble specified bijective parametrizations of disjoint blocks.
 * This lemma itself makes no choice of parametrizations.
 */
object PartitionProduct extends lisa.Main {
  private val A, B, Q, H, C, D, x, y, z, p, q, f = variable[Ind]
  private val F = variable[Ind >>: Ind >>: Ind]

  val bijection = Theorem(
    (
      ∀(C, ∀(y, (C ∈ Q /\ y ∈ C) ==> y ∈ A)),
      ∀(y, y ∈ A ==> ∃(C, C ∈ Q /\ y ∈ C)),
      ∀(C, ∀(D, ∀(y, (C ∈ Q /\ D ∈ Q /\ y ∈ C /\ y ∈ D) ==> (C === D)))),
      ∀(C, ∀(x, (C ∈ Q /\ x ∈ H) ==> F(C)(x) ∈ C)),
      ∀(C, ∀(y, (C ∈ Q /\ y ∈ C) ==> ∃(x, x ∈ H /\ (F(C)(x) === y)))),
      ∀(C, ∀(x, ∀(z, (C ∈ Q /\ x ∈ H /\ z ∈ H /\ (F(C)(x) === F(C)(z))) ==> (x === z))))
    ) |- ∃(f, bijective(f)(Q × H)(A))
  ) {
    val bounded = assume(∀(C, ∀(y, (C ∈ Q /\ y ∈ C) ==> y ∈ A)))
    val covers = assume(∀(y, y ∈ A ==> ∃(C, C ∈ Q /\ y ∈ C)))
    val disjoint = assume(∀(C, ∀(D, ∀(y, (C ∈ Q /\ D ∈ Q /\ y ∈ C /\ y ∈ D) ==> (C === D)))))
    val typed = assume(∀(C, ∀(x, (C ∈ Q /\ x ∈ H) ==> F(C)(x) ∈ C)))
    val onto = assume(∀(C, ∀(y, (C ∈ Q /\ y ∈ C) ==> ∃(x, x ∈ H /\ (F(C)(x) === y)))))
    val inject = assume(∀(C, ∀(x, ∀(z, (C ∈ Q /\ x ∈ H /\ z ∈ H /\ (F(C)(x) === F(C)(z))) ==> (x === z)))))
    val product = Q × H
    def value(p: Expr[Ind]) = F(fst(p))(snd(p))
    have(p ∈ product ==> (fst(p) ∈ Q /\ snd(p) ∈ H /\ (p === pair(fst(p))(snd(p))))) by Tautology.from(
      CartesianProduct.fstMembership of (A := Q, B := H, z := p),
      CartesianProduct.sndMembership of (A := Q, B := H, z := p),
      CartesianProduct.inversion of (A := Q, B := H, z := p)
    )
    val projections = thenHave(∀(p, p ∈ product ==> (fst(p) ∈ Q /\ snd(p) ∈ H /\ (p === pair(fst(p))(snd(p)))))) by RightForall
    val total = have(∀(p, p ∈ product ==> ∃(y, y ∈ A /\ (value(p) === y)))) by Superpose.from(projections, typed, bounded)

    have((C ∈ Q, x ∈ H) |- ∃(p, p ∈ product /\ (value(p) === F(C)(x)))) subproof {
      assume(C ∈ Q)
      assume(x ∈ H)
      val pairTyped = have(pair(C)(x) ∈ product) by Tautology.from(CartesianProduct.pairMembership of (A := Q, B := H, x := C, y := x))
      have(value(pair(C)(x)) === F(C)(x)) by Congruence.from(Pair.pairFst of (x := C, y := x), Pair.pairSnd of (x := C, y := x))
      thenHave(pair(C)(x) ∈ product /\ (value(pair(C)(x)) === F(C)(x))) by Tautology.fromLastStep(pairTyped)
      thenHave(thesis) by RightExists
    }
    thenHave((C ∈ Q /\ x ∈ H) ==> ∃(p, p ∈ product /\ (value(p) === F(C)(x)))) by Restate
    val pairWitness = thenHave(∀(C, ∀(x, (C ∈ Q /\ x ∈ H) ==> ∃(p, p ∈ product /\ (value(p) === F(C)(x)))))) by Generalize
    have(y ∈ A |- ∃(p, p ∈ product /\ (value(p) === y))) subproof {
      assume(y ∈ A)
      have((C ∈ Q, y ∈ C) |- ∃(p, p ∈ product /\ (value(p) === y))) subproof {
        assume(C ∈ Q)
        assume(y ∈ C)
        have((x ∈ H, F(C)(x) === y) |- ∃(p, p ∈ product /\ (value(p) === y))) subproof {
          assume(x ∈ H)
          assume(F(C)(x) === y)
          have((C ∈ Q /\ x ∈ H) ==> ∃(p, p ∈ product /\ (value(p) === F(C)(x)))) by InstantiateForall(C, x)(pairWitness)
          thenHave(∃(p, p ∈ product /\ (value(p) === F(C)(x)))) by Tautology.fromLastStep()
          thenHave(thesis) by Substitute(F(C)(x) === y)
        }
        thenHave(x ∈ H /\ (F(C)(x) === y) |- ∃(p, p ∈ product /\ (value(p) === y))) by Restate
        val witness = thenHave(∃(x, x ∈ H /\ (F(C)(x) === y)) |- ∃(p, p ∈ product /\ (value(p) === y))) by LeftExists
        have((C ∈ Q /\ y ∈ C) ==> ∃(x, x ∈ H /\ (F(C)(x) === y))) by InstantiateForall(C, y)(onto)
        thenHave(thesis) by Tautology.fromLastStep(witness)
      }
      thenHave(C ∈ Q /\ y ∈ C |- ∃(p, p ∈ product /\ (value(p) === y))) by Restate
      val block = thenHave(∃(C, C ∈ Q /\ y ∈ C) |- ∃(p, p ∈ product /\ (value(p) === y))) by LeftExists
      have(y ∈ A ==> ∃(C, C ∈ Q /\ y ∈ C)) by InstantiateForall(y)(covers)
      thenHave(thesis) by Tautology.fromLastStep(block)
    }
    thenHave(y ∈ A ==> ∃(p, p ∈ product /\ (value(p) === y))) by Restate
    val allOnto = thenHave(∀(y, y ∈ A ==> ∃(p, p ∈ product /\ (value(p) === y)))) by RightForall
    val unique = have(∀(p, ∀(y, ∀(z, (p ∈ product /\ y ∈ A /\ z ∈ A /\ (value(p) === y) /\ (value(p) === z)) ==> (y === z))))) by Superpose
    val valueInjective = have((p ∈ product, q ∈ product, value(p) === value(q)) |- p === q) subproof {
      assumeAll
      have(p ∈ product ==> (fst(p) ∈ Q /\ snd(p) ∈ H /\ (p === pair(fst(p))(snd(p))))) by InstantiateForall(p)(projections)
      val pp = thenHave(fst(p) ∈ Q /\ snd(p) ∈ H /\ (p === pair(fst(p))(snd(p)))) by Tautology.fromLastStep()
      have(q ∈ product ==> (fst(q) ∈ Q /\ snd(q) ∈ H /\ (q === pair(fst(q))(snd(q))))) by InstantiateForall(q)(projections)
      val pq = thenHave(fst(q) ∈ Q /\ snd(q) ∈ H /\ (q === pair(fst(q))(snd(q)))) by Tautology.fromLastStep()
      have((fst(p) ∈ Q /\ snd(p) ∈ H) ==> value(p) ∈ fst(p)) by InstantiateForall(fst(p), snd(p))(typed)
      val inP = thenHave(value(p) ∈ fst(p)) by Tautology.fromLastStep(pp)
      have((fst(q) ∈ Q /\ snd(q) ∈ H) ==> value(q) ∈ fst(q)) by InstantiateForall(fst(q), snd(q))(typed)
      thenHave(value(q) ∈ fst(q)) by Tautology.fromLastStep(pq)
      val inQ = thenHave(value(p) ∈ fst(q)) by Congruence
      have((fst(p) ∈ Q /\ fst(q) ∈ Q /\ value(p) ∈ fst(p) /\ value(p) ∈ fst(q)) ==> (fst(p) === fst(q))) by InstantiateForall(fst(p), fst(q), value(p))(disjoint)
      val sameBlock = thenHave(fst(p) === fst(q)) by Tautology.fromLastStep(pp, pq, inP, inQ)
      val sameValue = have(F(fst(p))(snd(p)) === F(fst(p))(snd(q))) by Congruence.from(sameBlock)
      have((fst(p) ∈ Q /\ snd(p) ∈ H /\ snd(q) ∈ H /\ (F(fst(p))(snd(p)) === F(fst(p))(snd(q)))) ==> (snd(p) === snd(q))) by InstantiateForall(fst(p), snd(p), snd(q))(inject)
      val sameArgument = thenHave(snd(p) === snd(q)) by Tautology.fromLastStep(pp, pq, sameValue)
      val pPair = have(p === pair(fst(p))(snd(p))) by Tautology.from(pp)
      val qPair = have(q === pair(fst(q))(snd(q))) by Tautology.from(pq)
      have(thesis) by Congruence.from(sameBlock, sameArgument, pPair, qPair)
    }
    have((p ∈ product, q ∈ product, y ∈ A, value(p) === y, value(q) === y) |- p === q) subproof {
      assumeAll
      have(value(p) === value(q)) by Congruence
      thenHave(thesis) by Tautology.fromLastStep(valueInjective)
    }
    thenHave((p ∈ product /\ q ∈ product /\ y ∈ A /\ (value(p) === y) /\ (value(q) === y)) ==> (p === q)) by Restate
    val reverseUnique = thenHave(∀(p, ∀(q, ∀(y, (p ∈ product /\ q ∈ product /\ y ∈ A /\ (value(p) === y) /\ (value(q) === y)) ==> (p === q))))) by Generalize
    have(thesis) by Tautology.from(total, allOnto, unique, reverseUnique, Matching.bijection of (A := product, B := A, Variable[Ind >>: Ind >>: Prop]("P") := λ(p, λ(y, value(p) === y))))
  }
}
