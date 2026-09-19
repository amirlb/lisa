package lisa.maths.Algebra

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Cardinal.Cardinal
import lisa.maths.SetTheory.Functions.PartitionProduct
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Lagrange in its bijective/cardinal form: (G/H) × H is equipotent to G.
 * Representatives are selected using LISA's existing Hilbert epsilon.
 * Consequently this construction also applies to infinite groups.
 */
object Lagrange extends lisa.Main {
  private val G, H, m, e, i, a, C, D, x, y, z, f, A, B, Q = variable[Ind]
  private def mul(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = m(pair(x)(y))

  val cosets = DEF(λ(G, λ(H, λ(m, { Coset.left(G)(H)(m)(a) | a ∈ G }))))
  val representative = DEF(λ(G, λ(H, λ(m, λ(C, ε(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C)))))))
  private def rep(C: Expr[Ind]): Expr[Ind] = representative(G)(H)(m)(C)

  val cosetsMembership = Theorem(C ∈ cosets(G)(H)(m) <=> ∃(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C))) {
    have(C ∈ { Coset.left(G)(H)(m)(a) | a ∈ G } <=> ∃(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C))) by Replacement.apply
    thenHave(thesis) by Substitute(cosets.definition)
  }
  val selection = Theorem(C ∈ cosets(G)(H)(m) |- rep(C) ∈ G /\ (Coset.left(G)(H)(m)(rep(C)) === C)) {
    assume(C ∈ cosets(G)(H)(m))
    have(∃(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C))) by Tautology.from(cosetsMembership)
    thenHave(
      ε(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C)) ∈ G /\
        (Coset.left(G)(H)(m)(ε(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C))) === C)
    ) by Tautology.fromLastStep(Quantifiers.existsEpsilon of (P := λ(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === C))))
    thenHave(thesis) by Substitute(representative.definition)
  }

  val bounded = Theorem((C ∈ cosets(G)(H)(m), y ∈ C) |- y ∈ G) {
    assumeAll
    val eq = have(Coset.left(G)(H)(m)(rep(C)) === C) by Tautology.from(selection)
    have(y ∈ Coset.left(G)(H)(m)(rep(C))) by Congruence.from(eq)
    thenHave(thesis) by Tautology.fromLastStep(Coset.membership of (a := rep(C), x := y))
  }
  val covers = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), y ∈ G) |- ∃(C, C ∈ cosets(G)(H)(m) /\ y ∈ C)) {
    assumeAll
    val member = have(y ∈ Coset.left(G)(H)(m)(y)) by Tautology.from(Coset.representativeMember of (a := y))
    have(y ∈ G /\ (Coset.left(G)(H)(m)(y) === Coset.left(G)(H)(m)(y))) by Tautology
    thenHave(∃(a, a ∈ G /\ (Coset.left(G)(H)(m)(a) === Coset.left(G)(H)(m)(y)))) by RightExists
    thenHave(Coset.left(G)(H)(m)(y) ∈ cosets(G)(H)(m)) by Tautology.fromLastStep(cosetsMembership of (C := Coset.left(G)(H)(m)(y)))
    thenHave(Coset.left(G)(H)(m)(y) ∈ cosets(G)(H)(m) /\ y ∈ Coset.left(G)(H)(m)(y)) by Tautology.fromLastStep(member)
    thenHave(thesis) by RightExists
  }
  val disjoint = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), C ∈ cosets(G)(H)(m), D ∈ cosets(G)(H)(m), y ∈ C, y ∈ D) |- C === D) {
    assumeAll
    val cEq = have(Coset.left(G)(H)(m)(rep(C)) === C) by Tautology.from(selection)
    val dEq = have(Coset.left(G)(H)(m)(rep(D)) === D) by Tautology.from(selection of (C := D))
    val cMember = have(y ∈ Coset.left(G)(H)(m)(rep(C))) by Congruence.from(cEq)
    val dMember = have(y ∈ Coset.left(G)(H)(m)(rep(D))) by Congruence.from(dEq)
    have(Coset.left(G)(H)(m)(rep(C)) === Coset.left(G)(H)(m)(rep(D))) by Tautology.from(cMember, dMember, selection, selection of (C := D), Coset.overlap of (a := rep(C), b := rep(D), x := y))
    have(thesis) by Congruence.from(lastStep, cEq, dEq)
  }

  val translationTyped = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), C ∈ cosets(G)(H)(m), x ∈ H) |- mul(rep(C), x) ∈ C) {
    assumeAll
    val eq = have(Coset.left(G)(H)(m)(rep(C)) === C) by Tautology.from(selection)
    have(mul(rep(C), x) ∈ Coset.left(G)(H)(m)(rep(C))) by Tautology.from(selection, Coset.productMember of (a := rep(C), h := x))
    have(thesis) by Congruence.from(lastStep, eq)
  }
  val translationOnto = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), C ∈ cosets(G)(H)(m), y ∈ C) |- ∃(x, x ∈ H /\ (mul(rep(C), x) === y))) {
    assumeAll
    val eq = have(Coset.left(G)(H)(m)(rep(C)) === C) by Tautology.from(selection)
    have(y ∈ Coset.left(G)(H)(m)(rep(C))) by Congruence.from(eq)
    thenHave(thesis) by Tautology.fromLastStep(Coset.membership of (a := rep(C), x := y))
  }
  val translationInjective = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), C ∈ cosets(G)(H)(m), x ∈ H, z ∈ H, mul(rep(C), x) === mul(rep(C), z)) |- x === z) {
    have(thesis) by Tautology.from(selection, Subgroup.ambientGroup, Subgroup.member, Subgroup.member of (x := z), Group.leftCancellation of (x := rep(C), y := x))
  }

  val bijection = Theorem(Subgroup.subgroup(H)(G)(m)(e)(i) |- ∃(f, bijective(f)(cosets(G)(H)(m) × H)(G))) {
    assumeAll
    val blocks = cosets(G)(H)(m)
    have((C ∈ blocks /\ y ∈ C) ==> y ∈ G) by Tautology.from(bounded)
    val allBounded = thenHave(∀(C, ∀(y, (C ∈ blocks /\ y ∈ C) ==> y ∈ G))) by Generalize
    have(y ∈ G ==> ∃(C, C ∈ blocks /\ y ∈ C)) by Tautology.from(covers)
    val allCovers = thenHave(∀(y, y ∈ G ==> ∃(C, C ∈ blocks /\ y ∈ C))) by RightForall
    have((C ∈ blocks /\ D ∈ blocks /\ y ∈ C /\ y ∈ D) ==> (C === D)) by Tautology.from(disjoint)
    val allDisjoint = thenHave(∀(C, ∀(D, ∀(y, (C ∈ blocks /\ D ∈ blocks /\ y ∈ C /\ y ∈ D) ==> (C === D))))) by Generalize
    have((C ∈ blocks /\ x ∈ H) ==> mul(rep(C), x) ∈ C) by Tautology.from(translationTyped)
    val allTyped = thenHave(∀(C, ∀(x, (C ∈ blocks /\ x ∈ H) ==> mul(rep(C), x) ∈ C))) by Generalize
    have((C ∈ blocks /\ y ∈ C) ==> ∃(x, x ∈ H /\ (mul(rep(C), x) === y))) by Tautology.from(translationOnto)
    val allOnto = thenHave(∀(C, ∀(y, (C ∈ blocks /\ y ∈ C) ==> ∃(x, x ∈ H /\ (mul(rep(C), x) === y))))) by Generalize
    have((C ∈ blocks /\ x ∈ H /\ z ∈ H /\ (mul(rep(C), x) === mul(rep(C), z))) ==> (x === z)) by Tautology.from(translationInjective)
    val allInjective = thenHave(∀(C, ∀(x, ∀(z, (C ∈ blocks /\ x ∈ H /\ z ∈ H /\ (mul(rep(C), x) === mul(rep(C), z))) ==> (x === z))))) by Generalize
    have(thesis) by Tautology.from(
      allBounded,
      allCovers,
      allDisjoint,
      allTyped,
      allOnto,
      allInjective,
      PartitionProduct.bijection of (A := G, Q := blocks, Variable[Ind >>: Ind >>: Ind]("F") := λ(C, λ(x, mul(rep(C), x))))
    )
  }

  /**
   * |G/H| · |H| = |G|, with products represented by Cartesian products.
   */
  val cardinalIdentity = Theorem(Subgroup.subgroup(H)(G)(m)(e)(i) |- Cardinal.equinumerosity(cosets(G)(H)(m) × H)(G)) {
    have(thesis) by Substitute(Cardinal.equinumerosity.definition of (A := (cosets(G)(H)(m) × H), B := G))(bijection)
  }

  /**
   * Cardinal divisibility: there is a set of copies of H bijective with G.
   * This is not a definition of natural-number divisibility.
   */
  val cardinalDivisibility = Theorem(Subgroup.subgroup(H)(G)(m)(e)(i) |- ∃(Q, Cardinal.equinumerosity(Q × H)(G))) {
    assumeAll
    have(Cardinal.equinumerosity(cosets(G)(H)(m) × H)(G)) by Tautology.from(cardinalIdentity)
    thenHave(thesis) by RightExists
  }
}
