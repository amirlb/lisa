package lisa.maths.Algebra

import lisa.automation.Superpose
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Matching
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Left cosets; no normality assumption is used.
 */
object Coset extends lisa.Main {
  private val G, H, m, e, i, a, b, c, k, x, y, z, h, f, A, B = variable[Ind]
  private def mul(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = m(pair(x)(y))

  val left = DEF(λ(G, λ(H, λ(m, λ(a, { x ∈ G | ∃(h, h ∈ H /\ (mul(a, h) === x)) })))))

  val membership = Theorem(x ∈ left(G)(H)(m)(a) <=> x ∈ G /\ ∃(h, h ∈ H /\ (mul(a, h) === x))) {
    have(x ∈ { x ∈ G | ∃(h, h ∈ H /\ (mul(a, h) === x)) } <=> x ∈ G /\ ∃(h, h ∈ H /\ (mul(a, h) === x))) by Comprehension.apply
    thenHave(thesis) by Substitute(left.definition)
  }
  val subset = Theorem(left(G)(H)(m)(a) ⊆ G) {
    have({ x ∈ G | ∃(h, h ∈ H /\ (mul(a, h) === x)) } ⊆ G) by Restate.from(
      Comprehension.subset of (y := G, φ := λ(x, ∃(h, h ∈ H /\ (mul(a, h) === x))))
    )
    thenHave(thesis) by Substitute(left.definition)
  }

  val representativeMember = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G) |- a ∈ left(G)(H)(m)(a)) {
    assumeAll
    have(e ∈ H /\ (mul(a, e) === a)) by Tautology.from(Subgroup.identityMember, Subgroup.ambientGroup, Group.identity of (x := a))
    thenHave(∃(h, h ∈ H /\ (mul(a, h) === a))) by RightExists
    thenHave(thesis) by Tautology.fromLastStep(membership of (x := a))
  }

  val productMember = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G, h ∈ H) |- mul(a, h) ∈ left(G)(H)(m)(a)) {
    assumeAll
    val typed = have(mul(a, h) ∈ G) by Tautology.from(Subgroup.ambientGroup, Subgroup.member of (x := h), Group.closure of (x := a, y := h))
    have(h ∈ H /\ (mul(a, h) === mul(a, h))) by Tautology
    thenHave(∃(k, k ∈ H /\ (mul(a, k) === mul(a, h)))) by RightExists
    thenHave(thesis) by Tautology.fromLastStep(typed, membership of (x := mul(a, h)))
  }

  /**
   * Membership in another coset is symmetric on the group carrier.
   */
  val symmetric = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G, b ∈ G, b ∈ left(G)(H)(m)(a)) |- a ∈ left(G)(H)(m)(b)) {
    assumeAll
    have((h ∈ H, mul(a, h) === b) |- a ∈ left(G)(H)(m)(b)) subproof {
      assume(h ∈ H)
      assume(mul(a, h) === b)
      val invH = have(i(h) ∈ H) by Tautology.from(Subgroup.inverseMember of (x := h))
      val undo = have(mul(mul(a, h), i(h)) === a) by Tautology.from(Subgroup.ambientGroup, Subgroup.member of (x := h), Group.rightUndo of (x := h, y := a))
      have(mul(b, i(h)) ∈ left(G)(H)(m)(b)) by Tautology.from(invH, productMember of (a := b, h := i(h)))
      have(thesis) by Congruence.from(lastStep, undo)
    }
    thenHave(h ∈ H /\ (mul(a, h) === b) |- a ∈ left(G)(H)(m)(b)) by Restate
    thenHave(∃(h, h ∈ H /\ (mul(a, h) === b)) |- a ∈ left(G)(H)(m)(b)) by LeftExists
    thenHave(thesis) by Tautology.fromLastStep(membership of (x := b))
  }

  /**
   * The relation x ∈ aH is transitive.
   */
  val transitive = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G, b ∈ G, c ∈ G, b ∈ left(G)(H)(m)(a), c ∈ left(G)(H)(m)(b)) |- c ∈ left(G)(H)(m)(a)) {
    assumeAll
    have((h ∈ H, mul(a, h) === b, k ∈ H, mul(b, k) === c) |- c ∈ left(G)(H)(m)(a)) subproof {
      assume(h ∈ H)
      assume(mul(a, h) === b)
      assume(k ∈ H)
      assume(mul(b, k) === c)
      val closed = have(mul(h, k) ∈ H) by Tautology.from(Subgroup.closure of (x := h, y := k))
      val assoc =
        have(mul(mul(a, h), k) === mul(a, mul(h, k))) by Tautology.from(Subgroup.ambientGroup, Subgroup.member of (x := h), Subgroup.member of (x := k), Group.associative of (x := a, y := h, z := k))
      have(mul(a, mul(h, k)) ∈ left(G)(H)(m)(a)) by Tautology.from(closed, productMember of (h := mul(h, k)))
      have(thesis) by Congruence.from(lastStep, assoc)
    }
    thenHave((h ∈ H /\ (mul(a, h) === b), k ∈ H /\ (mul(b, k) === c)) |- c ∈ left(G)(H)(m)(a)) by Restate
    thenHave((h ∈ H /\ (mul(a, h) === b), ∃(k, k ∈ H /\ (mul(b, k) === c))) |- c ∈ left(G)(H)(m)(a)) by LeftExists
    thenHave((∃(h, h ∈ H /\ (mul(a, h) === b)), ∃(k, k ∈ H /\ (mul(b, k) === c))) |- c ∈ left(G)(H)(m)(a)) by LeftExists
    thenHave(thesis) by Tautology.fromLastStep(membership of (x := b), membership of (a := b, x := c))
  }

  val sameCoset = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G, b ∈ G, b ∈ left(G)(H)(m)(a)) |- left(G)(H)(m)(a) === left(G)(H)(m)(b)) {
    assumeAll
    val reverse = have(a ∈ left(G)(H)(m)(b)) by Tautology.from(symmetric)
    val typedA = have(x ∈ left(G)(H)(m)(a) ==> x ∈ G) by Tautology.from(membership)
    val typedB = have(x ∈ left(G)(H)(m)(b) ==> x ∈ G) by Tautology.from(membership of (a := b))
    have(x ∈ left(G)(H)(m)(a) <=> x ∈ left(G)(H)(m)(b)) by Tautology.from(reverse, typedA, typedB, transitive of (c := x), transitive of (a := b, b := a, c := x))
    thenHave(thesis) by Extensionality
  }

  val overlap = Theorem((Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G, b ∈ G, x ∈ left(G)(H)(m)(a), x ∈ left(G)(H)(m)(b)) |- left(G)(H)(m)(a) === left(G)(H)(m)(b)) {
    assumeAll
    val typed = have(x ∈ G) by Tautology.from(membership)
    val first = have(left(G)(H)(m)(a) === left(G)(H)(m)(x)) by Tautology.from(typed, sameCoset of (b := x))
    have(left(G)(H)(m)(b) === left(G)(H)(m)(x)) by Tautology.from(typed, sameCoset of (a := b, b := x))
    have(thesis) by Congruence.from(lastStep, first)
  }

  /**
   * The graph of left multiplication is a bijection H → aH.
   */
  val translationBijection = Theorem(
    (Subgroup.subgroup(H)(G)(m)(e)(i), a ∈ G) |- ∃(f, bijective(f)(H)(left(G)(H)(m)(a)))
  ) {
    assumeAll
    val C = left(G)(H)(m)(a)
    val groupFact = have(Group.group(G)(m)(e)(i)) by Tautology.from(Subgroup.ambientGroup)
    have(x ∈ H ==> x ∈ G) by Tautology.from(Subgroup.member)
    val inclusion = thenHave(∀(x, x ∈ H ==> x ∈ G)) by RightForall
    have(x ∈ H ==> mul(a, x) ∈ G) by Tautology.from(Subgroup.member, groupFact, Group.closure of (x := a, y := x))
    val typed = thenHave(∀(x, x ∈ H ==> mul(a, x) ∈ G)) by RightForall
    have(y ∈ C <=> y ∈ G /\ ∃(x, x ∈ H /\ (mul(a, x) === y))) by Tautology.from(membership of (x := y))
    val members = thenHave(∀(y, y ∈ C <=> y ∈ G /\ ∃(x, x ∈ H /\ (mul(a, x) === y)))) by RightForall
    val total = have(∀(x, x ∈ H ==> ∃(y, y ∈ C /\ (mul(a, x) === y)))) by Superpose.from(typed, members)
    val onto = have(∀(y, y ∈ C ==> ∃(x, x ∈ H /\ (mul(a, x) === y)))) by Superpose.from(members)
    val unique = have(∀(x, ∀(y, ∀(z, (x ∈ H /\ y ∈ C /\ z ∈ C /\ (mul(a, x) === y) /\ (mul(a, x) === z)) ==> (y === z))))) by Superpose
    have((x ∈ G /\ z ∈ G /\ (mul(a, x) === mul(a, z))) ==> (x === z)) by Tautology.from(groupFact, Group.leftCancellation of (x := a, y := x))
    val cancel = thenHave(∀(x, ∀(z, (x ∈ G /\ z ∈ G /\ (mul(a, x) === mul(a, z))) ==> (x === z)))) by Generalize
    val reverseUnique = have(∀(x, ∀(z, ∀(y, (x ∈ H /\ z ∈ H /\ y ∈ C /\ (mul(a, x) === y) /\ (mul(a, z) === y)) ==> (x === z))))) by Superpose.from(inclusion, cancel)
    have(thesis) by Tautology.from(total, onto, unique, reverseUnique, Matching.bijection of (A := H, B := C, Variable[Ind >>: Ind >>: Prop]("P") := λ(x, λ(y, mul(a, x) === y))))
  }
}
