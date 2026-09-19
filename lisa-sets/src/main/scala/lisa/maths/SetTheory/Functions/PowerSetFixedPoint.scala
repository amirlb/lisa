package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{_, given}

/**
 * A monotone self-map of a powerset has a fixed point (no ordinal recursion).
 */
object PowerSetFixedPoint extends lisa.Main {
  private val A, C, S, T, x = variable[Ind]
  private val H = variable[Ind >>: Ind]

  val fixedPoint = Theorem(
    (
      ∀(S, S ⊆ A ==> H(S) ⊆ A),
      ∀(S, ∀(T, (S ⊆ A /\ T ⊆ A /\ S ⊆ T) ==> H(S) ⊆ H(T)))
    ) |- ∃(C, C ⊆ A /\ (H(C) === C))
  ) {
    val bounded = assume(∀(S, S ⊆ A ==> H(S) ⊆ A))
    val monotone = assume(∀(S, ∀(T, (S ⊆ A /\ T ⊆ A /\ S ⊆ T) ==> H(S) ⊆ H(T))))
    val L = { x ∈ A | ∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S) }
    val lSubset = have(L ⊆ A) by Tautology.from(Comprehension.subset of (y := A, φ := λ(x, ∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S))))
    have(L ⊆ A ==> H(L) ⊆ A) by InstantiateForall(L)(bounded)
    val hlSubset = thenHave(H(L) ⊆ A) by Tautology.fromLastStep(lSubset)

    // L lies below every pre-fixed subset of A.
    val least = have((S ⊆ A, H(S) ⊆ S) |- L ⊆ S) subproof {
      assume(S ⊆ A)
      assume(H(S) ⊆ S)
      have(x ∈ L |- x ∈ S) subproof {
        assume(x ∈ L)
        have(x ∈ L <=> x ∈ A /\ ∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S)) by Comprehension.apply
        thenHave(∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S)) by Tautology.fromLastStep()
        thenHave((S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S) by InstantiateForall(S)
        thenHave(thesis) by Tautology.fromLastStep()
      }
      thenHave(x ∈ L ==> x ∈ S) by Restate
      thenHave(∀(x, x ∈ L ==> x ∈ S)) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := L, y := S))
    }

    // Monotonicity shows H(L) also lies below every pre-fixed subset.
    have((S ⊆ A, H(S) ⊆ S) |- H(L) ⊆ S) subproof {
      assume(S ⊆ A)
      assume(H(S) ⊆ S)
      val lBelow = have(L ⊆ S) by Tautology.from(least)
      have((L ⊆ A /\ S ⊆ A /\ L ⊆ S) ==> H(L) ⊆ H(S)) by InstantiateForall(L, S)(monotone)
      thenHave(H(L) ⊆ H(S)) by Tautology.fromLastStep(lSubset, lBelow)
      thenHave(thesis) by Tautology.fromLastStep(Subset.transitivity of (x := H(L), y := H(S), z := S))
    }
    thenHave((S ⊆ A /\ H(S) ⊆ S) ==> H(L) ⊆ S) by Restate
    val belowAll = thenHave(∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> H(L) ⊆ S)) by RightForall
    val preFixed = have(H(L) ⊆ L) subproof {
      have(x ∈ H(L) |- x ∈ L) subproof {
        assume(x ∈ H(L))
        val inA = have(x ∈ A) by Tautology.from(hlSubset, Subset.membership of (x := H(L), y := A, z := x))
        have((S ⊆ A /\ H(S) ⊆ S) ==> H(L) ⊆ S) by InstantiateForall(S)(belowAll)
        thenHave((S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S) by Tautology.fromLastStep(Subset.membership of (x := H(L), y := S, z := x))
        val all = thenHave(∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S)) by RightForall
        have(x ∈ L <=> x ∈ A /\ ∀(S, (S ⊆ A /\ H(S) ⊆ S) ==> x ∈ S)) by Comprehension.apply
        thenHave(thesis) by Tautology.fromLastStep(inA, all)
      }
      thenHave(x ∈ H(L) ==> x ∈ L) by Restate
      thenHave(∀(x, x ∈ H(L) ==> x ∈ L)) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := H(L), y := L))
    }

    have((H(L) ⊆ A /\ L ⊆ A /\ H(L) ⊆ L) ==> H(H(L)) ⊆ H(L)) by InstantiateForall(H(L), L)(monotone)
    val hhBelow = thenHave(H(H(L)) ⊆ H(L)) by Tautology.fromLastStep(hlSubset, lSubset, preFixed)
    val postFixed = have(L ⊆ H(L)) by Tautology.from(least of (S := H(L)), hlSubset, hhBelow)
    have(H(L) === L) by Tautology.from(preFixed, postFixed, Subset.doubleInclusion of (x := H(L), y := L))
    thenHave(L ⊆ A /\ (H(L) === L)) by Tautology.fromLastStep(lSubset)
    thenHave(thesis) by RightExists
  }
}
