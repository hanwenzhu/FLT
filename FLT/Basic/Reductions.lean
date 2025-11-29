import Architect
import FLT.GaloisRepresentation.HardlyRamified.Frey
/-!

# Preliminary reductions of FLT

This file reduces Fermat's Last Theorem
to Mazur's theorem and the Wiles/Taylor--Wiles theorem.

# Main theorems

* `FLT.FreyPackage.false`: There is no Frey Package.
* `Wiles_Taylor_Wiles` : Fermat's Last Theorem is true.

-/

/-!

Given an elliptic curve over `ℚ`, the p-torsion points defined over an algebraic
closure of `ℚ` are a 2-dimensional Galois representation.

What can we say about the Galois
representation attached to the p-torsion of the Frey curve attached to a Frey package?

It follows (after a little work!) from a profound theorem of Mazur that this representation
must be irreducible.

-/

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

open WeierstrassCurve

@[blueprint
  "Mazur_Frey"
  (title := "Mazur")
  (statement := /-- If $\rho$ is the mod $p$ Galois representation associated to a Frey package
    $(a,b,c,p)$ then
    $\rho$ is irreducible. -/)
  (proof := /-- This follows from a profound and long result of Mazur \cite{mazur-torsion} from
    1977,
    namely the fact that the torsion subgroup of an elliptic curve over $\Q$ can have size at
    most~16.
    In fact there is still a little more work which needs to be done to deduce the theorem from
    Mazur's result. A pre-1990 reference for the full proof of this claim is Proposition~6
    in~\S4.1 of~\cite{serreconj}. -/)
  (proofUses := ["Frey_curve_irreducible"])]
theorem Mazur_Frey (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry

/-!

But it follows from a profound theorem of Ribet, and the even more profound theorem
(proved by Wiles) that the representation cannot be irreducible.

-/

@[blueprint
  "Wiles_Frey"
  (title := "Wiles,Taylor--Wiles, Ribet,\\ldots")
  (statement := /-- If $\rho$ is the mod $p$ Galois representation associated to a Frey package
    $(a,b,c,p)$ then
    $\rho$ is reducible. -/)
  (proof := /-- %
      This is the main content of Wiles' magnum opus.
      We omit the argument for now, although later on in this project
      we will have a lot to say about a proof of this. -/)]
theorem Wiles_Frey (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  FreyCurve.torsion_not_isIrreducible P

/-!

It follows that there is no Frey package.

-/

/-- There is no Frey package. This profound result is proved using
work of Mazur and Wiles/Ribet to rule out all possibilities for the
$p$-torsion in the corresponding Frey curve. -/
@[blueprint
  "FreyPackage.false"
  (statement := /-- There is no Frey package. -/)
  (proof := /-- Follows immediately from the previous two
     theorems~\ref{Mazur_Frey} and~\ref{Wiles_Frey}. -/)
  (latexEnv := "corollary")]
theorem FreyPackage.false (P : FreyPackage) : False := by
  -- by Wiles' result, the p-torsion is not irreducible
  apply Wiles_Frey P
  -- but by Mazur's result, the p-torsion is irreducible!
  exact Mazur_Frey P
  -- Contradiction!

/-- Fermat's Last Theorem is true -/
@[blueprint
  "FLT"
  (statement := /-- Fermat's Last Theorem is true. In other words, there are no positive integers
    $a,b,c$ and
    natural $n\geq3$ such that $a^n+b^n=c^n$. -/)
  (proof := /-- Assume there is a there is a counterexample $a^n+b^n=c^n$.
    By Corollary \ref{FermatLastTheorem.of_p_ge_5} we may assume that there is also a counterexample
    $a^p+b^p=c^p$ with $p\geq 5$ and prime.
    Then there is a Frey package $(a,b,c,p)$ by~\ref{FreyPackage.of_not_FermatLastTheorem_p_ge_5},
    contradicting Corollary~\ref{FreyPackage.false}. -/)
  (latexEnv := "corollary")]
theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  -- Suppose Fermat's Last Theorem is false
  by_contra h
  -- then there exists a Frey package
  obtain ⟨P : FreyPackage⟩ := FreyPackage.of_not_FermatLastTheorem h
  -- but there is no Frey package
  exact P.false
