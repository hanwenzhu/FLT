import Architect
import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.Basic.FreyPackage

variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

@[blueprint
  "Frey_curve_hardly_ramified"
  (statement := /-- The $\ell$-torsion $\rho:\GQ\to\GL_2(\Z/\ell\Z)$ in the Frey curve associated to
    a Frey
    package $(a,b,c,\ell)$ is hardly ramified. -/)
  (proof := /-- This was well-known in the 1980s. A proof sketch is as follows.
    First note that $\ell\geq5>3$ by definition of a Frey package. Let $\rho$
    denote the Galois representation on the $\ell$-torsion of the Frey curve.
    The fact that $\rho$ is 2-dimensional is~Corollary
    III.6.4(b) of~\cite{silverman1}, and the fact that its determinant is
    cyclotomic is Proposition~III.8.3 of the same reference. These results hold for elliptic curves
    in general. The remaining claims are specific to the Frey curve and lie
    deeper. The fact that $\rho$ is unramified outside $2\ell$ is a consequence
    of (4.1.12) and (4.1.13) of~\cite{serreconj}. The fact that $\rho$ at 2
    has an unramified 1-dimensional quotient of order at most 2 follows from
    the fact that the Frey curve is semistable at~2 (see (4.1.5) of~\cite{serreconj})
    and the theory of the Tate curve. Finally, the claim that $\rho$ is flat at $\ell$
    is Proposition~5 and (4.1.13) of~\cite{serreconj}. -/)]
theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd sorry
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

@[blueprint
  "hardly_ramified_reducible"
  (statement := /-- If $\ell\geq 3$ is a prime and $\rho:\GQ\to\GL_2(\Z/\ell\Z)$ is hardly ramified,
    then $\rho$ is reducible. -/)
  (proof := /-- Assume for a contradiction that $\overline{\rho}$ is irreducible. By
    theorem~\ref{hardly_ramified_lifts},
    $\overline{\rho}$ lifts to a hardly ramified $\ell$-adic reprepresentation $\rho$. By
    theorem~\ref{hardly_ramified_spreads_out}, $\rho$ is part of a compatible family of
    $q$-adic Galois representations. By theorem~\ref{hardly_ramified_3adic_reducible},
    any 3-adic member $\rho_3$ of this family has semisimplification $1\oplus\chi_3$ and in
    particular
    for $p\nmid 6$ we have that the characteristic polynomial of $\rho_3(\Frob_p)=(X-p)(X-1).$
    By compatibility of the family we deduce that for $p\nmid 6\ell$ the characteristic
    polynomial of $\rho(\Frob_p)$ is $(X-p)(X-1)$, and thus the characteristic polynomial
    of $\overline{\rho}(\Frob_p)$ is $(X-p)(X-1)$. By the Cebotarev density theorem,
    $\overline{\rho}$ and $1\oplus\chi$ have the same characteristic polynomials everywhere
    (here $\chi$ is the mod $\ell$ cyclotomic character). Thus by the Brauer-Nesbitt theorem,
    $\overline{\rho}$ is reducible, the contradiction we seek. -/)
  (proofUses := ["hardly_ramified_lifts", "hardly_ramified_spreads_out",
    "hardly_ramified_3adic_reducible"])]
theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry -- TODO prove this
