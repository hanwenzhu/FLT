import Architect
import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.GaloisRepresentation.HardlyRamified.ModThree -- will be needed for proof

namespace GaloisRepresentation.IsHardlyRamified

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

-- TODO -- make some API for "I have a rank 1 quotient where Galois acts trivially"
-- e.g. this implies trace(Frob_p) is (1+p)

/--
A 3-adic hardly ramified representation has trace(Frob_p) = 1 + p for all p ≠ 2,3
-/
@[blueprint
  "hardly_ramified_3adic_reducible"
  (statement := /-- Suppose $L/\Q_3$ is a finite extension, with integer ring $\calO_L$, and suppose
    $\rho_3:\GQ\to\GL_2(\calO_L)$ is hardly ramified. Then (considered as a representation
    to $\GL_2(L)$) $\rho_3^{ss}=1\oplus\chi_3$
    where $1$ is the trivial character and $\chi_3$ is the 3-adic cyclotomic character. -/)
  (proof := /-- Omitted for now {\bf TODO} -/)]
theorem three_adic {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ p (hp : Nat.Prime p) (hp5 : 5 ≤ p),
      letI v := hp.toHeightOneSpectrumRingOfIntegersRat -- p as a finite place of ℚ
      (ρ.toLocal v (Frob v)).trace _ _ = 1 + p := sorry

end GaloisRepresentation.IsHardlyRamified
