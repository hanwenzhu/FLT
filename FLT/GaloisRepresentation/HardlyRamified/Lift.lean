import Architect
import FLT.GaloisRepresentation.HardlyRamified.Defs

namespace GaloisRepresentation.IsHardlyRamified

universe u v

variable {k : Type u} [Fintype k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k]
    [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2)

open TensorProduct

/--
An irreducible mod p hardly ramified represntation lifts to a p-adic one.
-/
@[blueprint
  "hardly_ramified_lifts"
  (statement := /-- If $\ell\geq3$ is prime and $\overline{\rho}:\GQ\to\GL_2(\Z/\ell\Z)$
    is hardly ramified and irreducible, then there exists a finite extension~$K$ of $\Q_\ell$
    with integer ring~$\calO$ and maximal ideal $\mathfrak{m}$
    and a hardly ramified representation
    $\rho:\GQ\to\GL_2(\calO)$ whose reduction modulo~$\m$ is isomorphic to $\rho$. -/)
  (proof := /-- Omitted for now {\bf TODO} -/)]
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry

end GaloisRepresentation.IsHardlyRamified
