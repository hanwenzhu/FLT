import Architect
import FLT.GaloisRepresentation.HardlyRamified.Defs

namespace GaloisRepresentation.IsHardlyRamified

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

/-- A mod 3 hardly ramified representation is an extension of trivial by cyclo -/
@[blueprint
  "hardly_ramified_mod3_reducible"
  (statement := /-- Suppose $k$ is a finite field of characteristic 3, and suppose
    $\overline{rho}:\GQ\to\GL_2(k)$ is hardly ramified. Then $\overline{\rho}$ is an extension
    of the cyclotomic character by the trivial representation. -/)
  (proof := /-- Omitted for now. {\bf TODO} -/)]
-- Probably `Field k` can be replaced with `(3 : k) = 0`
theorem mod_three {k : Type u} [Fintype k] [Field k] [Algebra ℤ_[3] k] --
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  sorry

end GaloisRepresentation.IsHardlyRamified
