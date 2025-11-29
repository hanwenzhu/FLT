import Architect
import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.Deformations.RepresentationTheory.GaloisRepFamily

namespace GaloisRepresentation.IsHardlyRamified

open GaloisRepresentation IsDedekindDomain

open scoped TensorProduct

universe u v

-- let ρ : G_ℚ → GL_2(R) be hardly ramified, where R is the integers in a finite
-- extension of ℚ_p
variable {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

@[blueprint
  "hardly_ramified_spreads_out"
  (statement := /-- If $\ell\geq3$ is prime, $K$ is a finite extension of $\Q_\ell$
    with integers $\calO$ and if $\rho:\GQ\to\GL_2(\calO)$ is a hardly ramified representation
    whose reduction is irreducible,
    then there exists a number field $M$ and, for each finite place $\mu$ of $M$
    of characteristic prime to 2, with completion $M_\mu$ having integer ring $R_\mu$,
    a hardly ramified semisimple representation $\rho_\mu:\GQ\to\GL_2(R_\mu)$ (by which we
    mean the generic fibre is semisimple), with the following properties:
    \begin{itemize}
      \item There is some $\lambda\mid\ell$ of $M$ such that $\rho_\lambda\cong\rho$,
        the isomorphism happening over some appropriate local field containing a copy
        of $M_\lambda$ and a copy of~$K$;
      \item If $\mu_1$ and $\mu_2$ are two finite places of $M$ with odd residue characteristics
      $m_1$
        and $m_2$, and if $p\nmid 2m_1m_2$ is prime, then $\rho_{\mu_1}$ and $\rho_{\mu_2}$
        are both unramified at~$p$ and the characteristic polynomials $\rho_{\mu_1}(\Frob_p)$
        and $\rho_{\mu_2}(\Frob_p)$ lie in $M[X]$ and are equal.
    \end{itemize} -/)
  (proof := /-- Omitted for now {\bf TODO} -/)]
theorem mem_isCompatible (hρ : IsHardlyRamified hpodd hv ρ) :
    -- Then `ρ` lives in a compatible family of Galois representations
    -- i.e., there's a family σ of 2-dimensional representations of Γ_ℚ
    -- parametrised by maps from a number field M → ℚ_p-bar
    ∃ (E : Type v) (_ : Field E) (_ : NumberField E) (σ : GaloisRepFamily ℚ E 2),
    -- which are compatible, and
    σ.isCompatible ∧
    -- are "hardly ramified" for ℓ>2,
    (∀ {ℓ : ℕ} (hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ) (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      -- by which we mean that for a representation σ_φ in the family,
      -- there's a hardly-ramified representation `τ` to GL_2(A)
      -- for A a module-finite free ℤ_ℓ-algebra
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A) (_ : Module.Finite ℤ_[ℓ] A)
        (_ : Module.Free ℤ_[ℓ] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ])) (_ : IsModuleTopology ℤ_[ℓ] A)
        (_ : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]))
        (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
        (_ : Module.Free A W) (hW : Module.rank A W = 2)
        (τ : GaloisRep ℚ A W)
        (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        -- whose base extension to GL_2(ℚ_p-bar) is φ_σ
        (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ) ∧
    -- and `ρ` is part of the family.
    (∃ (_ : Algebra R (AlgebraicClosure ℚ_[p])) (_ : ContinuousSMul R (AlgebraicClosure ℚ_[p]))
      (ψ : E →+* AlgebraicClosure ℚ_[p])
      (r' : AlgebraicClosure ℚ_[p] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[p]]
        Fin 2 → AlgebraicClosure ℚ_[p]),
      (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ) :=
  sorry

end GaloisRepresentation.IsHardlyRamified
