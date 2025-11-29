import Architect
import FLT.AutomorphicForm.QuaternionAlgebra.Defs
import FLT.DivisionAlgebra.Finiteness
import FLT.Mathlib.Algebra.IsQuaternionAlgebra
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain NumberField IsQuaternionAlgebra
open scoped TensorProduct TensorProduct.RightActions

-- let F be a number field
variable {F : Type*} [Field F] [NumberField F]
    -- and let D be a finite-dimensional division ring over F
    {D : Type*} [DivisionRing D] [Algebra F D] [Module.Finite F D]
    [Algebra.IsCentral F D]
-- Let K be a coefficient field
variable (K : Type*) [Field K]
    -- and let U, the level, be a subgroup of `(D ⊗ 𝔸_F^∞)ˣ`
    -- (which will be open in the theorem)
    {U : Subgroup (Dfx F D)}

open TotallyDefiniteQuaternionAlgebra

-- A linter complains that the below theorem (which at the time of writing is not sorry-free)
-- Note that we do not ever assume `[IsTotallyReal F]`, `[IsQuaternionAlgebra F D]`
-- or `[IsTotallyDefinite F D]`.
-- The crucial fact is apparently that D is a division ring.
-- Perhaps what's going on is that if D is something like the discriminant 6 quat alg
-- over ℚ (so unramified at infinity) then maybe the space is trivially only the constant
-- functions, or something. Perhaps some of these hypotheses might need to be re-added
-- later on.

-- If it's any help, the below argument will also show that the space of forms is
-- finitely-generated if `K` is an arbitrary Noetherian ring.
/--
Let `D/F` be a totally definite quaterion algebra over a totally real
field. Then the space of `K`-valued weight 2 level `U` quaternionic automorphic forms
for `Dˣ` is finite-dimensional over `K`.
-/
@[blueprint
  "TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.finiteDimensional"
  (statement := /-- Let $k$ be a field. Then the space $S^D(U;k)$ is a finite-dimensional $k$-vector
    space. -/)
  (proof := /-- The finite-dimensionality theorem is in fact an easy consequence of Fujisaki's
    lemma,
    proved in the Fukisaki miniproject, chapter~\ref{Fujisaki_project}.
    Write $(D\otimes_F\A_F^\infty)^\times$ as a disjoint union of double cosets
    $\coprod_i D^\times g_i U$. This open cover descends to a disjoint open
    cover of $D^\times\backslash (D\otimes_F\A_F^\infty)^\times$,
    and this latter space is compact by
    theorem~\ref{NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact}.
    Hence the cover is finite; write the double coset representatives
    as $g_1,g_2,\ldots,g_n$. We claim that
    the function $S^D(U;k)\to W^n$ sending $f$ to $(f(g_1),f(g_2),\ldots,f(g_n))$
    is injective and $k$-linear, which suffices by finite-dimensionality of $W$.
    $k$-linearity is easy, so let's talk about injectivity.
    
    Say $f_1$ and $f_2$ are two elements of $S^D(U;k)$ which agree on
    each $g_i$. It suffices to prove that $f_1(g)=f_2(g)$ for all
    $g\in(D\otimes_F\A_F^\infty)^\times$. So say $g\in(D\otimes_F\A_F^\infty)^\times$,
    and write $g=\delta g_iu$ for $\delta \in D^\times$ and $u\in U$.
    Then $f_1(g)=f_1(\delta g_iu)=f_1(g_i)$ (by the definition of $S^D(U;k)$), and similarly
    $f_2(g)=f_2(g_i)$
    and because $f_1(g_i)=f_2(g_i)$ by assumption, we deduce $f_1(g)=f_2(g)$ as required. -/)]
theorem WeightTwoAutomorphicForm.finiteDimensional
    (hU : IsOpen (U : Set (Dfx F D))) :
    FiniteDimensional K (WeightTwoAutomorphicFormOfLevel U K) := by
  let H' : Subgroup (Dfx F D) := (incl₁ F D).range
  -- We will define a free K-module with a basis indexed by
  -- the elements of a double coset space which (in the totally
  -- definite case) is finite)
  let X := DoubleCoset.Quotient (Set.range (incl₁ F D)) U
  -- (the finiteness claim below is the nontrivial input to this proof)
  have h : Finite X := NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F D hU
  -- We then define a linear map φ from V to the free K_module spanned by this finite set.
  -- V is a space of functions, and the map consists of evaluating
  -- a function on representatives given by the rep function above.
  let φ : (WeightTwoAutomorphicFormOfLevel U K) →ₗ[K] (X → K) := {
    toFun v x := v (Quot.out x),
    map_add' v₁ v₂ := rfl
    map_smul' c v := rfl
  }
  -- Since we have a linear map φ from V to a finite-dimensional space,
  -- it's enough to check that φ is injective. So say φ v₁ = φ v₂.
  apply FiniteDimensional.of_injective φ
  intro v₁ v₂ h
  ext d
  -- Show v₁ = v₂ because they agree on reps and the
  -- space is determined by those values
  let d' := Quot.out (Quot.mk _ d : X)
  -- Because d' is a representative for the double coset containing d
  obtain ⟨γ, u, hu, hd⟩ : ∃ γ : Dˣ, ∃ u ∈ U, d = (incl₁ F D γ) * d' * u := by
    have h_rel : (DoubleCoset.setoid H' U) d' d := Quotient.exact (Quotient.out_eq ⟦d⟧)
      -- Apply DoubleCoset.rel_iff to extract the witnesses
    rw [DoubleCoset.rel_iff] at h_rel
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, h_eq⟩ := h_rel
    use γ, k, hk
  -- now it's all easy
  rw [hd, mul_assoc, v₁.left_invt γ (d' * u), v₂.left_invt γ (d' * u),
    WeightTwoAutomorphicFormOfLevel.right_invt v₁ d' ⟨u, hu⟩,
    WeightTwoAutomorphicFormOfLevel.right_invt v₂ d' ⟨u, hu⟩]
  exact congr_fun h (Quot.mk _ d)

end TotallyDefiniteQuaternionAlgebra
