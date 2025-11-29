import Architect
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.MetricSpace.Pseudo.Matrix
import FLT.NumberField.InfinitePlace.Dimension
import FLT.NumberField.InfinitePlace.WeakApproximation

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion SemialgHom

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
  {wv : v.Extension L}

instance {v : InfinitePlace K} : NontriviallyNormedField (v.Completion) where
  toNormedField := InfinitePlace.Completion.instNormedField v
  non_trivial :=
    let ⟨x, hx⟩ := v.isNontrivial.exists_abv_gt_one
    ⟨x, by rw [UniformSpace.Completion.norm_coe]; exact hx⟩

instance : NormedSpace v.Completion wv.1.Completion where
  norm_smul_le x y := by
    rw [Algebra.smul_def, norm_mul, SemialgHom.algebraMap_apply,
      ← isometry_semiAlgHomOfComp (comp_of_comap_eq wv.2) |>.norm_map_of_map_zero (map_zero _)]

noncomputable instance : FiniteDimensional v.Completion wv.1.Completion :=
  FiniteDimensional.of_locallyCompactSpace v.Completion

/-- The map from `v.Completion` to `w.Completion` whenever the infinite place `w` of `L` lies
above the infinite place `v` of `K`. -/
abbrev comapHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap (WithAbs v.1) (WithAbs w.1)] w.Completion :=
  semialgHomOfComp (comp_of_comap_eq h)

theorem comapHom_cont (h : w.comap (algebraMap K L) = v) : Continuous (comapHom h) := continuous_map

variable (L v)

/-- The map from `v.Completion` to the product of all completions of `L` lying above `v`. -/
@[blueprint
  "NumberField.InfinitePlace.Completion.piExtension"
  (statement := /-- Let $v$ be an infinite place of $K$. There is a continuous $K$-algebra
    homomorphism
    $K_v \to \prod_{w\mid v}L_w$, whose restriction to $K$ corresponds to the global embedding
    of $K$ into $(L_w)_w$. -/)]
def piExtension :
    v.Completion →ₛₐ[algebraMap K L] (wv : v.Extension L) → wv.1.Completion :=
  Pi.semialgHom _ _ fun wv => comapHom wv.2

@[simp]
theorem piExtension_apply (x : v.Completion) :
    piExtension L v x = fun wv : v.Extension L => comapHom wv.2 x := rfl

open scoped TensorProduct.RightActions

instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) := ⟨rfl⟩

/-- The `L`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L` lying
above `v`, induced by `piExtension`. -/
@[blueprint
  "NumberField.InfinitePlace.Completion.baseChange"
  (statement := /-- Let $v$ be an infinite place of $K$. There is a natural $L$-algebra homomorphism
    $L\otimes_K K_v \to \prod_{w\mid v}L_w$, whose restriction to $1\otimes_K K_v$ corresponds to
    the map in~\ref{NumberField.InfinitePlace.Completion.piExtension}. -/)]
abbrev baseChange :
    L ⊗[K] v.Completion →ₐ[L] (wv : v.Extension L) → wv.1.Completion :=
  baseChange_of_algebraMap (piExtension L v)

/- The motivation for changing the scalars of `baseChange L v` to `v.Completion` is that
both sides are _finite-dimensional_ `v.Completion`-modules, which have the same dimension.
This fact is used to show that `baseChangeRight` (and therefore `baseChange`) is surjective. -/
/-- The `v.Completion`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L`
lying above `v`, induced by `piExtension`. -/
abbrev baseChangeRight :
    L ⊗[K] v.Completion →ₐ[v.Completion] ((wv : v.Extension L) → wv.1.Completion) :=
  baseChangeRightOfAlgebraMap (piExtension L v)

variable [NumberField L]

variable {L v}

-- A shortcut as this instance takes a while to synth
instance : Module.Free v.Completion wv.1.Completion :=
  Module.free_of_finite_type_torsion_free'

variable (L v)

open scoped Classical in
theorem finrank_prod_eq_finrank [NumberField K] :
    Module.finrank v.Completion ((wv : Extension L v) → wv.1.Completion) =
      Module.finrank K L := by
  classical
  rw [Module.finrank_pi_fintype v.Completion, ← Extension.sum_ramificationIdx_eq L v]
  exact Finset.sum_congr rfl (fun w _ => finrank_eq_ramificationIdx w)

@[blueprint
  "NumberField.InfinitePlace.Completion.finrank_pi_eq_finrank_tensorProduct"
  (statement := /-- For a fixed infinite place $v$ of $K$, we have
    $\text{dim}_{K_v} \prod_{w\mid v} L_w = \text{dim}_{K_v} L\otimes_K K_v$. -/)
  (latexEnv := "theorem")]
theorem finrank_pi_eq_finrank_tensorProduct [NumberField K] :
    Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion) =
      Module.finrank v.Completion (L ⊗[K] v.Completion) := by
  rw [(TensorProduct.RightActions.Algebra.TensorProduct.comm
       K v.Completion L).symm.toLinearEquiv.finrank_eq,
      Module.finrank_tensorProduct, Module.finrank_self, one_mul,
    finrank_prod_eq_finrank]

open scoped Classical in
@[blueprint
  "NumberField.InfinitePlace.Completion.baseChange_surjective"
  (statement := /-- For a fixed infinite place $v$ of $K$, the map $L\otimes_K K_v \to\prod_{w\mid
    v}L_w$ is
    surjective. -/)
  (proof := /-- Let $(x_i)_i$ be a $K_v$-basis of $\prod_{w\mid v}L_w$. By the density of $L$ in
    $\prod_{w\mid v}L_w$
    (Theorem~\ref{NumberField.InfinitePlace.Completion.denseRange_algebraMap_subtype_pi}), we can
    find $\alpha_i \in L$ arbitrarily close to $x_i\prod_{w\mid v}L_w$ with respect to the sup norm
    when embedded globally in $\prod_{w\mid v}L_w$.
    In particular, it is possible to choose such $\alpha_i$ so that the matrix representing
    the vector $((\alpha_i)_{w \mid v})_i$ in the basis $(x_i)_i$ has non-zero determinant.
    Since $(\alpha_i)_{w \mid v}$ is the image of $1\otimes \alpha_i$ under base change, we have
    that $(1 \otimes \alpha_i)_i$ also forms a basis of $L\otimes_K K_v$, and base change
    is surjective. -/)]
theorem baseChange_surjective : Function.Surjective (baseChange L v) := by
  -- Let `Bw` be a `K_v` basis of `Π v | w, L_w`
  let Bw := Module.finBasis v.Completion ((w : v.Extension L) → w.1.Completion)
  -- `L` is dense inside Π v | w, L_w
  have := denseRange_algebraMap_subtype_pi _ fun w : InfinitePlace L => w.comap (algebraMap K L) = v
  -- So there exists a vector `α ∈ L^d` whose matrix wrt `Bw` gets close to `1` (has non-zero det)
  classical
  let ⟨α, h⟩ := (DenseRange.piMap fun _ => this).exists_matrix_det_ne_zero
    (Basis.toMatrix_continuous Bw) Bw.toMatrix_self
  -- Therefore `α` is a basis under the image of `piExtension L v`, hence it's surjective
  rw [← isUnit_iff_ne_zero, ← Bw.det_apply, ← Module.Basis.is_basis_iff_det Bw] at h
  rw [← baseChangeRightOfAlgebraMap_coe, ← LinearMap.range_eq_top, ← top_le_iff, ← h.2,
    Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact ⟨α i ⊗ₜ 1, by simp⟩

variable [NumberField K]

@[blueprint
  "NumberField.InfinitePlace.Completion.baseChange_injective"
  (statement := /-- For a fixed infinite place $v$ of $K$, the map $L\otimes_K K_v \to\prod_{w\mid
    v}L_w$ is
    injective. -/)
  (proof := /-- The $L$-algebra map $L\otimes_K K_v \to\prod_{w\mid v}L_w$ can equivalently be
    thought of
    as $K_v$-linear, which is injective, because it is surjective by
    Theorem~\ref{NumberField.InfinitePlace.Completion.baseChange_surjective}, and both side have the
    same
    $K_v$-dimension by
    Theorem~\ref{NumberField.InfinitePlace.Completion.finrank_pi_eq_finrank_tensorProduct}. -/)]
theorem baseChange_injective :
    Function.Injective (baseChange L v) := by
  rw [← baseChangeRightOfAlgebraMap_coe, ← AlgHom.coe_toLinearMap,
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_pi_eq_finrank_tensorProduct L v).symm]
  simp [baseChange_surjective L v]

@[blueprint
  "NumberField.InfinitePlace.Completion.instIsModuleTopologyValEqComapAlgebraMap_fLT"
  (statement := /-- If $w \mid v$ is an infinite place of $L$ lying above the infinite place $v$ of
    $K$, then
    $L_w$ has the $K_v$-module topology. -/)
  (proof := /-- Because $L_w$ is a finite-dimensional normed $K_v$ vector space, there exists a
    $K_v$-linear
    linear homeomorphism $L_w \cong K_v^n$, from which $L_w$ has the $K_v$-module topology. -/)]
instance : IsModuleTopology v.Completion wv.1.Completion :=
  IsModuleTopology.iso (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (Module.finrank_fin_fun v.Completion)).some

/-- The `L`-algebra homeomorphism between `L ⊗[K] v.Completion` and the product of all completions
of `L` lying above `v`. -/
@[blueprint
  "NumberField.InfinitePlace.Completion.baseChangeEquiv"
  (statement := /-- Let $v$ be an infinite place of $K$. There is a natural $L$-algebra
    homeomorphism
    $L\otimes_K K_v \cong_L \prod_{w\mid v}L_w$, whose restriction to $1\otimes_K K_v$ corresponds
    to
    the map in~\ref{NumberField.InfinitePlace.Completion.piExtension}. -/)
  (proof := /-- The map in~\ref{NumberField.InfinitePlace.Completion.baseChange} is an $L$-algebra
    isomorphism by Theorem~\ref{NumberField.InfinitePlace.Completion.baseChange_surjective}
    and Theorem~\ref{NumberField.InfinitePlace.Completion.baseChange_injective}.
    Every $K_v$-algebra isomorphism between two $K_v$-module topological spaces is a homeomorphism.
    Since the $L$-algebra isomorphism of
    Definition~\ref{NumberField.InfinitePlace.Completion.baseChange} can equivalently be viewed as
    a $K_v$-algebra isomorphism, it is also a homeomorphism. -/)]
def baseChangeEquiv :
    L ⊗[K] v.Completion ≃A[L] (wv : v.Extension L) → wv.1.Completion :=
  let e := AlgEquiv.ofBijective _ ⟨baseChange_injective L v, baseChange_surjective L v⟩
  IsModuleTopology.continuousAlgEquivOfIsScalarTower K v.Completion e
    (baseChange_of_algebraMap_tmul_right _)

@[simp]
theorem baseChangeEquiv_tmul (l : L) (x : v.Completion) :
    baseChangeEquiv L v (l ⊗ₜ[K] x) = fun wv : v.Extension L => l * comapHom wv.2 x := by
  simp [baseChangeEquiv, baseChange, SemialgHom.baseChange_of_algebraMap_tmul]
  rfl

/-- The `Kᵥ`-algebra homeomorphism between `L ⊗[K] v.Completion` and the product of all completions
of `L` lying above `v`. -/
def baseChangeEquivRight :
    L ⊗[K] v.Completion ≃A[v.Completion] (wv : v.Extension L) → wv.1.Completion :=
  let e := AlgEquiv.ofBijective _ ⟨baseChange_injective L v, baseChange_surjective L v⟩
  IsModuleTopology.continuousAlgEquivOfAlgEquiv
    (e.changeScalars K v.Completion (baseChange_of_algebraMap_tmul_right _))

open TensorProduct.AlgebraTensorModule in
/-- The `Kᵥ`-linear homeomorphism between `Kᵥ^d` and the product of all completions
of `L` lying above `v`, where `d = [K : L]`. -/
@[blueprint
  "NumberField.InfinitePlace.Completion.piEquiv"
  (statement := /-- Let $v$ be an infinite place of $K$. There is a natural $K_v$-linear
    homeomorphism
    $K_v^{[L:K]} \cong_{K_v} \prod_{w\mid v}L_w$. -/)
  (proof := /-- Compose the $K_v$-linear isomorphism $K_v^{[L:K]} \cong \prod_{w\mid v}L_w$ with the
    $K_v$-linear
    version of base change~\ref{NumberField.InfinitePlace.Completion.baseChangeEquiv} to get the
    isomorphism in the statement.
    Since both sides have the $K_v$-module topology, then this is also a homeomorphism. -/)]
def piEquiv :
    (Fin (Module.finrank K L) → v.Completion) ≃L[v.Completion]
      (wv : v.Extension L) → wv.1.Completion := by
  -- `L ⊗ Kᵥ ≃ₗ[Kᵥ] Kᵥ ⊗ L`
  let e₁ := (TensorProduct.RightActions.Algebra.TensorProduct.comm K v.Completion L).symm
     |>.toLinearEquiv
  -- `Kᵥ ⊗ L ≃ₗ[Kᵥ] Kᵥ^d`
  let e₂ := finiteEquivPi K L v.Completion
  -- Compose and apply module topologies to get the `Kᵥ`-linear homeomorphism
  -- `Kᵥ^d ≃L[Kᵥ] L ⊗ Kᵥ`
  let e₃ := IsModuleTopology.continuousLinearEquiv (e₁.trans <| e₂) |>.symm
  -- Compose with `Kᵥ`-scalar base change to finish
  -- `Kᵥ^d ≃L[Kᵥ] ∏ w | v, L_w`
  exact e₃.trans <| baseChangeEquivRight L v |>.toContinuousLinearEquiv

theorem piEquiv_smul (x : v.Completion) (y : Fin (Module.finrank K L) → v.Completion)
    (wv : v.Extension L) :
    piEquiv L v (x • y) wv = comapHom wv.2 x * piEquiv L v y wv := by
  simp_rw [(piEquiv L v).map_smul x y, Pi.smul_def, RingHom.smul_toAlgebra,
    SemialgHom.toRingHom_eq_coe, RingHom.coe_coe]

end NumberField.InfinitePlace.Completion
