import Architect
import FLT.HaarMeasure.HaarChar.Ring
import FLT.NumberField.AdeleRing
import FLT.Hacks.RightActionInstances
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Central.Defs
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Hacks.RightActionInstances
import FLT.NumberField.AdeleRing
/-!

# Global units are in the determinant of the adelic Haar character

If `K` is a number field and `B` is a finite-dimensional `K`-algebra
then `B ⊗ 𝔸_K` is a locally compact topological ring, so it admits
a Haar character `(B ⊗ 𝔸_K)ˣ → ℝ>0`. In this file we show
that the global units `Bˣ` are in the kernel of this character.

-/

open NumberField

open scoped TensorProduct

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

open scoped NumberField.AdeleRing -- for 𝔸 K notation

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [FiniteDimensional L V] [FiniteDimensional K V] -- the latter can be proved but
  -- can't be an instance as it uses L

local instance : SMulCommClass L (𝔸 K) (𝔸 L) :=
  SMulCommClass.of_commMonoid L (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)

attribute [local instance high] Localization.instSMulCommClassOfIsScalarTower

/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as L-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeAddEquiv :
    V ⊗[K] (𝔸 K) ≃ₗ[L] (V ⊗[L] (𝔸 L)) :=
  TensorProduct.AlgebraTensorModule.congr ((TensorProduct.rid L V).symm) (.refl _ _) ≪≫ₗ
  TensorProduct.AlgebraTensorModule.assoc K L L V L (𝔸 K) ≪≫ₗ
  (LinearEquiv.lTensor V
    ((NumberField.AdeleRing.baseChangeAdeleAlgEquiv K L).toLinearEquiv.symm)).symm

omit [FiniteDimensional L V] [FiniteDimensional K V] in
@[simp] lemma NumberField.AdeleRing.ModuleBaseChangeAddEquiv_apply
    (v : V) (a : 𝔸 K) : ModuleBaseChangeAddEquiv K L V (v ⊗ₜ a) = v ⊗ₜ algebraMap _ _ a := by
  simp [ModuleBaseChangeAddEquiv]

open scoped TensorProduct.RightActions in
/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeAddEquiv' [Module (𝔸 K) (V ⊗[L] 𝔸 L)]
    [IsScalarTower (𝔸 K) (𝔸 L) (V ⊗[L] 𝔸 L)] :
    V ⊗[K] (𝔸 K) ≃ₗ[𝔸 K] (V ⊗[L] (𝔸 L)) where
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddEquiv
  map_smul' a vb := by
    induction vb with
    | zero => simp
    | tmul x y =>
        simp [TensorProduct.smul_tmul', -algebraMap_smul,
          algebra_compatible_smul (AdeleRing (𝓞 L) L) a]
    | add x y _ _ => simp_all

open scoped TensorProduct.RightActions in
/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeContinuousSemilinearMap :
    V ⊗[K] (𝔸 K) →ₛₗ[algebraMap (𝔸 K) (𝔸 L)] V ⊗[L] 𝔸 L where
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddMonoidHom
  map_smul' a bc := by
    induction bc with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul', Algebra.smul_def]
    | add x y _ _ => simp_all

omit [FiniteDimensional L V] [FiniteDimensional K V] in
lemma NumberField.AdeleRing.ModuleBaseChangeContinuousSemilinearMap_apply
    (v : V) (a : 𝔸 K) :
    ModuleBaseChangeContinuousSemilinearMap K L V (v ⊗ₜ a) = v ⊗ₜ algebraMap _ _ a := by
  simp [ModuleBaseChangeContinuousSemilinearMap]

open scoped TensorProduct.RightActions in
/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological additive groups
for V an L-module and K ⊆ L number fields. -/
@[blueprint
  "NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv"
  (statement := /-- If $K$ is a number field and $V$ is an $K$-module, then
    the natural isomorphism $V\otimes_K\A_K=V\otimes_{\Q}\A_{\Q}$ induced by the natural
    isomorphism $\A_K=K\otimes_K\A_{\Q}$ is a homeomorphism if the left hand side has the
    $\A_K$-module
    topology and the right hand side has the $\A_{\Q}$-module topology. -/)
  (proof := /-- Lemma~\ref{IsModuleTopology.continuous_bilinear_of_finite_left} tells us that
    $V\otimes_K\A_K$
    has the $\A_{\Q}$-module topology, and it is easily checked that the isomorphism is
    $\A_{\Q}$-linear and hence automatically continuous.
    
    Note that in the Lean we prove this for a general extension $L/K$ rather than $K/\Q$. -/)
  (proofUses := ["IsModuleTopology.continuous_bilinear_of_finite_left"])
  (latexEnv := "corollary")]
noncomputable def NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv :
    V ⊗[K] (𝔸 K) ≃ₜ+ (V ⊗[L] (𝔸 L)) :=
  {
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddEquiv
  continuous_toFun := sorry
  continuous_invFun := sorry
  }

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] 𝔸 K)]
  [BorelSpace (B ⊗[K] 𝔸 K)] in
@[blueprint
  "NumberField.AdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul"
  (statement := /-- Let $B$ be a finite-dimensional central simple $K$-algebra.
    Say $u\in B_{\A}^\times$, and define $\ell_u$ and $r_u:B_{\A}\to B_{\A}$ by
    $\ell_u(x)=ux$ and $r_u(x)=xu$. Then $d_{B_{\A}}(\ell_u)=d_{B_{\A}}(r_u)$. -/)
  (proof := /-- We think of $B_{\A}$ as $B\otimes_K\A_K$.
    If $u=(u_v)$ as $v$ runs through the places of $K$ then
    $d_{B_{\A}}(\ell_u)=\prod_v d_{B_v}(\ell_{u_v})$ by
    theorem~\ref{MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight} (and the product is
    finite).
    By corollary~\ref{IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight}
    this equals $\prod_v d_{B_v}(r_{u_v})$, and again by
    theorem~\ref{MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight} this is
    $d_{B_{\A}}(r_u)$. -/)
  (proofUses := ["MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight",
    "IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight"])]
lemma NumberField.AdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (𝔸 K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  sorry

-- should be elsewhere TODO
instance (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
  LocallyCompactSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p) := sorry

variable [MeasurableSpace (𝔸 ℚ)] [BorelSpace (𝔸 ℚ)]
  [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
  [∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
    MeasurableSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p)]
  [∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
    BorelSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p)] in
@[blueprint
  "MeasureTheory.ringHaarChar_adeles_rat"
  (statement := /-- If $x\in\A_{\Q}^\times$ then $\delta_{\A_{\Q}}(x)=\prod_v|x_v|_v.$ -/)
  (proof := /-- By theorem~\ref{MeasureTheory.addEquivAddHaarChar_prodCongr}
    we have $\delta_{\A_{\Q}}(x)=\delta_{\A_{\Q}^\infty}(x^\infty)\times\delta_{\R}(x_\infty)$.
    By lemma~\ref{MeasureTheory.ringHaarChar_real} we have $\delta_{\R}(x_\infty)=|x|_\infty$, and
    by
    theorem~\ref{MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight} we have
    $\delta_{\A_{\Q}^\infty}=\prod_p\delta_{\Q_p}(x_p)$. By
    lemma~\ref{MeasureTheory.ringHaarChar_padic}
    we have $\delta_{\Q_p}(x_p)=|x_p|_p$ and putting everything together we get the result. -/)
  (proofUses := ["MeasureTheory.addEquivAddHaarChar_prodCongr",
    "MeasureTheory.ringHaarChar_real", "MeasureTheory.ringHaarChar_padic",
    "MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight"])
  (latexEnv := "lemma")]
lemma MeasureTheory.ringHaarChar_adeles_rat (x : (𝔸 ℚ)ˣ) :
  ringHaarChar x = ringHaarChar (MulEquiv.prodUnits x).1 *
    (∏ᶠ p, ringHaarChar (MulEquiv.restrictedProductUnits (MulEquiv.prodUnits x).2 p)) := sorry

@[blueprint
  "MeasureTheory.ringHaarChar_adeles_units_rat_eq_one"
  (statement := /-- If $x\in\Q^\times\subseteq\A_{\Q}^\times$ then $\delta_{\A_{\Q}}(x)=1.$ -/)
  (proof := /-- By lemma~\ref{MeasureTheory.ringHaarChar_adeles_rat} we have
    $\delta_{\A_{\Q}}(x)=\prod_v|x|_v$.
    But the product formula says that this is 1.
    A quick proof: if $x=\pm\prod_pp^{e_p}$ then $\prod_p|x|_p=\prod_pp^{-e_p}$
    and $|x|_\infty=\prod_pp^{e_p}$ so they cancel. -/)
  (proofUses := ["MeasureTheory.ringHaarChar_adeles_rat"])
  (latexEnv := "lemma")]
lemma MeasureTheory.ringHaarChar_adeles_units_rat_eq_one (x : ℚˣ)
    [MeasurableSpace ((𝔸 ℚ))] [BorelSpace (𝔸 ℚ)] :
  ringHaarChar (Units.map (algebraMap ℚ (𝔸 ℚ)) x : (𝔸 ℚ)ˣ) = 1 := sorry

-- TODO: need TensorProduct.RightActions.LinearEquiv.baseChange
open scoped TensorProduct.RightActions in
/-- The continuous A-linear map (A a topological ring, tensor products have the module
topology) A ⊗[R] M ≃ A ⊗[R] N associated to an abstract R-linear isomorphism M ≃ N. -/
noncomputable def ContinuousLinearEquiv.baseChange (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] [TopologicalSpace A]
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (φ : M ≃ₗ[R] N) : (M ⊗[R] A) ≃L[A] (N ⊗[R] A) where
  __ := TensorProduct.RightActions.LinearEquiv.baseChange _ _ _ _ φ
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := IsModuleTopology.continuous_of_linearMap _

open scoped TensorProduct.RightActions

@[blueprint
  "MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one"
  (statement := /-- In the above situation ($V$ a finite-dimensional $\Q$-vector space, $\phi:V\cong
    V$ is
    $\Q$-linear, $\phi_{\A}$ the base extension to $V_{\A}:=V\otimes_{\Q}{\A_{\Q}}$, a continuous
    linear
    endomorphism of $V_{\A}$ with the $\A_{\Q}$-module topology), we have $d_{V_{\A}}(\phi_{\A})=1.$
    -/)
  (proof := /-- Fix once and for all a $\Z$-lattice $L\subseteq V$
    (that is, a spanning $\Z^N$ in the $\Q^N$). Then $V\otimes_{\Q}\A_{\Q}=L\otimes_{\Z}\A_{\Q}$
    which is $L\otimes_{\Z}(\A_{\Q}^\infty\times\R)$.
    Because tensoring by a finitely presented module commute with restricted products and binary
    products this equals $\prod'_p(L\otimes_{\Z}\Q_p)\times(L\otimes_{\Q}\R)$, the restricted
    product being over $L\otimes_{\Z}\Z_p$, and this is
    $\prod'_p(V\otimes_{\Q}\Q_p)\times(V\otimes_{\Q}\R)$.
    If $V_v$ denotes $V\otimes_{\Q}\Q_v$ then the endomorphism $\phi_{\A}$ is the product of
    $\phi_p$ for all $p$ and $\phi_\infty$,
    where $\phi_v$ is a $\Q_v$-linear and and hence continuous automorphism of $V_v$.
    
    Hence by theorem~\ref{MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight}
    we have $d_{V_{\A}}(\phi_{\A})=\prod_p d_{V_p}(\phi_p)\times d_{V_\infty}(\phi_\infty)$,
    where we note that all but finitely many of the $d_{V_p}(\phi_p)$ are 1.
    
    By Lemma~\ref{MeasureTheory.addEquivAddHaarChar_eq_ringHaarChar_det} we have that
    $d_{V_v}(\phi_v)=\delta_{\Q_v}(\det(\phi_v))$, hence
    $d_{V_{\A}}(\phi_{\A})=\prod_v\delta_{\Q_v}(\det(\phi_v))$.
    But $\det(\phi_v)$ is equal to the determinant of $\phi$ on $V$ as $\Q$-vector space (because
    base change does not change determinant),
    which is some nonzero rational number $q$. Thus
    $d_{V_{\A}}(\phi_{\A})=\prod_v\delta_{\Q_v}(q)=1$
    by the product formula for $\Q$. -/)
  (proofUses := ["MeasureTheory.addEquivAddHaarChar_eq_ringHaarChar_det",
    "NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv",
    "MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight"])]
lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one (φ : V ≃ₗ[K] V)
    [MeasurableSpace (V ⊗[K] 𝔸 K)] [BorelSpace (V ⊗[K] 𝔸 K)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange K (𝔸 K) V V φ).toContinuousAddEquiv = 1 := by
  sorry

open scoped TensorProduct.RightActions in
/-- Left multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure. In other words, Bˣ is in the kernel of the `ringHaarChar` of `B ⊗ 𝔸_K`.
-/
@[blueprint
  "NumberField.AdeleRing.units_mem_ringHaarCharacter_ker"
  (statement := /-- If $B$ is a finite-dimensional $\Q$-algebra (for example a number field, or a
    quaternion algebra over a number field),
    if $B_{\A}$ denotes the ring $B\otimes_{\Q}\A_{\Q}$, and if $b\in B^\times$,
    then $\delta_{B_{\A}}(b)=1$. -/)
  (proof := /-- Follows immediately from the previous theorem. -/)
  (proofUses := ["MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one"])
  (latexEnv := "corollary")]
lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈
    ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := sorry

open scoped TensorProduct.RightActions in
/-- Right multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure.
-/
@[blueprint
  "NumberField.AdeleRing.addEquivAddHaarChar_mulRight_unit_eq_one"
  (statement := /-- If $B$ is a finite-dimensional $\Q$-algebra and
    if $b\in B^\times$ then right multiplication by $b$
    does not change Haar measure on $B_{\A}$. -/)
  (proof := /-- Follows immediately from the previous theorem. -/)
  (proofUses := ["MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one"])
  (latexEnv := "corollary")]
lemma NumberField.AdeleRing.addEquivAddHaarChar_mulRight_unit_eq_one
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    addEquivAddHaarChar
      (ContinuousAddEquiv.mulRight
        (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = 1 := by
  sorry
