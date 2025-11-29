/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
import Architect
import FLT.Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Central.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

variable (k : Type*) [Field k] {D : Type*} [Ring D] [Algebra k D]
open scoped TensorProduct

lemma mulLeft_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (x : K ⊗[k] D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulLeft K (e x) = e ∘ₗ LinearMap.mulLeft K x ∘ₗ e.symm := by
  apply LinearMap.ext
  simp

lemma mulRight_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (x : K ⊗[k] D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulRight K (e x) = e ∘ₗ LinearMap.mulRight K x ∘ₗ e.symm := by
  apply LinearMap.ext
  simp

lemma mulLeft_conj_ofLinear (K : Type*) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K) :
    (((Matrix.ofLinearEquiv K ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K K).symm.toLinearMap
    ∘ₗ (LinearMap.mulLeft K N) ∘ₗ ((Matrix.ofLinearEquiv K) ≪≫ₗ Matrix.transposeLinearEquiv
    (Fin n) (Fin n) K K).toLinearMap)) = LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N) i).comp
    (LinearMap.proj i) := rfl

lemma mulRight_conj_ofLinear (K : Type*) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K) :
    ((Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ
    LinearMap.mulRight K N ∘ₗ (Matrix.ofLinearEquiv K).toLinearMap :
    (Fin n → Fin n → K) →ₗ[K] (Fin n) → Fin n → K) =
    LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N.transpose) i).comp (LinearMap.proj i) := by
  apply LinearMap.ext
  intro M
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

variable [Algebra.IsCentral k D] [IsSimpleRing D] [FiniteDimensional k D]

/-- This is instance is in a repo on brauergroup which will soon be PRed into mathlib,
  the associated issue task is #631. -/
instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (A ⊗[k] B) := sorry

@[blueprint
  "IsSimpleRing.mulLeft_det_eq_mulRight_det"
  (statement := /-- Say $B$ is a finite-dimensional central simple algebra over a field~$k$,
    and $u\in B^\times$. Let $\ell_u:B\to B$ be the $k$-linear mapping $x$ to $ux$ and
    let $r_u:B\to B$ be the $k$-linear map sending $x$ to $xu$. Then
    $\det(\ell_u)=\det(r_u)$. -/)
  (proof := /-- Determinants are unchanged by base extension, so WLOG $k$ is algebraically closed.
    Then it's known that $B$ must be a matrix algebra, say $M_n(k)$. Now $u$ can be thought
    of as a matrix which has its own intrinsic determinant $d$, and $B$ as a left $B$-module
    becomes a direct sum of $n$ copies of $V$, the standard $n$-dimensional representation of $B$.
    Thus $\det(\ell_u)=d^n$. Similarly $\det(r_u)=d^n$ and in particular they are equal. -/)
  (discussion := 518)
  (latexEnv := "lemma")]
lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det := by
  let K' := AlgebraicClosure k
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K' (K' ⊗[k] D)
  have h1 : (LinearMap.mulLeft k d).baseChange K' = LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  have h2 : (LinearMap.mulRight k d).baseChange K' = LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  apply FaithfulSMul.algebraMap_injective k K'
  rw [LinearMap.det_baseChange (LinearMap.mulLeft k d) |>.symm, LinearMap.det_baseChange
    (LinearMap.mulRight k d) |>.symm, h1, h2]
  have h5 : LinearMap.det (LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulLeft K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulLeft _ _) e.toLinearEquiv, mulLeft_conj]
    rfl
  have h6: LinearMap.det (LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulRight K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulRight _ _) e.toLinearEquiv, mulRight_conj]
    rfl
  rw [h5, h6, ← LinearMap.det_conj (LinearMap.mulRight K' (e (1 ⊗ₜ[k] d))) <|
    (Matrix.ofLinearEquiv K').symm, LinearEquiv.symm_symm, mulRight_conj_ofLinear,
    LinearMap.det_pi, ← LinearMap.det_conj (LinearMap.mulLeft K' (e (1 ⊗ₜ[k] d))) <|
    (((Matrix.ofLinearEquiv K') ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K' K')).symm,
    LinearEquiv.symm_symm, mulLeft_conj_ofLinear, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det' (d : Dˣ) :
    (LinearEquiv.mulLeft k d).det = (LinearEquiv.mulRight k d).det := by
  ext
  simp [mulLeft_det_eq_mulRight_det]


/-!
### Auxiliary lemmas about linear equivalences and matrices
-/
section LinearEquiv

variable {F : Type*} [CommRing F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V]

lemma LinearEquiv.det_ne_zero
  {F : Type*} [CommRing F] [Nontrivial F] {V : Type*} [AddCommGroup V] [Module F V]
  (e : V ≃ₗ[F] V) : e.toLinearMap.det ≠ 0 := (isUnit_det' e).ne_zero

lemma Matrix.toLinearEquiv_toLinearMap
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (toLinearEquiv b M h).toLinearMap = Matrix.toLin b b M := rfl

lemma LinearEquiv.det_toLinearEquiv
    (b : Module.Basis ι F V) {M : Matrix ι ι F} (h : IsUnit M.det) :
    LinearEquiv.det (M.toLinearEquiv b h) = h.unit := by
  refine Units.val_inj.mp ?_
  simp [Matrix.toLinearEquiv_toLinearMap]

end LinearEquiv
