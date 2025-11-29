import Architect
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[blueprint
  "Submonoid.units_isOpen"
  (statement := /-- If $M$ is a topological monoid and $U$ is an open submonoid, then
    the units $U^\times$ of $U$ are naturally an open subgroup of $M^\times$. -/)
  (proof := /-- We have $U\times U$ is an open subset of $M\times M$, and if we imagine $M^\times$
    embedded in $M\times M$ as explained in the remark above, then the intersection
    of this subgroup with $U\times U$ is open in $M^\times$ and consists of the elements
    of $M^\times$ which are in $U$ and whose inverse is also in $U$, which is easily
    checked to be the copy of $U^\times$ we're talking about. -/)
  (discussion := 587)
  (latexEnv := "lemma")]
lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

/-- The monoid homeomorphism between the units of a product of topological monoids
and the product of the units of the monoids.
-/
@[blueprint
  "ContinuousMulEquiv.piUnits"
  (statement := /-- If $U_i$ are topological monoids then the canonical
    group isomorphism $(\prod_i U_i)^\times=\prod_i(U_i^\times)$ is a homeomorphism. -/)
  (proof := /-- We prove that the maps in both directions are continuous. Let's start
    with the map from left to right.
    
    A map into a product is continuous when the maps to the factors
    are continuous. A map into the units of a monoid is continuous when the
    two projection maps to the monoid (the inclusion and the map $u\mapsto u^{-1}$)
    are continuous (because $M^\times$ has the topology induced from $M\times M$).
    This reduces us to checking that the maps $(\prod_i U_i)^\times\to U_j$
    sending $(u_i)$ to $u_j$ resp $u_j^{-1}$ are continuous. But the former map
    is the continuous inclusion $(\prod_i U_i)^\times\to\prod_i U_i$ followed
    by the continuous projection to $U_j$, and the latter map is the continuous
    inclusion $(\prod_i U_i)^\times\to\prod_i U_i$ sending $x$ to $x^{-1}$
    followed by the projection.
    
    To go the other way: because the units have the induced topology it suffices
    to check that the two maps $\prod_i(U_i^\times)\to\prod_i U_i$
    sending $(u_i)$ to $(u_i)$ resp $(u_i^{-1})$ are continuous. A map
    to a product is continuous when the induced maps to the factors are.
    A projection from a project is continuous, and the identity and inverse are
    continuous maps $U_j^\times\to U_j$, and the maps we're concerned with are composites
    of these maps and are hence continuous. -/)
  (discussion := 581)
  (latexEnv := "lemma")]
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
    refine continuous_pi (fun i => ?_)
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · simp only [Function.comp_def, MulEquiv.val_piUnits_apply]
      exact (continuous_apply i).comp' Units.continuous_val
    · simp only [MulEquiv.val_inv_piUnits_apply, Units.inv_eq_val_inv]
      exact (continuous_apply i).comp' Units.continuous_coe_inv
  continuous_invFun :=  by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm]
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_pi (fun i => ?_)
      simp only [Function.comp_def, MulEquiv.val_piUnits_symm_apply]
      exact Units.continuous_val.comp' (continuous_apply i)
    · refine continuous_pi (fun i => ?_)
      simp only [MulEquiv.val_inv_piUnits_symm_apply, Units.inv_eq_val_inv]
      exact Units.continuous_coe_inv.comp' (continuous_apply i)
