import Architect
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.OpenPos
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open Topology MeasureTheory Measure

@[to_additive, blueprint
  "Topology.IsOpenEmbedding.isHaarMeasure_comap"
  (statement := /-- Let $A$ and $B$ be locally compact topological groups
    and let $f:A\to B$ be both a group homomorphism and open embedding.
    The pullback along $f$ of a Haar measure on $B$ is a Haar measure on $A$. -/)
  (proof := /-- Translation-invariance is easy, compact sets are finite because continuous
    image of compact is compact, open sets are bounded because image of open is open. -/)
  (discussion := 507)
  (latexEnv := "lemma")]
lemma Topology.IsOpenEmbedding.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
    {φ : G →* H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsHaarMeasure μ] :
    IsHaarMeasure (comap φ μ) where
  map_mul_left_eq_self := (hφ.measurableEmbedding.isMulLeftInvariant_comap μ).map_mul_left_eq_self
  lt_top_of_isCompact := (hφ.isFiniteMeasureOnCompacts_comap μ).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hφ).open_pos
