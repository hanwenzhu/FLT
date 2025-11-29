/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Architect
import FLT.DedekindDomain.AdicValuation
import FLT.Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!

# Completion of a number field at a finite place

-/

variable (K : Type*) [Field K] [NumberField K]

open NumberField

example (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Finite ((𝓞 K) ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

open IsDedekindDomain

variable (v : HeightOneSpectrum (𝓞 K))

open IsLocalRing

instance NumberField.instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

open scoped Valued in
instance : Finite (𝓀[v.adicCompletion K]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers K)))

@[blueprint
  "NumberField.instCompactSpaceAdicCompletionIntegers"
  (statement := /-- If $K$ is a number field and $v$ is a nonzero prime ideal of the integers of
    $K$,
    then the integers of $K_v$ is a compact open subgroup. -/)
  (proof := /-- Openness should follow from the fact that the integers are
     $\{x : v(x)<v(1/\pi)\}$ where $\pi$ is a uniformizer. Compactness needs
     finiteness of the residue field $\mathcal{O}_K/v$. -/)
  (discussion := 451)]
instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance

@[blueprint
  "NumberField.isOpenAdicCompletionIntegers"
  (statement := /-- $\calO_v$ is an open subring of $K_v$. -/)
  (proof := /-- Openness is already in mathlib. -/)
  (latexEnv := "lemma")]
lemma NumberField.isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _
