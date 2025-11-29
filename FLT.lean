import Architect
import FLT.Assumptions.KnownIn1980s
import FLT.Assumptions.Mazur
import FLT.Assumptions.Odlyzko
import FLT.AutomorphicForm.QuaternionAlgebra.Defs
import FLT.AutomorphicForm.QuaternionAlgebra.FiniteDimensional
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Local
import FLT.Basic.FreyPackage
import FLT.Basic.Reductions
import FLT.Data.Hurwitz
import FLT.Data.HurwitzRatHat
import FLT.Data.QHat
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.Completion.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.IsDirectLimitRestricted
import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct
import FLT.DedekindDomain.IntegralClosure
import FLT.Deformations.Algebra.InverseLimit.Basic
import FLT.Deformations.Algebra.InverseLimit.Topology
import FLT.Deformations.Categories
import FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformations.IsProartinian
import FLT.Deformations.IsResidueAlgebra
import FLT.Deformations.Lemmas
import FLT.Deformations.LiftFunctor
import FLT.Deformations.Representable
import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
import FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete
import FLT.Deformations.RepresentationTheory.Etale
import FLT.Deformations.RepresentationTheory.Frobenius
import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.Deformations.RepresentationTheory.GaloisRepFamily
import FLT.Deformations.RepresentationTheory.IntegralClosure
import FLT.Deformations.RepresentationTheory.Irreducible
import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Deformations.Subfunctor
import FLT.DivisionAlgebra.Finiteness
import FLT.EllipticCurve.Torsion
import FLT.GaloisRepresentation.Automorphic
import FLT.GaloisRepresentation.Cyclotomic
import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.GaloisRepresentation.HardlyRamified.Family
import FLT.GaloisRepresentation.HardlyRamified.Frey
import FLT.GaloisRepresentation.HardlyRamified.Lift
import FLT.GaloisRepresentation.HardlyRamified.ModThree
import FLT.GaloisRepresentation.HardlyRamified.Threeadic
import FLT.GlobalLanglandsConjectures.GLnDefs
import FLT.GlobalLanglandsConjectures.GLzero
import FLT.GroupScheme.FiniteFlat
import FLT.HaarMeasure.HaarChar.AddEquiv
import FLT.HaarMeasure.HaarChar.AdeleRing
import FLT.HaarMeasure.HaarChar.FiniteDimensional
import FLT.HaarMeasure.HaarChar.Padic
import FLT.HaarMeasure.HaarChar.RealComplex
import FLT.HaarMeasure.HaarChar.Ring
import FLT.HaarMeasure.MeasurableSpacePadics
import FLT.Hacks.RightActionInstances
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Hom
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Mathlib.Algebra.FixedPoints.Basic
import FLT.Mathlib.Algebra.IsDirectLimit
import FLT.Mathlib.Algebra.IsQuaternionAlgebra
import FLT.Mathlib.Algebra.Module.LinearMap.Defs
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.Algebra.Order.AbsoluteValue.Basic
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.Mathlib.Data.Fin.Basic
import FLT.Mathlib.Data.Set.Prod
import FLT.Mathlib.GroupTheory.DoubleCoset
import FLT.Mathlib.GroupTheory.Index
import FLT.Mathlib.LinearAlgebra.Determinant
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import FLT.Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.LinearAlgebra.Span.Defs
import FLT.Mathlib.Logic.Equiv.Basic
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.Mathlib.MeasureTheory.Group.Measure
import FLT.Mathlib.MeasureTheory.Measure.Regular
import FLT.Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.NumberTheory.NumberField.Completion
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import FLT.Mathlib.RingTheory.Ideal.Quotient.Basic
import FLT.Mathlib.RingTheory.LocalRing.Defs
import FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import FLT.Mathlib.RingTheory.Localization.BaseChange
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.RingTheory.Valuation.ValuationSubring
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.Topology.Algebra.Group.Units
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.Module.Quotient
import FLT.Mathlib.Topology.Algebra.Monoid
import FLT.Mathlib.Topology.Algebra.MulAction
import FLT.Mathlib.Topology.Algebra.Order.Field
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import FLT.Mathlib.Topology.Constructions
import FLT.Mathlib.Topology.HomToDiscrete
import FLT.Mathlib.Topology.Homeomorph
import FLT.Mathlib.Topology.Instances.Matrix
import FLT.Mathlib.Topology.MetricSpace.Pseudo.Matrix
import FLT.NumberField.AdeleRing
import FLT.NumberField.Completion.Finite
import FLT.NumberField.Completion.Infinite
import FLT.NumberField.DiscriminantBounds
import FLT.NumberField.FiniteAdeleRing
import FLT.NumberField.InfiniteAdeleRing
import FLT.NumberField.InfinitePlace.Dimension
import FLT.NumberField.InfinitePlace.Extension
import FLT.NumberField.InfinitePlace.WeakApproximation
import FLT.NumberField.Padics.RestrictedProduct
import FLT.Patching.Algebra
import FLT.Patching.Module
import FLT.Patching.Over
import FLT.Patching.REqualsT
import FLT.Patching.System
import FLT.Patching.Ultraproduct
import FLT.Patching.Utils.AdicTopology
import FLT.Patching.Utils.Depth
import FLT.Patching.Utils.InverseLimit
import FLT.Patching.Utils.Lemmas
import FLT.Patching.Utils.StructureFiniteness
import FLT.Patching.Utils.TopologicallyFG
import FLT.Patching.VanishingFilter
import FLT.QuaternionAlgebra.NumberField
import FLT.TateCurve.TateCurve

attribute [blueprint
  "IsModuleTopology.continuous_bilinear_of_finite_left"
  (statement := /-- Say $R$ and $S$ are topological rings, and $S$ is an $R$-algebra, finite as an
    $R$-module.
    Assume that the topology
    on $S$ is the $R$-module topology. Now say $M$ is an $S$-module, and give it the induced
    $R$-module structure. Then the $R$-module topology and $S$-module topology on~$M$ coincide. -/)
  (proof := /-- Let $i:R\to S$ denote the structure map. First observe that $S$ has the $R$-module
    topology
    so the $R$-action map $R\times S\to S$ (explicitly defined by $(r,s)\mapsto i(r)s$)
    is continuous, and restricting to $s=1$ we deduce that $i$ is continuous.
    
    Now let $M_R$ and $M_S$ denote $M$ with the $R$-module and $S$-module topologies respectively.
    It suffices to prove that the identity maps $M_R\to M_S$ and $M_S\to M_R$ are continuous.
    Equivalently, because the $A$-module topology on an $A$-module is the finest topology
    making it into a topological module, we need to prove that $M_R$ is a topological $S$-module
    and that $M_S$ is a topological $R$-module. We start with the latter claim.
    
    First observe that $M_S$ is a topological $S$-module, so addition is continuous.
    Next note that the map $R\times M_S\to M_S$ factors through $S\times M_S$ and is hence the
    composite of two continuous maps and thus continuous. Hence $M_S$ is a topological $R$-module.
    
    It thus remains to check that $M_R$ is a topological $S$-module, or equivalently
    that the map $S\times M_R\to M_R$ is continuous. But this map is $R$-bilinear, and
    by the result {\tt Module.continuous\_bilinear\_of\_finite} in {\tt mathlib}, any
    $R$-bilinear map between modules with the $R$-module topology is automatically continuous
    if one of the source modules is finitely-generated. The result applies because $S$ is
    assumed to be a finite $R$-module and the proof is complete. -/)
  (latexEnv := "lemma")]
  IsModuleTopology.continuous_bilinear_of_finite_left

attribute [blueprint
  "Submonoid.units_isCompact"
  (statement := /-- If $M$ is a Hausdorff topological monoid and $U$ is a compact submonoid,
    then the units $U^\times$ of $U$ are naturally a compact subgroup of $M^\times$. -/)
  (proof := /-- First I claim that $M^\times$ embedded in $M\times M$ via $g\mapsto (g,g^{-1})$
    is a closed subset of $M\times M$. Indeed, if $p:M\times M\to M$ is $(a,b)\mapsto ab$
    and $q:M\times M\to M$ is $(a,b)\mapsto ba$, then $p$ and $q$ are continuous,
    $M^\times\subseteq M\times M$ is the intersection
    $p^{-1}\{1\}\cap q^{-1}\{1\}$, and $\{1\}$ is closed because $M$ is Hausdorff.
    
    We have $U\times U$ is a compact subset of $M\times M$, and so
    $U^\times=M^\times\cap U\times U$ is a closed subspace of a compact space
    and is thus compact. -/)
  (discussion := 588)
  (latexEnv := "lemma")]
  Submonoid.units_isCompact
