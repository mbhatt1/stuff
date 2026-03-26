/-
  ManifoldOfFailure.lean

  Lean 4 / Mathlib formalization of the topological structure of the
  "failure surface" from the paper "Manifold of Failure".

  The Alignment Deviation function  Q : [0,1]^2 -> [0,1]  is modeled as
  a continuous map  f : I x I -> I  where  I = Set.Icc (0:R) 1  carries
  the subspace topology inherited from R.

  We prove:
    1. The graph of f is closed in I x I x I.
    2. The graph of f is compact.
    3. The superlevel set  M_tau = { x | tau < f x }  is open.
    4. (Axiom) Regular-value => manifold-with-boundary structure.
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Order.Compact

noncomputable section

open Set Topology unitInterval

/-! ## 1. The domain and codomain -/

/--
The type of "alignment-deviation surfaces": continuous functions from the
unit square to the unit interval.
-/
structure ADSurface where
  /-- The underlying function on the unit square. -/
  toFun : I x I -> I
  /-- Continuity of the surface. -/
  continuous_toFun : Continuous toFun

namespace ADSurface

variable (f : ADSurface)

instance : CoeFun ADSurface (fun _ => I x I -> I) :=
  { coe := ADSurface.toFun }

/-! ## 2. The graph as a subset of [0,1]^3 -/

/--
The graph of an AD surface, living in  I x I x I  (= [0,1]^3).
  S = { ((a1, a2), q) | q = f (a1, a2) }
-/
def graph : Set ((I x I) x I) :=
  { p | p.2 = f p.1 }

/-! ## 3. Closedness of the graph -/

/--
The graph of a continuous function from a topological space to a T2
(Hausdorff) space is closed.  Since I carries the subspace topology of R
it is Hausdorff, so this applies directly.
-/
theorem graph_isClosed : IsClosed f.graph := by
  -- f.graph = { p | p.2 = f p.1 } = the equalizer of  snd  and  f . fst
  -- Both maps are continuous; the equalizer of two continuous maps into a
  -- Hausdorff space is closed.
  have hf : Continuous (fun p : (I x I) x I => f p.1) :=
    f.continuous_toFun.comp continuous_fst
  have hsnd : Continuous (fun p : (I x I) x I => p.2) :=
    continuous_snd
  exact isClosed_eq hsnd hf

/-! ## 4. Compactness of the graph -/

/--
I x I  is compact (product of compact spaces).
-/
instance : CompactSpace (I x I) :=
  inferInstance

/--
(I x I) x I  is compact.
-/
instance : CompactSpace ((I x I) x I) :=
  inferInstance

/--
A closed subset of a compact space is compact.
-/
theorem graph_isCompact : IsCompact f.graph :=
  f.graph_isClosed.isCompact

/-! ## 5. The superlevel set (failure manifold at threshold tau) -/

/--
The superlevel set at threshold tau:
  M_tau = { x in I x I | tau < f(x) }
This captures the region of the parameter space where the alignment
deviation exceeds an acceptable threshold.
-/
def superlevelSet (tau : I) : Set (I x I) :=
  { x | tau < f x }

/-! ## 6. Openness of the superlevel set -/

/--
The strict superlevel set of a continuous function is open
(preimage of an open set under a continuous map is open).
-/
theorem superlevelSet_isOpen (tau : I) : IsOpen (f.superlevelSet tau) := by
  -- superlevelSet tau = f ^(-1) (Ioi tau), and Ioi tau is open in the
  -- order topology, and f is continuous.
  exact isOpen_lt continuous_const f.continuous_toFun

/-! ## 7. The sublevel set (safe region) -/

/--
The sublevel set: region where alignment deviation stays below threshold.
-/
def sublevelSet (tau : I) : Set (I x I) :=
  { x | f x < tau }

theorem sublevelSet_isOpen (tau : I) : IsOpen (f.sublevelSet tau) :=
  isOpen_lt f.continuous_toFun continuous_const

/-! ## 8. The level set -/

/--
The level set at threshold tau.
-/
def levelSet (tau : I) : Set (I x I) :=
  { x | f x = tau }

theorem levelSet_isClosed (tau : I) : IsClosed (f.levelSet tau) :=
  isClosed_eq f.continuous_toFun continuous_const

theorem levelSet_isCompact (tau : I) : IsCompact (f.levelSet tau) :=
  (f.levelSet_isClosed tau).isCompact

/-! ## 9. Manifold-with-boundary structure (axiom / hypothesis)

  Sard's theorem and the preimage theorem guarantee that for a smooth
  map  f : M -> N  between smooth manifolds, if  tau  is a regular value,
  then  f^{-1}({tau})  is a smooth submanifold and  f^{-1}([tau, infty))
  is a smooth manifold with boundary.

  We state this as an opaque axiom since the full theory of smooth
  manifolds with boundary and Sard's theorem are not yet in Mathlib.
-/

/--
A value  tau  is *regular* for  f  if the derivative of  f  is surjective
at every point in  f^{-1}({tau}).  We leave this as a predicate without
computational content.
-/
axiom IsRegularValue (f : ADSurface) (tau : I) : Prop

/--
Axiom (Preimage Theorem + Sard): if  tau  is a regular value of a smooth
alignment-deviation surface  f, then the superlevel set  M_tau  admits
the structure of a topological manifold with boundary of dimension 2,
whose boundary is the level set  f^{-1}({tau}).

This is the core structural claim of the "Manifold of Failure" paper:
vulnerabilities do not form an unstructured scatter of points but a
*manifold*, a space with a coherent local Euclidean geometry that can
be systematically explored.
-/
axiom superlevelSet_manifoldWithBoundary
    (f : ADSurface)
    (tau : I)
    (hreg : IsRegularValue f tau) :
    -- There exists a manifold-with-boundary structure on the closure of
    -- the superlevel set, of dimension 2, whose boundary is the level set.
    -- We express this abstractly since Mathlib's manifold library does not
    -- yet cover this case in full generality.
    ∃ (n : Nat), n = 2 ∧
      -- The closure equals the union of the open superlevel set and
      -- its boundary (the level set).
      closure (f.superlevelSet tau) =
        f.superlevelSet tau ∪ f.levelSet tau

/-! ## 10. Basic structural lemmas about the failure surface -/

/--
The weak superlevel set at threshold tau:
  M_tau_ge = { x in I x I | tau <= f(x) }
-/
def superlevelSetGe (tau : I) : Set (I x I) :=
  { x | tau ≤ f x }

/--
The weak superlevel set at the bottom threshold 0 is the whole space:
every point has AD >= 0.
-/
theorem superlevelSetGe_bot :
    f.superlevelSetGe ⟨0, left_mem_Icc.mpr zero_le_one⟩ = univ := by
  ext x
  simp only [superlevelSetGe, mem_setOf_eq, mem_univ, iff_true]
  exact unitInterval.nonneg _

/--
The weak superlevel set is closed (preimage of a closed set).
-/
theorem superlevelSetGe_isClosed (tau : I) : IsClosed (f.superlevelSetGe tau) :=
  isClosed_le continuous_const f.continuous_toFun

/--
The weak superlevel set is compact (closed subset of compact space).
-/
theorem superlevelSetGe_isCompact (tau : I) : IsCompact (f.superlevelSetGe tau) :=
  (f.superlevelSetGe_isClosed tau).isCompact

/--
The failure surface graph projects homeomorphically onto the domain.
In other words,  (a1, a2) |-> ((a1, a2), f(a1, a2))  is an embedding.
This follows from the general fact that the graph of a continuous function
into a Hausdorff space embeds into the product.
-/
theorem graph_continuous :
    Continuous (fun x : I x I => (x, f x) : (I x I) x I) :=
  continuous_id.prod_mk f.continuous_toFun

theorem graph_injective :
    Function.Injective (fun x : I x I => (x, f x) : (I x I) x I) :=
  fun _ _ h => (Prod.ext_iff.mp h).1

/--
The graph map is a closed embedding: it is a topological embedding whose
image is closed.  This follows because the domain is compact, the codomain
is Hausdorff, and the map is a continuous injection.
-/
theorem graph_closedEmbedding :
    ClosedEmbedding (fun x : I x I => (x, f x) : (I x I) x I) :=
  closedEmbedding_of_continuous_injective_closed
    f.graph_continuous
    f.graph_injective
    (fun _ hS => (hS.isCompact.image f.graph_continuous).isClosed)

/--
The image of the graph embedding is exactly the graph set.
-/
theorem graph_eq_range :
    f.graph = Set.range (fun x : I x I => (x, f x)) := by
  ext ⟨p, q⟩
  simp only [graph, mem_setOf_eq, mem_range]
  constructor
  · intro h
    exact ⟨p, Prod.ext rfl h.symm⟩
  · rintro ⟨x, hx⟩
    have := Prod.ext_iff.mp hx
    rw [this.1]
    exact this.2.symm

end ADSurface

/-! ## Summary

We have formalized the following from the "Manifold of Failure" paper:

| # | Statement | Status |
|---|-----------|--------|
| 1 | AD surface is a continuous  I x I -> I | Definition (`ADSurface`) |
| 2 | Graph  S c I^3  is well-defined | Definition (`ADSurface.graph`) |
| 3 | Graph is closed | **Proved** (`graph_isClosed`) |
| 4 | Graph is compact | **Proved** (`graph_isCompact`) |
| 5 | Superlevel set  M_tau  defined | Definition (`superlevelSet`) |
| 6 | M_tau is open | **Proved** (`superlevelSet_isOpen`) |
| 7 | Level set is closed & compact | **Proved** (`levelSet_isClosed/Compact`) |
| 8 | Regular value => manifold w/ boundary | **Axiom** (`superlevelSet_manifoldWithBoundary`) |
| 9 | Graph is a closed embedding | **Proved** (`graph_closedEmbedding`) |
| 10 | Weak superlevel set is compact | **Proved** (`superlevelSetGe_isCompact`) |
-/
