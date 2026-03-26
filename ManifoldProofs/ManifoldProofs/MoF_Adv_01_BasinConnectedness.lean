import Mathlib

/-!
# Manifold of Failure — Advanced Topic 1: Basin Connectedness

We study the connectedness properties of vulnerability basins (superlevel sets).
The key question: **Are basins one region or many?**

## Main results

- `basin_connected_of_convex_domain` — convex basins in TVS are connected
- `basin_connected_components_open` — connected components of open basins are open
- `basin_components_countable` — in second-countable spaces, open sets have countably many components
- `basin_preconnected_of_path_connected` — path-connected basins are connected
- `superlevel_disconnected_example` — basins can be disconnected on discrete spaces
-/

open Set Topology Filter

noncomputable section

namespace MoF

/-- The vulnerability basin (superlevel set). -/
def Basin' {X : Type*} (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x > τ}

/-! ## Theorem 1: Convex basins are connected -/

/-- If the basin `{f > τ}` is convex in a topological vector space, then it is connected.
This uses the fact that convex sets in real topological vector spaces are preconnected. -/
theorem basin_connected_of_convex_domain
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {f : E → ℝ} {τ : ℝ}
    (hconv : Convex ℝ (Basin' f τ))
    (hne : (Basin' f τ).Nonempty) :
    IsConnected (Basin' f τ) :=
  ⟨hne, hconv.isPreconnected⟩

/-! ## Theorem 2: Connected components of open basins are open -/

/-- Each connected component of the open set `{f > τ}` is open,
provided the ambient space is locally connected. -/
theorem basin_connected_components_open
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (τ : ℝ) (x : X) :
    IsOpen (connectedComponentIn (Basin' f τ) x) := by
  have hopen : IsOpen (Basin' f τ) :=
    isOpen_lt continuous_const hf
  exact hopen.connectedComponentIn

/-! ## Theorem 3: Countably many connected components in second-countable spaces -/

/-- In a second-countable locally connected space, the open set `{f > τ}` has at most
countably many distinct connected components. Each component is open and nonempty,
so it meets any dense set. A countable dense set yields the injection. -/
theorem basin_components_countable
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [LocallyConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (τ : ℝ) :
    Set.Countable {C : Set X | ∃ x ∈ Basin' f τ, C = connectedComponentIn (Basin' f τ) x} := by
  have hopen : IsOpen (Basin' f τ) := isOpen_lt continuous_const hf
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense X
  apply Set.Countable.mono (s₂ := D.image (fun d => connectedComponentIn (Basin' f τ) d))
  · intro C hC
    obtain ⟨x, hx, hCeq⟩ := hC
    subst hCeq
    have hCopen := hopen.connectedComponentIn (x := x)
    have hxmem : x ∈ connectedComponentIn (Basin' f τ) x :=
      mem_of_mem_nhds (connectedComponentIn_mem_nhds (hopen.mem_nhds hx))
    obtain ⟨d, hdD, hdC⟩ := hDdense.exists_mem_open hCopen ⟨x, hxmem⟩
    exact ⟨d, hdD, (connectedComponentIn_eq hdC).symm⟩
  · exact hDcount.image _

/-! ## Theorem 4: Path-connected basins are connected -/

/-- If the basin `{f > τ}` is path-connected, it is connected. -/
theorem basin_preconnected_of_path_connected
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {τ : ℝ}
    (hpc : IsPathConnected (Basin' f τ)) :
    IsConnected (Basin' f τ) :=
  hpc.isConnected

/-! ## Theorem 5: Basins CAN be disconnected -/

/-- There exist a topological space, a continuous function, and a threshold
such that the basin is not connected. We use Bool with the discrete topology:
the constant function f = 1 gives basin = univ, which is disconnected on Bool. -/
theorem superlevel_disconnected_example :
    ∃ (X : Type) (_ : TopologicalSpace X) (f : X → ℝ),
      Continuous f ∧ ¬IsConnected {x : X | f x > 0} := by
  refine ⟨Bool, inferInstance, fun _ => 1, continuous_const, ?_⟩
  intro ⟨_, hpre⟩
  have heq : {x : Bool | (1 : ℝ) > 0} = Set.univ := by
    ext x; simp
  rw [heq] at hpre
  have hclopen : IsClopen ({true} : Set Bool) := ⟨isClosed_discrete _, isOpen_discrete _⟩
  have hsub := hpre.subset_isClopen hclopen ⟨true, mem_univ _, mem_singleton _⟩
  exact absurd (hsub (mem_univ false)) (by simp)

end MoF
