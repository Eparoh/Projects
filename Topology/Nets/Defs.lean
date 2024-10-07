import Topology.Nets.DirectedSets

open Set Filter Topology Classical Function DirectedSet

namespace Net

/- ### Definitions about nets ### -/

/- A net is simply a map s: D → X from a  directed set to  topological space X. -/

/- We say that a net s: D → X converges to a point x in X if for every neighborhood U of x there exists a d₀ in D such that
   for any d in D with d₀ ≤ d, we obtain that s d ∈ U. -/
def Limit {X D: Type*} [TopologicalSpace X] [DirectedSet D] (s : D → X) (x: X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ (d₀ : D), ∀ (d : D), d₀ ≤ d → s d ∈ U

/- We say that a point x in X is a cluster point of a net s: D → X if for every d in D and every neighborhood U of x there exists
   an e in D such that d ≤ e and s e ∈ U. -/
def ClusterPoint {X D: Type*} [TopologicalSpace X] [DirectedSet D] (s: D → X) (x : X): Prop :=
  ∀ (d : D), ∀ U ∈ 𝓝 x, ∃ (e : D), (d ≤ e ∧ s e ∈ U)

/- We say that a net s': E → X is a subnet of a net s: D → X if there exists a cofinal map i : E → D such that s' = s ∘ i.
   With cofinal we mean that given any d in D, there exists an e₀ in E such that for any e in E, if e₀ ≤ e then d ≤ i e. -/
def Subnet {X D E: Type*} [DirectedSet D] [DirectedSet E] (s: D → X) (s': E → X) : Prop :=
  ∃ (i: E → D), (∀ (d : D), ∃ (e₀ : E), ∀ (e : E), (e₀ ≤ e →  d ≤ (i e))) ∧ s' = s ∘ i
