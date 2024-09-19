import Mathlib.Topology.Instances.Real

noncomputable section

open Set Filter Topology Classical Function

set_option linter.unusedVariables false
set_option linter.simpsNoConstructor false






/-! ### Direceted sets and net definitions -/

/- We define a net as an structure that includes a directed set D (with the condition that is nonempty)
   and a function form D to X-/

/- Definition of (nonempty) directed set -/
class DirectedSet (D: Type) extends Preorder D, Inhabited D where
  directed : ∀ (d e : D), ∃ (f : D), d ≤ f ∧ e ≤ f

namespace DirectedSet

/- Default element in any directed set -/
def default' (D: Type) [DirectedSet D] := @Inhabited.default D toInhabited

-- Any finite set on a directed set has a supremum
theorem sup_finite_set {D : Type} [DirectedSet D] (I : Finset D): ∃ (d: D), ∀ c ∈ I, c ≤ d := by
  induction' I using Finset.induction_on with d I dninI ih
  · simp
  · simp
    rcases ih with ⟨d₀, leI⟩
    rcases DirectedSet.directed d d₀ with ⟨d₁, ledd₀⟩
    use d₁
    apply And.intro (ledd₀.1) _
    intro a ainI
    exact le_trans (leI a ainI) ledd₀.2

end DirectedSet

/- Definition of net -/
structure Net (X: Type) where
  D: Type
  [directedSet: DirectedSet D]
  net : D → X


/- It includes in the typeclass inference system the assertion that the domain of a net
   is a directed set, so that Lean can synthesized it when needed -/
attribute [instance] Net.directedSet

-- Constructor for nets given a directed set D and a function s: D → X
def Net.mk' {X: Type} {D: Type} (h: DirectedSet D) (s: D → X) : Net X :=
{
  D := D
  directedSet := h
  net := s
}





/-! ### Lemmas -/

/- Here we stablish several non-related results that will be used later -/

-- univ is a neighbourhood for every point x in a topological space X
lemma univ_nhds {X: Type} [TopologicalSpace X] (x : X) : univ ∈ 𝓝 x := by
  simp

-- The intersection of neighbourhoods of x is a neighbourhood of x
lemma inter_nhds {X: Type} [TopologicalSpace X] (A B : Set X) (x : X) :
  A ∈ 𝓝 x → B ∈ 𝓝 x → A ∩ B ∈ 𝓝 x := by
  intro A_nhds B_nhds
  rw [mem_nhds_iff] at *
  rcases A_nhds with ⟨tA, tAsubA, tA_open, xintA⟩
  rcases B_nhds with ⟨tB, tBsubB, tB_open, xintB⟩
  use tA ∩ tB
  exact And.intro (inter_subset_inter tAsubA tBsubB)
    (And.intro (IsOpen.inter tA_open tB_open) (And.intro xintA xintB))

-- The union of neighbourhoods of x is a neighbourhood of x
lemma union_nhds {X: Type} [TopologicalSpace X] (A B : Set X) (x : X) :
  A ∈ 𝓝 x → B ∈ 𝓝 x → A ∪ B ∈ 𝓝 x := by
  intro A_nhds B_nhds
  rw [mem_nhds_iff] at *
  rcases A_nhds with ⟨tA, tAsubA, tA_open, xintA⟩
  rcases B_nhds with ⟨tB, tBsubB, tB_open, xintB⟩
  use tA ∪ tB
  exact And.intro (union_subset_union tAsubA tBsubB)
    (And.intro (IsOpen.union tA_open tB_open) (Or.inl xintA))

-- Characterization of being nonempty
lemma neq_nonempty_iff_exists (s : Set X) : s ≠ ∅ ↔ ∃ y, y ∈ s := by
  rw [← nonempty_iff_ne_empty, nonempty_def]

-- If f: ℕ → ℕ is strictly increasing, then n ≤ f n
lemma Nat_StrictMono_le_self (f: ℕ → ℕ): StrictMono f → ∀ (n : ℕ), n ≤ f n := by
  intro h n
  induction' n with n ih
  · apply Nat.zero_le
  · have : f n < f (n+1) := by
      apply h
      rw [Nat.add_one, Nat.lt_succ]
    have : n < f (n+1) := by
      apply lt_of_le_of_lt ih this
    linarith

-- Characterization of "Disjoint" for sets
lemma disjoint_sets_iff {X : Type} {A B : Set X} : Disjoint A B ↔ A ∩ B = ∅ := by
  constructor
  · intro h
    by_contra inter_nempty
    rw [← Ne, neq_nonempty_iff_exists] at inter_nempty
    rcases inter_nempty with ⟨x, xinAB⟩
    dsimp [Disjoint] at h
    have subA : {x} ⊆ A := by
      rw [singleton_subset_iff]
      exact xinAB.1
    have subB : {x} ⊆ B := by
      rw [singleton_subset_iff]
      exact xinAB.2
    have := h subA subB
    rw [subset_empty_iff] at this
    exact (singleton_ne_empty x) this
  · intro h
    dsimp [Disjoint]
    intro C CsubA CsubB
    have : C ⊆ A ∩ B := by
      apply subset_inter CsubA CsubB
    rw [h] at this
    assumption





/-! ### Instances -/

/- We stablish several useful instances for directed sets (and so for nets using the previous
   defined constructor) -/

-- ℕ (with its usual order relation) is a directed set and so every sequence is a net

instance DirectedSet.instNat : DirectedSet ℕ where
  directed := by
    intro d e
    use max d e
    exact And.intro (le_max_left d e) (le_max_right d e)

@[simps]
instance Net.instSequences {X: Type} (s: ℕ → X) : Net X := Net.mk' DirectedSet.instNat s

/- EXTRA INFO
--You can be explicit with universes too. I'm not necessarily recommending this here, but just so you know, this is possible:

structure Net'.{v, u} (X : Type u) where
  D : Type v
  [directedSet : DirectedSet D]
  net : D → X

#check Net'.{0, 0} Nat
-- The second `0` is inferred from `Nat`, so you can do this for short:
#check Net'.{0} Nat

--Notice I put v first in Net's universe level list to make the second #check possible to write.
-/

-- The set of neighbourhoods of a point x (ordered by ⊆) is a directed set

instance DirectedSet.instNeighbourhoodRight {X: Type} [TopologicalSpace X] (x : X) : DirectedSet {U | U ∈ 𝓝 x} where
  default := ⟨univ, univ_nhds x⟩
  directed := by
    intro d e
    use ⟨d.1 ∪ e.1, union_nhds d.1 e.1 x d.2 e.2⟩
    constructor
    · apply subset_union_left
    · apply subset_union_right

@[simps]
instance Net.instNeighbourhoodRight {X: Type} [TopologicalSpace X] (x : X) (s: {U | U ∈ 𝓝 x} → X) : Net X :=
  Net.mk' (DirectedSet.instNeighbourhoodRight x) s

-- The set of neighbourhoods of a point x (ordered by ⊇) is a directed set

@[simps]
instance Preorder.SetSubLeft (X : Type) : Preorder (Set X) where
  toLE := {le := fun U ↦ (fun V ↦ V ⊆ U)}
  toLT := {lt := fun U ↦ (fun V ↦ V ⊆ U ∧ ¬ U ⊆ V)}
  le_refl := by
    intro U
    exact le_refl U
  le_trans := by
    intro U V W UleV VleW
    exact subset_trans VleW UleV
  lt_iff_le_not_le := by
    intro U V
    constructor
    repeat
      intro h
      exact h

instance DirectedSet.instNeighbourhoodLeft {X: Type} [TopologicalSpace X] (x : X) : DirectedSet {U | U ∈ 𝓝 x} where
  toPreorder := @Subtype.preorder (Set X) (Preorder.SetSubLeft X) (fun U => U ∈ 𝓝 x)
  default := ⟨univ, univ_nhds x⟩
  directed := by
    intro d e
    use ⟨d.1 ∩ e.1, inter_nhds d.1 e.1 x d.2 e.2⟩
    constructor
    · apply inter_subset_left
    · apply inter_subset_right

@[simps]
instance Net.instNeighbourhoodLeft {X: Type} [TopologicalSpace X] (x : X) (s: {U | U ∈ 𝓝 x} → X) : Net X :=
  Net.mk' (DirectedSet.instNeighbourhoodLeft x) s

-- The product of directed sets is a directed set with the order relation defined pointwise

@[simps]
instance LE.instProduct {α β : Type} [LE α] [LE β] : LE (α × β) where
  le := fun (a, b) ↦ (fun (a', b') ↦ a ≤ a' ∧ b ≤ b')

instance Preorder.instProduct {α β : Type} [Preorder α] [Preorder β] : Preorder (α × β) where
  toLE := LE.instProduct
  toLT := {lt := fun u ↦ (fun v ↦ u ≤ v ∧ ¬ v ≤ u)}
  le_refl := by
    intro u
    constructor <;> rfl
  le_trans := by
    intro u v w ulev vlew
    constructor
    · exact le_trans u.1 v.1 w.1 ulev.1 vlew.1
    · exact le_trans u.2 v.2 w.2 ulev.2 vlew.2
  lt_iff_le_not_le := by
    intro u v
    simp

instance DirectedSet.instProduct (D E : Type) [DirectedSet D] [DirectedSet E] : DirectedSet (D × E) where
  toPreorder := Preorder.instProduct
  default := (DirectedSet.default' D, DirectedSet.default' E)
  directed := by
    intro u v
    rcases DirectedSet.directed u.1 v.1 with ⟨f1, f1le⟩
    rcases DirectedSet.directed u.2 v.2 with ⟨f2, f2le⟩
    use (f1, f2)
    exact And.intro (And.intro f1le.1 f2le.1) (And.intro f1le.2 f2le.2)

@[simps]
instance Net.instProduct {X: Type} {D E : Type} (hD : DirectedSet D) (hE : DirectedSet E) (s: D × E → X) : Net X :=
  Net.mk' (DirectedSet.instProduct D E) s

-- Set of finite intersections of sets is directed by ⊇

/- We include an optional argument "K" that by default will be univ, and so the set will be equal to
   the set of finite intersections as stated -/

instance Preorder.instFiniteInterLeft {X F: Type} {A: F → Set X} (K := univ) : Preorder {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} where
toLE := {le := fun U ↦ (fun V ↦ V.1 ⊆ U.1)}
toLT := {lt := fun U ↦ (fun V ↦ V.1 ⊆ U.1 ∧ ¬ U.1 ⊆ V.1)}
le_refl := by
  intro a
  exact le_refl a
le_trans := by
  intro a b c aleb blec
  exact subset_trans blec aleb
lt_iff_le_not_le := by
  intro a b
  constructor
  repeat
    intro h
    exact h

instance DirectedSet.instFiniteInterLeft {X F: Type} {A: F → Set X} (K := univ) : DirectedSet {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} where
  default := by
    have : K ∈ {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} := by
      dsimp
      use ∅
      simp
    exact ⟨K, this⟩
  directed := by
      dsimp
      intro d e
      have : ∃ (u : Finset F),  d.1 ∩ e.1 = K ∩ ⋂ i ∈ u, A i := by
        rcases d.2 with ⟨u, d_eq_int⟩
        rcases e.2 with ⟨v, e_eq_int⟩
        use u ∪ v
        ext x
        constructor
        · intro ⟨xind, xine⟩
          simp
          rw [d_eq_int] at xind
          rw [e_eq_int] at xine
          constructor
          · exact xind.1
          · intro i iinuv
            rcases iinuv with iinu | iinv
            · simp at xind
              exact xind.2 i iinu
            · simp at xine
              exact xine.2 i iinv
        · intro h
          simp at h
          constructor
          · rw [d_eq_int]
            simp
            constructor
            · exact h.1
            · intro i iinu
              exact h.2 i (Or.inl iinu)
          · rw [e_eq_int]
            simp
            constructor
            · exact h.1
            · intro i iinv
              exact h.2 i (Or.inr iinv)
      use ⟨d.1 ∩ e.1, this⟩
      constructor
      · apply inter_subset_left
      · apply inter_subset_right

@[simps]
instance Net.instFiniteInterLeft {X F: Type} {A: F → Set X} {K: Set X} (s: {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} → X) : Net X :=
  Net.mk' (DirectedSet.instFiniteInterLeft K) s





namespace Net
open Net

/-! ### Definitions about nets -/

def Net_limit {X: Type} [TopologicalSpace X] (s : Net X) (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ (d₀ : s.D), ∀ (d : s.D), d₀ ≤ d → s.net d ∈ U

def AccumulationPoint {X: Type} [TopologicalSpace X] (s: Net X) (x : X): Prop :=
  ∀ (d : s.D), ∀ U ∈ 𝓝 x, ∃ (e : s.D), (d ≤ e ∧ s.net e ∈ U)

def Subnet {X: Type} [TopologicalSpace X] (s s': Net X) : Prop :=
  ∃ (i: s'.D → s.D), (∀ (d : s.D), ∃ (e₀ : s'.D), ∀ (e : s'.D), (e₀ ≤ e →  d ≤ (i e))) ∧
  s'.net = s.net ∘ i





/-! ### Theorems -/

/- Subsequences are subnets -/
theorem subsequence_is_subnet {X: Type} [TopologicalSpace X] (s s' : ℕ → X) :
  (∃ (i: ℕ → ℕ), StrictMono i ∧ s' = s ∘ i) → Subnet (instSequences s) (instSequences s') := by
  intro h
  dsimp [Subnet]
  rcases h with ⟨i, stricmono_i, s'eqscompi⟩
  use i
  constructor
  · intro d
    use d
    intro e dlee
    exact le_trans dlee (Nat_StrictMono_le_self i stricmono_i e)
  · assumption

/- If a net converges to x, then every subnet converges to x -/
theorem subnet_same_limit {X : Type} [TopologicalSpace X] {s s' : Net X} {x y : X} :
  Subnet s s' → Net_limit s x → Net_limit s' x := by
    intro subnet slimitx
    dsimp [Net_limit] at *
    intro U U_nhds
    dsimp [Subnet] at subnet
    rcases subnet with ⟨i, crec, comp⟩
    rw [comp]
    rcases slimitx U U_nhds with ⟨d, eq_d⟩ -- We take d so that if d ≤ d' then s(d') ∈ U
    rcases crec d with ⟨e, eq_e⟩ -- We take e so that if e ≤ e' then d ≤ i(e')
    /- Then, if e ≤ e', we have that d ≤ i(e') and so s(i(e')) ∈ U as wanted -/
    use e
    intro e' elee'
    have := eq_e e' elee'
    have := eq_d (i e') this
    exact this

/- A topological space is T2 (Hausdorff) iff every convergent net in X has a unique limit -/
theorem t2_iff_net_unique_limit {X : Type} [TopologicalSpace X] :
  T2Space X ↔ ∀ (s : Net X) (x y : X), (Net_limit s x ∧ Net_limit s y) → x = y := by
    constructor
    · intro h s x y ⟨slimitx, slimity⟩
      by_contra! xney
      /- If x ≠ y, then there exists U and V open, disjoint and such that x ∈ U and y ∈ V -/
      have t2X := T2Space.t2 xney
      dsimp at t2X
      rcases t2X with ⟨U, eq⟩
      rcases eq with ⟨V, Uopen, Vopen, xinU, xinV, disjointUV⟩
      rw [disjoint_sets_iff] at disjointUV
      dsimp [Net_limit] at *
      have U_nhds : U ∈ 𝓝 x := by
        rw [mem_nhds_iff]
        use U
      have V_nhds : V ∈ 𝓝 y := by
        rw [mem_nhds_iff]
        use V
      /- As s: D → X converges to x and y, U and V are neighbourhoods of x and y respectively
         there exist d₁, d₂ in D such that if d₁ ≤ d' then s(d') ∈ U and if d₂ ≤ d' then s(d') ∈ V.
         Using that D is directed, there exists some d in D with d₁, d₁ ≤ d, and so s(d) ∈ U ∩ V-/
      rcases slimitx U U_nhds with ⟨d₁, d1cond⟩
      rcases slimity V V_nhds with ⟨d₂, d2cond⟩
      rcases DirectedSet.directed d₁ d₂ with ⟨d, d1led, d2led⟩
      have : s.net d ∈ U ∩ V := by
        constructor
        · exact d1cond d d1led
        · exact d2cond d d2led
      rw [disjointUV, mem_empty_iff_false] at this
      assumption
    · intro h
      rw [t2Space_iff]
      /- If X is not Hausdorff, then there exist x ≠ y in X such that for any neighbourhoods U and V
         of x and y respectively they must be disjoint. We first stablish it for open neighbourhoods
         and then in general -/
      by_contra not_haus
      dsimp [Pairwise] at not_haus
      push_neg at not_haus
      rcases not_haus with ⟨x, eq⟩
      rcases eq with ⟨y, xneqy, not_haus⟩
      have not_haus : ∀ U ∈ {U | U ∈ 𝓝 x}, ∀ V ∈ {U | U ∈ 𝓝 y}, ∃ (x : X), x ∈ U ∩ V := by
        intro U U_nhds V V_nhds
        dsimp at U_nhds
        dsimp at V_nhds
        rw [mem_nhds_iff] at U_nhds
        rw [mem_nhds_iff] at V_nhds
        rcases U_nhds with ⟨U', U'subU, U'open, xinU'⟩
        rcases V_nhds with ⟨V', V'subV, V'open, yinV'⟩
        have := not_haus U' V' U'open V'open xinU' yinV'
        rw [disjoint_sets_iff, ← Ne, neq_nonempty_iff_exists] at this
        rcases this with ⟨z, zinU'V'⟩
        use z
        have : U' ∩ V' ⊆ U ∩ V := by
          exact inter_subset_inter U'subU V'subV
        apply this
        assumption
      /- We define a net over the set (𝓝 x) × (𝓝 y) (directed by ⊇ pointwise) by just picking an element
         in the intersection of any pair of neighbourhoods of x and y respectively (which always
         exists by "not_haus") -/
      let r: {U | U ∈ 𝓝 x} × {U | U ∈ 𝓝 y} → X := fun (⟨U, U_in⟩ ,⟨V, V_in⟩) ↦ if h: ∃ (x : X), x ∈ U ∩ V then Classical.choose h else x
      let s : Net X := instProduct (DirectedSet.instNeighbourhoodLeft x) (DirectedSet.instNeighbourhoodLeft y) r
      /- We have that this net converges both to x and y because given any neighbourhood U of x, we
         can take (U, Y) and if (U, Y) ≤ (W₁, W₂), then s(W₁, W₂) ∈ W₁ ∩ W₂ (by definition of the net)
         and W₁ ⊆ U, so we obtain that s(W₁, W₂) ∈ U as wanted. For y is analogous -/
      have slimit : Net_limit s x ∧ Net_limit s y := by
        constructor
        · dsimp [Net_limit]
          intro U U_nhds
          use (⟨U, U_nhds⟩, ⟨univ, univ_nhds y⟩)
          intro W le_W
          simp [s] at le_W
          dsimp [s] at W
          dsimp [s, r]
          rw [dif_pos (not_haus W.1 W.1.2 W.2 W.2.2)] -- choose = s(W₁, W₂)
          have := Classical.choose_spec (not_haus W.1 W.1.2 W.2 W.2.2)
          apply (subset_trans _ le_W) this
          apply inter_subset_left
        · dsimp [Net_limit]
          intro V V_nhds
          use (⟨univ, univ_nhds x⟩, ⟨V, V_nhds⟩)
          intro W le_W
          simp [s] at le_W
          dsimp [s] at W
          dsimp [s, r]
          rw [dif_pos (not_haus W.1 W.1.2 W.2 W.2.2)]
          have := Classical.choose_spec (not_haus W.1 W.1.2 W.2 W.2.2)
          apply (subset_trans _ le_W) this
          apply inter_subset_right
      exact xneqy (h s x y slimit)

/- A point x is an accumulation point of a net s iff there exists a subnet that converges to x -/
theorem accumulationPoint_iff_exists_subnet {X: Type} [TopologicalSpace X] (x: X) (s: Net X) :
  AccumulationPoint s x ↔ ∃ (s': Net X), (Subnet s s' ∧ Net_limit s' x) := by
    constructor
    · intro h
      dsimp [AccumulationPoint] at h
      have existence : ∀ V ∈ 𝓝 x, ∀ (d: s.D), ∃ (e: s.D), (d ≤ e ∧ s.net e ∈ V) := by
        intro V V_nhds d
        exact h d V V_nhds
      /- Since given any neighbourhood V of x and any d of D there exists an element e of D such that
         d ≤ e and s(e) ∈ V, we'll define i(V, d) = e and the subnet s' = s ∘ i (with 𝓝 x
         ordered by ⊇), so s'(V,d) ∈ V -/
      let i : {V | V ∈ 𝓝 x} × s.D → s.D := fun (⟨V, V_in⟩, d)  ↦  if h: ∃ (e: s.D), (d ≤ e ∧ s.net e ∈ V) then Classical.choose h else d
      let s' : Net X := Net.instProduct (DirectedSet.instNeighbourhoodLeft x) (s.directedSet) (s.net ∘ i)
      use s'
      constructor
      · dsimp [Subnet]
        use i
        constructor
        · intro d
          /- Using (X, d), we have that if (X, d) ≤ e = (e₁, e₂), then d ≤ e₂ and, As e₂ ≤ i(e), we
             obtain that d ≤ i(e) -/
          use (⟨univ, univ_nhds x⟩ , d)
          intro e h'
          simp [s'] at h'
          dsimp [i]
          rw [dif_pos (existence e.1 e.1.2 e.2)] -- choose = i(e)
          have := Classical.choose_spec (existence e.1 e.1.2 e.2)
          apply le_trans h' this.1
        · rfl
      · dsimp [Net_limit]
        intro U U_nhds
        /- Given any d in D, we can use (U, d). In fact, if (U, d) ≤ e = (e₁, e₂), then e₁ ⊆ U
           and s(i(e)) ∈ e₁, so s(i(e)) ∈ U -/
        let d := DirectedSet.default' s.D
        use (⟨U, U_nhds⟩ , d)
        intro e le_e
        simp [s'] at le_e
        dsimp [s', i]
        rw [dif_pos (existence e.1.1 e.1.2 e.2)] -- choose = i(e)
        have := (Classical.choose_spec (existence e.1.1 e.1.2 e.2)).right
        exact le_e.1 this
    · intro h
      rcases h with ⟨s', subnet_s', limit_s'⟩
      dsimp [AccumulationPoint]
      intro d U U_nhds
      /- As s' is a subnet of s, there exists an i: s'.D → s.D such that there exists an e₀ with the
         property that if e₀ ≤ e, then d ≤ i(e). Furthermore, as s' converges to x there exists an e₁
         in s'.D such that if e₁ ≤ e, then s'(e) = s(i(e)) ∈ U. So, it suffices to use an e in s.D with
         e₀, e₁ ≤ e. -/
      dsimp [Subnet] at subnet_s'
      rcases subnet_s' with ⟨i, i_crec, s'eqscompi⟩
      rcases i_crec d with ⟨e₀, e₀_eq⟩
      dsimp [Net_limit] at limit_s'
      rcases limit_s' U U_nhds with ⟨e₁, e₁_eq⟩
      rcases DirectedSet.directed e₀ e₁ with ⟨e, e₀lee, e₁lee⟩
      use i e
      constructor
      · exact e₀_eq e e₀lee
      · have : s.net (i e) = (s.net ∘ i) e := by
          rfl
        rw [this, ← s'eqscompi]
        apply e₁_eq e e₁lee

/- Characterization of closure by nets:
    x is in the closure of A iff exists a net in A convergent to x -/
theorem mem_closure_iff_exists_net {X: Type} [TopologicalSpace X] (A: Set X) (x : X):
  x ∈ closure A ↔ ∃ (s: Net X), (∀ (d: s.D), s.net d ∈ A) ∧ Net_limit s x := by
    constructor
    · intro h
      /- As x is in the closure of A, by definition for every neighbourhood of x V, there exists
         some point y ∈ V ∩ A. We then define a net as s: 𝓝 x → X such that s(V) ∈ V ∩ A,
         where 𝓝 x is directed by ⊇ -/
      have existence : ∀ V ∈ (𝓝 x), ∃ (y : X), y ∈ V ∩ A := by
        intro V V_nhds
        rw [mem_closure_iff_nhds] at h
        have int_nonempty := h V V_nhds
        rwa [nonempty_def] at int_nonempty
      let r : {V | V ∈ 𝓝 x} → X := fun ⟨V, V_in⟩ ↦ if h: ∃ (y : X), y ∈ V ∩ A then Classical.choose h else x
      let s : Net X := Net.instNeighbourhoodLeft x r
      use s
      constructor
        /- By definition the net is in A -/
      · intro d
        dsimp [s, r]
        rw [dif_pos (existence d.1 d.2)]
        have := Classical.choose_spec (existence d.1 d.2) -- choose = s(d)
        rw [mem_inter_iff] at this
        exact this.2
        /- Given a neighbourhood U of x, we have that if U ≤ d, then d ⊆ U, and as s(d) ∈ d ∩ A ⊆ U,
           we can conclude that s converges to x -/
      · dsimp [Net_limit]
        intro U U_nhds
        use ⟨U, U_nhds⟩
        intro d le_eq
        simp [s] at le_eq
        dsimp [s, r]
        rw [dif_pos (existence d.1 d.2)]
        have := Classical.choose_spec (existence d.1 d.2) -- choose = s(d)
        exact le_eq this.1
    · intro h
      rcases h with ⟨s, sinA, slimitx⟩
      rw [mem_closure_iff_nhds]
      /- Given s a net in A converging to x and U a neighbourhood of x, there exists a d₀ ∈ s.D
         such that if d₀ ≤ d, then s(d) ∈ U. Furthermore, as s is in A, s(d₀) ∈ A ∩ U as wanted -/
      intro U U_nhds
      rw [nonempty_def]
      dsimp [Net_limit] at slimitx
      rcases slimitx U U_nhds with ⟨d₀, d₀_eq⟩
      use s.net d₀
      exact And.intro (d₀_eq d₀ (le_refl d₀)) (sinA d₀)

/- Characterization of closed sets by nets:
    C is closed iff for every convergent net in C its limit is in C -/
theorem isClosed_iff_net_limit_self {X: Type} [TopologicalSpace X] (C: Set X) :
  IsClosed C ↔ ∀ (x : X), ∀ (s : Net X), (∀ (d: s.D), s.net d ∈ C) → Net_limit s x → x ∈ C := by
    constructor
    /- If C is closed, then C = closure C, so given any net in C converging to some x, by the previous
       theorem x ∈ closure C = C. -/
    · intro C_closed x s sinC slimitx
      rw [← closure_eq_iff_isClosed] at C_closed
      rw [← C_closed]
      rw [mem_closure_iff_exists_net C x]
      use s
    /- C is closed iff closure C ⊆ C, so it is enough to see that given c ∈ closure C, then c ∈ C.
       Now, by the previous theorem, if c ∈ closure C, then there exists a net s in C converging to c,
       and by hypothesis, c must belong to C as wanted. -/
    · intro h
      rw [← closure_subset_iff_isClosed]
      intro c cincl
      rw [mem_closure_iff_exists_net] at cincl
      rcases cincl with ⟨s, sinC, slimitc⟩
      exact h c s sinC slimitc

/- Characterization of compact sets by nets:
    K is comapact iff every net in K has a convergent subnet-/
theorem compact_iff_net_has_convergent_subnet {X : Type} [TopologicalSpace X] (K: Set X) : IsCompact K ↔
K = ∅ ∨ ∀ (s : Net X), (∀ (d : s.D), s.net d ∈ K) → (∃ (s': Net X), ∃ x ∈ K, Subnet s s' ∧ Net_limit s' x) := by
  constructor
  · intro K_Compact
    /- If K is compact and empty, then the second condition is trivially true because there are
       not nets in K, so we just need to proof this second assertion -/
    right
    intro s sinK
    /- K is compact iff any family of closed sets in K (so of the form K ∩ F with F closed)
       have the FIP (finite intersection property), that is, if every subfamily of finite sets
       has nonempty intersection, then the whole family has nonempty intersection -/
    rw [isCompact_iff_finite_subfamily_closed] at K_Compact
    /- Given a net s: D → X, for every c in D we define the set A(c) = closure {s(d) | c ≤ d} -/
    let A : s.D → Set X := fun c ↦ closure {x | ∃ (d : s.D), c ≤ d ∧ x = s.net d}
    /- Is then clear that every A(c) is closed -/
    have mem_A_closed : (∀ (d : s.D), IsClosed (A d)):= by
      intro d
      dsimp [A]
      exact isClosed_closure
    /- By the characterization of compactness given, the family {A(c) | c ∈ D} has the FIP -/
    have A_FIP : (∀ (u : Finset s.D), K ∩ ⋂ i ∈ u, A i ≠ ∅) → K ∩ ⋂ i, A i ≠ ∅ := by
      contrapose!
      exact K_Compact A mem_A_closed
    /- Furthermore, the hypothesis for the FIP is satisfied. If u is a finite subset of D
       we define d₀ has an element in D greater than every element of d
       (d₀ exists because D is directed). Then, as s is in K, s(d₀) ∈ K, and
       as for every c in u c ≤ d₀, s(d₀) ∈ {s(d) | c ≤ d} ⊆ A(c) -/
    have : ∀ (u : Finset s.D), K ∩ ⋂ i ∈ u, A i ≠ ∅ := by
      intro u
      rw [neq_nonempty_iff_exists]
      have sup_u := DirectedSet.sup_finite_set u
      rcases sup_u with ⟨d₀, d₀supu⟩
      use (s.net d₀)
      constructor
      · exact sinK d₀
      · rw [mem_iInter]
        intro c
        rw [mem_iInter]
        intro cinu
        have : {x | ∃ d_1, c ≤ d_1 ∧ x = s.net d_1} ⊆ A c := by
          exact subset_closure
        apply this
        dsimp
        use d₀
        exact And.intro (d₀supu c cinu) (by rfl)
    have := A_FIP this
    rw [neq_nonempty_iff_exists] at this
    /- If we take x in K ∩ ⋂ i, A i it is enough to see that it is an accumulation point of s
       by the characterization of this type of points given before -/
    rcases this with ⟨x, xinK, xinInter⟩
    have xAcc : AccumulationPoint s x := by
      dsimp [AccumulationPoint]
      intro d U U_nhds
      /- Given any d in D and U a neighbourhood of x, then x ∈ A(d) and by the definition of A(d)
         we obtain that there exists a y ∈ U ∩ {s(c) | d ≤ c}. Taking e in D such that y = s(e) we
         conclude that d ≤ e and y = s(e) ∈ U as wanted -/
      have : x ∈ A d := by
        rw [mem_iInter] at xinInter
        exact xinInter d
      dsimp [A] at this
      rw [mem_closure_iff_nhds] at this
      rcases this U U_nhds with ⟨y, yinU, yinAd⟩
      dsimp [A] at yinAd
      rcases yinAd with ⟨e, dlee, yeq⟩
      use e
      rw [yeq] at yinU
      exact And.intro dlee yinU
    rw [accumulationPoint_iff_exists_subnet] at xAcc
    rcases xAcc with ⟨s', Subnet_s', limit⟩
    use s', x
  · intro h
    /- We'll distinguish two cases with K empty or not -/
    rcases Classical.em (K = ∅) with K_empty | K_nempty
    · rw [K_empty]
      exact isCompact_empty
    · have h := Or.resolve_left h K_nempty -- We consider the second part of the hypothesis as K ≠ ∅
      /- Again, to prove that K is compact we'll prove that any family of closed sets in K has
         the FIP. -/
      rw [isCompact_iff_finite_subfamily_closed]
      intro F A mem_A_closed
      contrapose!
      intro A_finite_inter_nonempty
      /- As finite intersections of elements of the family {A(i) | i ∈ F} (intersected with K)
         is nonempty, we can define a net over this set of all finite intersections
        (directed by ⊇) that assigns to every finite intersection an element of that intersection.
        Then, to prove that K ∩ ⋂ i, A i is nonempty we will proof that any of its accumulation
        points are in this intersection and, by hypothesis and the characterization of accumulation
        points, there exists at least one -/
      rw [nonempty_def]
      have cond : ∀ U ∈ {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i}, ∃ x, x ∈ U := by
        simp
        intro u
        have := A_finite_inter_nonempty u
        rw [nonempty_def] at this
        simp at this
        exact this
      rw [← Ne, neq_nonempty_iff_exists] at K_nempty
      rcases K_nempty with ⟨x, xinK⟩ -- We obtain an element of K just to define the net (the "else" case)
      let r : {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} → X := fun U ↦ if h: ∃ x, x ∈ U.1 then Classical.choose h else x
      let s : Net X := Net.instFiniteInterLeft r
      /- We prove that s is in K (which is true by the given definition) -/
      have sinK : ∀ (d : s.D), s.net d ∈ K := by
        intro d
        dsimp [s, r]
        rw [dif_pos (cond d.1 d.2)]
        have := Classical.choose_spec (cond d.1 d.2) -- choose = s(d)
        have dsubsetK : d.1 ⊆ K := by
          rcases d.2 with ⟨u, d_eq⟩
          rw [d_eq]
          apply inter_subset_left
        exact dsubsetK this
      /- By hypothesis, as s is in K, there exists a convergent subnet of s converging to some
         point in K. By the characterization given before, this limit is an accumulation porint of s -/
      rcases h s sinK with ⟨s', eq⟩
      rcases eq with ⟨x, xinK, subnet, limit⟩
      have Accpointx : AccumulationPoint s x := by
        rw [accumulationPoint_iff_exists_subnet]
        use s'
      use x
      constructor
      · exact xinK
      · rw [mem_iInter]
        intro i
        /- As A(i) is closed, to se that an element is in A(i) it it enough to see that it the
           intersection of A(i) with any neighbourhood of x is nonempty -/
        rw [← (closure_eq_iff_isClosed).mpr (mem_A_closed i), mem_closure_iff_nhds]
        intro U U_nhds
        rw [nonempty_def]
        dsimp [AccumulationPoint] at Accpointx
        /- As K ∩ A(i) is a finite intersection of elements of {A(j) | j ∈ F} (intersected with K)
           and x is an accumulation point of s, there exists a G in s.D such that G ⊆ K ∩ A(i) and
           s(G) ∈ U. By definition, s(G) ∈ G and G ⊆ K ∩ A(i) ⊆ A(i), so s(G) ∈ A(i) and, finally,
           s(G) ∈ U ∩ A(i) -/
        have : K ∩ A i ∈ {U | ∃ (u : Finset F), U = K ∩ ⋂ i ∈ u, A i} := by
          dsimp
          use {i}
          simp
        rcases Accpointx ⟨K ∩ (A i), this⟩ U U_nhds with ⟨G, leG, sGinU⟩
        simp [s] at leG
        use s.net G
        constructor
        · assumption
        · dsimp [s, r]
          rw [dif_pos (cond G.1 G.2)]
          have := Classical.choose_spec (cond G.1 G.2) -- choose = s(G)
          exact leG.2 this
