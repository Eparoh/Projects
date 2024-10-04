import  Topology.Nets.DirectedSets

noncomputable section

open Set Filter Topology Classical Function DirectedSet

set_option trace.Meta.Tactic.simp false
namespace Net

/- ### Definitions about nets ### -/

def Limit {X D: Type*} [TopologicalSpace X] [DirectedSet D] (s : D → X) (x: X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ (d₀ : D), ∀ (d : D), d₀ ≤ d → s d ∈ U

def ClusterPoint {X D: Type*} [TopologicalSpace X] [DirectedSet D] (s: D → X) (x : X): Prop :=
  ∀ (d : D), ∀ U ∈ 𝓝 x, ∃ (e : D), (d ≤ e ∧ s e ∈ U)

def Subnet {X D E: Type*} [DirectedSet D] [DirectedSet E] (s: D → X) (s': E → X) : Prop :=
  ∃ (i: E → D), (∀ (d : D), ∃ (e₀ : E), ∀ (e : E), (e₀ ≤ e →  d ≤ (i e))) ∧ s' = s ∘ i

/- ### Basic results ### -/

/- Subsequences are subnets -/
theorem subsequence_is_subnet {X: Type} [TopologicalSpace X] (s s' : ℕ → X) :
  (∃ (i: ℕ → ℕ), StrictMono i ∧ s' = s ∘ i) → Subnet s s' := by
  intro h
  dsimp [Subnet]
  rcases h with ⟨i, stricmono_i, s'eqscompi⟩
  use i
  constructor
  · intro d
    use d
    intro e dlee
    exact le_trans dlee (StrictMono.id_le stricmono_i e)
  · assumption

/- If a net converges to x, then every subnet converges to x -/
theorem subnet_same_limit {X D E: Type*} [TopologicalSpace X] [DirectedSet D] [DirectedSet E]
  {s : D → X} {s' : E → X} {x : X} : Subnet s s' → Limit s x → Limit s' x := by
    intro subnet slimitx
    dsimp [Limit] at *
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

theorem subnet_clusterpoint_implies_net_clusterpoint {X D E: Type*} [TopologicalSpace X] [DirectedSet D] [DirectedSet E]
  {s : D → X} {s' : E → X} {x : X} : Subnet s s' → ClusterPoint s' x → ClusterPoint s x := by
    intro subnet clpoints'x
    dsimp [ClusterPoint] at *
    intro d U Unhds
    dsimp [Subnet] at subnet
    rcases subnet with ⟨i, crec, comp⟩
    rcases crec d with ⟨e₀, eq⟩
    rcases clpoints'x e₀ U Unhds with ⟨e, e₀lee, s'einU⟩
    use i e
    constructor
    · exact eq e e₀lee
    · rw [← @comp_apply D X E s i e, ← comp]
      assumption

/- A point x is an accumulation point of a net s iff there exists a subnet that converges to x -/
theorem ClPoint_iff_exists_subnet {X D: Type*} [TopologicalSpace X] [h: DirectedSet D] (s: D → X) (x : X) :
  ClusterPoint s x ↔ ∃ (E: Type (max u_1 u_2)) (h': DirectedSet E) (s': E → X), (Subnet s s' ∧ Limit s' x) := by
    constructor
    · intro t
      dsimp [ClusterPoint] at t
      have existence : ∀ V ∈ 𝓝 x, ∀ (d: D), ∃ (e: D), (d ≤ e ∧ s e ∈ V) := by
        intro V V_nhds d
        exact t d V V_nhds
      /- Since given any neighbourhood V of x and any d of D there exists an element e of D such that
         d ≤ e and s(e) ∈ V, we'll define i(V, d) = e and the subnet s' = s ∘ i (with 𝓝 x
         ordered by ⊇), so s'(V,d) ∈ V -/
      let i : {V | V ∈ 𝓝 x} × D → D := fun (⟨V, _⟩, d)  ↦  if h: ∃ (e: D), (d ≤ e ∧ s e ∈ V) then Classical.choose h else d
      let s' : {V | V ∈ 𝓝 x} × D → X := s ∘ i
      use ({V | V ∈ 𝓝 x} × D), (@instProduct {V | V ∈ 𝓝 x} D (instNeighbourhoodLeft x) h), s'
      constructor
      · unfold Subnet
        use i
        constructor
        · intro d
          /- Using (X, d), we have that if (X, d) ≤ e = (e₁, e₂), then d ≤ e₂ and, As e₂ ≤ i(e), we
             obtain that d ≤ i(e) -/
          use (⟨univ, univ_mem⟩ , d)
          intro e t'
          simp only [Prod.le_def] at t'
          dsimp only [i]
          rw [dif_pos (existence e.1 e.1.2 e.2)] -- choose = i(e)
          have := Classical.choose_spec (existence e.1 e.1.2 e.2)
          apply le_trans t'.2 this.1
        · rfl
      · dsimp [Limit]
        intro U U_nhds
        /- Given any d in D, we can use (U, d). In fact, if (U, d) ≤ e = (e₁, e₂), then e₁ ⊆ U
           and s(i(e)) ∈ e₁, so s(i(e)) ∈ U -/
        let d := DirectedSet.default' D
        use (⟨U, U_nhds⟩ , d)
        intro e le_e
        simp only [Prod.le_def] at le_e
        dsimp [s', i]
        rw [dif_pos (existence e.1.1 e.1.2 e.2)] -- choose = i(e)
        have := (Classical.choose_spec (existence e.1.1 e.1.2 e.2)).right
        exact le_e.1 this
    · intro t
      rcases t with ⟨E, h', s', subnet_s', limit_s'⟩
      dsimp [ClusterPoint]
      intro d U U_nhds
      /- As s' is a subnet of s, there exists an i: s'.D → s.D such that there exists an e₀ with the
         property that if e₀ ≤ e, then d ≤ i(e). Furthermore, as s' converges to x there exists an e₁
         in s'.D such that if e₁ ≤ e, then s'(e) = s(i(e)) ∈ U. So, it suffices to use an e in s.D with
         e₀, e₁ ≤ e. -/
      dsimp [Subnet] at subnet_s'
      rcases subnet_s' with ⟨i, i_crec, s'eqscompi⟩
      rcases i_crec d with ⟨e₀, e₀_eq⟩
      dsimp [Limit] at limit_s'
      rcases limit_s' U U_nhds with ⟨e₁, e₁_eq⟩
      rcases DirectedSet.directed' e₀ e₁ with ⟨e, e₀lee, e₁lee⟩
      use i e
      constructor
      · exact e₀_eq e e₀lee
      · have : s (i e) = (s ∘ i) e := by
          rfl
        rw [this, ← s'eqscompi]
        apply e₁_eq e e₁lee

/- ### Relation between nets and filters ### -/

def FNet {X D : Type*} [DirectedSet D] (s : D → X) : Filter X := {
  sets := {A : Set X | ∃ d : D, ∀ d' : D, (d ≤ d' → s d' ∈ A)}
  univ_sets := by
    simp only [Set.mem_setOf_eq, mem_univ, implies_true, exists_const]
  sets_of_superset := by
    intro A B Ain AsubB
    rcases Ain with ⟨d, sinA⟩
    rw [Set.mem_setOf_eq]
    use d
    intro d' dled'
    exact AsubB (sinA d' dled')
  inter_sets := by
    intro A B Ain Bin
    rcases Ain with ⟨d, sdin⟩
    rcases Bin with ⟨e, sein⟩
    rcases directed' d e with ⟨f, dlef, elef⟩
    rw [Set.mem_setOf_eq]
    use f
    intro d' fled'
    constructor
    · exact sdin d' (le_trans dlef fled')
    · exact sein d' (le_trans elef fled')
}

instance FNet.instNeBot {X D : Type*} [DirectedSet D] (s : D → X) : Filter.NeBot (FNet s) where
  ne' := by
    intro emptyinF
    simp only [← empty_mem_iff_bot, FNet, Filter.mem_mk, Set.mem_setOf_eq, mem_empty_iff_false] at emptyinF
    rcases emptyinF with ⟨d, eq⟩
    exact eq d (le_refl d)

theorem limit_net_iff_filter {X D : Type*} [TopologicalSpace X] [DirectedSet D] (s : D → X) (x: X) : Limit s x ↔ FNet s ≤ 𝓝 x := by
  constructor
  · intro limitsx
    intro U Unhds
    rcases limitsx U Unhds with ⟨d, eq⟩
    simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq]
    use d
  · intro limitFx U Unhds
    have UinF := limitFx Unhds
    simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq] at UinF
    assumption

theorem ClPoint_net_iff_filter {X D : Type*} [TopologicalSpace X] [DirectedSet D] (s : D → X) (x: X) : ClusterPoint s x ↔ ClusterPt x (FNet s) := by
  constructor
  · intro clpointsx
    rw [clusterPt_iff]
    intro U Unhds V VinF
    rw [nonempty_def]
    simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq] at VinF
    rcases VinF with ⟨d, eq⟩
    rcases clpointsx d U Unhds with ⟨e, dlee, seinU⟩
    use s e
    constructor
    · assumption
    · exact eq e dlee
  · intro clpointFx
    intro d U Unhds
    rw [clusterPt_iff] at clpointFx
    have : s '' {e: D | d ≤ e} ∈ FNet s := by
      simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq]
      use d
      intro d' dled'
      rw [mem_image]
      use d'
      constructor
      · assumption
      · rfl
    have := clpointFx Unhds this
    rcases this with ⟨z, zinU, zinV⟩
    rcases zinV with ⟨f, dlef, sfeqz⟩
    rw [Set.mem_setOf_eq] at dlef
    use f
    constructor
    · assumption
    · rw [sfeqz]
      assumption

def DirectedSetF {X: Type*} (F: Filter X) := {P : X × Set X | P.1 ∈ P.2 ∧ P.2 ∈ F}

def NetF {X: Type*} (F: Filter X): DirectedSetF F → X := fun (P: DirectedSetF F) ↦ P.1.1

instance DirectedSetF.isntDirectedSet {X: Type*} (F: Filter X) [Filter.NeBot F] : DirectedSet (DirectedSetF F) where
  le := fun P Q ↦ Q.1.2 ⊆ P.1.2
  le_refl := by
    intro P x xin
    exact xin
  le_trans := by
    intro P Q R PleQ QleR
    apply subset_trans QleR PleQ
  default := by
    have : Inhabited X := by
      have : @univ X ≠ ∅ := by
        intro univempty
        have := empty_not_mem F
        rw [← univempty] at this
        have := Filter.univ_sets F
        contradiction
      rw [← nonempty_iff_ne_empty, nonempty_def] at this
      exact inhabited_of_exists this
    let x := @Inhabited.default X _
    have : (x, univ) ∈ DirectedSetF F := by
      simp only [DirectedSetF, Set.mem_setOf_eq]
      exact And.intro (mem_univ x) univ_mem
    exact ⟨(x, univ), this⟩
  directed := by
    intro P Q
    have : P.1.2 ∩ Q.1.2 ∈ F := by
      exact inter_mem (P.2.2) (Q.2.2)
    have : ∃ (x: X), x ∈ P.1.2 ∩ Q.1.2 := by
      exact Eventually.exists this
    rcases this with ⟨x, xininter⟩
    have : (x, P.1.2 ∩ Q.1.2) ∈ DirectedSetF F := by
      simp only [DirectedSetF, Set.mem_setOf_eq]
      constructor
      · assumption
      · assumption
    use ⟨(x, P.1.2 ∩ Q.1.2), this⟩
    constructor
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right

theorem DirectedSetF_le_iff {X: Type*} (F: Filter X) [Filter.NeBot F] : ∀ (P Q : DirectedSetF F), P ≤ Q ↔ Q.1.2 ⊆ P.1.2 := by
  intro P Q
  rfl

theorem limit_filter_iff_net {X: Type*} [TopologicalSpace X] (F: Filter X) [Filter.NeBot F] (x: X) :
  F ≤ 𝓝 x ↔ Limit (NetF F) x := by
    constructor
    · intro limitFx
      intro U Unhds
      have : (x, U) ∈ DirectedSetF F := by
        simp only [DirectedSetF, Set.mem_setOf_eq]
        constructor
        · exact mem_of_mem_nhds Unhds
        · exact limitFx Unhds
      use ⟨(x, U), this⟩
      intro e dlee
      simp only [NetF]
      simp only [DirectedSetF_le_iff] at dlee
      exact dlee e.2.1
    · intro limitsx U Unhds
      rcases limitsx U Unhds with ⟨d, eq⟩
      apply Filter.sets_of_superset F d.2.2
      intro y yind2
      have : (y, d.1.2) ∈ DirectedSetF F := by
        simp only [DirectedSetF, Set.mem_setOf_eq]
        exact And.intro yind2 d.2.2
      have := eq ⟨(y, d.1.2), this⟩ (by simp only [DirectedSetF_le_iff]; exact subset_rfl)
      simp only [NetF] at this
      assumption

theorem ClPoint_filter_iff_net {X: Type*} [TopologicalSpace X] (F: Filter X) [h: Filter.NeBot F] (x: X) :
  ClusterPt x F ↔ ClusterPoint (NetF F) x := by
    constructor
    · intro clpointFx
      intro d U Unhds
      rw [clusterPt_iff] at clpointFx
      rcases clpointFx Unhds d.2.2 with ⟨y, yinU, yind⟩
      use ⟨(y, d.1.2), And.intro yind d.2.2⟩
      constructor
      · simp only [DirectedSetF_le_iff]
        exact subset_rfl
      · simp only [NetF]
        assumption
    · intro clpoinsx
      rw [clusterPt_iff]
      intro U Unhds V VinF
      rcases NeBot.nonempty_of_mem h VinF with ⟨v, vinV⟩
      rcases clpoinsx ⟨(v, V), And.intro vinV VinF⟩ U Unhds with ⟨e, vVlee, seinU⟩
      use e.1.1
      constructor
      · exact seinU
      · exact vVlee e.2.1

lemma net_in_set_implies_set_in_filter {X: Type*} [TopologicalSpace X] (A: Set X):
  ∀ (D: Type u_1) (h: DirectedSet D) (s: D → X), (∀ (d: D), s d ∈ A) → A ∈ FNet s := by
    intro D h s sinA
    have : s '' {d: D | (default' D) ≤ d} ∈ FNet s := by
      simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq]
      use default' D
      intro d' defled'
      use d'
      constructor
      · rw [Set.mem_setOf_eq]
        assumption
      · rfl
    apply Filter.sets_of_superset (FNet s) this
    intro x xin
    rcases xin with ⟨d, _, sdeqx⟩
    rw [← sdeqx]
    exact sinA d

def DirectedSetFA {X: Type*} (F: Filter X) (A: Set X) (_: A ∈ F) := {P : X × Set X | P.1 ∈ P.2 ∧ P.2 ∈ F ∧ P.2 ⊆ A}

instance DirectedSetFA.isntDirectedSet {X: Type*} (F: Filter X) [Filter.NeBot F] (A: Set X) (h: A ∈ F) : DirectedSet (DirectedSetFA F A h) where
  le := fun P Q ↦ Q.1.2 ⊆ P.1.2
  le_refl := by
    intro P x xin
    exact xin
  le_trans := by
    intro P Q R PleQ QleR
    apply subset_trans QleR PleQ
  default := by
    have : A ≠ ∅ := by
      intro Aempty
      have := empty_not_mem F
      rw [← Aempty] at this
      contradiction
    rw [← nonempty_iff_ne_empty, nonempty_def] at this
    let a := Classical.choose this
    exact ⟨(a, A), And.intro (Classical.choose_spec this) (And.intro h subset_rfl)⟩
  directed := by
    intro P Q
    have : P.1.2 ∩ Q.1.2 ∈ F := by
      exact inter_mem (P.2.2.1) (Q.2.2.1)
    have : ∃ (x: X), x ∈ P.1.2 ∩ Q.1.2 := by
      exact Eventually.exists this
    rcases this with ⟨x, xininter⟩
    have : (x, P.1.2 ∩ Q.1.2) ∈ DirectedSetFA F A h := by
      simp only [DirectedSetFA, Set.mem_setOf_eq]
      constructor
      · assumption
      · constructor
        · assumption
        · intro x xininter
          apply P.2.2.2
          exact xininter.1
    use ⟨(x, P.1.2 ∩ Q.1.2), this⟩
    constructor
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right

def NFinclusion {X: Type*} (F: Filter X) [Filter.NeBot F] (A: Set X) (h: A ∈ F)  : DirectedSetFA F A h → DirectedSetF F := fun P ↦ ⟨P, And.intro P.2.1 P.2.2.1⟩

theorem DirectedSetFA_le_iff {X: Type*} (F: Filter X) [Filter.NeBot F] (A: Set X) (h: A ∈ F) : ∀ (P Q : DirectedSetFA F A h), P ≤ Q ↔ Q.1.2 ⊆ P.1.2 := by
  intro P Q
  rfl

theorem NetF_inclusion_in_set {X: Type*} [TopologicalSpace X] (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) :
  ∀ (d: DirectedSetFA F A h), (NetF F ∘ NFinclusion F A h) d ∈ A := by
    intro d
    simp only [comp_apply, NetF]
    exact d.2.2.2 d.2.1

theorem NetF_inclusion_subnet {X: Type*} [TopologicalSpace X] (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) :
  Subnet (NetF F) (NetF F ∘ NFinclusion F A h) := by
    use NFinclusion F A h
    constructor
    · intro d
      have : ∃ (y: X), y ∈ A ∩ d.1.2 := by
        rw [← nonempty_def, nonempty_iff_ne_empty]
        intro empty
        have : A ∩ d.1.2 ∈ F := by
          exact inter_mem h d.2.2
        rw [empty] at this
        have := empty_not_mem F
        contradiction
      rcases this with ⟨y, yininter⟩
      have : (y, A ∩ d.1.2) ∈ DirectedSetFA F A h := by
        simp only [DirectedSetFA, Set.mem_setOf_eq]
        constructor
        · exact yininter
        · constructor
          · exact inter_mem h d.2.2
          · intro a aininter
            exact aininter.1
      use ⟨(y, A ∩ d.1.2), this⟩
      intro e lee
      simp only [DirectedSetF_le_iff]
      simp only [DirectedSetFA_le_iff] at lee
      apply subset_trans lee
      intro x xininter
      exact xininter.2
    · rfl

theorem NetF_inclusion_same_limit {X: Type*} [TopologicalSpace X] (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) (x: X) :
  F ≤ 𝓝 x → Limit (NetF F ∘ NFinclusion F A h) x := by
    intro limitFx
    rw [limit_filter_iff_net] at limitFx
    exact subnet_same_limit (NetF_inclusion_subnet F A h) limitFx

theorem clupoint_NetF_inclusion_implies_clpoint {X: Type*} [TopologicalSpace X] (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) (x: X) :
  ClusterPoint (NetF F ∘ NFinclusion F A h) x → ClusterPt x F := by
    intro clpointsx
    have := subnet_clusterpoint_implies_net_clusterpoint (NetF_inclusion_subnet F A h) clpointsx
    rw [← ClPoint_filter_iff_net] at this
    assumption

/- ### Classic characterizations ### -/

theorem mem_closure_iff_exists_filter {X: Type*} [TopologicalSpace X] (A: Set X) (x : X) :
  x ∈ closure A ↔ ∃ (F: Filter X), F.NeBot ∧  A ∈ F ∧ F ≤ 𝓝 x := by
    constructor
    · intro xinclos
      let G:= Filter.generate ({U | U ∈ 𝓝 x} ∪ {A})
      use G
      constructor
      · rw [Filter.generate_neBot_iff]
        intro Y Ysub Yfin
        by_cases AinY : A ∈ Y
        · have : ⋂₀ (Y \ {A}) ∈ 𝓝 x := by
            rw [Filter.sInter_mem]
            · intro U UinY
              simp at UinY
              rcases Ysub UinY.1 with h | h
              · assumption
              · rw [mem_singleton_iff] at h
                have := UinY.2
                contradiction
            · exact Finite.diff Yfin {A}
          rw [mem_closure_iff_nhds] at xinclos
          have:= xinclos (⋂₀ (Y \ {A})) this
          have : ⋂₀ (Y \ {A}) ∩ A = ⋂₀ Y := by
            ext y
            constructor
            · intro yin
              simp at *
              intro t tinY
              by_cases teqA : t = A
              · rw [teqA]
                exact yin.2
              · exact yin.1 t tinY teqA
            · intro yin
              simp at *
              constructor
              · intro t tinY _
                exact yin t tinY
              · exact yin A AinY
          rw [← this]
          assumption
        · have : ⋂₀ Y ∈ 𝓝 x := by
            rw [Filter.sInter_mem]
            · intro U UinY
              rcases Ysub UinY with h | h
              · exact h
              · rw [mem_singleton_iff] at h
                rw [h] at UinY
                contradiction
            · assumption
          use x
          exact mem_of_mem_nhds this
      · constructor
        · apply mem_generate_of_mem
          simp
        · intro U Unhds
          apply mem_generate_of_mem
          simp
          right
          assumption
    · intro h
      rcases h with ⟨F, Fnebot, AinF, limitFx⟩
      rw [mem_closure_iff_nhds]
      intro U Unhds
      have : U ∩ A ∈ F := by
        exact inter_mem (limitFx Unhds) AinF
      exact NeBot.nonempty_of_mem Fnebot this

theorem mem_closure_iff_exists_net {X: Type*} [TopologicalSpace X] (A: Set X) (x : X):
  x ∈ closure A ↔ ∃ (D: Type u_1) (h: DirectedSet D) (s: D → X), (∀ (d: D), s d ∈ A) ∧ Limit s x := by
    have : Inhabited X := by
      exact { default := x }
    rw [mem_closure_iff_exists_filter]
    constructor
    · intro cond
      rcases cond with ⟨F, Fnebot, AinF, limitFx⟩
      use DirectedSetFA F A AinF, DirectedSetFA.isntDirectedSet F A AinF , NetF F ∘ NFinclusion F A AinF
      exact And.intro (NetF_inclusion_in_set F A AinF) (NetF_inclusion_same_limit F A AinF x limitFx)
    · intro cond
      rcases cond with ⟨D, h, s, sinA, limitsx⟩
      use FNet s
      exact And.intro (FNet.instNeBot s) (And.intro (net_in_set_implies_set_in_filter A D h s sinA)
        ((limit_net_iff_filter s x).mp limitsx))

theorem isClosed_iff_limit_self {X: Type*} [TopologicalSpace X] (C: Set X) :
  IsClosed C ↔ ∀ (x : X), ∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d: D), s d ∈ C) → Limit s x → x ∈ C := by
    rw [isClosed_iff_forall_filter]
    constructor
    · intro cond
      intro x D h s sinC limitsx
      have : FNet s ≤ 𝓟 C := by
        rw [le_principal_iff]
        exact net_in_set_implies_set_in_filter C D h s sinC
      exact cond x (FNet s) (FNet.instNeBot s) this ((limit_net_iff_filter s x).mpr limitsx)
    · intro cond
      intro x F Fnebot CinF limitFx
      rw [le_principal_iff] at CinF
      exact cond x (DirectedSetFA F C CinF) (DirectedSetFA.isntDirectedSet F C CinF) (NetF F ∘ NFinclusion F C CinF)
        (NetF_inclusion_in_set F C CinF) (NetF_inclusion_same_limit F C CinF x limitFx)

theorem compact_iff_net_has_accumulationpoint {X : Type*} [TopologicalSpace X] (K: Set X) : IsCompact K ↔
  K = ∅ ∨ ∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) → (∃ x ∈ K, ClusterPoint s x) := by
    constructor
    · intro Kcomp
      by_cases Kem : K = ∅
      · left
        assumption
      · right
        intro D h s sinK
        simp only [IsCompact] at Kcomp
        rcases Kcomp ((le_principal_iff).mpr (net_in_set_implies_set_in_filter K D h s sinK)) with ⟨x, xinK, clpointFx⟩
        use x
        exact And.intro xinK ((ClPoint_net_iff_filter s x).mpr clpointFx)
    · intro cond
      rcases cond with cond | cond
      · rw [cond]
        exact isCompact_empty
      · simp only [IsCompact]
        intro F Fnebot KinF
        rw [le_principal_iff] at KinF
        rcases cond (DirectedSetFA F K KinF) (DirectedSetFA.isntDirectedSet F K KinF) (NetF F ∘ NFinclusion F K KinF)
          (NetF_inclusion_in_set F K KinF) with ⟨x, xinK, clpoint⟩
        use x
        exact And.intro xinK (clupoint_NetF_inclusion_implies_clpoint F K KinF x clpoint)

theorem compact_iff_net_has_convergent_subnet {X : Type*} [TopologicalSpace X] (K: Set X) : IsCompact K ↔
  K = ∅ ∨ ∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) →
  (∃ (E: Type u_1) (h': DirectedSet E) (s': E → X), ∃ x ∈ K, Subnet s s' ∧ Limit s' x) := by
    have : (∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) → ∃ (E: Type u_1) (h': DirectedSet E) (s': E → X), ∃ x ∈ K, Subnet s s' ∧ Limit s' x) ↔
             (∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) → ∃ x ∈ K, ClusterPoint s x) := by
              constructor
              · intro t D h s dinK
                rcases t D h s dinK with ⟨E, h', s', x, xinK, eq⟩
                use x, xinK
                rw [ClPoint_iff_exists_subnet]
                use E, h', s'
              · intro t D h s dinK
                rcases t D h s dinK with ⟨x, xinK, eq⟩
                rw [ClPoint_iff_exists_subnet] at eq
                rcases eq with ⟨E, h', s', eq⟩
                use E, h', s', x
    rw [compact_iff_net_has_accumulationpoint, this]

theorem continuous_iff_image_of_net_converges {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f: X → Y) (x : X):
  ContinuousAt f x ↔ ∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), Limit s x → Limit (f ∘ s) (f x) := by
    constructor
    · intro fcontatx D h s limitsx
      unfold ContinuousAt at fcontatx
      rw [Filter.tendsto_def] at fcontatx
      rw [limit_net_iff_filter]
      intro V Vnhds
      simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq]
      have := limitsx (f ⁻¹' V) (fcontatx V Vnhds)
      simp only [mem_preimage] at this
      simp only [comp_apply]
      assumption
    · intro cond
      unfold ContinuousAt
      rw [Filter.tendsto_def]
      intro V Vnhds
      have : Limit (NetF (𝓝 x)) x := by
        intro U Unhds
        use ⟨(x, U), And.intro (mem_of_mem_nhds Unhds) Unhds⟩
        intro d xUled
        simp only [NetF]
        simp only [DirectedSetF_le_iff] at xUled
        exact xUled d.2.1
      rcases cond (DirectedSetF (𝓝 x)) (DirectedSetF.isntDirectedSet (𝓝 x)) (NetF (𝓝 x)) this V Vnhds with ⟨d, eq⟩
      have : d.1.2 ⊆ f ⁻¹' V := by
        intro z zind2
        rw [mem_preimage]
        have : d ≤ ⟨(z, d.1.2), And.intro zind2 d.2.2⟩ := by
          rw [DirectedSetF_le_iff]
        have := eq ⟨(z, d.1.2), And.intro zind2 d.2.2⟩ this
        simp only [NetF, comp_apply] at this
        assumption
      exact mem_of_superset d.2.2 this

theorem t2_iff_net_unique_limit_filter {X : Type*} [TopologicalSpace X] :
  T2Space X ↔ ∀ (F: Filter X) (_: Filter.NeBot F) (x y : X), F ≤ 𝓝 x → F ≤ 𝓝 y → x = y := by
    constructor
    · intro t2
      intro F h x y limitFx limitFy
      by_contra! xneqy
      rw [← disjoint_nhds_nhds] at xneqy
      unfold Disjoint at xneqy
      have := xneqy limitFx limitFy
      simp at this
      rw [Filter.neBot_iff] at h
      contradiction
    · intro cond
      rw [t2Space_iff_disjoint_nhds]
      by_contra not_haus
      dsimp only [Pairwise] at not_haus
      push_neg at not_haus
      rcases not_haus with ⟨x, y, xneqy, disjnhds⟩
      dsimp only [Disjoint] at disjnhds
      push_neg at disjnhds
      rcases disjnhds with ⟨F, limitFx, limitFy, nebotF⟩
      simp at nebotF
      rw [← Ne, ← Filter.neBot_iff] at nebotF
      exact xneqy (cond F nebotF x y limitFx limitFy)

theorem t2_iff_net_unique_limit {X : Type*} [TopologicalSpace X] :
  T2Space X ↔ ∀ (D: Type u_1) (h: DirectedSet D) (s : D → X) (x y : X), Limit s x → Limit s y → x = y := by
    rw [t2_iff_net_unique_limit_filter]
    constructor
    · intro cond
      intro D h s x y limitsx limitsy
      rw [limit_net_iff_filter] at *
      exact cond (FNet s) (FNet.instNeBot s) x y limitsx limitsy
    · intro cond F Fnebot x y limitFx limitFy
      rw [limit_filter_iff_net] at *
      exact cond (DirectedSetF F) (DirectedSetF.isntDirectedSet F) (NetF F) x y limitFx limitFy
