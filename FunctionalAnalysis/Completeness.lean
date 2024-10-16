import Topology.Nets.Theorems

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Classical Function DirectedSet Net

theorem Real_archimedean' (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  simpa using exists_lt_nsmul x_pos y

lemma Net.cauchy_metric_iff {X D: Type*} [DirectedSet D] [MetricSpace X] (s: D → X):
  CauchyNet s ↔ ∀ (n: ℕ), ∃ (d₀: D), (∀ (d e: D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < 1/(n + 1)) := by
    sorry

def seqfromnet {X D: Type*} [MetricSpace X] [DirectedSet D] (s: D → X): ℕ → D
  | 0 => if h: ∃ d₀, (∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < 1) then Classical.choose h else default' D
  | n + 1 => if h: ∃ (d₀: D), ((seqfromnet s n) ≤ d₀ ∧ ((∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < 1 / (n + 2)))) then Classical.choose h else default' D

lemma seqfromnet_prop {X D: Type*} [MetricSpace X] [DirectedSet D] (s: D → X)
  (h: CauchyNet s):
    ∀ (n: ℕ), ∀ (d e : D), seqfromnet s n ≤ d → seqfromnet s n ≤ e → dist (s d) (s e) < 1/(n + 1) := by
      rw [cauchy_metric_iff] at h
      intro n
      by_cases nz: n = 0
      · have cond := h 0
        rw [nz]
        dsimp only [seqfromnet]
        rw [Nat.cast_zero, zero_add, div_self one_ne_zero] at cond
        rw [dif_pos cond]
        rw [Nat.cast_zero, zero_add, div_self one_ne_zero]
        exact Classical.choose_spec cond
      · rcases Nat.exists_eq_succ_of_ne_zero nz with ⟨m, neqm1⟩
        rw [Nat.succ_eq_add_one] at neqm1
        rw [neqm1]
        dsimp only [seqfromnet]
        have cond : ∃ d₀, seqfromnet s m ≤ d₀ ∧ ∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < 1 / (m + 2) := by
          rcases h (m + 1) with ⟨d₁, eq⟩
          rcases directed' (seqfromnet s m) d₁ with ⟨d₀, seqmled₀, d₁led₀⟩
          use d₀
          constructor
          · assumption
          · intro d e d₀led d₀lee
            rw [Nat.cast_add, add_assoc, Nat.cast_one, one_add_one_eq_two] at eq
            exact eq d e (le_trans d₁led₀ d₀led) (le_trans d₁led₀ d₀lee)
        rw [dif_pos cond]
        rw [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
        exact (Classical.choose_spec cond).2

lemma seqfromnet_incr' {X D: Type*} [MetricSpace X] [DirectedSet D] (s: D → X) (h: CauchyNet s):
  ∀ (n: ℕ), seqfromnet s n ≤ seqfromnet s (n + 1) := by
    intro n
    rw [cauchy_metric_iff] at h
    have cond : ∃ d₀, seqfromnet s n ≤ d₀ ∧ ∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < 1 / (n + 2) := by
      rcases h (n + 1) with ⟨d₁, eq⟩
      rcases directed' (seqfromnet s n) d₁ with ⟨d₀, seqmled₀, d₁led₀⟩
      use d₀
      constructor
      · assumption
      · intro d e d₀led d₀lee
        rw [Nat.cast_add, add_assoc, Nat.cast_one, one_add_one_eq_two] at eq
        exact eq d e (le_trans d₁led₀ d₀led) (le_trans d₁led₀ d₀lee)
    dsimp only [seqfromnet]
    rw [dif_pos cond]
    exact (Classical.choose_spec cond).1

lemma seqfromnet_incr {X D: Type*} [MetricSpace X] [DirectedSet D] (s: D → X) (h: CauchyNet s):
  ∀ (n m: ℕ), n ≤ m →  seqfromnet s n ≤ seqfromnet s m := by
    intro n m nltm
    induction' m with m ih
    · rw [Nat.le_zero] at nltm
      rw [nltm]
    · rw [Nat.le_succ_iff_eq_or_le] at nltm
      rcases nltm with neqm1 | nlem
      · rw [Nat.succ_eq_add_one] at neqm1
        rw [← neqm1]
      · exact le_trans (ih nlem) (seqfromnet_incr' s h m)

theorem Metric.complete_iff {X: Type*} [MetricSpace X]:
  CompleteSpace X ↔ ∀ (s: ℕ → X), CauchyNet s → ∃ (x: X), Limit s x := by
    constructor
    · intro completeX s cauchys
      rw [cauchy_net_iff_filter] at cauchys
      rcases completeX.complete cauchys with ⟨x, limitFx⟩
      use x
      rw [limit_net_iff_filter]
      assumption
    · intro cauchyconv
      rw [complete_iff_netcomplete]
      unfold CompleteNet
      intro D h s cauchys
      let i := seqfromnet s
      have cauchysi : CauchyNet (s ∘ i) := by
        rw [cauchy_metric_iff]
        intro n
        use n
        intro m p nlem nlep
        simp only [i, comp_apply]
        exact seqfromnet_prop s cauchys n (seqfromnet s m) (seqfromnet s p)
          (seqfromnet_incr s cauchys n m nlem) (seqfromnet_incr s cauchys n p nlep)
      rcases cauchyconv (s ∘ i) cauchysi with ⟨x, limisix⟩
      use x
      unfold Limit at *
      intro U Unhds
      rw [Metric.mem_nhds_iff] at Unhds
      rcases Unhds with ⟨ε, εpos, ballsubU⟩
      rcases limisix (ball x (ε/2)) (by apply ball_mem_nhds x (by linarith)) with ⟨n', eq⟩
      have: ∃ (n₀: ℕ), n' ≤ n₀ ∧ 1/(n₀ + 1) < ε/2 := by
        rcases Real_archimedean' 1 (2/ε - 1) zero_lt_one with ⟨n₁, eq⟩
        use max n₁ n'
        constructor
        · exact Nat.le_max_right n₁ n'
        · rw [one_div_lt]
          · rw [one_div, inv_div]
            rw [mul_one, sub_lt_iff_lt_add] at eq
            apply lt_of_lt_of_le eq
            rw [add_le_add_iff_right, Nat.cast_max]
            apply le_max_left
          · linarith
          · linarith
      rcases this with ⟨n₀, n'len₀, lte⟩
      use i n₀
      intro d inled
      apply ballsubU
      rw [mem_ball]
      calc
        dist (s d) x ≤ dist (s d) (s (i n₀)) + dist (s (i n₀)) x := by
          exact dist_triangle (s d) (s (i n₀)) x
        _ < dist (s d) (s (i n₀)) + ε/2 := by
          rw [add_lt_add_iff_left, ← mem_ball]
          exact eq n₀ n'len₀
        _ < 1/(n₀ + 1) + ε/2 := by
          rw [add_lt_add_iff_right]
          dsimp only [i] at *
          exact seqfromnet_prop s cauchys n₀ d (seqfromnet s n₀) inled (le_refl _)
        _ < ε/2 + ε/2 := by
          rw [add_lt_add_iff_right]
          exact lte
        _ = ε := by
          linarith
