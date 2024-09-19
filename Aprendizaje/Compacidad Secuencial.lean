import MIL.Common
import Mathlib.Topology.Instances.Real

noncomputable section

open Set Filter Topology Classical

set_option linter.unusedVariables false

def IsOpenCover {X: Type} [TopologicalSpace X] (B : Set (Set X)) (A: Set X): Prop :=
  ∀ U ∈ B, (IsOpen U ∧ A ⊆ ⋃ U ∈ B, U)

def IsSubCover {X: Type} [TopologicalSpace X] (B : Set (Set X)) (C : Set (Set X)) (A: Set X): Prop :=
  C ⊆ B ∧ A ⊆ ⋃ U ∈ C, U

def IsCompact_open {X: Type} [TopologicalSpace X] (K: Set X): Prop :=
  ∀ (B : Set (Set X)), (IsOpenCover B K → ∃ (F: Set (Set X)), (F.Finite ∧ IsSubCover B F K))

def ConvergesTo {X: Type} [TopologicalSpace X] (s : ℕ → X) (x : X) :=
  ∀ U ∈ (𝓝 x), ∃ (n₀ : ℕ), ∀ (n : ℕ), n₀ ≤ n → s n ∈ U

def Rec_def {X: Type} [TopologicalSpace X] (s: ℕ → X) (A: ℕ → Set X): ℕ → ℕ
    | 0 => 1
    | m + 1 => if h: ∃ (n : ℕ), ((Rec_def s A m) < n ∧ (s n) ∈ A (Rec_def s A m)) then Classical.choose h else 0

theorem Nat_lt_iff_exists (a b : ℕ): a < b ↔ ∃ (p : ℕ), b = a + (p + 1) := by
  constructor
  · intro h
    induction' a with a ih
    · use (Nat.pred b)
      have : b ≠ 0 := by
        apply Nat.not_eq_zero_of_lt h
      rw [zero_add, ← Nat.succ_eq_add_one, Nat.succ_pred this]
    · have altb : a < b := by
        apply lt_trans (Nat.lt_succ_self a) h
      rcases (ih altb) with ⟨p, p_eq⟩
      have pnzero : p ≠ 0 := by
        by_contra p_zero
        rw [p_zero, zero_add] at p_eq
        rw [p_eq] at h
        linarith
      use Nat.pred p
      nth_rw 2 [← Nat.succ_eq_add_one]
      rw [Nat.succ_pred pnzero]
      linarith
  · intro h
    rcases h with ⟨p, p_eq⟩
    rw [p_eq, Nat.lt_iff_le_and_ne]
    constructor
    · apply Nat.le_add_right
    · by_contra h
      linarith

lemma aux {f: ℕ → ℕ}: (∀ (n : ℕ), f n < f (n+1)) → ∀ (p n : ℕ), f n < f (n + p + 1) := by
  intro h
  intro p n
  induction' p with p ih
  · rw [add_zero]
    exact h n
  · apply lt_trans ih
    rw [← add_assoc]
    exact h (n + p + 1)

theorem Nat_StrictMono (f: ℕ → ℕ): StrictMono f ↔ ∀ (n : ℕ), f n < f  (n+1) := by
  constructor
  · intro h n
    dsimp [StrictMono] at h
    have : n < n+1 := by
      linarith
    exact h this
  · intro h
    dsimp [StrictMono]
    intro a b altb
    rw [Nat_lt_iff_exists] at altb
    rcases altb with ⟨p, p_eq⟩
    rw [p_eq, ← add_assoc]
    apply aux h p

theorem Nat_StrictMono_le_self (f: ℕ → ℕ): StrictMono f → ∀ (n : ℕ), n ≤ f n := by
  intro h n
  induction' n with n ih
  · apply Nat.zero_le
  · have : f n < f (n+1) := by
      apply h
      rw [Nat.add_one, Nat.lt_succ]
    have : n < f (n+1) := by
      apply lt_of_le_of_lt ih this
    linarith

theorem Real_archimedean (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  use (Nat.floor (y/x)) + 1
  have : y/x < (Nat.floor (y/x)) + 1 := by
    by_contra h
    push_neg at h
    have : (Nat.floor (y/x)) + 1 ≤ (Nat.floor (y/x)) := by
      apply Nat.le_floor
      norm_cast at h
    have : (Nat.floor (y/x)) < (Nat.floor (y/x)) + 1 := by
      linarith
    linarith
  rw [div_lt_iff] at this
  norm_cast at this
  exact x_pos

#check exists_lt_nsmul

theorem Real_archimedean' (x y : ℝ) : (0 < x) → (0 < y) → ∃ (n : ℕ), y < n * x := by
  intro x_pos y_pos
  have : ∃ (n : ℕ), y ≤ n • x := by
    apply Archimedean.arch y x_pos
  rcases this with ⟨n, n_eq⟩
  have : n • x = ↑n * x := by
    rw [nsmul_eq_mul] -- Incluido en el simplificador
  use (n + 1)
  rw [this] at n_eq
  apply lt_of_le_of_lt n_eq
  apply mul_lt_mul
  · norm_cast
    linarith
  · rfl
  · exact x_pos
  · norm_cast
    linarith

theorem Real_archimedean'' (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  simpa using exists_lt_nsmul x_pos y

theorem metric_compactopen_if_seq_compact (X: Type) [MetricSpace X] (K: Set X): IsCompact_open K →
  ∀ (s: ℕ → X), ((∀ (n: ℕ), s n ∈ K) → ∃ x ∈ K, ∃ (φ: ℕ → ℕ), (StrictMono φ ∧ ConvergesTo (s ∘ φ) x)) := by
  intro h s sK
  by_contra Nosub
  push_neg at Nosub
  have h1 : ∀ x ∈ K, ∃ U ∈ (𝓝 x), (IsOpen U ∧ Finite {n | s n ∈ U}) := by
    intro x xK
    by_contra hc
    push_neg at hc
    have Ball_nhds : ∀ (n : ℕ),  Metric.ball x (1/(n+1)) ∈ (𝓝 x) := by
      intro n
      apply Metric.ball_mem_nhds
      norm_num
      norm_cast
      norm_num
    have : ∀ (m : ℕ), ∃ (n : ℕ), (m < n ∧ (s n) ∈ Metric.ball x (1 / (m + 1))) := by
      intro m
      have := hc (Metric.ball x (1 / (m + 1))) (Ball_nhds m) Metric.isOpen_ball
      rw [← Set.Finite, ← Set.Infinite, infinite_iff_exists_gt] at this
      dsimp at this
      have := this m
      rcases this with ⟨n, snin, mltn⟩
      use n
    let f_ball : ℕ → Set X := fun n ↦ Metric.ball x (1 / (n + 1))
    let φ := Rec_def s f_ball
    have phimono: StrictMono φ := by
      rw [Nat_StrictMono]
      intro n
      dsimp [φ]
      rw [Rec_def, dif_pos (this (Rec_def s f_ball n))]
      apply (Classical.choose_spec (this (Rec_def s f_ball n))).left
    have Noconv : ¬ConvergesTo (s ∘ φ) x := by
      apply Nosub x xK φ phimono
    have Conv : ConvergesTo (s ∘ φ) x := by
      dsimp [ConvergesTo]
      intro U U_nhds
      rw [Metric.mem_nhds_iff] at U_nhds
      rcases U_nhds with ⟨e, e_eq⟩
      have : ∃ (n : ℕ), (0 < n) ∧ 1/n ≤ e := by
        have : ∃ (n : ℕ), 1 < n * e := by
          apply Real_archimedean _
          exact e_eq.left
        rcases this with ⟨n, n_eq⟩
        use n
        have n_pos : 0 < n := by
          by_contra n_neg
          push_neg at n_neg
          rw [Nat.le_zero] at n_neg
          rw [n_neg] at n_eq
          norm_cast at n_eq
          rw [zero_mul] at n_eq
          linarith
        constructor
        · exact n_pos
        · rw [div_le_iff]
          · rw [lt_iff_le_and_ne, mul_comm] at n_eq
            exact n_eq.left
          · norm_cast
      rcases this with ⟨n₀, n₀_eq⟩
      have sub_balls : Metric.ball x (1/n₀) ⊆ Metric.ball x e := by
        apply Metric.ball_subset_ball n₀_eq.right
      have def_pos : ∀ (m : ℕ), 0 < Rec_def s f_ball m := by
        intro m
        induction' m with m ih
        · rw [Rec_def]
          linarith
        · have : ∀ (m: ℕ), Rec_def s f_ball m = φ m := by
            intro m
            rfl
          rw [this (m+1)]
          rw [this m] at ih
          apply lt_trans ih
          apply phimono
          linarith
      have clave : ∀ (m : ℕ), s (φ (m + 1)) ∈ Metric.ball x (1/φ m) := by
          intro m
          dsimp [φ]
          rw [Rec_def, dif_pos (this (Rec_def s f_ball m))]
          have s_in := (Classical.choose_spec (this (Rec_def s f_ball m))).right
          have : ∀ (p : ℕ), (0 < p) → Metric.ball x (1 / (p + 1)) ⊆ Metric.ball x (1 / p) := by
            intro p p_pos
            apply Metric.ball_subset_ball _
            norm_cast
            apply div_le_div
            · linarith
            · rfl
            · norm_cast
            · norm_cast
              apply Nat.le_succ
          apply this (↑(Rec_def s f_ball m)) _ s_in
          exact def_pos m
      use n₀ + 1
      intro n le_eq
      rcases n with _ | n
      · linarith
      · have le_eq2 : n₀ ≤ n := by
          apply Nat.le_of_succ_le_succ le_eq
        have sub_balls2 : Metric.ball x (1 / (φ n)) ⊆ Metric.ball x (1 / n) := by
          apply Metric.ball_subset_ball
          apply div_le_div
          · linarith
          · rfl
          · norm_cast
            apply lt_of_lt_of_le (n₀_eq.left) le_eq2
          · norm_cast
            exact Nat_StrictMono_le_self φ phimono n
        have sub_balls3 : Metric.ball x (1 / n) ⊆ Metric.ball x (1 / n₀) := by
          apply Metric.ball_subset_ball
          apply div_le_div
          · linarith
          · rfl
          · norm_cast
            apply n₀_eq.left
          · norm_cast
        exact e_eq.right (sub_balls (sub_balls3 (sub_balls2 (clave n))))
    contradiction
  let f: X → Set X := fun x ↦ if h: ∃ U ∈ (𝓝 x), (IsOpen U ∧ Finite {n | s n ∈ U}) then Classical.choose h else univ
  have op_cover :  IsOpenCover (f '' K) K := by
    dsimp [IsOpenCover]
    intro U h
    rw [mem_image] at h
    rcases h with ⟨x, xK, x_im⟩
    dsimp [f] at x_im
    dsimp at h1
    rw [dif_pos (h1 x xK)] at x_im
    rw [← x_im]
    have := (Classical.choose_spec (h1 x xK))
    constructor
    · exact this.right.left
    · intro k kK
      rw [mem_iUnion₂]
      use f k
      have : f k ∈ f '' K := by
        rw [mem_image]
        use k
      use this
      dsimp [f]
      rw [dif_pos (h1 k kK)]
      have := (Classical.choose_spec (h1 k kK)).left
      rw [mem_nhds_iff] at this
      rcases this with ⟨t, t1, t2, t3⟩
      exact t1 t3
  have Fin_subcover := h (f '' K) op_cover
  rcases Fin_subcover with ⟨F, F_eq⟩
  have N : {n | n = n} = {n | s n ∈ K} := by
    ext n
    constructor
    · intro hn
      dsimp
      exact sK n
    · intro hn
      dsimp
  have Infinito : {n | s n ∈ K}.Infinite := by
    let idN : ℕ → ℕ := fun n ↦ n
    have injec : Function.Injective idN := by
      intro n m
      dsimp [idN]
      intro h
      assumption
    have : {n : ℕ | n = n} = range (idN) := by
      ext n
      simp
    rw [← N, this, infinite_range_iff injec]
    apply instInfiniteNat
  have Finito : {n | s n ∈ K}.Finite := by
    have : {n | s n ∈ K} = ⋃ U ∈ F, {n | s n ∈ U} := by
      ext n
      constructor
      · intro h
        dsimp at *
        have := F_eq.right
        dsimp [IsSubCover] at this
        have := this.right
        have : ∃ U ∈ F, (s n) ∈ U := by
          have : (s n) ∈ ⋃ U ∈ F, U := by
            exact this h
          rw [mem_iUnion₂] at this
          rcases this with ⟨U, ⟨UinF, sninU⟩⟩
          use U
        rw [mem_iUnion₂]
        rcases this with ⟨U, UinF, sninU⟩
        use U
        use UinF
        dsimp
        exact sninU
      · intro h
        dsimp
        exact sK n
    rw [this]
    dsimp [Set.Finite] at *
    have F_finite := F_eq.left
    apply Finite.Set.finite_biUnion F _ _
    intro U hU
    have : U ∈ f '' K := by
      have := F_eq.right
      dsimp [IsSubCover] at this
      exact this.left hU
    rw [mem_image] at this
    rcases this with ⟨x, xK, x_im⟩
    dsimp [f] at x_im
    rw [dif_pos (h1 x xK)] at x_im
    rw [← x_im]
    dsimp
    have := (Classical.choose_spec (h1 x xK)).right.right
    exact this
  contradiction
