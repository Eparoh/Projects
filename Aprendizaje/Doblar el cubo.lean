import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.LinearIndependent

noncomputable section

open Real Classical Function

set_option linter.unusedVariables false
set_option linter.simpsNoConstructor false

/- -------------------------------- -/
def ORn (P : ℕ → Prop): ℕ → Prop
  | 0 => P 0
  | n + 1 => P 0 ∨ ORn (P ∘ Nat.succ) n

example (P: ℕ → Prop): ORn P 4 ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 := by
  rfl

lemma ORn_zero {P: ℕ → Prop} : ORn P 0 ↔ P 0 := by
  rfl

lemma ORn_recdef (P: ℕ → Prop) (n : ℕ) : ORn P (n + 1) ↔ P 0 ∨ ORn (P ∘ Nat.succ) n := by
  rfl

theorem cosita (n : ℕ) (P: ℕ → Prop) : P 0 ∨ ORn (P ∘ Nat.succ) n ↔ ORn P (n + 1) := by
  induction' n with n ih
  · dsimp [ORn]
    rfl
  · dsimp [ORn]
    rfl

theorem coso''' (n : ℕ) : ∀ (P : ℕ → Prop), ORn P n ∨ P (n + 1) ↔ ORn P (n + 1) := by
  induction' n with n ih
  · intro P
    simp
    dsimp [ORn]
    rfl
  · intro P
    rw [← cosita, ORn_recdef, ← ih (P ∘ Nat.succ), ← or_assoc]
    nth_rw 3 [comp_def]


theorem coso'' (n : ℕ) (P: ℕ → Prop) : ORn P n ∨ P (n + 1) ↔ ORn P (n + 1) := by
  exact coso''' n P


theorem coso' {x : ℕ} (n : ℕ) : x ≤ n ↔ ORn (fun k ↦ x = k) n := by
  induction' n with n ih
  · rw [Nat.le_zero]
    dsimp [ORn]
    rfl
  · rw [Nat.le_succ_iff, ih]
    apply coso'' n (fun k ↦ x = k)

theorem coso {x : ℕ} (n : ℕ) (h: 0 < n): x < n ↔ ORn (fun k ↦ x = k) (n - 1) := by
  induction' n with n ih
  · contradiction
  · simp
    rcases Classical.em (n = 0) with nz | nnz
    · rw [nz]
      simp
      dsimp [ORn]
      rfl
    · rw [← Ne, Nat.ne_zero_iff_zero_lt] at nnz
      have := ih nnz
      rw [Nat.lt_succ_iff]
      exact coso' n
/- -------------------------------------------------------- -/

/- Distance between two points in ℝ × ℝ -/
def distance (A B : ℝ × ℝ) : ℝ := Real.sqrt ((A.1 - B.1)^2 + (A.2 - B.2)^2)

/- Intersection of two lines that goes throw the points A, B and C, D respectively -/
def line (A B: ℝ × ℝ) := {P | ∃ (t : ℝ), P = A + t • (B-A)}

def circunference (c: ℝ × ℝ) (r : ℝ) := {P | distance P c = r}

def IsConstruction (Γ : Set (ℝ × ℝ)) (n : ℕ) (f: ℕ → ℝ × ℝ) : Prop := (1 ≤ n) ∧ ∀ (i : ℕ), i < n →
  (f i ∈ Γ ∨
  (∃ (j₁ j₂ k₁ k₂ : ℕ), j₁ < i ∧ j₂ < i ∧  k₁ < i ∧ k₂ < i ∧ (line (f j₁) (f j₂) ≠ line (f k₁) (f k₂) ∧ f i ∈ (line (f j₁) (f j₂)) ∩ (line (f k₁) (f k₂)))) ∨
  (∃ (j₁ j₂ c r₁ r₂ : ℕ), j₁ < i ∧ j₂ < i ∧  c < i ∧ r₁ < i ∧ r₂ < i ∧ f i ∈ (line (f j₁) (f j₂)) ∩ (circunference (f c) (distance (f r₁) (f r₂)))) ∨
  (∃ (c₁ c₂ r₁ r₂ s₁ s₂ : ℕ), c₁ < i ∧ c₂ < i ∧ r₁ < i ∧ r₂ < i ∧ s₁ < i ∧ s₂ < i ∧ (((f c₁) ≠ (f c₂) ∨ distance (f r₁) (f r₂) ≠ distance (f s₁) (f s₂)) ∧ f i ∈ (circunference (f c₁) (distance (f r₁) (f r₂))) ∩ (circunference (f c₂) (distance (f s₁) (f s₂))))))

def partial_fun (n : ℕ) (p : ℕ → Prop) (P Q : ℝ × ℝ): ℝ × ℝ :=
  if p n then
    P
  else
    Q

theorem eval_pos (n: ℕ) (p : ℕ → Prop) {P Q : ℝ × ℝ} (h: p n) : partial_fun n p P Q = P := by
  dsimp [partial_fun]
  simp
  intro npn
  contradiction

theorem eval_neg (n: ℕ) (p : ℕ → Prop) {P Q : ℝ × ℝ} (h: ¬ p n) : partial_fun n p P Q = Q := by
  dsimp [partial_fun]
  simp
  intro npn
  contradiction

def zero_comp (f g: ℕ → ℝ × ℝ) (n : ℕ) : ℕ → ℝ × ℝ := fun m ↦ partial_fun m (fun x ↦ x < n) (f m) (g (m - n))

theorem zero_comp_less (f g: ℕ → ℝ × ℝ) (n : ℕ) : ∀ m < n, zero_comp f g n m = f m := by
  intro m mlen
  dsimp [zero_comp]
  rw [eval_pos m (fun x => x < n) mlen]

theorem zero_comp_more (f g: ℕ → ℝ × ℝ) (n : ℕ) : ∀ m, (n ≤ m) → zero_comp f g n m = g (m - n) := by
  intro m nltm
  dsimp [zero_comp]
  have : ¬ m < n := by
    apply Nat.not_lt_of_ge nltm
  rw [eval_neg m (fun x => x < n) this]

theorem add_construction (Γ : Set (ℝ × ℝ)) (n m : ℕ) (f g: ℕ → ℝ × ℝ): IsConstruction Γ n f → IsConstruction Γ m g →
  IsConstruction Γ (n + m) (zero_comp f g n) := by
    intro f_cons g_cons
    dsimp [IsConstruction]
    constructor
    · exact le_add_right f_cons.1
    · intro i ilt
      have : i < n ∨ (n ≤ i ∧ i < n + m) := by
        rcases Classical.em (i < n) with iltn1 | inletn1
        · left
          assumption
        · right
          constructor
          · linarith
          · assumption
      rcases this with h | h
      · have jlen : ∀ {x : ℕ}, x < i → x < n := by
          intro x xlti
          linarith
        rcases f_cons.2 i h with h' | h' | h' | h'
        · left
          rw [zero_comp_less f g n i h]
          assumption
        · right
          left
          rcases h' with ⟨j1, j2, k1, k2, eq⟩
          use j1, j2, k1, k2
          rw [zero_comp_less f g n i h, zero_comp_less f g n j1 (jlen eq.1),
              zero_comp_less f g n j2 (jlen eq.2.1), zero_comp_less f g n k1 (jlen eq.2.2.1),
              zero_comp_less f g n k2 (jlen eq.2.2.2.1)]
          exact eq
        · right
          right
          left
          rcases h' with ⟨j1, j2, c, r1, r2, eq⟩
          use j1, j2, c, r1, r2
          rw [zero_comp_less f g n i h, zero_comp_less f g n j1 (jlen eq.1),
              zero_comp_less f g n j2 (jlen eq.2.1), zero_comp_less f g n c (jlen eq.2.2.1),
              zero_comp_less f g n r1 (jlen eq.2.2.2.1), zero_comp_less f g n r2 (jlen eq.2.2.2.2.1)]
          exact eq
        · right
          right
          right
          rcases h' with ⟨c1, c2, r1, r2, s1, s2, eq⟩
          use c1, c2, r1, r2, s1, s2
          rw [zero_comp_less f g n i h, zero_comp_less f g n c1 (jlen eq.1),
              zero_comp_less f g n c2 (jlen eq.2.1), zero_comp_less f g n r1 (jlen eq.2.2.1),
              zero_comp_less f g n r2 (jlen eq.2.2.2.1), zero_comp_less f g n s1 (jlen eq.2.2.2.2.1),
              zero_comp_less f g n s2 (jlen eq.2.2.2.2.2.1)]
          exact eq
      · have ilt : i - n < m := by
          rw [Nat.sub_lt_iff_lt_add h.1]
          assumption
        have jilt : ∀ x, n ≤ x + n := by
          intro x
          linarith
        have aux1 : ∀ x, x + n < i ↔ x < i - n := by
            intro x
            exact Iff.symm Nat.lt_sub_iff_add_lt
        have aux2 : ∀ x, x + n - n = x := by
          intro x
          simp
        rcases g_cons.2 (i - n) ilt with h' | h' | h' | h'
        · left
          rw [zero_comp_more f g n i h.1]
          assumption
        · right
          left
          rcases h' with ⟨j1, j2, k1, k2, eq⟩
          use j1 + n, j2 + n, k1 + n, k2 + n
          rw [zero_comp_more f g n i h.1, zero_comp_more f g n (j1 + n) (jilt j1),
              zero_comp_more f g n (j2 + n) (jilt j2), zero_comp_more f g n (k1 + n) (jilt k1),
              zero_comp_more f g n (k2 + n) (jilt k2), aux1 j1, aux1 j2, aux1 k1, aux1 k2,
              aux2 j1, aux2 j2, aux2 k1, aux2 k2]
          exact eq
        · right
          right
          left
          rcases h' with ⟨j1, j2, c, r1, r2, eq⟩
          use j1 + n, j2 + n, c + n , r1 + n, r2 + n
          rw [zero_comp_more f g n i h.1, zero_comp_more f g n (j1 + n) (jilt j1),
              zero_comp_more f g n (j2 + n) (jilt j2), zero_comp_more f g n (c + n) (jilt c),
              zero_comp_more f g n (r1 + n) (jilt r1), zero_comp_more f g n (r2 + n) (jilt r2),
              aux1 j1, aux1 j2, aux1 c, aux1 r1, aux1 r2, aux2 j1, aux2 j2, aux2 c, aux2 r1, aux2 r2]
          exact eq
        · right
          right
          right
          rcases h' with ⟨c1, c2, r1, r2, s1, s2, eq⟩
          use c1 + n, c2 + n, r1 + n, r2 + n, s1 + n, s2 + n
          rw [zero_comp_more f g n i h.1, zero_comp_more f g n (c1 + n) (jilt c1),
              zero_comp_more f g n (c2 + n) (jilt c2), zero_comp_more f g n (r1 + n) (jilt r1),
              zero_comp_more f g n (r2 + n) (jilt r2), zero_comp_more f g n (s1 + n) (jilt s1),
              zero_comp_more f g n (s2 + n) (jilt s2), aux1 c1, aux1 c2, aux1 r1, aux1 r2,
              aux1 s1, aux1 s2, aux2 c1, aux2 c2, aux2 r1, aux2 r2, aux2 s1, aux2 s2]
          exact eq

def constructible_point (Γ : Set (ℝ × ℝ)) (P: ℝ × ℝ) : Prop := ∃ (n : ℕ) (f: ℕ → ℝ × ℝ), P = f (n - 1) ∧ IsConstruction Γ n f

def constructible_set : Set (ℝ × ℝ) := {P | constructible_point {(0,0), (1,0)} P}

def constructible_real_set : Set ℝ := {x | (x, 0) ∈ constructible_set}

theorem add_construction' (Γ : Set (ℝ × ℝ)) {n : ℕ} {f: ℕ → ℝ × ℝ} (P : ℝ × ℝ): IsConstruction Γ n f → constructible_point {Q | ∃ i < n, Q = f i} P →
  constructible_point Γ P := by
    intro f_cons P_cons
    dsimp [constructible_point] at *
    rcases P_cons with ⟨m, g, P_eq, g_cons⟩
    let h : ℕ → ℝ × ℝ := zero_comp f g n
    use n + m, h
    constructor
    · dsimp [h]
      have : n ≤ n + m - 1 := by
        rw [Nat.add_sub_assoc]
        apply Nat.le_add_right
        exact g_cons.1
      rw [zero_comp_more f g n (n + m - 1) this]
      · have : n + m - 1 - n = m - 1:= by
          rw [Nat.sub_eq_iff_eq_add this,
              Nat.sub_eq_iff_eq_add (by apply Nat.le_trans f_cons.1 (Nat.le_add_right n m)),
              add_comm (m - 1) n, add_assoc, Nat.sub_add_cancel (by exact g_cons.1)]
        rw [this]
        assumption
    · dsimp [IsConstruction]
      constructor
      · exact Nat.le_trans f_cons.1 (Nat.le_add_right n m)
      · intro i iltnm
        rcases Classical.em (i < n) with iltn | inltn
        · dsimp [h]
          rcases f_cons.2 i iltn with h' | h' | h' | h'
          · left
            rw [zero_comp_less f g n i iltn]
            assumption
          · right
            left
            rcases h' with ⟨j1, j2, k1, k2, eq⟩
            use j1, j2, k1, k2
            rw [zero_comp_less f g n i iltn,
                zero_comp_less f g n j1 (by apply lt_trans eq.1 iltn),
                zero_comp_less f g n j2 (by apply lt_trans eq.2.1 iltn),
                zero_comp_less f g n k1 (by apply lt_trans eq.2.2.1 iltn),
                zero_comp_less f g n k2 (by apply lt_trans eq.2.2.2.1 iltn)]
            assumption
          · right
            right
            left
            rcases h' with ⟨j1, j2, c, r1, r2, eq⟩
            use j1, j2, c, r1, r2
            rw [zero_comp_less f g n i iltn,
                zero_comp_less f g n j1 (by apply lt_trans eq.1 iltn),
                zero_comp_less f g n j2 (by apply lt_trans eq.2.1 iltn),
                zero_comp_less f g n c (by apply lt_trans eq.2.2.1 iltn),
                zero_comp_less f g n r1 (by apply lt_trans eq.2.2.2.1 iltn),
                zero_comp_less f g n r2 (by apply lt_trans eq.2.2.2.2.1 iltn)]
            assumption
          · right
            right
            right
            rcases h' with ⟨c1, c2, r1, r2, s1, s2, eq⟩
            use c1, c2, r1, r2, s1, s2
            rw [zero_comp_less f g n i iltn,
                zero_comp_less f g n c1 (by apply lt_trans eq.1 iltn),
                zero_comp_less f g n c2 (by apply lt_trans eq.2.1 iltn),
                zero_comp_less f g n r1 (by apply lt_trans eq.2.2.1 iltn),
                zero_comp_less f g n r2 (by apply lt_trans eq.2.2.2.1 iltn),
                zero_comp_less f g n s1 (by apply lt_trans eq.2.2.2.2.1 iltn),
                zero_comp_less f g n s2 (by apply lt_trans eq.2.2.2.2.2.1 iltn)]
            assumption
        · simp at inltn
          dsimp [h]
          have : i - n < m := by
            rw [Nat.sub_lt_iff_lt_add inltn]
            assumption
          rcases g_cons.2 (i - n) this with h' | h' | h' | h'
          · dsimp at h'
            rcases h' with ⟨j, jltn, geqf⟩
            rcases f_cons.2 j jltn with h'' | h'' | h'' | h''
            · left
              rw [zero_comp_more f g n i inltn, geqf]
              assumption
            · right
              left
              rcases h'' with ⟨j1, j2, k1, k2, eq⟩
              have : j1 < i ∧ j2 < i ∧ k1 < i ∧ k2 < i ∧ line (f j1) (f j2) ≠ line (f k1) (f k2) ∧ f j ∈ line (f j1) (f j2) ∩ line (f k1) (f k2) := by
                have jlti : j < i := by
                  apply Nat.lt_of_lt_of_le jltn inltn
                constructor
                · apply lt_trans eq.1 jlti
                · constructor
                  · apply lt_trans eq.2.1 jlti
                  · constructor
                    · apply lt_trans eq.2.2.1 jlti
                    · constructor
                      · apply lt_trans eq.2.2.2.1 jlti
                      · apply eq.2.2.2.2
              use j1, j2, k1, k2
              rw [zero_comp_more f g n i inltn, geqf,
                  zero_comp_less f g n j1 (by apply lt_trans eq.1 jltn),
                  zero_comp_less f g n j2 (by apply lt_trans eq.2.1 jltn),
                  zero_comp_less f g n k1 (by apply lt_trans eq.2.2.1 jltn),
                  zero_comp_less f g n k2 (by apply lt_trans eq.2.2.2.1 jltn)]
              assumption
            · right
              right
              left
              rcases h'' with ⟨j1, j2, c, r1, r2, eq⟩
              have : j1 < i ∧ j2 < i ∧ c < i ∧ r1 < i ∧ r2 < i ∧ f j ∈ line (f j1) (f j2) ∩ circunference (f c) (distance (f r1) (f r2)) := by
                have jlti : j < i := by
                  apply Nat.lt_of_lt_of_le jltn inltn
                constructor
                · apply lt_trans eq.1 jlti
                · constructor
                  · apply lt_trans eq.2.1 jlti
                  · constructor
                    · apply lt_trans eq.2.2.1 jlti
                    · constructor
                      · apply lt_trans eq.2.2.2.1 jlti
                      · constructor
                        · apply lt_trans eq.2.2.2.2.1 jlti
                        · apply eq.2.2.2.2.2
              use j1, j2, c, r1, r2
              rw [zero_comp_more f g n i inltn, geqf,
                  zero_comp_less f g n j1 (by apply lt_trans eq.1 jltn),
                  zero_comp_less f g n j2 (by apply lt_trans eq.2.1 jltn),
                  zero_comp_less f g n c (by apply lt_trans eq.2.2.1 jltn),
                  zero_comp_less f g n r1 (by apply lt_trans eq.2.2.2.1 jltn),
                  zero_comp_less f g n r2 (by apply lt_trans eq.2.2.2.2.1 jltn)]
              assumption
            · right
              right
              right
              rcases h'' with ⟨c1, c2, r1, r2, s1, s2, eq⟩
              have : c1 < i ∧ c2 < i ∧ r1 < i ∧ r2 < i ∧ s1 < i ∧ s2 < i ∧ (f c1 ≠ f c2 ∨ distance (f r1) (f r2) ≠ distance (f s1) (f s2)) ∧
                     f j ∈ circunference (f c1) (distance (f r1) (f r2)) ∩ circunference (f c2) (distance (f s1) (f s2)) := by
                have jlti : j < i := by
                  apply Nat.lt_of_lt_of_le jltn inltn
                constructor
                · apply lt_trans eq.1 jlti
                · constructor
                  · apply lt_trans eq.2.1 jlti
                  · constructor
                    · apply lt_trans eq.2.2.1 jlti
                    · constructor
                      · apply lt_trans eq.2.2.2.1 jlti
                      · constructor
                        · apply lt_trans eq.2.2.2.2.1 jlti
                        · constructor
                          · apply lt_trans eq.2.2.2.2.2.1 jlti
                          · apply eq.2.2.2.2.2.2
              use c1, c2, r1, r2, s1, s2
              rw [zero_comp_more f g n i inltn, geqf,
                  zero_comp_less f g n c1 (by apply lt_trans eq.1 jltn),
                  zero_comp_less f g n c2 (by apply lt_trans eq.2.1 jltn),
                  zero_comp_less f g n r1 (by apply lt_trans eq.2.2.1 jltn),
                  zero_comp_less f g n r2 (by apply lt_trans eq.2.2.2.1 jltn),
                  zero_comp_less f g n s1 (by apply lt_trans eq.2.2.2.2.1 jltn),
                  zero_comp_less f g n s2 (by apply lt_trans eq.2.2.2.2.2.1 jltn)]
              assumption
          · right
            left
            rcases h' with ⟨j1, j2, k1, k2, eq⟩
            use j1 + n, j2 + n, k1 + n, k2 + n
            rw [zero_comp_more f g n i inltn,
                zero_comp_more f g n (j1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (j2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (k1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (k2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel]
            rw [Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt ,Nat.lt_sub_iff_add_lt] at eq
            assumption
          · right
            right
            left
            rcases h' with ⟨j1, j2, c, r1, r2, eq⟩
            use j1 + n, j2 + n, c + n, r1 + n, r2 + n
            rw [zero_comp_more f g n i inltn,
                zero_comp_more f g n (j1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (j2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (c + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (r1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (r2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel]
            rw [Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt ,Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt] at eq
            assumption
          · right
            right
            right
            rcases h' with ⟨c1, c2, r1, r2, s1, s2, eq⟩
            use c1 + n, c2 + n, r1 + n, r2 + n, s1 + n, s2 + n
            rw [zero_comp_more f g n i inltn,
                zero_comp_more f g n (c1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (c2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (r1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (r2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (s1 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel,
                zero_comp_more f g n (s2 + n) (by apply Nat.le_add_left), Nat.add_sub_cancel]
            rw [Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt ,Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt, Nat.lt_sub_iff_add_lt] at eq
            assumption


theorem line_line_intersection {P Q R S: ℝ × ℝ} (h: line P Q ≠ line R S):
P ∈ constructible_set → Q ∈ constructible_set →  R ∈ constructible_set → S ∈ constructible_set → ∀ T ∈ (line P Q ∩ line R S), T ∈ constructible_set := by
  intro P_cons Q_cons R_cons S_cons T Tininter
  dsimp [constructible_set, constructible_point] at P_cons Q_cons R_cons S_cons
  dsimp [constructible_set]
  rcases P_cons with ⟨nP, fP, Pconds⟩
  rcases Q_cons with ⟨nQ, fQ, Qconds⟩
  rcases R_cons with ⟨nR, fR, Rconds⟩
  rcases S_cons with ⟨nS, fS, Sconds⟩
  let fPQ := zero_comp fP fQ nP
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ) fPQ := add_construction {(0, 0), (1, 0)} nP nQ fP fQ Pconds.2 Qconds.2
  let fPQR := zero_comp fPQ fR (nP + nQ)
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR) fPQR := add_construction {(0, 0), (1, 0)} (nP + nQ) nR fPQ fR this Rconds.2
  let fPQRS := zero_comp fPQR fS (nP + nQ + nR)
  have fPQRS_cons : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR + nS) fPQRS := add_construction {(0, 0), (1, 0)} (nP + nQ + nR) nS fPQR fS this Sconds.2
  have atP : fPQRS (nP - 1) = P := by
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQR]
    rw [zero_comp_less fPQ fR (nP + nQ) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQ]
    rw [zero_comp_less fP fQ nP (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    exact Pconds.1.symm
  have atQ : fPQRS (nP + nQ - 1) = Q := by
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQR]
    rw [zero_comp_less fPQ fR (nP + nQ) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQ]
    rw [zero_comp_more fP fQ nP (nP + nQ - 1) (by rw [Nat.add_sub_assoc]; apply Nat.le_add_right nP (nQ - 1); exact Qconds.2.1)]
    rw [Nat.sub_sub, add_comm 1 nP, ← Nat.sub_sub]
    simp
    exact Qconds.1.symm
  have atR : fPQRS (nP + nQ +nR - 1) = R := by
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP + nQ + nR - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQR]
    rw [zero_comp_more fPQ fR (nP + nQ) (nP + nQ + nR - 1) (by rw [Nat.add_sub_assoc Rconds.2.1]; apply Nat.le_add_right)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Rconds.1.symm
  have atS : fPQRS (nP + nQ + nR + nS - 1) = S := by
    dsimp [fPQRS]
    rw [zero_comp_more fPQR fS (nP + nQ + nR) (nP + nQ + nR + nS - 1) (by rw [Nat.add_sub_assoc Sconds.2.1]; apply Nat.le_add_right)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Sconds.1.symm
  let G : ℕ → ℝ × ℝ := fun k ↦ partial_fun k (fun n ↦ n = 0) P
                                (partial_fun k (fun n ↦ n = 1) Q
                                (partial_fun k (fun n ↦ n = 2) R
                                (partial_fun k (fun n ↦ n = 3) S T)))
  have G0 : G 0 = P := by
    dsimp [G]
    rw [eval_pos 0 (fun n => n = 0) (by rfl)]
  have G1 : G 1 = Q := by
    dsimp [G]
    rw [eval_neg 1 (fun n => n = 0) (by simp),
        eval_pos 1 (fun n => n = 1) (by rfl)]
  have G2 : G 2 = R := by
    dsimp [G]
    rw [eval_neg 2 (fun n => n = 0) (by simp),
        eval_neg 2 (fun n => n = 1) (by simp),
        eval_pos 2 (fun n => n = 2) (by rfl)]
  have G3 : G 3 = S := by
    dsimp [G]
    rw [eval_neg 3 (fun n => n = 0) (by simp),
        eval_neg 3 (fun n => n = 1) (by simp),
        eval_neg 3 (fun n => n = 2) (by simp),
        eval_pos 3 (fun n => n = 3) (by rfl)]
  have G4 : G 4 = T := by
    dsimp [G]
    rw [eval_neg 4 (fun n => n = 0) (by simp),
        eval_neg 4 (fun n => n = 1) (by simp),
        eval_neg 4 (fun n => n = 2) (by simp),
        eval_neg 4 (fun n => n = 3) (by simp)]
  apply add_construction' {(0, 0), (1, 0)} T fPQRS_cons
  use 5, G
  constructor
  · simp
    exact G4.symm
  · dsimp [IsConstruction]
    constructor
    · linarith
    · intro i ilt5
      -- Mejor usar "interval_cases i" (también tener en cuenta para el futuro "fin_cases")
      rw [coso 5 (by linarith)] at ilt5
      dsimp [ORn] at ilt5
      rcases ilt5 with h' | h' | h' | h' | h'
      · rw [h', G0]
        left
        use nP - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          exact Pconds.2.1
        · rw [atP]
      · rw [h', G1]
        left
        use nP + nQ - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          apply le_trans Pconds.2.1 (Nat.le_add_right nP nQ)
        · rw [atQ]
      · rw [h', G2]
        left
        use nP + nQ + nR - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atR]
      · rw [h', G3]
        left
        use nP + nQ + nR + nS - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc, add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atS]
      · right
        left
        rw [h']
        use 0, 1, 2, 3
        constructor
        · linarith
        · constructor
          · linarith
          · constructor
            · linarith
            · constructor
              · linarith
              · rw [G0, G1, G2, G3, G4]
                exact And.intro h Tininter

theorem line_circunference_intersection {P Q R S T: ℝ × ℝ}: P ∈ constructible_set →
  Q ∈ constructible_set →  R ∈ constructible_set → S ∈ constructible_set →
  T ∈ constructible_set → ∀ U ∈ (line P Q ∩ circunference R (distance S T)), U ∈ constructible_set := by
  intro P_cons Q_cons R_cons S_cons T_cons U Uininter
  dsimp [constructible_set, constructible_point] at P_cons Q_cons R_cons S_cons T_cons
  dsimp [constructible_set]
  rcases P_cons with ⟨nP, fP, Pconds⟩
  rcases Q_cons with ⟨nQ, fQ, Qconds⟩
  rcases R_cons with ⟨nR, fR, Rconds⟩
  rcases S_cons with ⟨nS, fS, Sconds⟩
  rcases T_cons with ⟨nT, fT, Tconds⟩
  let fPQ := zero_comp fP fQ nP
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ) fPQ := add_construction {(0, 0), (1, 0)} nP nQ fP fQ Pconds.2 Qconds.2
  let fPQR := zero_comp fPQ fR (nP + nQ)
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR) fPQR := add_construction {(0, 0), (1, 0)} (nP + nQ) nR fPQ fR this Rconds.2
  let fPQRS := zero_comp fPQR fS (nP + nQ + nR)
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR + nS) fPQRS := add_construction {(0, 0), (1, 0)} (nP + nQ + nR) nS fPQR fS this Sconds.2
  let fPQRST := zero_comp fPQRS fT (nP + nQ + nR + nS)
  have fPQRST_iscons : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR + nS + nT) fPQRST := add_construction {(0, 0), (1, 0)} (nP + nQ + nR + nS) nT fPQRS fT this Tconds.2
  have atP : fPQRST (nP - 1) = P := by
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQR]
    rw [zero_comp_less fPQ fR (nP + nQ) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQ]
    rw [zero_comp_less fP fQ nP (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    exact Pconds.1.symm
  have atQ : fPQRST (nP + nQ - 1) = Q := by
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQR]
    rw [zero_comp_less fPQ fR (nP + nQ) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQ]
    rw [zero_comp_more fP fQ nP (nP + nQ - 1) (by rw [Nat.add_sub_assoc]; apply Nat.le_add_right nP (nQ - 1); exact Qconds.2.1)]
    rw [Nat.sub_sub, add_comm 1 nP, ← Nat.sub_sub]
    simp
    exact Qconds.1.symm
  have atR : fPQRST (nP + nQ + nR - 1) = R := by
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP + nQ + nR - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP + nQ + nR - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQR]
    rw [zero_comp_more fPQ fR (nP + nQ) (nP + nQ + nR - 1) (by rw [Nat.add_sub_assoc Rconds.2.1]; apply Nat.le_add_right)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Rconds.1.symm
  have atS : fPQRST (nP + nQ + nR + nS - 1) = S := by
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP + nQ + nR + nS - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc, add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRS]
    rw [zero_comp_more fPQR fS (nP + nQ + nR) (nP + nQ + nR + nS - 1) (by rw [Nat.add_sub_assoc Sconds.2.1]; apply Nat.le_add_right)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Sconds.1.symm
  have atT : fPQRST (nP + nQ + nR + nS + nT - 1) = T := by
    dsimp [fPQRST]
    rw [zero_comp_more fPQRS fT (nP + nQ + nR + nS) (nP + nQ + nR + nS + nT - 1)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Tconds.1.symm
    rw [add_assoc, add_assoc]
    apply Nat.le_sub_one_of_lt
    norm_num
    apply lt_of_lt_of_le Nat.zero_lt_one Tconds.2.1
  let G : ℕ → ℝ × ℝ := fun k ↦ partial_fun k (fun n ↦ n = 0) P
                                (partial_fun k (fun n ↦ n = 1) Q
                                (partial_fun k (fun n ↦ n = 2) R
                                (partial_fun k (fun n ↦ n = 3) S
                                (partial_fun k (fun n ↦ n = 4) T U))))
  have G0 : G 0 = P := by
    dsimp [G]
    rw [eval_pos 0 (fun n => n = 0) (by rfl)]
  have G1 : G 1 = Q := by
    dsimp [G]
    rw [eval_neg 1 (fun n => n = 0) (by simp),
        eval_pos 1 (fun n => n = 1) (by rfl)]
  have G2 : G 2 = R := by
    dsimp [G]
    rw [eval_neg 2 (fun n => n = 0) (by simp),
        eval_neg 2 (fun n => n = 1) (by simp),
        eval_pos 2 (fun n => n = 2) (by rfl)]
  have G3 : G 3 = S := by
    dsimp [G]
    rw [eval_neg 3 (fun n => n = 0) (by simp),
        eval_neg 3 (fun n => n = 1) (by simp),
        eval_neg 3 (fun n => n = 2) (by simp),
        eval_pos 3 (fun n => n = 3) (by rfl)]
  have G4 : G 4 = T := by
    dsimp [G]
    rw [eval_neg 4 (fun n => n = 0) (by simp),
        eval_neg 4 (fun n => n = 1) (by simp),
        eval_neg 4 (fun n => n = 2) (by simp),
        eval_neg 4 (fun n => n = 3) (by simp),
        eval_pos 4 (fun n => n = 4) (by rfl)]
  have G5 : G 5 = U := by
    dsimp [G]
    rw [eval_neg 5 (fun n => n = 0) (by simp),
        eval_neg 5 (fun n => n = 1) (by simp),
        eval_neg 5 (fun n => n = 2) (by simp),
        eval_neg 5 (fun n => n = 3) (by simp),
        eval_neg 5 (fun n => n = 4) (by simp)]
  apply add_construction' {(0, 0), (1, 0)} U fPQRST_iscons
  use 6, G
  constructor
  · simp
    exact G5.symm
  · dsimp [IsConstruction]
    constructor
    · linarith
    · intro i ilt6
      rw [coso 6 (by linarith)] at ilt6
      dsimp [ORn] at ilt6
      rcases ilt6 with h' | h' | h' | h' | h' | h'
      · rw [h', G0]
        left
        use nP - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          exact Pconds.2.1
        · rw [atP]
      · rw [h', G1]
        left
        use nP + nQ - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          apply le_trans Pconds.2.1 (Nat.le_add_right nP nQ)
        · rw [atQ]
      · rw [h', G2]
        left
        use nP + nQ + nR - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atR]
      · rw [h', G3]
        left
        use nP + nQ + nR + nS - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc, add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atS]
      · rw [h', G4]
        left
        use nP + nQ + nR + nS + nT - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc, add_assoc, add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atT]
      · right
        right
        left
        rw [h']
        use 0, 1, 2, 3, 4
        constructor
        · linarith
        · constructor
          · linarith
          · constructor
            · linarith
            · constructor
              · linarith
              · constructor
                · linarith
                · rw [G0, G1, G2, G3, G4, G5]
                  exact Uininter

theorem circunference_circunference_intersection {P Q R S T U: ℝ × ℝ} (h: P ≠ Q ∨ distance R S ≠ distance T U):
  P ∈ constructible_set → Q ∈ constructible_set →  R ∈ constructible_set → S ∈ constructible_set →
  T ∈ constructible_set → U ∈ constructible_set → ∀ V ∈ (circunference P (distance R S) ∩ circunference Q (distance T U)), V ∈ constructible_set := by
  intro P_cons Q_cons R_cons S_cons T_cons U_cons V Vininter
  dsimp [constructible_set, constructible_point] at P_cons Q_cons R_cons S_cons T_cons U_cons
  dsimp [constructible_set]
  rcases P_cons with ⟨nP, fP, Pconds⟩
  rcases Q_cons with ⟨nQ, fQ, Qconds⟩
  rcases R_cons with ⟨nR, fR, Rconds⟩
  rcases S_cons with ⟨nS, fS, Sconds⟩
  rcases T_cons with ⟨nT, fT, Tconds⟩
  rcases U_cons with ⟨nU, fU, Uconds⟩
  let fPQ := zero_comp fP fQ nP
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ) fPQ := add_construction {(0, 0), (1, 0)} nP nQ fP fQ Pconds.2 Qconds.2
  let fPQR := zero_comp fPQ fR (nP + nQ)
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR) fPQR := add_construction {(0, 0), (1, 0)} (nP + nQ) nR fPQ fR this Rconds.2
  let fPQRS := zero_comp fPQR fS (nP + nQ + nR)
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR + nS) fPQRS := add_construction {(0, 0), (1, 0)} (nP + nQ + nR) nS fPQR fS this Sconds.2
  let fPQRST := zero_comp fPQRS fT (nP + nQ + nR + nS)
  have : IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR + nS + nT) fPQRST := add_construction {(0, 0), (1, 0)} (nP + nQ + nR + nS) nT fPQRS fT this Tconds.2
  let f := zero_comp fPQRST fU (nP + nQ + nR + nS + nT)
  have f_cons: IsConstruction {(0, 0), (1, 0)} (nP + nQ + nR + nS + nT + nU) f := add_construction {(0, 0), (1, 0)} (nP + nQ + nR + nS + nT) nU fPQRST fU this Uconds.2
  have atP : f (nP - 1) = P := by
    dsimp [f]
    rw [zero_comp_less fPQRST fU (nP + nQ + nR + nS + nT) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQR]
    rw [zero_comp_less fPQ fR (nP + nQ) (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    dsimp [fPQ]
    rw [zero_comp_less fP fQ nP (nP - 1) (by rw [Nat.sub_lt_iff_lt_add Pconds.2.1]; linarith)]
    exact Pconds.1.symm
  have atQ : f (nP + nQ - 1) = Q := by
    dsimp [f]
    rw [zero_comp_less fPQRST fU (nP + nQ + nR + nS + nT) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQR]
    rw [zero_comp_less fPQ fR (nP + nQ) (nP + nQ - 1) (by rw [Nat.sub_lt_iff_lt_add (le_trans Pconds.2.1 (Nat.le_add_right nP nQ))]; linarith)]
    dsimp [fPQ]
    rw [zero_comp_more fP fQ nP (nP + nQ - 1) (by rw [Nat.add_sub_assoc]; apply Nat.le_add_right nP (nQ - 1); exact Qconds.2.1)]
    rw [Nat.sub_sub, add_comm 1 nP, ← Nat.sub_sub]
    simp
    exact Qconds.1.symm
  have atR : f (nP + nQ + nR - 1) = R := by
    dsimp [f]
    rw [zero_comp_less fPQRST fU (nP + nQ + nR + nS + nT) (nP + nQ + nR - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP + nQ + nR - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRS]
    rw [zero_comp_less fPQR fS (nP + nQ + nR) (nP + nQ + nR - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQR]
    rw [zero_comp_more fPQ fR (nP + nQ) (nP + nQ + nR - 1) (by rw [Nat.add_sub_assoc Rconds.2.1]; apply Nat.le_add_right)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Rconds.1.symm
  have atS : f (nP + nQ + nR + nS - 1) = S := by
    dsimp [f]
    rw [zero_comp_less fPQRST fU (nP + nQ + nR + nS + nT) (nP + nQ + nR + nS - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc, add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRST]
    rw [zero_comp_less fPQRS fT (nP + nQ + nR + nS) (nP + nQ + nR + nS - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc, add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRS]
    rw [zero_comp_more fPQR fS (nP + nQ + nR) (nP + nQ + nR + nS - 1) (by rw [Nat.add_sub_assoc Sconds.2.1]; apply Nat.le_add_right)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Sconds.1.symm
  have atT : f (nP + nQ + nR + nS + nT - 1) = T := by
    dsimp [f]
    rw [zero_comp_less fPQRST fU (nP + nQ + nR + nS + nT) (nP + nQ + nR + nS + nT - 1) (by rw [Nat.sub_lt_iff_lt_add]; linarith; rw [add_assoc, add_assoc, add_assoc]; apply le_trans Pconds.2.1 (Nat.le_add_right nP _))]
    dsimp [fPQRST]
    rw [zero_comp_more fPQRS fT (nP + nQ + nR + nS) (nP + nQ + nR + nS + nT - 1)]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    exact Tconds.1.symm
    rw [add_assoc, add_assoc]
    apply Nat.le_sub_one_of_lt
    norm_num
    apply lt_of_lt_of_le Nat.zero_lt_one Tconds.2.1
  have atU : f (nP + nQ + nR + nS + nT + nU - 1) = U := by
    dsimp [f]
    rw [zero_comp_more]
    rw [Nat.sub_sub, add_comm 1 _, ← Nat.sub_sub]
    simp
    · exact Uconds.1.symm
    · rw [add_assoc, add_assoc, add_assoc]
      apply Nat.le_sub_one_of_lt
      norm_num
      apply Uconds.2.1
  let G : ℕ → ℝ × ℝ := fun k ↦ partial_fun k (fun n ↦ n = 0) P
                                (partial_fun k (fun n ↦ n = 1) Q
                                (partial_fun k (fun n ↦ n = 2) R
                                (partial_fun k (fun n ↦ n = 3) S
                                (partial_fun k (fun n ↦ n = 4) T
                                (partial_fun k (fun n ↦ n = 5) U V)))))
  have G0 : G 0 = P := by
    dsimp [G]
    rw [eval_pos 0 (fun n => n = 0) (by rfl)]
  have G1 : G 1 = Q := by
    dsimp [G]
    rw [eval_neg 1 (fun n => n = 0) (by simp),
        eval_pos 1 (fun n => n = 1) (by rfl)]
  have G2 : G 2 = R := by
    dsimp [G]
    rw [eval_neg 2 (fun n => n = 0) (by simp),
        eval_neg 2 (fun n => n = 1) (by simp),
        eval_pos 2 (fun n => n = 2) (by rfl)]
  have G3 : G 3 = S := by
    dsimp [G]
    rw [eval_neg 3 (fun n => n = 0) (by simp),
        eval_neg 3 (fun n => n = 1) (by simp),
        eval_neg 3 (fun n => n = 2) (by simp),
        eval_pos 3 (fun n => n = 3) (by rfl)]
  have G4 : G 4 = T := by
    dsimp [G]
    rw [eval_neg 4 (fun n => n = 0) (by simp),
        eval_neg 4 (fun n => n = 1) (by simp),
        eval_neg 4 (fun n => n = 2) (by simp),
        eval_neg 4 (fun n => n = 3) (by simp),
        eval_pos 4 (fun n => n = 4) (by rfl)]
  have G5 : G 5 = U := by
    dsimp [G]
    rw [eval_neg 5 (fun n => n = 0) (by simp),
        eval_neg 5 (fun n => n = 1) (by simp),
        eval_neg 5 (fun n => n = 2) (by simp),
        eval_neg 5 (fun n => n = 3) (by simp),
        eval_neg 5 (fun n => n = 4) (by simp),
        eval_pos 5 (fun n => n = 5) (by rfl)]
  have G6 : G 6 = V := by
    dsimp [G]
    rw [eval_neg 6 (fun n => n = 0) (by simp),
        eval_neg 6 (fun n => n = 1) (by simp),
        eval_neg 6 (fun n => n = 2) (by simp),
        eval_neg 6 (fun n => n = 3) (by simp),
        eval_neg 6 (fun n => n = 4) (by simp),
        eval_neg 6 (fun n => n = 5) (by simp)]
  apply add_construction' {(0, 0), (1, 0)} V f_cons
  use 7, G
  constructor
  · simp
    exact G6.symm
  · dsimp [IsConstruction]
    constructor
    · linarith
    · intro i ilt7
      rw [coso 7 (by linarith)] at ilt7
      dsimp [ORn] at ilt7
      rcases ilt7 with h' | h' | h' | h' | h' | h' | h'
      · rw [h', G0]
        left
        use nP - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          exact Pconds.2.1
        · rw [atP]
      · rw [h', G1]
        left
        use nP + nQ - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          apply le_trans Pconds.2.1 (Nat.le_add_right nP nQ)
        · rw [atQ]
      · rw [h', G2]
        left
        use nP + nQ + nR - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atR]
      · rw [h', G3]
        left
        use nP + nQ + nR + nS - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc, add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atS]
      · rw [h', G4]
        left
        use nP + nQ + nR + nS + nT - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc, add_assoc, add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atT]
      · rw [h', G5]
        left
        use nP + nQ + nR + nS + nT + nU - 1
        constructor
        · rw [Nat.sub_lt_iff_lt_add]
          linarith
          rw [add_assoc, add_assoc, add_assoc, add_assoc]
          apply le_trans Pconds.2.1 (Nat.le_add_right nP _)
        · rw [atU]
      · right
        right
        right
        rw [h']
        use 0, 1, 2, 3, 4, 5
        constructor
        · linarith
        · constructor
          · linarith
          · constructor
            · linarith
            · constructor
              · linarith
              · constructor
                · linarith
                · constructor
                  · linarith
                  · rw [G0, G1, G2, G3, G4, G5, G6]
                    exact And.intro h Vininter


def basic_construction : ℕ → ℝ × ℝ := fun n ↦ partial_fun n (fun k ↦ k = 0) (0, 0) (1, 0)

lemma basic_construction_is_construction : IsConstruction {(0, 0), (1, 0)} 2 basic_construction := by
  dsimp [IsConstruction]
  constructor
  · linarith
  · intro i ilt2
    left
    dsimp[basic_construction]
    rcases Classical.em (i = 0) with iz | inz
    · rw [eval_pos i (fun k => k = 0) iz]
      simp
    · rw [eval_neg i (fun k => k = 0) inz]
      simp

def add_basic_construction (f: ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ := zero_comp basic_construction f 2

lemma add_basic_construction_isConstruction (f: ℕ → ℝ × ℝ) : IsConstruction {(0, 0), (1, 0)} n f → IsConstruction {(0, 0), (1, 0)} (n + 2) (add_basic_construction f) := by
  intro h
  dsimp [add_basic_construction]
  rw [add_comm]
  exact add_construction {(0, 0), (1, 0)} 2 n basic_construction f basic_construction_is_construction h

theorem zero_constructible : 0 ∈ constructible_real_set := by
  dsimp [constructible_real_set, constructible_set]
  use 2, fun m ↦ (0,0)
  constructor
  · rfl
  · constructor
    · linarith
    · intro i ile1
      left
      simp

theorem one_constructible : 1 ∈ constructible_real_set := by
  dsimp [constructible_real_set, constructible_set]
  push_cast
  use 2, fun m ↦ (1,0)
  constructor
  · rfl
  · constructor
    · linarith
    · intro i ile1
      left
      simp

def IsPerp (P Q R S : ℝ × ℝ) := (Q - P).1 * (S - R).1 + (Q - P).2 * (S - R).2 = 0

theorem open_compass (P Q R : ℝ × ℝ) : P ∈ constructible_set → Q ∈ constructible_set →
   R ∈ constructible_set → ∀ (n : ℕ), ∃ S T : ℝ × ℝ, (S ∈ constructible_set ∧ T ∈ constructible_set ∧
   S ∈ line P Q ∧ T ∈ line P Q ∧ n < distance R S ∧ distance R S = distance R T) := by
    intro P_cons Q_cons R_cons n
    sorry

theorem constructible_add (x y : ℝ) : x ∈ constructible_real_set → y ∈ constructible_real_set → (x + y) ∈ constructible_real_set := by
  intro x_const y_const
  have zero_const := zero_constructible
  have one_const := one_constructible
  dsimp [constructible_real_set] at *
  apply line_circunference_intersection zero_const one_const x_const zero_const y_const
  constructor
  · dsimp [line]
    use x + y
    simp
  · dsimp [distance, circunference]
    simp

theorem constructible_neg (x : ℝ) : x ∈ constructible_real_set → -x ∈ constructible_real_set := by
  intro x_const
  have zero_const := zero_constructible
  have one_const := one_constructible
  dsimp [constructible_real_set] at *
  apply line_circunference_intersection zero_const one_const zero_const zero_const x_const
  constructor
  · dsimp [line]
    use -x
    simp
  · dsimp [distance, circunference]
    simp

theorem ver_constructible : x ∈ constructible_real_set → (0, x) ∈ constructible_set := by
  intro x_const
  have zero_const := zero_constructible
  have one_const := one_constructible
  have mone_const := constructible_neg 1 one_const
  dsimp [constructible_real_set] at *
  have : (0, √3) ∈ constructible_set := by
    apply circunference_circunference_intersection _ one_const mone_const one_const mone_const one_const mone_const
    · dsimp [distance, circunference]
      simp
      norm_num
      rw [sqrt_eq_iff_mul_self_eq]
      · norm_num
      · linarith
      · linarith
    · left
      simp
  apply line_circunference_intersection zero_const this zero_const zero_const x_const
  dsimp [line, distance, circunference]
  simp
  use x / √3
  rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel (by norm_num), mul_one]

theorem constructible_prod (x y : ℝ) : x ∈ constructible_real_set → y ∈ constructible_real_set → (x * y) ∈ constructible_real_set := by
  intro x_const y_const
  have zero_const := zero_constructible
  have one_const := one_constructible
  have mone_const := constructible_neg 1 one_const
  dsimp [constructible_real_set] at *
  have zy_const := ver_constructible y_const
  sorry


theorem Nat_constructible : ∀ (n : ℕ), Nat.cast n ∈ constructible_real_set := by
  intro n
  induction' n with n ih
  · push_cast
    exact zero_constructible
  · push_cast
    apply constructible_add n 1 ih
    exact one_constructible

theorem Int_construtible : ∀ (n : ℤ), Int.cast n ∈ constructible_real_set := by
  intro n
  induction' n with n n
  · have : (Int.ofNat n : ℝ) = (n : ℝ) := by
      rfl
    rw [this]
    exact Nat_constructible n
  · have : (Int.negSucc n : ℝ) = (- (n + 1) : ℝ) := by
      rw [Int.negSucc_coe]
      push_cast
      rfl
    rw [this]
    have : Nat.cast n + 1 ∈ constructible_real_set := by
      apply constructible_add
      · exact Nat_constructible n
      · exact one_constructible
    apply constructible_neg
    assumption
