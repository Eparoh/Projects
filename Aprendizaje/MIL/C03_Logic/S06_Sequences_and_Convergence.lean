import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  dsimp
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
      congr
      linarith
    _ ≤ |s n - a| + |t n - b| := by
      apply abs_add
    _ < ε/2 + ε/2 := by
      have ns: Ns ≤ n := by
        calc
          Ns ≤ max Ns Nt := by
            apply le_max_left Ns
          _ ≤ n := by
            apply hn
      have ineq1:= hs n ns
      have nt: Nt ≤ n := by
        calc
          Nt ≤ max Ns Nt := by
            apply le_max_right Ns
          _ ≤ n := by
            apply hn
      have ineq2:= ht n nt
      apply add_lt_add ineq1 ineq2
    _ = ε := by
      linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  rcases em (c=0) with h|h
  · convert convergesTo_const 0
    · rw [h]
      ring
    · rw [h]
      ring
  · have acpos : 0 < |c| := abs_pos.mpr h
    dsimp [ConvergesTo]
    dsimp [ConvergesTo] at cs
    intro ε posε
    have posεc : ε / |c| > 0 := by
      norm_num [acpos, posε]
    let εc :=  ε / |c|
    rcases cs εc posεc with ⟨N, Na⟩
    use N
    intro n hn
    calc
      |c * s n - c * a| = |c| * |s n - a| := by
        rw [← mul_sub, abs_mul]
      _ < |c| * εc := by
        apply mul_lt_mul_of_pos_left _ acpos
        exact Na n hn
      _ = ε := by
        dsimp [εc]
        apply mul_div_cancel₀ ε
        apply (ne_of_lt acpos).symm

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n Nn
  calc
    |s n| = |a + (s n -a)| := by
      congr
      ring
    _ ≤ |a| + |s n - a| := by
      apply abs_add
    _ < |a| + 1 := by
      apply add_lt_add_of_le_of_lt (le_refl (|a|))
      exact h n Nn

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  let N:= max N₀ N₁
  use N
  intro n nN
  calc
    |s n * t n - 0| = |s n * t n| := by
      rw [sub_zero]
    _ = |s n| * |t n| := by
      apply abs_mul
    _ < B * (ε/B) := by
      apply mul_lt_mul''
      · apply h₀ n
        apply le_trans _ nN
        apply le_max_left
      · rw [← sub_zero (t n)]
        apply h₁ n
        apply le_trans _ nN
        apply le_max_right
      · apply abs_nonneg
      · apply abs_nonneg
    _ = ε := by
      apply mul_div_cancel₀
      apply Ne.symm
      apply ne_of_lt Bpos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    --have: ConvergesTo (fun n => t n + -b) (b + -b) := by
    --  apply convergesTo_add ct (convergesTo_const (-b))
    --rw [add_right_neg b] at this
    --exact this
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  --have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  --rw [zero_add, mul_comm] at this
  --have h₂: (fun n => s n * (t n + -b) + b * s n) = fun n => s n * t n := by
  --  ext n
  --  ring
  --rw [h₂] at this
  --exact this
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  · ring

-- Lemas para lo siguiente

lemma reverse_lt: ∀ (a b : ℝ), a < b ↔ b > a := by
  intro a b
  constructor
  repeat
  · intro h
    apply h

lemma lt_iff_lt_neg: ∀ (a b : ℝ), a < b ↔ -b < -a := by
  intro a b
  constructor
  repeat
  · intro h
    linarith

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    rw [← reverse_lt, lt_abs, lt_iff_lt_neg 0 (-(a-b)), neg_neg, neg_zero]
    rcases lt_trichotomy (a - b) 0 with h|h|h
    · right; apply h
    · rw [sub_eq_zero] at h; contradiction
    · left; apply h
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have : Na ≤ N := by
      change Na ≤ max Na Nb
      apply le_max_left
    apply hNa N this
  have absb : |s N - b| < ε := by
    have : Nb ≤ N := by
      change Nb ≤ max Na Nb
      apply le_max_right
    apply hNb N this
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(a - s N) + (s N - b)| := by
        congr
        ring
      _ ≤ |a - s N| + |s N - b| := by
        apply abs_add
      _ = |s N - a| + |s N - b| := by
        rw [← abs_neg, neg_sub]
      _ < ε + ε := by
        apply add_lt_add absa absb
      _ = |a - b| := by
        change |a - b| / 2 + |a - b| / 2 = |a - b|
        linarith
  exact lt_irrefl _ this

-- Mi intento :)

theorem convergesTo_unique_ {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
    by_contra aneqb
    dsimp [ConvergesTo] at sa
    dsimp [ConvergesTo] at sb
    have hposε : 0 < |b-a|/2  := by
      have aux : (0: ℝ) < (2: ℝ) := by
        norm_num
      rw [lt_div_iff' aux, mul_zero, lt_iff_le_and_ne]
      constructor
      · apply abs_nonneg
      · by_contra h
        have h':= Eq.symm h
        rw [abs_eq_zero, sub_eq_zero] at h'
        have h'':= Eq.symm h'
        apply aneqb h''
    rcases sa (|b-a|/2) hposε with ⟨Na, ha⟩
    rcases sb (|b-a|/2) hposε with ⟨Nb, hb⟩
    have ha_ := ha (max Na Nb) (le_max_left Na Nb)
    have hb_ := hb (max Na Nb) (le_max_right Na Nb)
    rw [abs_lt] at ha_
    rw [abs_lt] at hb_
    rcases lt_trichotomy a b with h1|h1|h1
    · rw [← sub_lt_zero] at h1
      have h1': 0 ≤  b-a := by
        linarith
      rw [abs_of_nonneg h1'] at ha_
      rw [abs_of_nonneg h1'] at hb_
      have aux_a : s (max Na Nb) < (b+a)/2 := by
        have := ha_.right
        linarith
      have aux_b : (b+a)/2 < s (max Na Nb) := by
        have := hb_.left
        linarith
      have por_fin : (b+a)/2 < (b+a)/2 := by
        apply lt_trans  aux_b aux_a
      apply lt_irrefl ((b+a)/2) por_fin
    · contradiction
    · rw [← sub_lt_zero] at h1
      rw [abs_of_neg h1] at ha_
      rw [abs_of_neg h1] at hb_
      have aux_a : (b+a)/2 < s (max Na Nb) := by
        have := ha_.left
        linarith
      have aux_b : s (max Na Nb) < (b+a)/2 := by
        have := hb_.right
        linarith
      have por_fin : (b+a)/2 < (b+a)/2 := by
        apply lt_trans  aux_a aux_b
      apply lt_irrefl ((b+a)/2) por_fin

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const' (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  dsimp
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add' {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
      congr
      linarith
    _ ≤ |s n - a| + |t n - b| := by
      apply abs_add
    _ < ε/2 + ε/2 := by
      have ns: Ns ≤ n := by
        calc
          Ns ≤ max Ns Nt := by
            apply le_max_left Ns
          _ ≤ n := by
            apply hn
      have ineq1:= hs n ns
      have nt: Nt ≤ n := by
        calc
          Nt ≤ max Ns Nt := by
            apply le_max_right Ns
          _ ≤ n := by
            apply hn
      have ineq2:= ht n nt
      apply add_lt_add ineq1 ineq2
    _ = ε := by
      linarith

theorem convergesTo_mul_const' {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  rcases em (c=0) with h|h
  · convert convergesTo_const 0
    · rw [h]
      ring
    · rw [h]
      ring
  · have acpos : 0 < |c| := abs_pos.mpr h
    dsimp [ConvergesTo]
    dsimp [ConvergesTo] at cs
    intro ε posε
    have posεc : ε / |c| > 0 := by
      norm_num [acpos, posε]
    let εc :=  ε / |c|
    rcases cs εc posεc with ⟨N, Na⟩
    use N
    intro n hn
    calc
      |c * s n - c * a| = |c| * |s n - a| := by
        rw [← mul_sub, abs_mul]
      _ < |c| * εc := by
        apply mul_lt_mul_of_pos_left _ acpos
        exact Na n hn
      _ = ε := by
        dsimp [εc]
        apply mul_div_cancel₀ ε
        apply (ne_of_lt acpos).symm

theorem exists_abs_le_of_convergesTo' {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n Nn
  calc
    |s n| = |a + (s n -a)| := by
      congr
      ring
    _ ≤ |a| + |s n - a| := by
      apply abs_add
    _ < |a| + 1 := by
      apply add_lt_add_of_le_of_lt (le_refl (|a|))
      exact h n Nn

theorem convergesTo_unique' {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    rw [← reverse_lt, lt_abs, lt_iff_lt_neg 0 (-(a-b)), neg_neg, neg_zero]
    rcases lt_trichotomy (a - b) 0 with h|h|h
    · right; apply h
    · rw [sub_eq_zero] at h; contradiction
    · left; apply h
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have : Na ≤ N := by
      change Na ≤ max Na Nb
      apply le_max_left
    apply hNa N this
  have absb : |s N - b| < ε := by
    have : Nb ≤ N := by
      change Nb ≤ max Na Nb
      apply le_max_right
    apply hNb N this
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(a - s N) + (s N - b)| := by
        congr
        ring
      _ ≤ |a - s N| + |s N - b| := by
        apply abs_add
      _ = |s N - a| + |s N - b| := by
        rw [← abs_neg, neg_sub]
      _ < ε + ε := by
        apply add_lt_add absa absb
      _ = |a - b| := by
        change |a - b| / 2 + |a - b| / 2 = |a - b|
        linarith
  exact lt_irrefl _ this

theorem convergesTo_unique_' {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
    by_contra aneqb
    dsimp [ConvergesTo] at sa
    dsimp [ConvergesTo] at sb
    have hposε : 0 < |b-a|/2  := by
      have aux : (0: ℝ) < (2: ℝ) := by
        norm_num
      rw [lt_div_iff' aux, mul_zero, lt_iff_le_and_ne]
      constructor
      · apply abs_nonneg
      · by_contra h
        have h':= Eq.symm h
        rw [abs_eq_zero, sub_eq_zero] at h'
        have h'':= Eq.symm h'
        apply aneqb h''
    rcases sa (|b-a|/2) hposε with ⟨Na, ha⟩
    rcases sb (|b-a|/2) hposε with ⟨Nb, hb⟩
    have ha_ := ha (max Na Nb) (le_max_left Na Nb)
    have hb_ := hb (max Na Nb) (le_max_right Na Nb)
    rw [abs_lt] at ha_
    rw [abs_lt] at hb_
    rcases lt_trichotomy a b with h1|h1|h1
    · rw [← sub_lt_zero] at h1
      have h1': 0 ≤  b-a := by
        linarith
      rw [abs_of_nonneg h1'] at ha_
      rw [abs_of_nonneg h1'] at hb_
      have aux_a : s (max Na Nb) < (b+a)/2 := by
        have := ha_.right
        linarith
      have aux_b : (b+a)/2 < s (max Na Nb) := by
        have := hb_.left
        linarith
      have por_fin : (b+a)/2 < (b+a)/2 := by
        apply lt_trans  aux_b aux_a
      apply lt_irrefl ((b+a)/2) por_fin
    · contradiction
    · rw [← sub_lt_zero] at h1
      rw [abs_of_neg h1] at ha_
      rw [abs_of_neg h1] at hb_
      have aux_a : (b+a)/2 < s (max Na Nb) := by
        have := ha_.left
        linarith
      have aux_b : s (max Na Nb) < (b+a)/2 := by
        have := hb_.right
        linarith
      have por_fin : (b+a)/2 < (b+a)/2 := by
        apply lt_trans  aux_a aux_b
      apply lt_irrefl ((b+a)/2) por_fin

end
