import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h1; left; exact h1
  . rw [abs_of_neg h]
    intro h1; right; exact h1

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    apply add_le_add (le_abs_self x) (le_abs_self y)
  · rw [abs_of_neg h, neg_add]
    apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy] at h
      left
      exact h
    · rw [abs_of_neg hy] at h
      right
      exact h
  · intro h
    rcases h with h1|h1
    · apply lt_of_lt_of_le h1 (le_abs_self y)
    · rcases le_or_gt 0 y  with h2 | h2
      · rw [abs_of_nonneg h2]
        have h3: x < 0 := by
          have h3: -y ≤ 0 := by
            linarith
          apply lt_of_lt_of_le h1 h3
        apply lt_of_lt_of_le h3 h2
      · rw [abs_of_neg h2]
        exact h1


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, b, rfl | rfl⟩ <;> linarith [sq_nonneg a, sq_nonneg b]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x - 1)*(x + 1) = 0 := by
    linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2|h2
  · left
    linarith
  · right
    linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x - y)*(x + y) = 0 := by
    linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2|h2
  · left
    linarith
  · right
    linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

#check eq_neg_iff_add_eq_zero
#check eq_of_sub_eq_zero

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x - 1)*(x + 1) = 0 := by
    calc
      (x - 1)*(x + 1) = x^2 - 1 := by
        noncomm_ring -- Para que también funcione con "Ring"
      _ = 0 := by
        rw [← sub_self 1, sub_left_inj]
        exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2|h2
  · left
    rw [← eq_of_sub_eq_zero h2]
  · right
    rw [← eq_neg_iff_add_eq_zero] at h2
    exact h2

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x - y)*(x + y) = 0 := by
    calc
      (x - y)*(x + y) = x^2 - y^2 := by
        ring
      _ = 0 := by
        rw [← sub_self (y^2), sub_left_inj]
        exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2|h2
  · left
    rw [← eq_of_sub_eq_zero h2]
  · right
    rw [← eq_neg_iff_add_eq_zero] at h2
    exact h2

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    rcases em P with h1|h1
    · right
      apply h h1
    · left
      exact h1
  · intro h h'
    rcases h with h1|h1
    · contradiction
    · exact h1
