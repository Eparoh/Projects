import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    · apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    · apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    · apply min_le_right
    · apply min_le_left
  apply le_antisymm
  · apply h
  · apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
  · apply max_le
    · apply le_max_right
    · apply le_max_left

example : min (min a b) c = min a (min b c) := by
  have h: ∀ x y z : ℝ, min (min x y) z ≤ min x (min y z):= by
    intro x y z
    apply le_min
    · calc
        min (min x y) z ≤ min x y := by apply min_le_left
        _ ≤ x := by apply min_le_left
    · apply le_min
      · calc
        min (min x y) z ≤ min x y := by apply min_le_left
        _ ≤ y := by apply min_le_right
      · apply min_le_right
  apply le_antisymm
  · apply h
  · rw[min_comm a (min b c), min_comm (min a b) c, min_comm b c, min_comm a b]
    apply h

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add
    · apply min_le_left
    · apply le_refl
  · apply add_le_add
    · apply min_le_right
    · apply le_refl

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · rw [← add_neg_cancel_right (min (a + c) (b + c)) (-c)]
    apply add_le_add
    · have h: ∀ (a b c: ℝ), min a b + c ≤ min (a + c) (b + c):= by
        intro a b c
        apply aux
      have h1:=h (a+c) (b+c) (-c)
      rw [add_neg_cancel_right, add_neg_cancel_right] at h1
      exact h1
    · rw [neg_neg]

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a-b) b
  nth_rw 2 [← neg_neg b] at h
  rw [sub_eq_add_neg a b, add_neg_cancel_right, ← sub_eq_add_neg a b] at h
  linarith

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

lemma dvd_mul_of_dvd_left_: ∀ (a b c: ℕ), (a ∣ b) → a ∣ b * c := by
  intro a b c h
  apply dvd_mul_of_dvd_left h


example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h1: x ∣ w^2 := by
    have h2:= dvd_mul_of_dvd_left_ x w w h
    rw [← pow_two w] at h2
    exact h2
  have h2: x ∣ y * (x * z) + x^2 := by
    apply dvd_add
    · rw [mul_comm x z,← mul_assoc]
      apply dvd_mul_left
    · apply dvd_mul_left
  apply dvd_add h2 h1
end

section
variable (a b c m n: ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h1: m.gcd n = gcd m n := by rfl
  have h2: n.gcd m = gcd n m := by rfl
  rw [h1, h2]
  apply dvd_antisymm
  repeat
    rw [dvd_gcd_iff]
    apply And.intro
    · apply gcd_dvd_right
    . apply gcd_dvd_left


#check (dvd_gcd_iff: ∀ (a b c : ℕ), a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c)
#check (dvd_gcd: a ∣ c → a ∣ b → a ∣ gcd c b)
#check (gcd_dvd_left: ∀ (a b : ℕ), gcd a b ∣ a)
#check (gcd_dvd_right: ∀ (a b : ℕ), gcd a b ∣ b)

end
