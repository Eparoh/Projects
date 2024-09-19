import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic
import MIL.Common

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

#check Nat.factorial

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  · rw [fac]
    exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  · rw [fac]
    rcases Nat.of_le_succ ile with h | h
    · apply dvd_mul_of_dvd_right (ih h)
    · rw [h]
      apply dvd_mul_right

#check pow_succ
#check pow_succ'
#check Nat.add_sub_assoc
#check mul_le_mul_left'
#check mul_le_mul_right
#check Nat.zero_le
#check mul_pos
#check Nat.succ_pos

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  · rw [fac, Nat.add_sub_assoc (le_refl 1), Nat.sub_self, add_zero]
    induction' n with n ih
    · simp [fac]
    · rw [fac, pow_succ']
      calc
        2 * 2^n ≤ 2 * ((n + 1) * fac n) := by
          apply mul_le_mul_left' ih
        _ ≤ (n+2) * ((n + 1) * fac n) := by
          have : 2 ≤ n+2 := by
            calc
              2 = 0 + 2 := by
                rw [zero_add]
              _ ≤ n + 2 := by
                apply add_le_add_right
                exact Nat.zero_le n
          have pos: 0 < (n + 1) * fac n := by
            apply mul_pos
            · exact Nat.succ_pos n
            · exact fac_pos n
          rw [mul_le_mul_right pos]
          exact this
        _ = (n+1+1) * ((n + 1) * fac n) := by
          norm_num

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

#check Finset.range n
#check Finset.sum_range_zero f
#check Finset.sum_range_succ f n
#check Finset.prod_range_zero f
#check Finset.prod_range_succ f n

example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · rw [fac, prod_range_zero]
  · rw [fac, ih, prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, mul_add 2, ← ih]
    ring

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with m ih
  · simp
  · rw [Finset.sum_range_succ, mul_add 6, ← ih]
    ring
end

inductive MyNat
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  · rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  · rw [add, ih, add]

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add, add]
  · rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' k with k ih
  · rw [add, add]
  · rw [add, add, ih, add]

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' k with k ih
  · rw [add, mul, add]
  · rw [add,mul, ih, mul, add_assoc]

theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with n ih
  · rw [mul]
  · rw [mul, add, ih]

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with n ih
  · rw [mul, add, mul]
  · rw [mul, add, ih, add, mul, add_assoc, add_assoc, add_comm m n]

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' n with n ih
  · rw [mul, zero_mul]
  · rw [mul, succ_mul, ih]

end MyNat

/- Resta truncada -/

def pred: Nat → Nat
  | 0 => 0
  | n + 1 => n

def trunc_sub: Nat → Nat → Nat
  | m, 0 => m
  | m, n + 1 => pred (trunc_sub m n)

#check Nat.zero_le
#check Nat.le_succ_iff
#check sub_sub
#check Nat.add_sub_assoc
#check Nat.le_succ
#check Nat.lt_succ
#check lt_of_lt_of_le
#check Nat.sub_pos_iff_lt

theorem succ_sub' (n: ℕ): ∀ (m: ℕ), trunc_sub (n+m) n = m := by
  induction' n with n ih
  · intro m
    rw [trunc_sub, zero_add]
  · intro m
    rw [trunc_sub, add_assoc, ih (1+m), add_comm, pred]

theorem succ_sub (n m: ℕ): trunc_sub (n+m) n = m := by
  exact succ_sub' n m

theorem small_sub_big_zero (m n : ℕ) (mlen: m ≤ n): trunc_sub m n = 0 := by
  induction' n with n ih
  · rw [trunc_sub]
    have: 0 ≤ m := by
      exact Nat.zero_le m
    exact le_antisymm mlen this
  · rw [trunc_sub]
    rw [Nat.le_succ_iff] at mlen
    rcases mlen with h | h
    · rw [ih h, pred]
    · rw [h, succ_sub n 1, pred]

theorem pred_sub_one (n: ℕ) (ngez: 0 < n): pred n = n - 1 := by
  rcases n with _ | n
  · contradiction
  · rw [Nat.add_sub_assoc (le_refl 1), Nat.sub_self, add_zero, pred]


theorem big_sub_small_sub (m n : ℕ) (mlen: n ≤ m): trunc_sub m n = m - n := by
  induction' n with n ih
  · rw [trunc_sub, Nat.sub_zero]
  · rw [trunc_sub]
    have : n ≤ m := by
      calc
        n ≤ n +1 := by
          exact Nat.le_succ n
        _ ≤ m := by
          exact mlen
    have nltm: 0 < m - n := by
      have : n < m := by
        exact lt_of_lt_of_le ((Nat.lt_succ).mpr (le_refl n)) mlen
      rw [Nat.sub_pos_iff_lt]
      exact this
    rw [← Nat.sub_sub, ih this, pred_sub_one _]
    exact nltm
