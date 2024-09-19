import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  rcases m with _ | m
  · contradiction
  · rcases m with _ | m
    · contradiction
    · repeat apply Nat.succ_le_succ
      apply zero_le

/- Mio -/
theorem two_le' {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  induction' m with m ih
  · contradiction
  · rcases em (m = 0 ∨ m = 1) with h | h
    · rcases h with h' | h'
      · rw [h'] at h1
        contradiction
      · rw [h']
    · push_neg at h
      have twolem: 2 ≤ m := by
        exact ih (h.left) (h.right)
      have mlesucc : m ≤ m + 1 := by
        linarith
      apply le_trans twolem mlesucc
/-  -/

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

#check Nat.minFac

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  rcases em n.Prime with n_prime | n_noprime
  · use n
  · induction' n using Nat.strong_induction_on with n ih
    rw [Nat.prime_def_lt] at n_noprime
    push_neg at n_noprime
    rcases n_noprime h with ⟨m, mltn, mdvdn, mne1⟩
    have : m ≠ 0 := by
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have mgt2 : 2 ≤ m := by
     exact two_le this mne1
    rcases em m.Prime with m_prime | m_noprime
    · use m
    . rcases ih m mltn mgt2 m_noprime with ⟨p, pp, pdvd⟩
      use p
      constructor
      · exact pp
      · apply pdvd.trans mdvdn

#check Nat.factorial_pos
#check Nat.dvd_factorial
#check Nat.dvd_sub
#check Nat.add_sub_assoc

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    induction' n with n ih
    · rw [Nat.factorial, Nat.factorial]
    · rw [Nat.factorial]
      dsimp
      rw [add_mul, one_mul, add_assoc]
      exact le_add_left ih
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  use p
  constructor
  · by_contra ple
    push_neg  at ple
    have : p ∣ Nat.factorial (n + 1) := by
      apply Nat.dvd_factorial
      · rw [Nat.prime_def_lt] at pp
        linarith
      · linarith
    have : p ∣ 1 := by
      have eq_one : (n + 1).factorial + 1 - (n + 1).factorial = 1 := by
        rw [add_comm, Nat.add_sub_assoc (le_refl (n + 1).factorial), Nat.sub_self, add_zero]
      rw [← eq_one]
      apply Nat.dvd_sub
      · linarith
      · exact pdvd
      · exact this
    have : p ≤ 1 := by
      apply Nat.le_of_dvd zero_lt_one this
    linarith [pp.two_le]
  · exact pp


open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)
/- DecidableEq dice que en α existe un procedimiento algorítmico para probar la igualdad de dos elementos.
   Esto es necesario para razonar con conjuntos finitos de forma computacional.-/

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

#check Finset.dvd_prod_of_mem

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i := by
  apply Finset.dvd_prod_of_mem
  exact h

#check Nat.Prime.eq_one_or_self_of_dvd

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  have : p = 1 ∨ p = q := by
    exact Nat.Prime.eq_one_or_self_of_dvd prime_q p h
  rcases this with h' | h'
  · have : 2 ≤ p := by
      exact prime_p.two_le
    linarith
  · exact h'

#check Finset.prod_empty
#check Finset.prod_insert
#check Finset.mem_insert

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  · simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
    rw [mem_insert]
    rcases h₁ with h | h
    · left
      exact _root_.Nat.Prime.eq_of_dvd_of_prime prime_p h₀.left h
    · right
      exact ih h₀.right h

#check Finset.filter
#check Finset.mem_filter

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

#check Finset.prod_pos
#check Nat.one_le_iff_ne_zero

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg  at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
    apply Nat.succ_le_succ
    have : 0 < ∏ i ∈ s', i := by
      apply Finset.prod_pos
      intro i is'
      rw [mem_s'] at is'
      linarith [is'.two_le]
    rw [Nat.one_le_iff_ne_zero]
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
    apply Finset.dvd_prod_of_mem
    rw [mem_s']
    exact pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  have : p ≤ 1 := by
      apply Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

#check Finset.sup
#check Finset.le_sup

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

#check Nat.mul_mod
#check Nat.mod_lt
#check Nat.mul_mod_mod
#check lt_iff_le_and_ne
#check Nat.lt_succ

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := by
    apply Nat.mod_lt m
    linarith
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := by
    apply Nat.mod_lt n
    linarith
  interval_cases n % 4 <;> simp

/- Mio -/

theorem mod_4_eq_3_or_mod_4_eq_3' {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  by_contra h'
  push_neg at h'
  rw [Nat.mul_mod] at h
  have b1 : m % 4 < 3 := by
    rw [lt_iff_le_and_ne, ← Nat.lt_succ]
    simp [h']
    apply Nat.mod_lt m
    linarith
  have b2 : n % 4 < 3 := by
    rw [lt_iff_le_and_ne, ← Nat.lt_succ]
    simp [h']
    apply Nat.mod_lt n
    linarith
  interval_cases m % 4 <;> interval_cases n % 4 <;> contradiction

/-  -/

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

#check Nat.div_dvd_of_dvd
#check Nat.div_lt_self
#check Nat.dvd_trans

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · apply Nat.div_dvd_of_dvd h₀
  · apply Nat.div_lt_self <;> linarith

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  rcases em (n.Prime) with np | nnep
  · use n
  · induction' n using Nat.strong_induction_on with n ih
    rw [Nat.prime_def_lt] at nnep
    push_neg  at nnep
    rcases nnep (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
    have mge2 : 2 ≤ m := by
      apply two_le _ mne1
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
    have : m % 4 = 3 ∨ n / m % 4 = 3 := by
      apply mod_4_eq_3_or_mod_4_eq_3
      rw [neq, h]
    rcases this with h1 | h1
    . rcases em (m.Prime) with mp | mnep
      · use m
      · rcases (ih m mltn h1 mnep) with ⟨p, pp, pdivm, pmod43⟩
        use p, pp
        constructor
        · exact Nat.dvd_trans pdivm mdvdn
        · exact pmod43
    · rcases em ((n/m).Prime) with ndivmp | mdivnnep
      · use n/m, ndivmp
        constructor
        · apply Nat.div_dvd_of_dvd mdvdn
        · exact h1
      · have ngt0 : 0 < n := by
          linarith
        have mgt1 : 1 < m := by
          linarith
        rcases (ih (n/m) (Nat.div_lt_self ngt0 mgt1) h1 mdivnnep) with ⟨p, pp, pdivm, pmod43⟩
        use p, pp
        constructor
        · apply Nat.dvd_trans pdivm _
          apply Nat.div_dvd_of_dvd mdvdn
        · exact pmod43

#check Finset.erase
#check Finset.mem_erase

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

#check Nat.dvd_add_iff_left
#check Nat.dvd_sub'
#check Nat.Prime.dvd_mul
#check Finset.dvd_prod_of_mem
#check Nat.Prime.dvd_mul
#check Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg  at h
  rcases h with ⟨n, hn⟩
  have : ∃ (s : Finset Nat), ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    intro k
    contrapose!
    intro nk kp
    exact hn k nk kp
  rcases this with ⟨s, hs⟩
  let s':= (4 * ∏ i in erase s 3, i) + 3
  have h₁ : s' % 4 = 3 := by
    dsimp [s']
    rw [add_comm, Nat.add_mul_mod_self_left]
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    apply (hs p).mp
    constructor
    · exact pp
    · exact p4eq
  have pne3 : p ≠ 3 := by
    intro peq3
    dsimp [s'] at pdvd
    rw [peq3, ← Nat.dvd_add_iff_left (dvd_refl 3), Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈  s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three
      · intro r hr
        simp at hr
        exact ((hs r).mpr hr.right).left
      · exact pdvd
    simp at this
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    rw [Nat.Prime.dvd_mul pp]
    right
    apply dvd_prod_of_mem
    simp
    constructor
    · exact pne3
    · exact ps
  have : p ∣ 3 := by
    have tres : 3 = s' - (4 * ∏ i ∈ s.erase 3, i) := by
      simp [s']
    rw [tres]
    apply Nat.dvd_sub' pdvd this
  have : p = 3 := by
    have := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three p this
    rcases this with h' | h'
    · have : 2 ≤ p := pp.two_le
      rw [h'] at this
      contradiction
    · exact h'
  contradiction
