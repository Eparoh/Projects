import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with xst | xsu
  · rw [mem_inter_iff] at *
    apply And.intro
    exact xst.left
    rw [mem_union]
    left
    exact xst.right
  · rw [mem_inter_iff] at *
    constructor
    · exact xsu.left
    · rw [mem_union]
      right
      exact xsu.right

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, nxtu⟩
  rw [mem_union] at nxtu
  push_neg at nxtu
  have nxt: x ∉ t := nxtu.left
  have nxu: x ∉ u := nxtu.right
  constructor
  · constructor
    · exact xs
    · exact nxt
  · exact nxu

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm sorry sorry

example : s ∩ (s ∪ t) = s := by
  ext x
  rw [mem_inter_iff, mem_union]
  constructor
  · rintro ⟨xs, xtu⟩
    exact xs
  · intro xs
    constructor
    · exact xs
    · left
      exact xs

example : s ∪ s ∩ t = s := by
  ext x
  rw [mem_union, mem_inter_iff]
  constructor
  · intro h
    rcases h with xs | xst
    · exact xs
    · exact xst.1
  · intro xs
    left
    exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x
  rw [mem_union, mem_union]
  constructor
  · rintro (⟨xs, xnt⟩ | xt)
    · left
      exact xs
    · right
      exact xt
  · rintro (xs | xt)
    · rcases em (x ∈ t) with xt | nxt
      · right
        exact xt
      · left
        exact And.intro xs nxt
    · right
      exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  rintro (⟨xs,nxt⟩ | ⟨xt, nxs⟩)
  · constructor
    · left
      exact xs
    · rintro ⟨xs, xt⟩
      contradiction
  · constructor
    · right
      exact xt
    · rintro ⟨xs, xt⟩
      contradiction
  · rintro ⟨(xs | xt), xnsit⟩
    · rw [mem_inter_iff] at xnsit
      push_neg at xnsit
      left
      exact And.intro xs (xnsit xs)
    · right
      use xt
      intro xs
      have xst: x ∈ s ∩ t := And.intro xs xt
      contradiction

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply em

-- Otra prueba echa por mi

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  constructor
  · intro h
    exact trivial
  · intro h
    rcases em (n ∈ {n | Even n}) with ev | odd
    · left
      exact ev
    · right
      dsimp
      dsimp at odd
      exact odd

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

#check  Nat.Prime.eq_two_or_odd
#check  Nat.even_iff
#check lt_irrefl

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro x
  simp
  intro xprime xg2 xeven
  rw [Nat.even_iff] at xeven
  rcases Nat.Prime.eq_two_or_odd xprime with h | h
  · rw [h] at xg2
    have n22: ¬ (2 < 2) := by
      apply lt_irrefl
    contradiction
  · rw [h] at xeven
    have n10: ¬ (1 = 0) := by
      norm_num
    contradiction

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · exact h₀ x (ssubt xs)
  · exact h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, nevenx, xprime⟩
  use x
  constructor
  · exact ssubt xs
  · exact xprime

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  constructor
  rintro (xs | xiA)
  · rw [mem_iInter]
    intro i
    rw [mem_union]
    right
    exact xs
  · rw [mem_iInter] at *
    intro i
    rw [mem_union]
    left
    apply xiA
  rw [mem_iInter]
  intro h
  rw [mem_union, mem_iInter]
  rcases em (x ∈ s) with xs | nxs
  · left
    exact xs
  · right
    intro i
    have xAis := h i
    rcases xAis with xAi | xs
    · exact xAi
    · contradiction

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext x
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

#check Nat.exists_prime_and_dvd
#check Nat.exists_infinite_primes

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  rw [mem_iUnion₂]
  have h:= Nat.exists_infinite_primes x
  rcases h with ⟨i, h⟩
  use i
  have iprime: i ∈ primes := by
     rw [primes]
     exact h.right
  use iprime
  exact h.left

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
