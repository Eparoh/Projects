import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left


example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · calc
        x ⊓ y ⊓ z ≤ x ⊓ y := by
          apply inf_le_left
        _ ≤ x := by
          apply inf_le_left
    · apply le_inf
      · calc
        x ⊓ y ⊓ z ≤ x ⊓ y := by
          apply inf_le_left
        _ ≤ y := by
          apply inf_le_right
      · apply inf_le_right
  . apply le_inf
    · apply le_inf
      · apply inf_le_left
      · calc
          x ⊓ (y ⊓ z) ≤ y ⊓ z := by
            apply inf_le_right
          _ ≤ y := by
            apply inf_le_left
    . calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z := by
          apply inf_le_right
        _ ≤ z := by
          apply inf_le_right


example : x ⊔ y = y ⊔ x := by
  apply sup_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply sup_inf_self

example : x ⊔ y ⊓ z = x ⊔ (y ⊓ z) := by -- x ⊔ y ⊓ z = x ⊔ (y ⊓ z): El ínfimo manda
  rfl


end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · apply le_inf
    · apply sup_le
      · apply le_sup_left
      · calc
          b ⊓ c ≤ b := by
            apply inf_le_left
          _ ≤ a ⊔ b := by
            apply le_sup_right
    · apply sup_le
      · apply le_sup_left
      · calc
          b ⊓ c ≤ c := by
            apply inf_le_right
          _ ≤ a ⊔ c := by
            apply le_sup_right
  · rw [h]
    apply sup_le
    · rw [inf_comm, inf_sup_self]
      apply le_sup_left
    · rw [inf_comm, h]
      apply sup_le
      · calc
          c ⊓ a ≤ a := by
            apply inf_le_right
          _ ≤ a ⊔ b ⊓ c := by
            apply le_sup_left
      · rw [inf_comm]
        apply le_sup_right

--example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
--  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have h1:= add_le_add_left h (-a)
  rw [add_left_neg, add_comm, ← sub_eq_add_neg b a] at h1
  exact h1

example (h: 0 ≤ b - a) : a ≤ b := by
  have h1:= add_le_add_left h a
  rw [add_zero, add_comm, sub_add, sub_self, sub_zero] at h1
  exact h1

-- Combianamos estos dos ejemplos en un lema para probar el siguiente

lemma le_dif: ∀ (x y: R), x ≤ y ↔ 0 ≤ y - x := by
  intro x y
  apply Iff.intro
  · intro h
    have h1:= add_le_add_left h (-x)
    rw [add_left_neg, add_comm, ← sub_eq_add_neg y x] at h1
    exact h1
  · intro h
    have h1:= add_le_add_left h x
    rw [add_zero, add_comm, sub_add, sub_self, sub_zero] at h1
    exact h1

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [le_dif, ← sub_mul]
  rw [le_dif] at h
  apply mul_nonneg h h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h1: 0 ≤ 2 * dist x y := by
    calc
      0 = dist x x := by
        rw [dist_self x]
      _ ≤ dist x y + dist y x := by
        apply dist_triangle
      _ = 2 * dist x y := by
        rw [← dist_comm x y, ← two_mul]
  have h2: (0: ℝ) < (2: ℝ) := by norm_num
  rw [mul_comm] at h1
  apply nonneg_of_mul_nonneg_left h1 h2

#check nonneg_of_mul_nonneg_left
end
