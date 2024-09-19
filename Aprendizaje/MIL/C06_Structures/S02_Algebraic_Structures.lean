import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

structure Group₁Cat where
  α : Type*
  str : Group₁ α

/- MIO -/
variable (α : Type*) (G : Group₁ α) (T: Group₁Cat)

#check Group₁ α
#check G
#check G.mul
#check T
#check T.α
#check T.str

#print Group
#print Group₁
#print Group₁Cat

/-  -/

section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end

example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

def permGroup {α : Type*} : Group₁ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc: ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_neg : ∀ x : α, add (neg x) x = zero


@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point where
  add p q := p.add q
  zero := zero
  neg p := p.neg
  add_assoc := by
    dsimp
    intro x y z
    rw [add, add, add, add]
    ext <;> dsimp
    repeat'
    apply add_assoc
  add_zero := by
    dsimp
    intro x
    rw [add]
    ext <;> dsimp
    repeat'
    rw [zero]
    dsimp
    rw [add_zero]
  zero_add := by
    dsimp
    intro x
    rw [add]
    ext <;> dsimp
    repeat'
    rw [zero]
    dsimp
    rw [zero_add]
  add_left_neg := by
    dsimp
    intro x
    rw [neg, add, zero]
    ext <;> dsimp
    repeat'
    ring

end Point

section
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by
  rw [mul_assoc, mul_right_inv, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

#print Inhabited

instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl

#print Add

instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end

class AddGroup₂ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc: ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_neg : ∀ x : α, add (neg x) x = zero


instance hasAddAddGroup₂ {α : Type*} [AddGroup₂ α] : Add α :=
  ⟨AddGroup₂.add⟩

instance hasZeroAddGroup₂ {α : Type*} [AddGroup₂ α] : Zero α :=
  ⟨AddGroup₂.zero⟩

instance hasNegAddGroup₂ {α : Type*} [AddGroup₂ α] : Neg α :=
  ⟨AddGroup₂.neg⟩

open Point

instance : AddGroup₂ Point where
  add p q := p.add q
  zero := Point.zero
  neg p := p.neg
  add_assoc := by
    dsimp
    intro x y z
    rw [add, add, add, add]
    ext <;> dsimp
    repeat'
    apply add_assoc
  add_zero := by
    dsimp
    intro x
    rw [add]
    ext <;> dsimp
    repeat'
    rw [zero]
    dsimp
    rw [add_zero]
  zero_add := by
    dsimp
    intro x
    rw [add]
    ext <;> dsimp
    repeat'
    rw [zero]
    dsimp
    rw [zero_add]
  add_left_neg := by
    dsimp
    intro x
    rw [neg, add, zero]
    ext <;> dsimp
    repeat'
    ring

example (a b : Point) : a + b = a.add b := rfl

/-  MIO  -/

class Group₃ (α : Type*) where
  mul' : α → α → α
  one' : α
  inv' : α → α
  mul_assoc' : ∀ x y z : α, mul' (mul' x y) z = mul' x (mul' y z)
  mul_one' : ∀ x : α, mul' x one' = x
  one_mul' : ∀ x : α, mul' one' x = x
  mul_left_inv' : ∀ x : α, mul' (inv' x) x = one'

-- Añadimos los símbolos usuales para trabajar con grupos

instance hasMulGroup₃ {α : Type*} [Group₃ α] : Mul α :=
  ⟨Group₃.mul'⟩

/- Otra forma para entender lo que se hace realmente al definir estas "instances".
   Es decir, lo que hacemos es decir que Gruop₃ es un caso particular de Mul-/

/-
instance hasMulGroup₃ {α : Type*} [Group₃ α] : Mul α where
  mul := Group₃.mul'
-/

instance hasOneGroup₃ {α : Type*} [Group₃ α] : One α :=
  ⟨Group₃.one'⟩

instance hasInvGroup₃ {α : Type*} [Group₃ α] : Inv α :=
  ⟨Group₃.inv'⟩

namespace Group₃

-- Añadimos los teoremas para poder usarlos con rw con la notación cómoda

theorem mul_assoc {α : Type*} [Group₃ α] : ∀ x y z : α, x * y * z = x * (y * z) := mul_assoc'
theorem mul_one {α : Type*} [Group₃ α] : ∀ x : α, x * 1  = x := mul_one'
theorem one_mul {α : Type*} [Group₃ α] : ∀ x : α, 1 * x  = x := one_mul'
theorem mul_left_inv {α : Type*} [Group₃ α] : ∀ x : α, x⁻¹ * x = 1 := mul_left_inv'

-- Algunos ejemplos

theorem mul_right_inv {α : Type*} [Group₃ α] (a : α) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem inv_unique {α : Type*} [Group₃ α] (y: α) : ∀ (x : α), (y * x = 1 → y = x⁻¹) := by
  intro x h
  have : (y * x) * x⁻¹ = x⁻¹ := by
    rw [h, one_mul]
  rwa [mul_assoc, mul_right_inv, mul_one] at this

-- Los teoremas funcionan para las "instance"

instance : Group₃ ℤ where
  mul' n m := n + m
  one' := 0
  inv' n := -n
  mul_assoc' := Int.add_assoc
  mul_one' := Int.add_zero
  one_mul' := Int.zero_add
  mul_left_inv' := Int.add_left_neg

example {a : ℤ} : a + (-a) = 0 := by
  exact Group₃.mul_right_inv a
