import Aprendizaje.MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true


class One₁ (α : Type) where
  /-- The element one -/
  one : α


#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one


example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (One₁.one : α) = 𝟙 := rfl


class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ " => Dia₁.dia


class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/- Al crear la clase de esta forma, "toDia₁" no se añade a la base de datos de los "instances" y hay
   que añadirlo a mano para poder utilizar la notación con el "⋄" -/

attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α


class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α


example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁

/- MIO -/

class Monoid₉₇₈ (α : Type) extends Semigroup₂ α, DiaOneClass₁ α

example {α : Type} [Monoid₉₇₈ α] :
  (Monoid₉₇₈.toSemigroup₂.toDia₁.dia : α → α → α) = Monoid₉₇₈.toDiaOneClass₁.toDia₁.dia := rfl

#check Monoid₉₇₈.mk
#print Monoid₉₇₈

/- Para Monoid₂ si aparacen dos operaciones "dia" distintas, la que proviene de Semigroup₁ y
   la de DiaOneClass₁. Sin embargo Monoid₂ (y Monoid₉₇₈), no toma DiaOneClass₁, sino que toma solo la
   parte con la que no hay "overlapping". Aún así, aunque no aparezca como un "field", si que incluye
   la "instance" Monoid₁.toDiaOneClass₁

   Por tanto, el siguiente ejemplo dará error

example {α : Type} [Monoid₂ α] :
  (Monoid₂.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₂.toDiaOneClass₁.toDia₁.dia := rfl
-/
/-  -/

class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

#print Group₁


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← Monoid₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)

example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  rw [← dia_one (a⁻¹), ← h, ← dia_assoc, inv_dia, one_dia]

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  rw [← inv_dia (a⁻¹), inv_eq_of_dia (inv_dia a)]





class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

#print MulOneClass
#print Monoid₃

-- Añade el atributo "to_additive" a "Monoid₃.toMulOneClass" (creo)
attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

-- Añade los lemas al simplificador
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [← mul_one (a⁻¹), ← h, ← mul_assoc₃, Group₃.inv_mul, one_mul]


@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  rw [← inv_mul (a⁻¹), inv_eq_of_mul (inv_mul a)]

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← Group₃.inv_mul a, mul_assoc₃, h, ← mul_assoc₃, Group₃.inv_mul a, one_mul]

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  simpa [mul_assoc₃] using congr_arg (· * a⁻¹) h

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G



class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

#print Ring₃
#print AddCommGroup₃

export AddCommGroup₃ (add_comm)

/- El siguiente ejemplo da error

example {R : Type} [Ring₃ R] (a b: R) : a + b = b + a := add_comm a b

   Sin embargo, a continuación veremos que un anillo es un ejemplo de grupo conmutativo y dejará de dar error
-/

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := by
      calc
        a + (a + b + b) = (a + a) + (b + b) := by rw [add_assoc₃, add_assoc₃]
        _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
        _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring₃.right_distrib]
        _ = (1 + 1) * (a + b) := by simp [Ring₃.left_distrib]
        _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring₃.right_distrib]
        _ = (a + b) + (a + b) := by simp
        _ = a + (b + a + b) := by simp [add_assoc₃]
    exact add_right_cancel₃ (add_left_cancel₃ this) }

/- Otra forma que me gusta más

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R where
  add_comm := by
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := by
      calc
        a + (a + b + b) = (a + a) + (b + b) := by rw [add_assoc₃, add_assoc₃]
        _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
        _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring₃.right_distrib]
        _ = (1 + 1) * (a + b) := by simp [Ring₃.left_distrib]
        _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring₃.right_distrib]
        _ = (a + b) + (a + b) := by simp
        _ = a + (b + a + b) := by simp [add_assoc₃]
    exact add_right_cancel₃ (add_left_cancel₃ this)
    -/

/- Mio -/
example {R : Type} [Ring₃ R] (a b: R) : a + b = b + a := add_comm a b
/-  -/


instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type) extends LE₁ α where
/-- Order relation is reflexive -/
  le_refl : ∀ (a : α), a ≤₁ a
/-- Order relation is transitive -/
  le_trans : ∀ (a b c : α), a ≤₁ b → b ≤₁ c → a ≤₁ c

class PartialOrder₁ (α : Type) extends Preorder₁ α where
/-- Order relation is transitive -/
  le_antisymm : ∀ (a b : α), a ≤₁ b → b ≤₁ a → a = b

class OrderedCommMonoid₁ (α : Type) extends PartialOrder₁ α, CommMonoid₃ α where
  mul_of_le : ∀ (a b : α), a ≤₁ b → ∀ (c : α), c * a ≤₁ c * b

instance : OrderedCommMonoid₁ ℕ where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := fun a b c ↦ le_trans
  le_antisymm := fun a b ↦ le_antisymm
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_of_le := by
    intro a b h c
    apply Nat.mul_le_mul_left c h


class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul

class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

/- MIO -/

example (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] [Module₁ R M] (a b : M) (r : R) :
  (a + b = b + a) ∧ (r • (a + b) = r • a + r • b) := by
    constructor
    · exact AddCommGroup₃.add_comm  a b
    · exact Module₁.smul_add r a b

/-  -/

instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := (· * ·) -- fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a -- Se define para los enteros no negativos
  | Int.negSucc n, a => -nsmul₁ n.succ a -- Se define para los enteros negativos considerados como -(n+1) con n natural

#check Int.toNat_of_nonneg
#check Nat.add_comm

lemma nsmul₁_eq_zsmul₁ [Zero M] [Add M] [Neg M] (n: ℤ) (h: 0 ≤ n) : ∀ (m : M), nsmul₁ (Int.toNat n) m = zsmul₁ n m := by
  intro m
  rw [← Int.toNat_of_nonneg h]
  dsimp [zsmul₁]

---------- Terminar

#print AddSemigroup₃

lemma nsmul₁_of_add_eq_add_of_nsmul₁ [AddCommGroup₃ M] (a b : ℕ) (m : M) :
  nsmul₁ (a + b) m = nsmul₁ a m + nsmul₁ b m := by
  induction' a with a ih
  · rw [zero_add, nsmul₁, zero_add]
  · rw [add_assoc, Nat.add_comm 1 b, ← add_assoc, nsmul₁, nsmul₁, ih, ← add_assoc₃]

lemma nsmul₁_of_mul_eq_nsmul₁_of_nsmul₁ [AddCommGroup₃ M] (a b : ℕ) (m : M) :
  nsmul₁ (a * b) m = nsmul₁ a (nsmul₁ b m) := by
  induction' a with a ih
  · rw [zero_mul, nsmul₁, nsmul₁]
  · rw [add_mul, one_mul, Nat.add_comm]
    dsimp [nsmul₁]
    rw [← ih, nsmul₁_of_add_eq_add_of_nsmul₁]

lemma zsmul₁_of_mul_eq_zsmul₁_of_zsmul₁ [AddCommGroup₃ M] (a b : ℤ) (m : M) :
  zsmul₁ (a * b) m = zsmul₁ a (zsmul₁ b m) := by
  induction' a with a a
  · induction' b with b b
    dsimp
    · rw [← Int.ofNat_mul a b]
      dsimp [zsmul₁]
      apply nsmul₁_of_mul_eq_nsmul₁_of_nsmul₁
    · sorry
  sorry



----------------------------------------------------------

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := by
    intro m
    dsimp
    rfl
  one_smul := by
    intro m
    dsimp
    rw [← nsmul₁_eq_zsmul₁ 1 (zero_le_one) m]
    simp
    rw [nsmul₁, nsmul₁, add_zero]
  mul_smul := by
    intro a b m
    dsimp
    apply zsmul₁_of_mul_eq_zsmul₁_of_zsmul₁
  add_smul := sorry
  smul_add := sorry

#synth Module₁ ℤ ℤ -- abGrpModule ℤ


class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

#check Int.ofNat_add

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := by
    intro n m
    show (n + 1 : ℤ) * m = m + n * m
    rw [Int.add_mul, Int.add_comm, Int.one_mul]
  --nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
  --  by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- El "self" es para indicar que "instance" de SMul se va a utilizar

/- Menor estricto -/

class LT₁ (α : Type) where
  /-- The Less-Than relation -/
  lt : α → α → Prop

@[inherit_doc] infix:50 " <₁ " => LT₁.lt

class Preorder₂ (α : Type) extends LE₁ α, LT₁ α  where
/-- Order relation is reflexive -/
  le_refl : ∀ (a : α), a ≤₁ a
/-- Order relation is transitive -/
  le_trans : ∀ (a b c : α), a ≤₁ b → b ≤₁ c → a ≤₁ c
/-- Relación estricta de orden -/
  lt := fun a b ↦ a ≤₁ b ∧ a ≠ b
/-- Relación entre definiciones -/
  lt_iff_le_not_le : ∀ (a b : α), a <₁ b ↔ a ≤₁ b ∧ a ≠ b := by intros; rfl

class PartialOrder₂ (α : Type) extends Preorder₂ α where
/-- Order relation is transitive -/
  le_antisymm : ∀ (a b : α), a ≤₁ b → b ≤₁ a → a = b

class OrderedCommMonoid₂ (α : Type) extends PartialOrder₂ α, CommMonoid₃ α where
  mul_of_le : ∀ (a b : α), a ≤₁ b → ∀ (c : α), c * a ≤₁ c * b

instance : OrderedCommMonoid₂ ℕ where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := fun a b c ↦ le_trans
  le_antisymm := fun a b ↦ le_antisymm
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_of_le := by
    intro a b h c
    apply Nat.mul_le_mul_left c h

example : 2 <₁ 3 := by
  rw [Preorder₂.lt_iff_le_not_le]
  constructor
  · dsimp [LE₁.le]
    linarith
  · norm_num
