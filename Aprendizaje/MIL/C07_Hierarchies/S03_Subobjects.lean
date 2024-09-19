import MIL.Common
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
--coe := fun (x : Submonoid₁ M) ↦ x.carrier
  coe_injective' := Submonoid₁.ext
/-coe_injective' := by
    dsimp [Function.Injective]
    intro x y xeqy
    ext u
    rw [xeqy]-/



/- Gracias a tener la instancia de que es "como un conjunto", podemos hablar de pertenencia en
   los submonoides -/

example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N

/- SetLike también tiene una instancia que permite ver a
   N: Submonoid₁ M, como {x : M // x ∈ N} -/

example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.2


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))

/-instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := by
    intro x y z
    apply SetCoe.ext
    exact mul_assoc (x : M) y z
  one := ⟨1, N.one_mem⟩
  one_mul := by
    intro x
    apply SetCoe.ext
    exact one_mul (x : M)
  mul_one := by
    intro x
    apply SetCoe.ext
    exact mul_one (x : M)-/


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

/- Ejemplo con grupos -/

@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  /-- The inverse of an elements of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

/-- Subgroups in `G` can be seen as sets in `G`. -/
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := fun H ↦ H.toSubmonoid₁.carrier
  coe_injective' := Subgroup₁.ext

#print Subgroup₁

instance [Group G] (H : Subgroup₁ G) : Group H :=
{ SubMonoid₁Monoid H.toSubmonoid₁ with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  mul_left_inv := fun x ↦ SetCoe.ext (mul_left_inv (x : G)) }

/-instance [Group G] (H: Subgroup₁ G) : Group H where
  mul := fun x y ↦ ⟨x.1 * y.1, H.mul_mem x.2 y.2⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x: G) y z)
  one := ⟨1, H.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x: G))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x: G))
  inv := fun x ↦ ⟨x.1⁻¹, H.inv_mem x.2⟩
  mul_left_inv := fun x ↦ SetCoe.ext (mul_left_inv (x: G))-/

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] extends SubmonoidClass₁ S G where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := fun H ↦ H.toSubmonoid₁.mul_mem
  one_mem := fun H ↦ H.toSubmonoid₁.one_mem

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G where
  inv_mem := Subgroup₁.inv_mem

/- Fin ejemplo -/

instance [Monoid M] : Inf (Submonoid₁ M) where
  inf := fun S₁ S₂ ↦
         {carrier := S₁ ∩ S₂ -- S₁.carrier ∩ S₂.carrier
          one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
          mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩
         }

/-instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩-/


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P

#print Setoid -- Clase que especifica una relación de equivalencia sobre un tipo
#print Equivalence

def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z h₁ h₂
      rcases h₁ with ⟨u, uinN, v, vinN, eqxy⟩
      rcases h₂ with ⟨u', u'inN, v', v'inN, eqyz⟩
      use u * u', N.mul_mem uinN u'inN, v * v', N.mul_mem vinN v'inN
      rw [← mul_assoc, eqxy, mul_assoc, mul_comm v u', ← mul_assoc, eqyz, mul_assoc, mul_comm v' v]
  }

#print Quot -- Tipo para los espacios cociente
#check Quot.mk -- Funcion que dadas una relación r en α y un elemento a de α, devuelve un elemento de tipo Quot r (la clase de equivalencia de a por r)
#print HasQuotient -- Como "LE", pero para la notación "⧸"
#print Quotient -- Dado s : Setoid α, devuelve Quot s.r (el conjunto cociente en α para r)
#print Quotient.mk -- Dados s : Setoid α, devuelve una función de tipo α → Quotient s, tal que al evaluarla en a : α, se obtiene Quot.mk r.s a (la clase de equivalencia de a por r.s)


instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid


def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  /- Quotient.map₂' toma como argumentos una función f: α → β → γ y (h : (s1.r ⇒ s2.r ⇒ s3.r) f f) donde
     s1 : Setoid α, s2 : Setoid β , s3 : Setoid γ, y h se simplifica a:
     ∀ {a₁ a₂ : α }, s1.r a₁ a₂ → ∀ {b₁ b₂ : β}, s2.r b₁ b₂ → s3.r s3.r (f a₁ b₁) (f a₂ b₂)
     Es decir, que si a₁ y a₂ están relacionadas por s1.r (la relación de equivalencia en α)
     y b₁, b₂ están relacionadas por s2.r (la relación de equivalencia en β), entonces sus imágenes
     (f a₁ b₁) y (f a₂ b₂) estarán relacionadas por s3.r (la relación de equivalencia en γ).
     Con estos argumentos, devuelve una función F de tipo Quotient s₁ → Quotient s₂ → Quotient s₃, tal que
     dados Quot.mk r.s1 a : Quotient s₁, Quot.mk r.s2 b : Quotient s₂, entonces F a' b' = Quot.mk r.s3 (f a b)-/
  mul := Quotient.map₂' (· * ·) (by
      dsimp [Relator.LiftFun]
      intro a b arb x y xry
      dsimp [Submonoid.Setoid] at *
      rcases arb with ⟨u, uinN, v, vinN, eqab⟩
      rcases xry with ⟨u', u'inN, v', v'inN, eqxy⟩
      use u*u', N.mul_mem uinN u'inN, v*v', N.mul_mem vinN v'inN
      rw [mul_assoc, ← mul_assoc x u u', mul_comm x u, mul_assoc, ← mul_assoc, eqab, eqxy,
          mul_assoc b y _, mul_comm v v',← mul_assoc y v' v, mul_comm (y * v') v, mul_assoc]
        )
  mul_assoc := by
      intro a' b' c'
      rcases Quotient.exists_rep a' with ⟨a, eqa⟩ -- Quotient.exists_rep dice que existe un a tal que su clase de equivalencia es igual a a'
      rcases Quotient.exists_rep b' with ⟨b, eqb⟩
      rcases Quotient.exists_rep c' with ⟨c, eqc⟩
      rw [← eqa, ← eqb, ← eqc]
      apply Quotient.sound -- Si arb, entonces sus clases de equivalencia son iguales
      dsimp
      rw [mul_assoc]
      apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
      intro a'
      rcases Quotient.exists_rep a' with ⟨a, eqa⟩
      rw [← eqa]
      apply Quotient.sound
      dsimp
      rw [one_mul]
      apply @Setoid.refl M N.Setoid
  mul_one := by
      intro a'
      rcases Quotient.exists_rep a' with ⟨a, eqa⟩
      rw [← eqa]
      apply Quotient.sound
      dsimp
      rw [mul_one]
      apply @Setoid.refl M N.Setoid
