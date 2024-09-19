import Mathlib.Tactic
import Mathlib.Util.Delaborators

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section --Tacticas

open Real

section --exact
/- Permite terminar una demostración al pasarle el "goal exacto", es decir,si el término
   dado tiene como tipo el goal -/
end --exact
section --rfl
/- Permite terminar una demostración cuando se tiene una tautología -/
end --rfl
section --rw
/- Permite reescribir el goal o alguna hipótesis (e intenta terminar la demostración con un rfl):
   - rw [h] -> Si h es una demostración de p = q o p ↔ q (es decir, h: p = q o h: p ↔ q), cambia
                cualquier aparición de p (en el goal) por q.
   - rw [← h] -> Cambiará las q's por p's
   - rw [h] at h1 (rw [← h] at h1) -> Hace lo mismo que antes pero en la hipótesis h1, en lugar de en el goal
   - rw [h] at * -> Reescribe en el goal y todas las hipótesis
   - rw [h, g, f] (at h1) -> Es equivalente a escribir rw[h] rw[g] rw[f]
   - nth_rw m [h] (at h1) (nth_rw m [← h] (at h1)) -> Hace lo mismo que rw pero solo cambia la m-ésima ocurrencia de p -/

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

end --rw
section --apply
/- Si el goal es la conclusión de un teorema h, "apply h" cambiará el goal por las hipótesis del teorema -/
end --apply
section --intro
/- Introduce nuevas variables o hipótesis.
   - Si el goal es de la forma "p → q", "intro h" introducirá una nueva hipótesis h:p y cambiará
     el goal por "q".
   - Si el goal es de la forma "∀ (x: P), p x", "intro x" introducirá una nueva variable x de tipo P
      y cambiará el goal a "p x" -/
end --intro
section --have
/- "have h: p := by h1" introduce una nueva hipótesis h: p siempre que h1: p, es decir,
   si h1 sea una demostrción de p)

   Poniendo únicamente h:= h1, introduce una nueva hipótesis h: p donde h1: p siempre que esté claro quien es "p"

   Si ponemos "have : h1" con h1: p, pondrá como nombre de la nueva hipótesis "this" -/
end --have
section --ring
/- Permite demostrar identidades en semianillos conmutativos siempre que se deduzcan únicamente de los axiomas y sin usar hipótesis adicionales -/

example (a b c: ℕ): c * b * a = b * (a * c) := by
  ring

example (a b: ℤ): (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example (a b: ℚ): (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end --ring
section --noncomm_ring
/- Permite demostrar identidades en anillos no conmutativos siempre que se deduzcan únicamente de los axiomas y sin usar hipótesis adicionales -/
end --noncomm_ring
section --group
/- Permite demostrar identidades en grupos (multiplicativos) siempre que se deduzcan únicamente de los axiomas y sin usar hipótesis adicionales -/
end --group
section --abel
/- Permite demostrar identidades en grupos (aditivos) conmutativos siempre que se deduzcan únicamente de los axiomas y sin usar hipótesis adicionales -/
end --abel
section --field_simp
/- Permite simplificar identidades con denominadores en cuerpos -/

example (a b : ℝ) (h: a ≠ 0) (hyp : c/a = d * b) (hyp' : b = a^2) : c = d * a^3 := by
  field_simp at hyp
  rw [hyp, hyp']
  ring

end --field_simp
section --norm_num
/- Permite evaluar identidades numéricas en ℕ, ℤ, ℚ, ℝ o ℂ con las operaciones +, -, *, /, ^, %.
   También permite evaluar expresiones númericas de la forma A=B, A≠B, A < B, A ≤ B donde A y B son
   expresiones numéricas en algunos tipos más generales de estructuras algebraicas -/

variable {R : Type*} [Ring R]

example : 1 + 1 = (2 : R) := by
  norm_num

example : (2 : R) + 1 = (3 : R) := by
  norm_num

end --norm_num
section --calc
/- Permite hacer "cálculos" de forma ordenada -/

variable {R : Type*} [CommRing R]

example (a b: R): (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end --calc
section --linarith
/- Prueba desigualdades aritméticas lineales -/

example (a b d: ℝ ) (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

/- Si a ≤ b es una desigualdad no lineal, pero h: a ≤ b, entonces linarith [h] funcionará al mezclar
   dicha desigualdad con otras lineales. -/

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + 2 * exp b ≤ 3 * a + 2 * exp c := by
  linarith [exp_le_exp.mpr h'] -- exp_le_exp.mpr h' es una prueba de exp b ≤ exp c

end --linarith
section --apply?
/- Da sugerencias sobre como podría resolverse -/
end --apply?
section --repeat
/- "repeat" repite una demostración a todos los subcasos posibles hasta que falla en algún
   subcaso y entonces para.
   "repeat'" repite la demostración en cada subcaso, aunque haya fallado en uno anterior. -/

example (a b : ℝ): min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

end --repeat
section --use
/- Si queremos probar la existencia de cierto objeto y tenemos en mente que objeto lo cumple, la táctica
   "use" cambia el goal a probar que, en efecto, dicho objeto especificado cumple lo deseado -/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

/- Es posible darle demostraciones como entrada también. De hecho, automáticamente usa las
   hipótesis	disponibles -/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

/- También es posible dar el término de prueba (es decir, el término que tiene como tipo el teorema) -/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := -- No hay "by" porque no estamos usando tácticas, sino dando el término de prueba directamente
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

end --use
section --rcases

section -- Uso con el cuantificador existencial
/- Si una hipótesis tiene un cuantificador existencial, con rcases podemos definir un objeto que cumpla
   dicha hipótesis, así como la hipótesis que cumple -/

example : (∃ (a: ℝ), (∀ (b: ℝ), a < b)) → False := by
  intro h
  rcases h with ⟨a, ha⟩
  have h1: a < a := ha a
  apply lt_irrefl a
  exact h1

/- Puede utilizarse de forma directa para definir varios obtjetos si tenemos cuantificadores
   existenciales encadenados. Así, para esta definición -/

def SumOfSquares (x : ℤ) :=
  ∃ a b, x = a ^ 2 + b ^ 2

/- tenemos el siguiente resultado -/

example {x y : ℕ} (sosx : SumOfSquares x) (sosy : SumOfSquares y): SumOfSquares (x * y) := by
  rcases sosx with ⟨a, xeq1⟩
  rcases xeq1 with ⟨b, xeq⟩
  rcases sosy with ⟨c, yeq1⟩
  rcases yeq1 with ⟨d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d
  use a * d + b * c
  ring

/- que se escribe de forma más cómoda como: -/

example {x y : ℤ} (sosx : SumOfSquares x) (sosy : SumOfSquares y): SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

/- Dado que es muy habitual querer sustituir la fórmula obtenida tras eliminar un cuantificador
   existencial en el goal, existe la siguiente abreviatura: -/

example {x y : ℤ} (sosx : SumOfSquares x) (sosy : SumOfSquares y): SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

/- Observemos en el siguiente ejemplo que puede usarse con cualquier expresión (en este caso con h 2),
   no solo con hipótesis -/

example {f : ℝ → ℝ} (h : Function.Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

end -- Uso con el cuantificador existencial

section -- Uso con conjunción o bicondicional
/- También se utiliza para dividir una dividir una hipótesis de la forma h: A ∧ B o h: A ↔ B en dos -/

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

end -- Uso con conjunción o bicondicional

section -- Uso con la disyunción
/- Si tenemos que h: p ∨ q ∨ r ..., podemos dividir la demostración en varios casos, donde el nombre de
   la hipótesis	para cada caso lo dividimos con "|" -/

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right
    exact xgt

/- Es posible "encadenar" esta separación en casos y la particularización de un cuantificador existencial
   tal como se muestra en el siguiente ejemplo -/

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

/- Si estamos en una estructura inductiva, podemos dividir la demostración en un caso para cada "constructor"
   de la definción inductiva -/

def pred: Nat → Nat
  | 0 => 0
  | n + 1 => n

theorem pred_sub_one (n: ℕ) (ngez: 0 < n): pred n = n - 1 := by
  rcases n with _ | n
  · contradiction
  · rw [Nat.add_sub_assoc (le_refl 1), Nat.sub_self, add_zero, pred]

end -- Uso con la disyunción

end --rcases
section --obtain
/- Hace lo mismo que rcases, pero con otra sintaxis -/

example : (∃ (a: ℝ), (∀ (b: ℝ), a < b)) → False := by
  intro h
  obtain ⟨a, ha⟩  := h
  have h1: a < a := ha a
  apply lt_irrefl a
  exact h1

end --obtain
section --rintro
/- Es una combinación de intro + rcases -/

example : (∃ (a: ℝ), (∀ (b: ℝ), a < b)) → False := by
  rintro ⟨a, ha⟩
  have h1: a < a := ha a
  apply lt_irrefl a
  exact h1

end --rintro
section --let/set
/- Introduce una definición local a la prueba -/

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b aleb
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

/- "set a := t with h" añade el término a, pero también la hipótesis h: a = t y reemplaza t por a donde pueda
   "set a := t with ← h" hace lo mismo pero añade la hipótesis	h: t = a
   "set! a := t with h" hace lo mismo pero no reemplaza ninguna t-/

end --let/set
section --by_contra
/- "by_contra h" introduce la negación del goal como hipótesis h y cambia el goal a "false".
   Es importante en este punto tener en cuenta que "¬P" es equivalente a "P → False", por lo que
   cuando se tiene una hipótesis de esta forma se puede aplicar a "P" para obtener "False" -/

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h1
  apply h
  intro x
  by_contra h2
  have h3: ∃ x, ¬P x := by
    use x
  apply h1 h3

end --by_contra
section --push_neg
/- "push_neg (at h)" cambia el goal (o la hipótesis h) cuando esta comienza por una negación por una
   expresión equivalente con la negación "metida dentro" -/

variable (a: ℝ)

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

end --push_neg
section --simp/dsimp
/- "simp" simplifica el goal utilizando una serie de lemas preestablecidos (con atributo [simp]).

   "simp [h₁, ..., hκ ]" hace lo mismo que "simp", pero además también utiliza las expresiones dadas.
   Si alguna expresión es una definición, utilizará las ecuaciones asociadas, luego es una buena forma
   de "desentrañar" una definición.

   "simp [*]" utiliza los lemas preestablecidos y todas las hipótesis disponibles.

   "simp only [h₁, ..., hκ]" hace lo mismo que "simp [h₁, ..., hκ ]", pero no utiliza los lemas
   preestablecidos (con atributo [simp]).

   "simp ([l₁, ..., lμ]) at h₁ h₂ ... hκ" hace lo mismo que los anteriores pero con las hipótesis hi dichas.

   "simp ([l₁, ..., lμ]) at *" simplifica tanto las hipótesis como el goal

   "dsimp" hace lo mismo que "simp", pero únicamente utiliza teoremas que se cumplan por reflexividad,
   es decir, únicamente simplifica expresiones a otras definicionalmente equivalentes.-/

variable (a: ℝ)

def FnUb1 (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb1 (f : ℝ → ℝ) :=
  ∃ a, FnUb1 f a

example (h : ¬FnHasUb1 f) : ∀ a, ∃ x, f x > a := by
  dsimp [FnHasUb1, FnUb1] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb1 f) : ∀ a, ∃ x, f x > a := by
  simp [FnHasUb1, FnUb1] at h
  exact h

/- "simpa [h₁, ...] using e" intenta simplificar el goal y "e" con h₁,... y después intenta cerrar el
   goal con e -/

end --dsimp/simp
section --contrapose
/- Transforma un goal de la forma A → B a uno de la forma ¬B → ¬A.
   También, si queremos probar B y tenemos una hipótesis h: A, "contrapose h" pone como goal "¬ B" y
   como hiótesis h: ¬A.

   contrapose! hace lo mismo, pero también aplica push_neg al goal y las hipótesis-/

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  apply And.intro
  · linarith
  · linarith

end --contrapose
section --exfalso
/- Cambia el goal a "False" -/

example (h : 0 < 0) : (a: ℕ) > 37 := by
  exfalso
  apply lt_irrefl 0 h

end --exfalso
section --contradiction
/- Intenta finalizar la demostración buscando entre las hipótesis un par de la forma h: P y h': ¬P -/

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end --contradiction
section --constructor
/- Si el "goal" es de la forma A ∧ B o A ↔ B, divide la prueba en dos casos con goals A (A → B)
   y B (B → A) respectivamente

   Si se pone "<;>" tras "constructor" se le especifica que utilice el siguiente término
   en ambos goals a la vez-/

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · intro h
    constructor
    · exact h.left
    · intro h1
      rcases h with ⟨h2, h3⟩
      apply h3
      rw [h1]
  · intro h
    constructor
    · exact h.left
    · intro h1
      rcases h with ⟨h2, h3⟩
      apply h3
      apply le_antisymm h2 h1

end --constructor
section --left/right
/- Si el goal es una disyunción toma como nuevo goal la parte izquierda/derecha -/

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

end --left/right
section --ext
/- Permite demostrar que dos funciones son iguales viendo que toman los mismos valores en cada punto -/

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y
  ring

/- Permite también demostrar que dos conjuntos son iguales viendo que tienen los mismos elementos -/

variable {α : Type*}
variable (s t : Set α)
open Set

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩
    exact ⟨xs, xt⟩

end --ext
section --congr
/- Permite ver que dos expresiones son iguales viendo que las partes aparentemente diferentes son iguales -/

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

end --congr
section --convert
/- Intenta aplicar un teorema aunque no se ajuste concretamente y deja como nuevos goals las partes
   que necesita. Intenta técnicas de congruencia, viendo que puede "eliminar" o "incluir" que matenga las
   igualdades y permita utilizar el teorema dado -/

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).mpr h
  -- Ponemos la "_" como entrada del teorema porque no podemos/sabemos poner el argumetno exacto, pero
  -- lean lo rellenará por "unificación"
  · rw [one_mul]
  · exact lt_trans zero_lt_one h

/- En ocasiones al usar convert lean itera el algoritmo demasiadas veces dando goals imposibles de
   probar. Una posible solución es utilizar "using n" para limitar el número de iteraciones -/

example (h: Prime (2 * n + 1)) : Prime (n + n+ 1) := by
  convert h using 2
  ring

end --convert
section --change
/- change expr (at h) cambia el goal (o la hipótesis h) por expr siempre que sean iguales por definición -/
end --change
section --induction'
/- Permite realizar pruebas por inducción generando dos goals: el caso base sustituyendo la variable por cero y
   el paso inductivo donde podemos renombrar la variable y añadirá la hipótesis	de inducción con el nombre que
   se indique -/

theorem fac_pos (n : ℕ) : 0 < Nat.factorial n := by
  induction' n with m ih
  · rw [Nat.factorial]
    exact zero_lt_one
  · rw [Nat.factorial]
    exact mul_pos m.succ_pos ih

/- Para demostrar algo por inducción fuerte debemos usar la táctica:
   "induction' (variable) using Nat.strong_induction_on with (nombre variable) (nombre hip. inducción)" -/

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  rcases m with _ | m
  · contradiction
  · rcases m with _ | m
    · contradiction
    · repeat apply Nat.succ_le_succ
      apply zero_le

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

/- Existe también una táctica para demostrar que un resultado es cierto para conjuntos finitos arbitrarios.
   La inducción consiste en probar que es cierto para el conjunto vacío y que si es cierto para un conjunto finito
   cualquiera s, entonces lo es para s ∪ {a} con a ∉ s.
   "induction' s using Finset.induction_on with a s (nombre de la hipótesis a ∉ s) (hip. de inducción)"-/

open BigOperators
open Finset

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

end --induction'
section --symm
/- symm (at h) cambia el goal (o la hipótesis h) si es de la forma t ∼ u, con ∼ una relación simétrica, por
   u ∼ t -/
end --symm
section --interval_cases
/- "interval_cases n" busca cotas superiores e inferiores en la variable n, y si las encuentra, divide
   el goal en los posibles casos. -/

example (n : ℕ) (h₁ : n ≥ 3) (h₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  all_goals simp

/- Es posible especificarle las cotas superior e inferior a utilizar: interval_cases using hl, hu
   donde deben tener la forma hl : a ≤ n and hu : n < b -/

end --interval_cases
section --tauto
/- Intenta resolver tautologías lógicas -/

open Finset

variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

end --tauto
section --trans
/- Si el goal es de la forma a ∼ b, con ∼ una relación transitiva, entonces "trans s" cambia el goal
   por dos nuevos goals: "a ∼ s" y "s ∼ b" -/
end --trans
section --choose
/- Te permite "elegir" -/

example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
end --choose

end --Tacticas

section --Términos útiles
section --And.intro
/- Si h1: p y h2: q, entonces And.intro h1 h2 es una demostración de p ∧ q -/
end --And.intro
section --Iff.intro
/- Si h1: p → q, h2: q → p, entonces Iff.intro h1 h2 es una demostración de p ↔ q -/
end --Iff.intro
section --Or.inl/Or.inr
/- Si h: p (h: q), Or.inl h (Or.inr h) es una demostración de p ∨ q -/
end --Or.inl/Or.inr
section --left (right)
/- Si tenemos una demostración h: p ∧ q, entonces h.left: p y h.right: q -/

example (h: p ∧ q): p := by
  exact h.left

end --left (right)
section --mp (mpr)
/- Si tenemos una demostración h: p ↔ q, entonces h.mp: p → q y h.mpr: q → p -/

example (h: p ↔  q): q → p := by
  exact h.mpr

end -- mp (mpr)
section --absurd
/- Si tenemos h1: p y h2: ¬p, absurd h1 h2 es una demostración de cualquier término -/

example (h : 0 < 0) : (a: ℕ) > 37 :=
  absurd h (lt_irrefl 0)

end --absurd
section --em
/- "Excluded middle" - > em P: P ∨ ¬P -/

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

end --em
section --trivial
/- Prueba de "True" -/

example (x : ℕ) : x ∈ (Set.univ : Set ℕ) :=
  trivial

end --trivial
section --congr_arg
/- Permite pasar de "f: α → β" y "h: (a: α) = (b: β)" a "f a = f b" -/

example {G : Type} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
  have : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
    exact congr_arg (a⁻¹ * ·) h
  simpa

example {G : Type} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
  simpa using congr_arg (a⁻¹ * ·) h

end --congr_arg
end --Teoremas útiles

section  --Álgebra de números reales
/- Los mismos comandos sirven en general para grupos, anillos, etc. -/

variable (a b c: ℝ) -- Declara variables "fijas" a lo largo de la sección
variable (h1 : a + b = a + c)
variable (h2 : a + b = c + b)
variable (h3 : a + b = 0)

-- Conmutatividad
#check mul_comm a b -- a*b = b*a
#check add_comm a b -- a+b = b+a

-- Asociatividad
/- Nota sobre la asociatividad
Lean entiende que:
a+b+c = (a+b)+c
a+b+c+d = (a+b+c)+d = ((a+b)+c)+d -/
#check mul_assoc a b c -- a*b*c = a*(b*c)
#check add_assoc a b c -- a+b+c = a+(b+c)
#check add_sub a b c -- a+(b-c) = a+b-c
#check sub_sub a b c -- a-b-c = a-(b+c)

-- Distributividad
#check mul_add a b c -- a*(b+c) = a*b + a*c
#check add_mul a b c -- (a+b)*c = a*c + b*c
#check mul_sub a b c -- a*(b-c) = a*b - a*c
#check sub_mul a b c -- (a-b)*c = a*c - b*c

-- Potencias
#check two_mul a -- 2*a = a+a
#check pow_two a -- a^2 = a*a

-- Inversos y neutros
#check add_zero a -- a + 0 = a
#check zero_add a -- 0 + a = a
#check neg_add_cancel a -- -a + a = 0
#check add_neg_cancel a -- a + -a = 0
#check neg_add_cancel_left a b -- -a + (a + b) = b
#check add_neg_cancel_right a b -- a + b + -b = a
#check sub_eq_add_neg a b -- a - b = a + -b
#check neg_add a b -- -(a + b) = -a + -b
#check neg_add_eq_sub a b -- -a + b = b - a
#check (add_left_cancel h1 : b = c) -- Variables implícitas
#check (add_right_cancel h2 : a = c) -- Variables implícitas
#check sub_self a -- a - a = 0
#check mul_one a -- a * 1 = a
#check one_mul a -- 1 * a = a
#check mul_zero a -- a * 0 = 0
#check zero_mul a -- 0 * a = 0
#check (neg_eq_of_add_eq_zero_left h3)
#check (neg_eq_of_add_eq_zero_right h3)
#check (eq_neg_of_add_eq_zero_left h3)
#check (eq_neg_of_add_eq_zero_right h3)
#check (neg_zero)
#check neg_neg a -- --a = a
#check (mul_inv_cancel₀: a ≠ 0 → a * a⁻¹ = 1)
#check (inv_mul_cancel₀: a ≠ 0 → a⁻¹ * a = 1)
#check (div_eq_mul_inv a b: a / b = a * b⁻¹)

-- Valor absoluto

#check abs_add a b -- |a+b| ≤ |a| + |b|

end --Álgebra de números reales

section --Desigualdades en números reales

open Real
variable (a b c d e : ℝ)
variable (h: 0 < c)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm: a ≤ b → b ≤ a → a=b)
/- le_trans y le_antisymm no admiten variables de forma explícita, únicamente pruebas de a ≤ b (y después de b ≤ c o de b ≤ a)
IMPORTANTE:
Las implicaciones se asocian a la derecha: a ≤ b → b ≤ c → a ≤ c = a ≤ b → (b ≤ c → a ≤ c)-/

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check (sq_nonneg a)
#check (le_div_iff h)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

end --Desigualdades en números reales

section --Sobre lógica y definiciones

section --Cuantificador universal
/- Al definir un teorema con cuantificadores, si las variables se ponen entre paréntesis "()"
(o sin poner nada), entonces serán explícitas y se deben indicar al utilizar el teorema, pero si se
ponen entre llaves "{}", entonces son implícitas y no es posible "llamarlas" al usar la función
y será Lean quien las deducirá en base alas hipótesis.-/

theorem my_lemma1 : ∀ (x y ε : ℝ), 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma1 a b δ
#check my_lemma1 a b δ h₀ h₁
#check my_lemma1 a b δ h₀ h₁ ha hb

-- #check my_lemma1 h₀ h₁ -> Da error porque Lean no tiene suficiente información sobre cuales son las variables
#check my_lemma2 h₀ h₁ ha hb

-- Es posible desactivar las variables implícitas utilizando un "@"
#check @my_lemma2 a b δ

end --Cuantificador universal

section --Definiciones
/- Las definiciones se escriben como muestra el siguiente ejemplo -/

-- Cota superior de una función

def FnUB (f: ℝ → ℝ) (a: ℝ): Prop :=
  ∀ x, f x ≤ a

variable (f: ℝ → ℝ) (a: ℝ)

#check FnUB
#check FnUB f
#check FnUB f a

-- Así, si ahora por ejemplo podemos probar el siguiente teorema:
-- TEOREMA: Si a es cota superior de f y b es cota superior de g, entonces a+b es cota superior de f+g

theorem UB_of_f_add_g (hfa: FnUB f a) (hgb: FnUB g b): FnUB (fun x ↦ f x + g x) (a+b) := by
  intro x
  dsimp -- Simplifica la expresion de la función definida al evaluarla en x (siempre que sean iguales por definición)
  -- change f x + g x ≤ a + b
     /-Es otra forma de hacer lo mismo que antes, pero con mayor control sobre la salida.
       Es como rw pero solo aplicable a fórmulas iguales por definición-/
  apply add_le_add
  · rw [FnUB] at hfa
    apply hfa x
  · apply hgb x

#check UB_of_f_add_g

/- Las definiciones recursivas tienen la siguiente forma donde la primera línea es el caso
   base y la segunda el paso recursivo -/

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#check fac


end --Definiciones

end --Sobre lógica y definiciones

section --Conjuntos

section --Términos para conjuntos
variable {α : Type*}
variable (s t u : Set α)
open Set

#check subset_def
#check inter_def
#check union_def
#check mem_inter_iff
#check mem_union
#check Subset.antisymm
#check mem_iUnion
#check mem_iInter
#check mem_iUnion₂
#check mem_iInter₂
#check sUnion_eq_biUnion
#check sInter_eq_biInter

end --Términos para conjuntos
section --Funciones
open Set

-- Preimagen: Si f: α → β y p: Set β, entonces f ⁻¹' p = {x | f x ∈ p}
-- Imagen: Si f: α → β y s: Set α, entonces f '' s = {y | ∃ x, x ∈ s ∧ f x = y}

#check mem_image_of_mem
#check image_subset_iff

section --Función inversa (sin necesidad de conjuntos)

noncomputable section

variable {α β : Type*} [Inhabited α] [Nonempty β] -- "Inhabited α" hace que α sea no vacío y con un elemento destacado denominado "default"
variable (y: β)
variable (f : α → β)
open Classical
open Function

/- "Classical.choose h", donde "h: ∃ x, p x" (siendo p: α → Prop), escoge uno de los elementos
   x que satisfacen p (y lo denota por "choose h")

   "Classical.choose_spec h" con h como antes, es una demostración de "p (choose h)", es decir,
   Classical.choose_spec h: p (choose h) -/


def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h x
    rw [inverse]
    have h': ∃ z, f z = f x := by
      use x
    rw [dif_pos h']
    apply h
    exact Classical.choose_spec h'
  · intro h x y fxy
    simp [LeftInverse] at h
    calc
      x = inverse f (f x) := by
        exact (h x).symm
      _ = inverse f (f y) := by
        rw [fxy]
      _ = y := by
        exact h y

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    rw [inverse, dif_pos (h y)]
    exact Classical.choose_spec (h y)
  · intro h y
    dsimp [Function.RightInverse, LeftInverse] at h
    use inverse f y
    exact h y

-- Comandos preestablecidos en matlib para la inversa

#check invFun
#check (invFun f: β → α)
#check (leftInverse_invFun : Injective f → LeftInverse (invFun f) f)
#check (leftInverse_invFun : Injective f → ∀ x, invFun f (f x) = x)
#check (invFun_eq: (∃ x, f x = y) → f (invFun f y) = y)

end --Función inversa (sin necesidad de conjuntos)
end --Funciones

end --Conjuntos
