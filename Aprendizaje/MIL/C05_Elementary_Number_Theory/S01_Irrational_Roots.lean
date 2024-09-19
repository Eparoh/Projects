import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  Nat.Prime.eq_one_or_self_of_dvd prime_p

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

#check Nat.dvd_gcd
#check dvd_iff_exists_eq_mul_left

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have twodivm : 2 ∣ m := by
    apply even_of_even_sqr
    use n^2
  --rw [dvd_iff_exists_eq_mul_left] at twodivm
  rcases (dvd_iff_exists_eq_mul_left.mp twodivm) with ⟨k, meq⟩ -- Lo ponemos así para conservar "twodivm"
  --obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp twodivm
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    linarith
  have twodivn: 2 ∣ n := by
    apply even_of_even_sqr
    use k^2
    exact this.symm
  have : 2 ∣ m.gcd n := by
    exact Nat.dvd_gcd twodivm twodivn
  have : 2 ∣ 1 := by
    rw [coprime_mn] at this
    exact this
  norm_num at this

#check Nat.Prime.two_le
#check Nat.le_of_dvd
#check mul_pow

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have pdivm : p ∣ m := by
    have : p ∣ m^2 := by
      use n^2
    exact Nat.Prime.dvd_of_dvd_pow prime_p this
  rcases (dvd_iff_exists_eq_mul_left.mp pdivm) with ⟨k, meq⟩
  have : k^2 * p = n^2 := by
    rw [meq, mul_pow, mul_comm, pow_two, mul_assoc] at sqr_eq
    rw [mul_comm]
    apply (mul_right_inj' _).mp sqr_eq
    linarith [Nat.Prime.two_le prime_p]
  have pdivn : p ∣ n := by
    have : p ∣ n^2 := by
      use k^2
      linarith
    exact Nat.Prime.dvd_of_dvd_pow prime_p this
  have pdivgcdmn : p ∣ Nat.gcd m n := by
     exact Nat.dvd_gcd pdivm pdivn
  rw [coprime_mn] at pdivgcdmn
  have pgeq2 : 2 ≤ p := by
    exact Nat.Prime.two_le prime_p
  have : 0 < 1 := by
    linarith
  have pleq1 : p < 2 := by
    calc
      p ≤ 1 := by
        exact Nat.le_of_dvd this  pdivgcdmn
      _ < 2 := by
        linarith
  linarith

/- Generalización para raíces k-ésimas -/

#check Nat.exists_prime_and_dvd
#check dvd_mul_of_dvd_right
#check pow_add
#check pow_one
#check sub_self
#check Nat.add_sub_assoc
#check Nat.lt_one_iff

example {m n a k: ℕ} (coprime_mn : m.Coprime n) (knozero: k ≠ 0) (a_nopowk : ∀ (b: ℕ), a ≠ b^k) : m ^ k ≠ a * n ^ k := by
  rcases em (n = 1) with n_one | n_noone
  · rw [n_one, one_pow, mul_one]
    exact (a_nopowk m).symm
  · intro eq
    have := Nat.exists_prime_and_dvd n_noone
    rcases this with ⟨p, ⟨prime_p, pdivn⟩⟩
    have pdivm: p ∣ m := by
      have : p ∣ m^k := by
        rw [eq]
        apply dvd_mul_of_dvd_right _ a
        rcases pdivn with ⟨r, req⟩
        use p^(k-1) * r^k
        rw [req, mul_pow, ← mul_assoc]
        nth_rw 2 [← pow_one p]
        rw [← pow_add]
        have : k = 1 + (k-1) := by
          calc
            k = k + (1 - 1) := by
              have : 1 - 1 = 0 := by
                norm_num
              rw [this, add_zero]
            _ = 1 + (k-1) := by
              have: 1 ≤ k := by
                by_contra h
                push_neg at h
                rw [Nat.lt_one_iff] at h
                contradiction
              rw [← Nat.add_sub_assoc (le_refl 1) k, ← Nat.add_sub_assoc this 1, add_comm]
        rw [← this]
      apply Nat.Prime.dvd_of_dvd_pow prime_p this
    have pdivgcdmn: p ∣ m.gcd n := by
      exact Nat.dvd_gcd pdivm pdivn
    rw [coprime_mn] at pdivgcdmn
    have pgeq2 : 2 ≤ p := by
      exact Nat.Prime.two_le prime_p
    have : 0 < 1 := by
      linarith
    have pleq1 : p < 2 := by
      calc
        p ≤ 1 := by
          exact Nat.le_of_dvd this  pdivgcdmn
        _ < 2 := by
          linarith
    linarith

/- Fin -/

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique
#check List.Perm
#check Nat.factorization
#check Nat.Prime.factorization
#check Finsupp.single
#check Nat.Prime.ne_zero

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by
    simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [factorization_pow']
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul' (Nat.Prime.ne_zero prime_p) nsqr_nez, Nat.Prime.factorization' prime_p, factorization_pow', add_comm]
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

#check pow_eq_zero
#check Nat.mul_sub_left_distrib

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases em (r=0) with rez | rnez
  · rw [rez]
    simp
  · have npow_nz : n ^ k ≠ 0 := by
    --fun npowz ↦ nnz (pow_eq_zero npowz)
      intro npowz
      exact nnz (pow_eq_zero npowz)
    have eq1 : (m ^ k).factorization p = k * m.factorization p := by
      rw [factorization_pow']
    have eq2 : (r * n ^ k).factorization p =
      k * n.factorization p + r.factorization p := by
        rw [factorization_mul' rnez npow_nz, add_comm, factorization_pow']
    have : r.factorization p = k * (m.factorization p -  n.factorization p) := by
      calc
        r.factorization p = k * m.factorization p - k * n.factorization p := by
          rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
        _ = k * (m.factorization p -  n.factorization p) := by
          rw [Nat.mul_sub_left_distrib]
    use m.factorization p - n.factorization p

#check multiplicity
