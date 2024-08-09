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

#check even_of_even_sqr
#check Nat.dvd_gcd

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    -- rw [pow_two, pow_two] at sqr_eq
    refine even_of_even_sqr ?h
    exact Dvd.intro (n ^ 2) (id (Eq.symm sqr_eq))

  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have hihi: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have hoho: 2 * k ^ 2 = n ^ 2 :=
    (mul_right_inj' (show 2≠ 0 by linarith)).mp hihi

  have haha: 2 ∣ n := by
    apply even_of_even_sqr
    exact Dvd.intro (k ^ 2) hoho

  have cao: 2 ∣ m.gcd n := by
    exact Nat.dvd_gcd this haha
  have : 2 ∣ 1 := by
    exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod coprime_mn) m) this).mp cao
  norm_num at this

#check Nat.le_of_dvd

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  by_contra h
  have haha: m ^ 2 ∣ p * n^2 := by
    exact dvd_of_eq h
  have h' : m ∣ p * n ^ 2 := by
    exact Dvd.intro_left (m.pow 1) h
  have coprime_mnsq: m.Coprime (n^2):= by
    exact Nat.Coprime.pow_right 2 coprime_mn
  have coprime_msqnsq: (m^2).Coprime (n^2):= by
    exact Nat.Coprime.pow 2 2 coprime_mn
  rw [h] at coprime_msqnsq
  let haha := coprime_msqnsq.gcd_eq_one
  #check haha
  conv at haha =>
    lhs
    rhs
    rw [← Nat.one_mul (n^2)]

  rw [Nat.gcd_mul_right, ] at haha
  have : p.gcd 1 = 1:= by
    exact Nat.gcd_one_right p
  rw [this] at haha
  simp at haha
  rw [haha] at h
  simp at h
  have : ¬p.Prime := by
    rw [← h]
    refine Nat.Prime.not_prime_pow' ?hn
    simp
  apply this
  exact prime_p

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

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
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    exact factorization_pow' m 2 p
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [Nat.factorization_mul, Nat.Prime.factorization]
    rw [add_comm]
    simp
    assumption
    exact Nat.Prime.ne_zero prime_p
    exact nsqr_nez

  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    exact factorization_pow' m k p
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    simp
    rw [Nat.factorization_mul, add_comm]
    simp
    exact Ne.symm (Nat.zero_ne_add_one r)
    exact npow_nz
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  refine Nat.dvd_sub' ?succ.h₁ ?succ.h₂
  exact Nat.dvd_mul_right k (m.factorization p)
  exact Nat.dvd_mul_right k (n.factorization p)

#check multiplicity
