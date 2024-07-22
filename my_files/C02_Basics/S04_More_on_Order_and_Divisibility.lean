import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  . apply max_le
    exact le_max_right b a
    exact le_max_left b a
  . apply max_le
    exact le_max_right a b
    exact le_max_left a b

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    apply le_trans
    apply min_le_left
    apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    · apply le_trans
      apply min_le_right
      apply le_refl
  · repeat
      apply le_min
      apply le_min
      apply min_le_left
      apply le_trans
      apply min_le_right
      apply min_le_left
      apply le_trans
      apply min_le_right
      apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h (a b c: ℝ): a ≤ b -> a + c ≤ b + c :=
    fun a_1 => add_le_add_right a_1 c
  . apply le_min
    apply h
    apply min_le_left
    apply h
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  . have h: min (a + c) (b + c) - c ≤ min a b := by
      conv =>
        rhs
        rw [← add_neg_cancel_right a c, ← add_neg_cancel_right b c]
      apply aux
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h: |a - b + b| ≤ |a - b| + |b| := by
    apply abs_add
  conv at h => simp
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  refine Nat.dvd_add ?h₁ ?h₂
  · refine Nat.dvd_add ?h₁.h₁ ?h₁.h₂
    · rw [mul_comm]
      ring_nf
      apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_left
      exact Nat.dvd_refl x
    · apply dvd_mul_of_dvd_left
      exact Dvd.intro_left (x.pow 0) rfl
  · refine Dvd.dvd.pow h ?h₂.x
    simp
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · apply dvd_gcd
    · exact Nat.gcd_dvd_right m n
    · exact Nat.gcd_dvd_left m n
  · apply dvd_gcd
    · exact Nat.gcd_dvd_right n m
    · exact Nat.gcd_dvd_left n m
end
