import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n h
  have ngens := le_of_max_le_left h
  have ngent := le_of_max_le_right h
  have : |t n - b| + |s n - a| < ε / 2 + ε / 2  := by
    apply add_lt_add (ht n ngent) (hs n ngens)
  have h': |t n - b| + |s n - a| < ε := by
    convert this
    linarith
  have : |(t n - b) + (s n - a)| <= |t n - b| + |s n - a| := by
    apply abs_add
  have h'': |(t n - b) + (s n - a)| < ε := by
    exact lt_of_le_of_lt this h'
  have: |s n  + t n - (a + b)| = |(t n - b) + (s n - a)|:= by
    congr
    ring
  rw [this]
  exact h''

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  . have acpos : 0 < |c| := abs_pos.mpr h
    intro e egt0
    have : e/|c| > 0 := by
      exact div_pos egt0 acpos
    rcases cs (e/|c|) this with ⟨n₀, h''⟩
    use n₀
    intro n ngen0
    dsimp
    apply h'' at ngen0
    have := (mul_lt_mul_right acpos).mpr ngen0
    simp [mul_comm] at this
    rw [mul_div_cancel₀] at this
    have h: |c * s n - c * a| ≤ |c| * |s n - a| := by
      simp [← mul_sub]
      rw [abs_mul]

    linarith
    exact abs_ne_zero.mpr h


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  have h' := h _ nge
  have : |s n| - |a| ≤ |s n - a|:= by
    exact abs_sub_abs_le_abs_sub (s n) a
  have := lt_of_le_of_lt this h'
  simp [sub_eq_add_neg, add_comm, add_lt_add] at this
  exact this

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use (max N₁ N₀)
  intro n nge
  have nge1 := le_of_max_le_left nge
  have nge0 := le_of_max_le_right nge
  have h₃ := h₀ _ nge0
  have h₄ := h₁ _ nge1
  simp
  simp at h₄
  have h: |s n| * |t n| < B * (ε / B) := by
    exact mul_lt_mul'' h₃ h₄ (abs_nonneg _) (abs_nonneg _)
  have h' : |s n * t n| ≤ |s n| * |t n| := by
    rw [abs_mul]
  apply lt_of_le_of_lt h'
  rw [mul_div_cancel₀] at h
  exact h
  linarith

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    simp
    exact sub_ne_zero_of_ne abne
    done
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have NgeNa: N ≥ Na := by
      exact Nat.le_max_left Na Nb
    apply hNa N NgeNa
  have absb : |s N - b| < ε := by
    have NgeNb: N ≥ Nb := by
      exact Nat.le_max_right Na Nb
    apply hNb N NgeNb
  have : |a - b| < |a - b| := by
    have h₀: |s N - a| + |s N - b| ≥ |s N - a - (s N - b)| := by
      exact abs_sub (s N - a) (s N - b)
    have h₁: |s N - a - (s N - b)| = |a-b| := by
      simp
      exact abs_sub_comm b a
    have h₃ : |s N - a| + |s N - b| < ε + ε := by
      apply add_lt_add
      exact absa
      exact absb
    rw [h₁] at h₀
    apply lt_of_le_of_lt h₀
    have: ε+ε = |a-b|:= by ring
    rw [← this]
    exact h₃


  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
