import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt

  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  simp at *
  rintro h a afs
  rcases afs with ⟨a', ⟨a's, faeqa⟩⟩
  exact mem_of_eq_of_mem (id (Eq.symm faeqa)) (h a's)

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨w, ⟨ws, fwfx⟩⟩
  rw [← h fwfx]
  assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro a ⟨w, ⟨wfu, fwa⟩⟩
  simp at *
  rw [fwa] at wfu
  exact wfu


example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro a au
  simp at *
  rcases h a with ⟨x, fxa⟩
  use x
  constructor
  . rw [← fxa] at au
    exact au
  . exact fxa

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro a ⟨w, ⟨ws, fwa⟩⟩
  simp at *
  apply h at ws
  use w, ws

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro a b
  apply h
  exact b

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext a
  constructor
  · simp at *
  · simp at *

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro a ⟨w,⟨wsn, fwa⟩⟩
  simp at *
  constructor
  · use w, wsn.left
  · use w, wsn.right

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro a ⟨b, c, d⟩
  simp at *
  rcases b with ⟨w, ⟨ws, fwa⟩⟩
  use w
  constructor
  · constructor
    exact ws
    have h'': f w = f c :=
      calc f w
        _ = a := fwa
        _ = f c := Eq.symm d.right
    rw [← h h''] at d
    exact d.left
  · exact fwa

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro a ⟨l, r⟩
  simp at *
  rcases l with ⟨w, ⟨ws, fwa⟩⟩
  use w
  constructor
  · constructor
    exact ws
    by_cases h: w ∈ t
    · apply r at h
      contradiction
    · exact h
  · exact fwa

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro a ⟨l, r⟩
  simp at *
  exact ⟨l, r⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext a
  constructor
  · rintro ⟨l, r⟩
    simp at *
    rcases l with ⟨w, ⟨ws, fwa⟩⟩
    use w
    constructor
    · constructor
      exact ws
      rw [fwa]
      exact r
    · exact fwa
  · rintro ⟨w, ⟨⟨ws, h⟩, fla⟩⟩
    simp at *
    constructor
    · use w, ws
    · rw [← fla]
      exact h


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro a ⟨w, ⟨⟨ws, fwu⟩, fwa⟩⟩
  simp at *
  constructor
  · use w
  · rw [← fwa]
    use fwu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro a ⟨as, fau⟩
  simp at *
  constructor
  · use a
  · use fau

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro a (⟨as⟩ | h)
  simp at *
  · left
    use a
  · simp at *
    right
    use h


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext a
  simp at *
  constructor
  · rintro ⟨w, ⟨h, fwa⟩⟩
    rcases h with ⟨i, wai⟩
    use i, w
  · rintro ⟨i, ⟨w, ⟨wai, fwa⟩⟩⟩
    use w
    constructor
    · use i
    · use fwa

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro h
  simp at *
  rintro a b fah i
  apply b at i
  use a

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro b h
  simp at *
  rcases h with i
  rcases h i with ⟨w, ⟨wai, fwb⟩⟩
  use w
  constructor
  · intro i'
    rcases h i' with ⟨w', ⟨w'ai, fwb'⟩⟩
    have h': f w' = f w := by
      rw [← fwb] at fwb'
      exact fwb'
    rw [← injf h']
    exact w'ai
  · use fwb

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext a
  simp at *

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext a
  simp at *

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro h
  calc x
    _ = √x * √x := by exact Eq.symm (mul_self_sqrt xpos)
    _ = √y * √y := by exact abs_eq_iff_mul_self_eq.mp (congrArg abs h)
    _ = y := by exact mul_self_sqrt ypos



example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  intro h
  dsimp at h
  simp at *
  apply sq_eq_sq_iff_eq_or_eq_neg.mp at h
  rcases h with a | b
  use a
  rw [b] at xpos
  linarith

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext a
  constructor
  simp at *
  · intro x xge h
    rw [← h]
    exact sqrt_nonneg x
  · simp at *
    intro age
    use a^2
    constructor
    exact sq_nonneg a
    exact sqrt_sq age

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  · simp at *
    intro a h
    rw [← h]
    exact sq_nonneg a
  · simp at *
    intro h
    use √x
    exact sq_sqrt h

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · rintro injf x
    #check injf
    done
  · done

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
