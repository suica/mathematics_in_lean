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
    exact inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · refine inf_le_of_left_le ?_
      apply inf_le_left
    . refine inf_le_inf_right z ?_
      apply inf_le_right
  · apply le_inf
    · refine inf_le_inf_left x ?_
      exact inf_le_left
    · refine inf_le_of_right_le ?_
      exact inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · exact le_sup_right'
    · exact SemilatticeSup.le_sup_left y x
  · apply sup_le
    · exact le_sup_right'
    · exact SemilatticeSup.le_sup_left x y

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    . refine sup_le_sup_left ?_ x
      exact SemilatticeSup.le_sup_left y z
    . refine le_sup_of_le_right ?_
      exact le_sup_right'
  · refine SemilatticeSup.sup_le x (y ⊔ z) (x ⊔ y ⊔ z) ?_ ?_
    · refine le_sup_of_le_left ?_
      exact SemilatticeSup.le_sup_left x y
    · refine sup_le_sup_right ?_ z
      exact le_sup_right'

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · apply le_refl
    · exact inf_le_left
  · apply le_sup_left

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
  rw [h, inf_comm _ a, inf_comm (a⊔b) c, h, h]
  simp
  rw [inf_comm c, inf_comm c, ← sup_assoc, absorb2]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm _ a, absorb2, sup_comm (a⊓b), h, ← inf_assoc, sup_comm c a, absorb1, sup_comm]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  conv =>
    congr
    rw [← sub_self a]
    . rw [sub_eq_add_neg, add_comm]
    . rw [sub_eq_add_neg, add_comm]
  apply add_le_add_left at h
  apply h

theorem hoho (h : a ≤ b) : 0 ≤ b - a := by
  simp
  exact h

theorem haha (h: 0 ≤ b - a) : a ≤ b := by
  simp at h
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  apply haha
  rw [← sub_mul]
  apply mul_nonneg
  apply hoho
  exact h
  exact h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h: dist x x ≤ dist x y + dist y x:=by
    apply dist_triangle
  simp [dist_self, dist_comm] at h
  exact h

end
