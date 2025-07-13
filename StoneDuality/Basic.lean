import Mathlib.Order.Ideal
import Mathlib.Order.Hom.Basic

namespace Order

variable {P : Type*}

section Downset

variable [Preorder P]

def downset (x : P) := { y : P | y ≤ x }

instance downset_ideal (x : P) : Ideal P where
  carrier := downset x
  lower' := by 
    intro y z zy
    unfold downset; simp
    apply le_trans
    exact zy
  nonempty' := by
    use x
    unfold downset; simp
  directed' := by
    intro y yx z zx
    use x
    unfold downset
    simp
    use yx, zx

@[simp] lemma carrier_mem_ideal {S : Set P} {p : S.Nonempty} 
  {q : DirectedOn (· ≤ ·) S} {r : IsLowerSet S} {x : P} : 
  x ∈ {carrier := S, nonempty' := p, directed' := q, lower' := r : Ideal P} ↔ x ∈ S := Iff.rfl

@[simp] lemma mem_downset_ideal (x y : P) : y ∈ (downset_ideal x) ↔ y ∈ (downset x) := by
  unfold downset_ideal
  simp

@[simp] lemma mem_downset (x y : P) : y ∈ (downset x) ↔ y ≤ x := by 
  unfold downset
  simp

@[simp] lemma le_downset_ideal (x : P) (I : Ideal P) : 
  (downset_ideal x) ≤ I ↔ (downset x) ≤ I := by
  unfold downset_ideal
  apply Iff.rfl

@[simp] lemma downset_le (x : P) (I : Ideal P) : (downset x) ≤ (I : Set P)  ↔ x ∈ I := by
  constructor
  · intro xI
    apply xI
    simp
  · intro xI
    intro z
    simp
    intro zx
    apply I.lower'
    · exact zx
    · exact xI

end Downset
