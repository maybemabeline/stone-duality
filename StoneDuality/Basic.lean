import Mathlib.Order.Ideal
import Mathlib.Order.Hom.Basic

namespace Order

variable {P : Type*}

section Downset

variable [Preorder P]

def downset (x : P) := { y : P | y ≤ x }

instance downsetTop (x : P) : OrderTop (downset x) where
  top := by use x; unfold downset; simp
  le_top := by unfold downset; simp

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
    have H : IsDirected (downset x) (· ≤ ·) := inferInstance
    intro y yx z zx; simp
    have H1 := H.directed; simp at H1
    rcases H1 y yx z zx with ⟨z, zx⟩
    exists z
    apply and_assoc.1
    exact zx


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

@[simp] lemma le_downset (x : P) (I : Ideal P) : (downset x) ≤ I  ↔ x ∈ I := by
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
    
theorem mono_downset : Monotone (fun x : P => downset_ideal x) := by
  intro x y xy
  simp
  assumption

def downset_hom : P →o Ideal P where
  toFun := downset_ideal
  monotone' := mono_downset

end Downset
