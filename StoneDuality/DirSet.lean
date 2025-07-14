import Mathlib.Order.Hom.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Ideal
import Mathlib.Data.SetLike.Basic

variable {P : Type*}

namespace Order

@[ext]
structure DirSet (P) [LE P] where
  carrier : Set P
  nonempty' : carrier.Nonempty
  directed' : DirectedOn (· ≤ ·) carrier

class Directed [LE P] (A : Set P) where
  IsNonempty : A.Nonempty
  IsDirected : DirectedOn (· ≤ ·) A

namespace Directed

def toDirSet [LE P] (A : Set P) [D : Directed A] : DirSet P where
  carrier := A
  nonempty' := D.IsNonempty 
  directed' := D.IsDirected

def toIdeal [LE P] (A : Set P) [D : Directed A] (L : IsLowerSet A) : Ideal P where
  carrier := A
  nonempty' := D.IsNonempty
  directed' := D.IsDirected
  lower' := L

@[simp] lemma mem_toIDeal [LE P] (A : Set P) [Directed A] (L : IsLowerSet A) (x : P) :
  x ∈ (toIdeal A L) ↔ x ∈ A := Iff.rfl

end Directed

section Basic

variable [LE P]

instance instSetLIke : SetLike (DirSet P) P where
  coe s := s.carrier
  coe_injective' s t h := by
    cases t
    cases s
    congr

instance instPartialOrder : PartialOrder (DirSet P) :=
  PartialOrder.lift SetLike.coe SetLike.coe_injective

instance instDirectedDirSet (A : DirSet P) : (Directed (A : Set P)) where
  IsNonempty := A.nonempty'
  IsDirected := A.directed'

def SubsetDirSet {Q : Set P} (S : DirSet Q) : DirSet P where
  carrier := { x : P | ∃ y ∈ S, x = y }
  nonempty' := by
    rcases S.nonempty' with ⟨x, xS⟩
    use x
    simp
    exact xS
  directed' := by
    rintro _ ⟨x, xS, rfl⟩ _ ⟨y, yS, rfl⟩
    rcases S.directed' x xS y yS with ⟨z, zS, xz, yz⟩
    use z
    simp
    use zS

@[simp] lemma mem_SubsetDirset {Q : Set P} (S : DirSet Q) (x : P) : 
  x ∈ (SubsetDirSet S) ↔ ∃ y ∈ S, x = y := Iff.rfl
    
@[simp] lemma mem_toDirSet {A : Set P} (p : Directed A) (x : P) :
  x ∈ p.toDirSet ↔ x ∈ A := Iff.rfl

@[simp] lemma eq_toDirSet {A B : Set P} (p : Directed A) (q : Directed B) :
  p.toDirSet = q.toDirSet ↔ A = B := by
  unfold Directed.toDirSet
  simp

@[simp] lemma mem_carrier {S : DirSet P} {x : P}: x ∈ S.carrier ↔ x ∈ (S : Set P) := 
  Iff.rfl

@[simp] lemma carrier_eq_coe {S : DirSet P} : S.carrier = S := rfl

@[simp] lemma carrier_mem {S : Set P} {p : S.Nonempty} {q : DirectedOn (· ≤ ·) S} {x : P} : 
  x ∈ {carrier := S, nonempty' := p, directed' := q : DirSet P} ↔ x ∈ S := Iff.rfl

namespace Ideal

def toDirSet (I : Ideal P) : DirSet P where
  carrier := I.carrier
  nonempty' := I.nonempty'
  directed' := I.directed'

def toDirSet_hom : Ideal P →o DirSet P where
  toFun := toDirSet
  monotone' := by intro I J IJ; use IJ

@[simp] lemma mem_toDirSet {I : Ideal P} {x : P}: x ∈ toDirSet_hom I ↔ x ∈ (I : Set P) := Iff.rfl

instance instDirectedIdeal {I : Ideal P} : Directed (I : Set P) where
  IsNonempty := I.nonempty'
  IsDirected := I.directed'

end Ideal

end Basic

