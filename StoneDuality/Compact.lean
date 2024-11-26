import StoneDuality.DirSet
import StoneDuality.Dcpo
import StoneDuality.IdealCompletion

namespace Order
namespace Dcpo

def compact {P : Type*} [Dcpo P] (x : P) :=
  ∀ {S : Set P}, [Directed S] → x ≤ dir_sup S → ∃ s ∈ S, x ≤ s

def Compact (P) [Dcpo P] := { x : P | compact x }

class AlgebraicDcpo (P) extends Dcpo P where

  compact_dir : ∀ x : P, Directed { k ≤ x | compact k }
  compact_dir_sup : ∀ x : P, x = dir_sup { k ≤ x | compact k }

section IdealCompletion

variable {P : Type*}
variable [PartialOrder P]

theorem downset_ideal_compact (x : P) : compact (downset_ideal x) := by
  intro S D dxS
  simp at dxS
  rcases dxS with ⟨A, AS, xA⟩
  use A, AS
  simp
  use xA
    
def compact_ideal_downset (I : Ideal P) (IC : compact I) : 
  ∃ x ∈ I, downset_ideal x = I := by
  rcases IC (ideal_le_dir_sup_dirset I) with ⟨_, ⟨x, xI, rfl⟩, Ix⟩
  use x, xI
  apply le_antisymm
  · simp
    exact xI
  · exact Ix

def compact_ideals_downsets (I : Ideal P) : 
  { K ≤ I | compact K } = { downset_ideal x | x ∈ I } := by
  ext J
  simp
  constructor
  · rintro ⟨JI, JC⟩
    obtain ⟨x, xI, rfl⟩ := compact_ideal_downset J JC 
    use x
    simp
    apply JI
    simp
  · rintro ⟨x, xI, rfl⟩
    simp
    use xI
    exact downset_ideal_compact x

 def downset_ideal_injective : Function.Injective (fun x : P => downset_ideal x) := by
   intro x y xy
   have H := le_antisymm_iff.1 xy
   simp at H
   exact le_antisymm_iff.2 H

 noncomputable
 def compact_ideal_iso : P ≃o Compact (Ideal P) where
  toFun := fun x => ⟨downset_ideal x, downset_ideal_compact x⟩
  invFun := fun ⟨I, IC⟩ => (compact_ideal_downset I IC).choose
  left_inv := by
    intro x
    simp
    apply downset_ideal_injective
    exact (compact_ideal_downset (downset_ideal x) (downset_ideal_compact x)).choose_spec.2
  right_inv := by
    rintro ⟨I, IC⟩
    simp
    exact (compact_ideal_downset I IC).choose_spec.2
  map_rel_iff' := by simp

instance instDcpoAlgDcpo : AlgebraicDcpo (Ideal P) where
  compact_dir I := by
    rw [ compact_ideals_downsets I ]
    apply dirset_ideal
  compact_dir_sup I := by
    nth_rewrite 1 [ ideal_eq_dir_sup_dirset I]
    congr
    symm
    exact compact_ideals_downsets I

end IdealCompletion

namespace AlgebraicDcpo

variable {A : Type*} [AlgebraicDcpo A]

def compact_downset_ideal (x : A) : Ideal (Compact A) where
  carrier := { k | k ≤ x }
  lower' := by
    intro k t tk
    simp
    intro kx
    exact le_trans tk kx
  nonempty' := by
    simp
    rcases (compact_dir x).IsNonempty with ⟨y, yx, yk⟩
    use ⟨y, yk⟩
    exact yx
  directed' := by
    intro k kx t tx
    have H := (compact_dir x).IsDirected k.val ⟨kx, k.prop⟩ t.val ⟨tx, t.prop⟩
    rcases H with ⟨z, ⟨zx, zC⟩, kz, tz⟩
    use ⟨z, zC⟩
    simp
    use zx, kz, tz

instance instSubsetDirected (Q : Set A) (S : Set Q) [D : Directed S] : 
  Directed { x : A | ∃ y ∈ S, x = y } where
  IsNonempty := by
    rcases D.IsNonempty with ⟨x, xS⟩
    use x
    simp
    exact xS
  IsDirected := by
    rintro _ ⟨x, xS, rfl⟩ _ ⟨y, yS, rfl⟩
    rcases D.IsDirected x xS y yS with ⟨z, zS, xz, yz⟩
    use z
    simp
    use zS, xz, yz
  
def ideal_compact_iso : Ideal (Compact A) ≃o A where
  toFun := fun I => dir_sup { x : A | ∃ y ∈ I, x = y }
  invFun := fun x => compact_downset_ideal x
  left_inv := by
    intro I
    ext x
    constructor
    · unfold compact_downset_ideal
      intro xI
      obtain ⟨_, ⟨s, sI, rfl⟩, xs⟩ := x.prop xI
      exact I.lower' xs sI
    · intro xI
      apply le_dir_sup
      simp
      exact xI
  right_inv := by
    intro x
    unfold compact_downset_ideal
    nth_rewrite 2 [ compact_dir_sup x ]
    simp
    rfl
  map_rel_iff' := by
    intro I J
    constructor
    · intro IJ
      intro x xI
      have H := le_dir_sup { x : A | ∃ y ∈ I, x = y }
      specialize H x ⟨x, xI, rfl⟩
      · infer_instance
      obtain ⟨_, ⟨y, yJ, rfl⟩, xy⟩ := x.prop (le_trans H IJ)
      exact J.lower' xy yJ
    · intro IJ
      apply dir_sup_mono
      rintro _ ⟨x, xI, rfl⟩
      use x
      simp
      exact IJ xI
