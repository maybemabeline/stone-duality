import Mathlib.Order.Hom.Basic
import StoneDuality.Dcpo
import StoneDuality.DirSet

namespace Order
namespace Dcpo

variable {P : Type*}

section Definition

variable {Q : Type*}
variable [Dcpo P] [Dcpo Q]
variable (f : P →o Q)

theorem dir_sup_image_le (S : Set P) [Directed S] : dir_sup (f '' S) ≤ f (dir_sup S) := by
  apply dir_sup_le
  rintro y ⟨x, xS, rfl⟩
  apply f.monotone'
  apply le_dir_sup
  exact xS

def scott_cont := ∀ {S : Set P}, [Directed S] → f (dir_sup S) ≤ dir_sup (f '' S)

theorem scott_cont_eq {f : P →o Q} (m : scott_cont f) (S : Set P) [Directed S] :
  f (dir_sup S) = dir_sup (f '' S) := by
  apply le_antisymm
  · apply m
  · apply dir_sup_image_le

end Definition

section DirsetImage

variable {Q : Type*}
variable [Preorder P] [Preorder Q]
variable (f : P →o Q)

def dirset_image_hom : DirSet P →o DirSet Q where
  toFun S := Directed.toDirSet (f '' S)
  monotone' := by 
    intro S T ST y
    simp
    rintro x xS rfl
    exists x
    use ST xS

theorem dirset_image_scott_cont : scott_cont (dirset_image_hom f) := by
  intro S D
  unfold dirset_image_hom
  intro y
  rintro ⟨x, H, rfl⟩
  simp at H
  rcases H with ⟨A, AS, xA⟩
  simp
  use A, AS, x, xA

end DirsetImage

section DirSup

variable [Dcpo P]

def dir_sup_mono (S T : Set P) [Directed S] :
  S ≤ T → {_ : Directed T} → dir_sup S ≤ dir_sup T := by
  intro ST D
  apply dir_sup_le
  intro x xS
  apply le_dir_sup
  exact ST xS

def dir_sup_hom : (DirSet P) →o  P where
  toFun := fun S => dir_sup S
  monotone' := by
    intro S T ST
    apply dir_sup_mono
    exact ST

theorem dir_sup_scott_cont : scott_cont (dir_sup_hom : DirSet P →o P) := by 
  intro S D
  apply dir_sup_le
  intro x xS
  simp at xS
  rcases xS with ⟨A, AS, xA⟩
  apply le_trans
  · apply le_dir_sup A
    exact xA
    infer_instance
  · apply le_dir_sup
    simp
    exists A

end DirSup
