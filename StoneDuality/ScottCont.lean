import Mathlib.Order.Hom.Basic
import StoneDuality.Dcpo
import StoneDuality.DirSet

-- Definition of Scott continuity of monotone maps between dcpos. 
-- We establish the scott continuity of two maps:
-- Firstly, given a monotone map f : P -> Q between preorders, it induces a monotone map
-- between the dcpos of directed subsets of P and Q, given by the image. This
-- map is shown to be Scott continuous.
-- Secondly, given a dcpo P, the operation of taking the directed supremum itself
-- forms a monotone map between the dcpo of directed subsets of P and P. This
-- map too is shown to be Scott continuous.


namespace Order
namespace Dcpo

variable {P : Type*}

section Image

variable {Q : Type*}
variable [Preorder P] [Preorder Q]
variable (f : P →o Q)

-- In order to be able to speak about Scott continuity, we first establish
-- that taking the image with a monotone map preserves directedness.

instance dirset_image (S : Set P) [D : Directed S] : Directed (f '' S) where
  IsNonempty := by
    simp
    rcases D.IsNonempty with ⟨x, xS⟩
    use x, xS
  IsDirected := by
    rintro z ⟨x, xS, rfl⟩ w ⟨y, yS, rfl⟩
    rcases D.IsDirected x xS y yS with ⟨u, uS, xu, yu⟩
    use (f u)
    constructor
    · exact Set.mem_image_of_mem f uS
    · exact ⟨f.monotone' xu, f.monotone' yu⟩

end Image

section Definition

variable {Q : Type*}
variable [Dcpo P] [Dcpo Q]
variable (f : P →o Q)

-- Definition of Scott continuity; a map between dcpos is said to be Scott continuous if it
-- preserves directed suprema.

def scott_cont := ∀ {S : Set P}, [Directed S] → f (dir_sup S) ≤ dir_sup (f '' S)

-- Proof that opposite inequality always holds

theorem scott_cont_eq {f : P →o Q} (m : scott_cont f) (S : Set P) [Directed S] :
  f (dir_sup S) = dir_sup (f '' S) := by
  apply le_antisymm
  · apply m
  · apply dir_sup_le
    rintro y ⟨x, xS, rfl⟩
    apply f.monotone'
    apply le_dir_sup
    exact xS

end Definition

section DirsetImage

variable {Q : Type*}
variable [Preorder P] [Preorder Q]
variable (f : P →o Q)

-- As established above, taking the image with a monotone map preserves
-- directedness. This induces a Scott continuous monotone map between the 
-- dcpos of directed sets.

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

-- The operation of directed supremum is monotone under subset inclusion.

def dir_sup_mono (S T : Set P) [Directed S] :
  S ≤ T → {_ : Directed T} → dir_sup S ≤ dir_sup T := by
  intro ST D
  apply dir_sup_le
  intro x xS
  apply le_dir_sup
  exact ST xS

-- The operation of directed supremum induces a Scott continuous monotone
-- map between the dcpo of directed sets of P and P.

def dir_sup_hom : (DirSet P) →o P where
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
