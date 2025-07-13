import StoneDuality.DirSet
import StoneDuality.Dcpo
import StoneDuality.IdealCompletion

-- The aim of this file is to show that algebraic dcpos are exactly the ideal completions
-- of posets.
-- We first show that the dcpo of ideals is always algebraic. We do this by 
-- characterising the compact ideals of P as the downsets of elements of P, for which
-- we can show the appropriate properties to hold. Furthermore, since downsets correspond
-- to a unique top element, we also show that there is an order isomorphism between 
-- compact ideals of P and the elements of P.
-- Finally, we show that every algebraic dcpo is order isomorphic to the ideal completion
-- of its poset of compact elements.

namespace Order
namespace Dcpo

-- An element is called compact it is inaccessible by directed suprema.
-- That is to say, if an element x is covered by a directed set S,
-- it must already by below one of the elements of S.

def compact {P : Type*} [Dcpo P] (x : P) :=
  ∀ {S : Set P}, [Directed S] → x ≤ dir_sup S → ∃ s ∈ S, x ≤ s

def Compact (P) [Dcpo P] := { x : P | compact x }

-- We say that a dcpo is algebraic if downsets of compact elements below an element x
-- are directed and if their directed supremum is equal too x.

class AlgebraicDcpo (P) extends Dcpo P where

  compact_dir : ∀ x : P, Directed { k ≤ x | compact k }
  compact_dir_sup : ∀ x : P, x = dir_sup { k ≤ x | compact k }

section IdealCompletion

variable {P : Type*}
variable [PartialOrder P]

-- Downsets form compact ideals

theorem downset_ideal_compact (x : P) : compact (downset_ideal x) := by
  intro S D dxS
  simp at dxS
  rcases dxS with ⟨A, AS, xA⟩
  use A, AS
  simp
  use xA

-- Anticipating the downsets to be exactly the compact elements, we show that
-- the set of downsets below an ideal I has the required properties for algebracity.

-- The set of downsets below an ideal I is directed. 

instance (I : Ideal P) : Directed { downset_ideal x | x ∈ I } where
  IsNonempty := by
    rcases I.nonempty' with ⟨y, yI⟩
    use (downset_ideal y)
    simp
    use y, yI
  IsDirected := by
    rintro _ ⟨x, xI, rfl⟩ _ ⟨y, yI, rfl⟩
    rcases I.directed' x xI y yI with ⟨z, zI, xz, yz⟩
    use (downset_ideal z)
    simp
    constructor
    · use z, zI
    · exact ⟨xz, yz⟩

-- Every ideal is equal to the directed supremum of the downsets below it.

theorem ideal_le_dir_sup_dirset (I : Ideal P) : I ≤ dir_sup { downset_ideal x | x ∈ I } := by
  intro x xI
  simp
  use x, xI

theorem ideal_eq_dir_sup_dirset (I : Ideal P) : I = dir_sup { downset_ideal x | x ∈ I } := by
  apply le_antisymm
  · apply ideal_le_dir_sup_dirset
  · apply dir_sup_le
    intro J
    simp
    rintro x xI rfl
    simp
    exact xI

-- We show that every compact ideal is equal to the downset of one of its elements.
    
def compact_ideal_downset (I : Ideal P) (IC : compact I) : 
  ∃ x ∈ I, downset_ideal x = I := by
  rcases IC (ideal_le_dir_sup_dirset I) with ⟨_, ⟨x, xI, rfl⟩, Ix⟩
  use x, xI
  apply le_antisymm
  · simp
    exact xI
  · exact Ix

-- We characterise the compact ideals below an ideal I as exactly the downsets below it.

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
    apply xI
  · rintro ⟨x, xI, rfl⟩
    simp
    use xI
    exact downset_ideal_compact x

-- Using this characterisation and the properties established above, we show
-- that the dcpo of ideals is algebraic. 

instance instDcpoAlgDcpo : AlgebraicDcpo (Ideal P) where
compact_dir I := by
  rw [ compact_ideals_downsets I ]
  infer_instance
compact_dir_sup I := by
  simp_rw [ compact_ideals_downsets I ]
  exact ideal_eq_dir_sup_dirset I

-- Uniqueness of elements, corresponding to downsets. 

 def downset_ideal_injective : Function.Injective (fun x : P => downset_ideal x) := by
   intro x y xy
   have H := le_antisymm_iff.1 xy
   simp at H
   exact le_antisymm_iff.2 H

-- We construct the order isomorphism between P and the compact elements of its
-- ideal completion. For P -> Compact (Ideal P), we map x to the downset of x.
-- As for Compact (Ideal P) -> P, given a compact ideal I, we only have that there
-- merely exists a unique element x, such that I is equal to the downset of x.
-- We thus have to invoke unique choice to obtain the desired function.

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
    
end IdealCompletion

namespace AlgebraicDcpo

-- We now show that every algebraic dcpo is order isomorphic to to the ideal
-- completion of its poset of compact elements.

variable {A : Type*} [AlgebraicDcpo A]

-- To construct the map A -> Ideal (Compact A), we map x to the set of compact
-- elements below it, which can be shown to be an ideal.

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

-- To construct the map Ideal (Compact A) -> A, we want to send an ideal of
-- compact elements to its directed supremum. This works, since directedness of I
-- is independent of whether we consider it as a subest of Compact A or of A.
-- Here, we use a small hack. An ideal I in Compact A can be coerced to the 
-- type Set (Compact A), but not to Set A. However, Compact A itself has type
-- Set A, so we can use the construction below to coerce I to Set A.
-- We show that this coercion preserves directedness, as mentioned above. 

instance (Q : Set A) (S : Set Q) [D : Directed S] : 
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

-- Construction of the isomorphism

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
    simp
    symm
    exact (compact_dir_sup x)
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
