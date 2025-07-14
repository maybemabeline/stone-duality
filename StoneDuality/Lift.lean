import StoneDuality.Dcpo
import StoneDuality.ScottCont
import StoneDuality.IdealCompletion
import StoneDuality.DirSet
import StoneDuality.Compact
import StoneDuality.Basic
import Mathlib.Order.Hom.Lattice

-- In this file, we establish freeness properties of the ideal completion. 
-- We show that the ideal completion of a partial order P forms the free
-- dcpo over P. This establishes an adjunction between the category of partial
-- orders and monotone maps and the category of dcpos and Scott continuous maps.
-- Next, we show that the ideal completion of a semilattice with binary infima P
-- forms the free dcpo with binary infima over P. This establishes an adjunction
-- between the category of semilattices and semilattice homomorphisms and the
-- category of dcpos with binary infima and Scott continuous semilattice homomorphisms.

namespace Order
namespace Dcpo
variable {P : Type*}

section PartOrd

variable [PartialOrder P]

-- The unit of the adjunction is given by mapping each element x to the downset of x.

def downset_hom : P →o Ideal P where
  toFun := downset_ideal
  monotone' := by
    intro x y xy
    simp
    assumption

variable {Q : Type*} [Dcpo Q]
variable (f : P →o Q)

-- Given a monotone map f : P -> Q from a partial order P to a dcpo Q,
-- it lifts to a unique Scott continuous map from the ideal completion of P to Q.
-- The lift is given by mapping an ideal I to the directed supremum
-- of its image under f. This works since f preserves directedness
-- and directed suprema exist in Q.

def ideal_lift : Ideal P → Q := fun I => dir_sup (f '' I)

def ideal_lift_hom : (Ideal P) →o Q where
  toFun := ideal_lift f
  monotone' := by
    intro I J IJ
    unfold ideal_lift
    apply dir_sup_mono
    apply Set.image_mono
    use IJ

theorem ideal_lift_scott_cont : scott_cont (ideal_lift_hom f) := by
  intro S D
  unfold ideal_lift_hom; unfold ideal_lift
  simp
  apply le_trans
  · apply dir_sup_mono
    apply dirset_image_scott_cont
    infer_instance
  apply le_trans
  · apply dir_sup_scott_cont
  repeat simp_rw [ Set.image_image ]
  rfl

-- The lifting of f is in fact a lift of f along the unit map.

theorem ideal_lift_comm : f = (ideal_lift_hom f) ∘ downset_hom := by
  funext x
  unfold downset_hom; unfold ideal_lift_hom; unfold ideal_lift
  simp
  apply le_antisymm
  · apply le_dir_sup
    apply Set.mem_image_of_mem
    simp
  · apply dir_sup_le
    simp
    intro y yx
    exact f.monotone' yx

-- If two Scott continuous maps agree on the image of the unit map, they are equal.

theorem downset_hom_epi_scott_cont {h g : Ideal P →o Q} (m : scott_cont h) (n : scott_cont g) :
  g ∘ downset_hom = h ∘ downset_hom → g = h := by
  intro p
  ext I
  rw [ ideal_eq_dir_sup_dirset I, scott_cont_eq n, scott_cont_eq m]
  congr
  ext y
  simp
  apply exists_congr
  simp
  intro x xI
  apply Eq.congr
  apply congrFun p
  rfl

-- As a corrollary, we obtain the uniqueness of the lifting of f.
    
theorem ideal_lift_unique {g : Ideal P →o Q} (m : scott_cont g) : 
  g ∘ downset_hom = f → g = ideal_lift_hom f := by
  intro p
  apply downset_hom_epi_scott_cont
  · exact ideal_lift_scott_cont f
  · exact m
  · rw [ p ]
    apply ideal_lift_comm

end PartOrd

section InfLat

namespace InfDcpo

-- We now aim to show that given a semilattice homomorphism f : P -> Q from
-- a semilattice to a dcpo with binary infima, it lifts to a unique Scott
-- continuous semilattice homomorphism between the ideal completion of P and Q.
-- Since preserving binary infima is only an additional property of the map, the
-- uniqueness of the lift and the appropriate commutative triangle follow
-- from the properties established above. We only have to establish that
-- the lifting preserves binary infima.

variable [SemilatticeInf P]
variable {Q : Type*} [InfDcpo Q]
variable (f : InfHom P Q)

-- The unit map preserves binary infima.

def downset_inf : InfHom P (Ideal P) where
  toFun := downset_ideal
  map_inf' := by
    intro x y
    ext z
    simp
    constructor
    · rintro ⟨zx , zy⟩
      use zx, zy
    · rintro ⟨zx, zy⟩
      use zx, zy

-- Since instance resolution in Lean is not stable under rewriting, we
-- have to establish the directedness of several equal sets by hand. This
-- is a little janky, but I don't know how else to work with it.

section instanceLemmas

variable (S T : Set Q) [D : Directed S] [E : Directed T]

instance : Directed { x ⊓ y | (x ∈ S) (y ∈ T) } where
  IsNonempty := by
    obtain ⟨x, xS⟩ := D.IsNonempty
    obtain ⟨y, yT⟩ := E.IsNonempty
    use x ⊓ y
    simp
    use x, xS, y, yT
  IsDirected := by
    rintro _ ⟨x1, x1S, y1, y1T, rfl⟩
    rintro _ ⟨x2, x2S, y2, y2T, rfl⟩
    simp
    obtain ⟨z, zS, x1z, x2z⟩ := D.IsDirected x1 x1S x2 x2S
    obtain ⟨w, wT, y1w, y2w⟩ := E.IsDirected y1 y1T y2 y2T
    use z, zS, w, wT
    constructor
    · constructor
      · exact le_trans inf_le_left x1z
      · exact le_trans inf_le_right y1w
    · constructor
      · exact le_trans inf_le_left x2z
      · exact le_trans inf_le_right y2w

instance : Directed { dir_sup { x ⊓ y | x ∈ S } | y ∈ T } where
  IsNonempty := by
    obtain ⟨y, yT⟩ := E.IsNonempty
    use dir_sup { x ⊓ y | x ∈ S }
    simp
    use y, yT
  IsDirected := by
    rintro _ ⟨x, xT, rfl⟩ _ ⟨y, yT, rfl⟩
    obtain ⟨z, zT, xz, yz⟩ := E.IsDirected x xT y yT
    simp
    use z, zT
    constructor
    · apply dir_sup_le_dir_sup
      rintro _ ⟨w, wS, rfl⟩
      simp
      use w, wS
      constructor
      · exact inf_le_left
      · exact le_trans inf_le_right xz
    · apply dir_sup_le_dir_sup
      rintro _ ⟨w, wS, rfl⟩
      simp
      use w, wS
      constructor
      · exact inf_le_left
      · exact le_trans inf_le_right yz

instance : Directed  (⋃₀ { { x ⊓ y | x ∈ S } | y ∈ T }) where
  IsNonempty := by
    simp
    obtain ⟨y, yT⟩ := E.IsNonempty
    use y, yT
    obtain ⟨x, xS⟩ := D.IsNonempty
    use x ⊓ y
    simp
    use x, xS
  IsDirected := by
    rintro _ U1 _ U2
    simp at U1; simp at U2
    rcases U1 with ⟨y1, y1T, x1, x1S, rfl⟩
    rcases U2 with ⟨y2, y2T, x2, x2S, rfl⟩
    simp
    obtain ⟨z, zS, x1z, x2z⟩ := D.IsDirected x1 x1S x2 x2S
    obtain ⟨w, wT, y1w, y2w⟩ := E.IsDirected y1 y1T y2 y2T
    use w, wT, z, zS
    constructor
    · constructor
      · exact le_trans inf_le_left x1z
      · exact le_trans inf_le_right y1w
    · constructor
      · exact le_trans inf_le_left x2z
      · exact le_trans inf_le_right y2w

end instanceLemmas

-- Further lemmas about constructions involving directed suprema

lemma dir_sup_dir_sup_image (S : Set Q) (T : Set Q) [Directed S] [Directed T] :
  dir_sup { dir_sup { x ⊓ y | x ∈ S } | y ∈ T } ≤
  dir_sup ( ⋃₀ { { x ⊓ y | x ∈ S } | y ∈ T }) := by
  apply dir_sup_le
  rintro _ ⟨y, yT, rfl⟩
  apply dir_sup_mono
  rintro _ ⟨x, xS, rfl⟩
  simp
  use y, yT, x, xS

theorem inf_dir_sup_le_dir_sup_pwise_inf (S : Set Q) (T : Set Q) [Directed S] [Directed T] :
  (dir_sup S) ⊓ (dir_sup T) ≤ dir_sup { x ⊓ y | (x ∈ S) (y ∈ T) } := by
  apply le_trans
  · apply distr_inf_dir_sup
  apply le_trans
  · apply dir_sup_le_dir_sup _ { dir_sup { x ⊓ y | x ∈ S } | y ∈ T }
    rintro _ ⟨y, yT, rfl⟩
    use dir_sup { x ⊓ y | x ∈ S }
    constructor
    · use y, yT
    · apply distr_inf_dir_sup'
    infer_instance
  apply le_trans
  · apply dir_sup_dir_sup_image
  apply dir_sup_mono
  simp
  intro y yT x xS
  use x, xS, y, yT

-- The lifting of a semilattice homomorphism is a semilattice homomorphism.
  
def ideal_lift_inf : InfHom (Ideal P) Q where
  toFun := ideal_lift f
  map_inf' := by
    intro I J
    unfold ideal_lift
    apply le_antisymm
    · apply le_inf
      · apply dir_sup_mono
        apply Set.image_mono
        apply inf_le_left
      · apply dir_sup_mono
        apply Set.image_mono
        apply inf_le_right
    · simp_rw [ pwise_inf_ideal I J ]
      apply le_trans
      · apply inf_dir_sup_le_dir_sup_pwise_inf
      apply dir_sup_mono
      unfold Set.image
      simp

end InfDcpo
end InfLat




