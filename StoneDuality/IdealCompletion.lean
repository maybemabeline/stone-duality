import Mathlib.Order.Ideal
import Mathlib.Tactic.Linarith
import StoneDuality.Basic
import StoneDuality.Dcpo
import StoneDuality.ScottCont
import StoneDuality.DirSet

-- In this file, we establish properties of the ideal completion of a partial order P.
-- The ideal completion always forms a dcpo, but properties of P are also retained
-- in Ideal P and interact well with the dcpo structure.
-- In particular, we show that:
-- Ideal P forms a dcpo
-- Ideal P always has a top element
-- If P has a bottom element, then so does Ideal P
-- If P has binary infima, then so does Ideal P and these distribute over directed suprema.
-- If P has binary suprema, then so does Ideal P.
-- If binary suprema distribute over binary infima in P, then they also do so in Ideal P.

namespace Order
namespace Dcpo

variable {P : Type*}

section DcpoIdeal

variable [Preorder P]

-- The ideals of a preorder P form a dcpo. 
-- The directed supremum is given by the union of ideals.

instance instDcpoIdeal : Dcpo (Ideal P) where
  dir_sup S DS := by
    apply Directed.toIdeal (⋃ T ∈ (Ideal.toDirSet_hom '' S), T : Set P)
    intro x y yx
    simp
    intro I IS xI
    use I, IS
    exact I.lower' yx xI
  le_dir_sup S s sS D := by
    intro x xs
    simp
    use s, sS, xs
  dir_sup_le S I H D := by
    intro x xS
    simp at xS
    rcases xS with ⟨s, sS, xs⟩
    exact H s sS xs

@[simp] lemma mem_dir_sup_ideal (S : Set (Ideal P)) [Directed S] (x : P) : 
  x ∈ (dir_sup S) ↔ ∃ A ∈ S, x ∈ A := by
  unfold dir_sup
  unfold instDcpoIdeal
  simp

end DcpoIdeal

section TopDcpoIdeal

variable [LE P] [OrderTop P]

-- Ideal P always has a top element. The top ideal is given by the set P.
  
instance : OrderTop (Ideal P) where
  top := 
  {
    carrier := Set.univ
    lower' := fun _ _ _ H => H
    nonempty' := by simp
    directed' := fun _ _ _ _ => by use ⊤; simp
  }
  le_top I x xI := trivial

end TopDcpoIdeal

section BotDcpoIdeal

variable [PartialOrder P] [OrderBot P]

-- If P has a bottom element, then so does Ideal P. The bottom ideal is given
-- by the singleton set containing the bottom element of P. Note that since ideals
-- are required to be nonempty, the bottom ideal cannot be given by the empty set. 

instance : OrderBot (Ideal P) where
  bot :=
  {
    carrier := { ⊥ }
    lower' := by
      rintro _ _ xy rfl
      exact bot_unique xy
    nonempty' := by simp
    directed' := fun _ H _ K => by simp; use H; use K
  }
  bot_le := by
    rintro I _ rfl
    have ⟨_, xI⟩ := I.nonempty'
    exact I.lower' bot_le xI

end BotDcpoIdeal

section InfDcpoIdeal

variable [SemilatticeInf P]

-- If P has binary infima, then so does Ideal P. The infimum of two ideals is
-- given by their intersection. This does directly involve the infima of P,
-- but they are required to show that the intersection in fact forms an ideal.
-- Since intersections distribute over unions, it easy to show that binary infima
-- in Ideal P distribute over directed suprema.

instance : Min (Ideal P) where
  min I J := 
  { 
    carrier := I ∩ J
    lower' := fun x y yx ⟨xI, xJ⟩ => ⟨I.lower' yx xI, J.lower' yx xJ⟩
    nonempty' := by
      obtain ⟨x, xI⟩ := I.nonempty'
      obtain ⟨y, yJ⟩ := J.nonempty'
      use x ⊓ y
      exact ⟨I.lower' inf_le_left xI, J.lower' inf_le_right yJ⟩
    directed' := by
      rintro x ⟨xI, xJ⟩ y ⟨yI, yJ⟩
      obtain ⟨z, zI, xz, yz⟩ := I.directed' x xI y yI
      obtain ⟨w, wJ, xw, yw⟩ := J.directed' x xJ y yJ
      use z ⊓ w, ⟨I.lower' inf_le_left zI, J.lower' inf_le_right wJ⟩
      simp
      use ⟨xz, xw⟩, yz, yw
  }

instance instInfDcpoIdeal : InfDcpo (Ideal P) :=
  { instDcpoIdeal with
    inf := min
    inf_le_right := fun _ _ => Set.inter_subset_right
    inf_le_left := fun _ _ => Set.inter_subset_left
    le_inf := fun _ _ _ IK JK => Set.subset_inter IK JK
    distr_inf_dir_sup := by
      rintro _ _ _ _ ⟨xI, xS⟩
      simp at xS; rcases xS with ⟨A, AS, xA⟩
      simp
      use A, AS
      use xI, xA
  }

-- We characterise the infimum of two ideals as the set of the pointwise infima of their elements.
-- In some situations, this definition is more convenient, but it is much harder
-- to show that it forms the infimum directly.

theorem pwise_inf_ideal (I J : Ideal P) : I ⊓ J = { x ⊓ y | (x ∈ I) (y ∈ J) } := by
  ext z
  constructor
  · rintro ⟨zI, zJ⟩
    use z ⊓ z
    simp
    use zI, z, zJ
  · rintro ⟨x, xI, y, yJ, rfl⟩
    exact ⟨I.lower' inf_le_left xI, J.lower' inf_le_right yJ⟩

end InfDcpoIdeal

section SemilatticeSup

variable [SemilatticeSup P]

-- If P has binary suprema, then so does Ideal P. We want to define the supremum 
-- of two ideals to be the set of the pointwise suprema of their elements, but this
-- set turns out not to be lower closed. Therefore, we consider its lower closure,
-- defining the supremum to be the set of elements of P lying below some pointwise
-- supremum of elements from the two ideals.

instance : Max (Ideal P) where
  max I J :=
  {
    carrier := { z : P | ∃ x ∈ I, ∃ y ∈ J, z ≤ x ⊔ y}
    lower' := by
      intro z w wz ⟨x, xI, y, yJ, zxy⟩
      simp
      use x, xI, y, yJ
      apply le_trans wz zxy
    nonempty' := by
      have ⟨x, xI⟩ := I.nonempty'
      have ⟨y, yJ⟩ := J.nonempty'
      use x ⊔ y
      use x, xI, y, yJ
    directed' := by
      rintro z ⟨x1, x1I, y1, y1J, zxy1⟩
      rintro w ⟨x2, x2I, y2, y2J, wxy2⟩
      use z ⊔ w
      simp
      use x1 ⊔ x2, Ideal.sup_mem x1I x2I
      use y1 ⊔ y2, Ideal.sup_mem y1J y2J   
      constructor
      · apply le_trans
        · exact zxy1
        · simp
          constructor
          · apply le_trans
            · apply le_sup_left; use x2
            · apply le_sup_left
          · apply le_trans
            · apply le_sup_left; use y2
            · apply le_sup_right
      · apply le_trans
        · exact wxy2
        · simp
          constructor
          · apply le_trans
            · apply le_sup_right; use x1
            · apply le_sup_left
          · apply le_trans
            · apply le_sup_right; use y1
            · apply le_sup_right
  }


instance : SemilatticeSup (Ideal P) where
  sup := max
  le_sup_left I J := by
    intro x xI
    have ⟨y, yJ⟩ := J.nonempty'
    use x, xI, y, yJ
    apply le_sup_left
  le_sup_right I J := by
    intro y yJ
    have ⟨x, xI⟩ := I.nonempty'
    use x, xI, y, yJ
    apply le_sup_right
  sup_le := by
    intro I J K IK JK
    unfold max; unfold instMaxIdeal; simp
    rintro z ⟨x, xI, y, yJ, zxy⟩
    apply K.lower' zxy (Ideal.sup_mem (IK xI) (JK yJ))


end SemilatticeSup

section DistribLattice

variable [DistribLattice P]

-- Finaly, we show that if binary suprema distribute over binary infima in P,
-- then they also do so in Ideal P.

instance : DistribLattice (Ideal P) where
  le_sup_inf := by
    intro I J K z zH
    rcases zH with ⟨⟨x, xI, y, yJ, zxy⟩, u, uI, v, vK, zuv⟩
    simp
    use x ⊔ u, Ideal.sup_mem xI uI
    use y ⊓ v
    constructor
    · use J.lower' inf_le_left yJ
      use K.lower' inf_le_right vK
    · rw [sup_inf_left]
      simp
      constructor
      · apply le_trans zxy
        simp
        refine le_trans ?_ le_sup_left
        apply le_sup_left
      · apply le_trans zuv
        simp
        refine le_trans ?_ le_sup_left
        apply le_sup_right

end DistribLattice
