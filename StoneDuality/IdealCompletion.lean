import Mathlib.Order.Ideal
import Mathlib.Tactic.Linarith
import StoneDuality.Basic
import StoneDuality.Dcpo
import StoneDuality.ScottCont
import StoneDuality.DirSet

namespace Order
namespace Dcpo

variable {P : Type*}

section DcpoIdeal

variable [Preorder P]

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

instance dirset_ideal (I : Ideal P) : Directed { downset_ideal x | x ∈ I } where
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

end DcpoIdeal

section TopDcpoIdeal

variable [LE P] [OrderTop P]
  
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

instance : SemilatticeSup (Ideal P) where
  sup I J :=
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
    simp
    rintro z ⟨x, xI, y, yJ, zxy⟩
    apply K.lower' zxy (Ideal.sup_mem (IK xI) (JK yJ))


end SemilatticeSup

section DistribLattice

variable [DistribLattice P]

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
