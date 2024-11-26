import Mathlib.Order.Ideal
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

section InfDcpoIdeal

variable [SemilatticeInf P]

instance instMinIdeal : Min (Ideal P) where
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
