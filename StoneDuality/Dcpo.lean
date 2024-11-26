import StoneDuality.DirSet
import StoneDuality.Basic

variable {P : Type*}

namespace Order

class Dcpo (P) extends PartialOrder P where

  /-- The supremum of a directed set -/
  dir_sup : ∀ S : Set P, [Directed S] → P
  /-- The supremum is an upper bound for the set -/
  le_dir_sup : ∀ S : Set P, ∀ s ∈ S, {_ : Directed S} → s ≤ dir_sup S
  /-- The supremum is a *least* upper bound for the set -/
  dir_sup_le : ∀ S : Set P, ∀ x : P, (∀ s ∈ S, s ≤ x) → {_ : Directed S} → dir_sup S ≤ x

namespace Dcpo

section Basic

theorem dir_sup_le_dir_sup [Dcpo P] (S T : Set P) {_ : Directed S} :
  (∀ x ∈ S, ∃ y ∈ T, x ≤ y) → {_ : Directed T} → dir_sup S ≤ dir_sup T := by
  intro H _
  apply dir_sup_le
  intro x xS
  obtain ⟨y, yT, xy⟩ := H x xS
  apply le_trans xy
  apply le_dir_sup
  exact yT

instance instDcpoSet : Dcpo (Set P) where
  dir_sup := fun S _ => Set.sUnion S
  le_dir_sup := by 
    intro S A AS _
    simp
    intro x xA
    simp
    use A, AS, xA
  dir_sup_le := by
    intro S x H _
    simp
    exact H
    
end Basic

section DirSet

variable [LE P]

instance dir_sup_dirset (S : Set (DirSet P)) [D : Directed S] : Directed (⋃ A ∈ S, (A : Set P)) where
  IsNonempty := by
    rcases D.IsNonempty with ⟨A, AS⟩
    simp
    use A, AS
    exact A.nonempty'
  IsDirected := by
    intro x xS y yS; simp at xS; simp at yS
    rcases xS with ⟨A, AS, xA⟩
    rcases yS with ⟨B, BS, yB⟩
    have ⟨C, CS, AC, BC⟩ := D.IsDirected A AS B BS
    have ⟨z, zC, xz, yz⟩ := C.directed' x (AC xA) y (BC yB)
    simp
    use z, ⟨C, CS, zC⟩, xz, yz

instance instDcpoDirSet : Dcpo (DirSet P) where
  dir_sup := fun S => (dir_sup_dirset S).toDirSet
  le_dir_sup := by
    intro S A AS D
    unfold Directed.toDirSet
    intro x xA
    simp
    use A, AS, xA
  dir_sup_le := by
    intro S A H D
    unfold Directed.toDirSet
    intro x xS
    simp at xS
    rcases xS with ⟨B, BS, xB⟩
    exact H B BS xB

@[simp] lemma mem_dir_sup_dirset (S : Set (DirSet P)) [Directed S] (x : P) : 
  x ∈ (dir_sup S) ↔ ∃ A ∈ S, x ∈ A := by
  unfold dir_sup
  unfold instDcpoDirSet
  simp

end DirSet

instance instMeetDirected [SemilatticeInf P] (S : Set P) [D : Directed S] (x : P) :
  Directed { x ⊓ s | s ∈ S } where
  IsNonempty := by
    rcases D.IsNonempty with ⟨s, sS⟩
    use x ⊓ s
    simp
    use s
  IsDirected := by
    rintro _ ⟨s, sS, rfl⟩ _ ⟨t, tS, rfl⟩
    rcases D.IsDirected s sS t tS with ⟨u, uS, su, tu⟩
    use x ⊓ u
    simp
    use ⟨u, uS, rfl⟩
    constructor
    · apply le_trans
      · apply inf_le_right
      · exact su
    · apply le_trans
      · apply inf_le_right
      · exact tu

instance instMeetDirected' [SemilatticeInf P] (S : Set P) [D : Directed S] (x : P) :
  Directed { s ⊓ x | s ∈ S} := by
  conv =>
    congr
    enter [1, y, 1, s, 2]
    rw [ inf_comm ]
  infer_instance
 
class InfDcpo (P) extends SemilatticeInf P, Dcpo P where
  distr_inf_dir_sup : ∀ S : Set P, {_ : Directed S} → 
    ∀ x : P, x ⊓ (dir_sup S) ≤ dir_sup { x ⊓ s | s ∈ S }

instance instInfDcpoSet : InfDcpo (Set P) :=
  { Lattice.toSemilatticeInf with
    dir_sup := dir_sup
    le_dir_sup := le_dir_sup
    dir_sup_le := dir_sup_le
    distr_inf_dir_sup := by
      intro S _ A
      unfold dir_sup; unfold instDcpoSet
      simp
      intro x ⟨xA, xS⟩
      rcases xS with ⟨B, xB, BS⟩
      simp
      use B
}

namespace InfDcpo

def distr_inf_dir_sup' [InfDcpo P] : ∀ S : Set P, {_ : Directed S} → 
   ∀ x : P, (dir_sup S) ⊓ x ≤ dir_sup { s ⊓ x | s ∈ S } := by
   intro S D x
   rw [ inf_comm ]
   conv =>
     rhs
     congr
     enter [1, y, 1, s, 2]
     rw [ inf_comm ]
   apply distr_inf_dir_sup
   
theorem distr_inf_dir_sup_eq [InfDcpo P] (S : Set P) {_ : Directed S} :
  ∀ x : P, x ⊓ (dir_sup S) = Dcpo.dir_sup { x ⊓ s | s ∈ S } := by
  intro x
  apply le_antisymm
  · apply distr_inf_dir_sup
  · apply dir_sup_le
    rintro _ ⟨y, yS, rfl⟩
    simp
    apply le_trans
    · apply inf_le_right
    · apply le_dir_sup
      exact yS

end InfDcpo
