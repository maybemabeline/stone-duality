import StoneDuality.Dcpo

namespace Order
namespace Dcpo

variable {P : Type*}

class Frame' (P) extends DistribLattice P, Dcpo P where
  distr_inf_dir_sup : ∀ S : Set P, {_ : Directed S} → 
    ∀ x : P, x ⊓ (dir_sup S) ≤ dir_sup { x ⊓ s | s ∈ S }
