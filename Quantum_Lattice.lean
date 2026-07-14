import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.Basic

open Complex

-- Defining Hilbert spaces
variable {H : Type*}

/- A Hilbert space is a complete normed inner-product space.
We specify the norm even though norm is induced by inner-product.-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-The structure for closed Hilbert spaces-/
structure ClosedSubspace (C : Type*) (H : Type*) [NormedAddCommGroup H]
 [InnerProductSpace ℂ H] [CompleteSpace H] :=
 (submodule : Submodule ℂ H)
 (is_closed : IsClosed (submodule : Set H))

instance : SetLike (ClosedSubspace ℂ H) H where
  coe P := P.submodule
  coe_injective' P Q h := by
    cases P
    cases Q
    congr
    exact SetLike.coe_injective h

/-In order to build the complete lattice, we need a partial order.
In this case, this is done via inclusion of Hilbert spaces-/
instance : PartialOrder (ClosedSubspace ℂ H) where
 le A B := (A : Set H) ⊆ (B : Set H)

 le_refl A := Set.Subset.refl (A : Set H)

 le_trans A B C hAB hBC := by
  exact Set.Subset.trans hAB hBC

 le_antisymm A B hAB hBA := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm hAB hBA

instance : CompleteLattice (ClosedSubspace ℂ H) where
  le := (·.submodule ≤ ·.submodule)

  le_refl := by
    sorry

  le_trans := by
    sorry

  le_antisymm := by
    sorry

  sup A B := by
    sorry

  le_sup_left := by
    sorry

  le_sup_right := by
    sorry

  sup_le := by
    sorry

  inf A B := by
    sorry

  inf_le_left := by
    sorry

  inf_le_right := by
    sorry

  le_inf := by
    sorry

  top := by
    sorry

  le_top := by
    sorry

  bot := by
    sorry

  bot_le := by
    sorry

  sSup := by
    sorry

  le_sSup := by
    sorry

  sSup_le := by
    sorry

  sInf := by
    sorry

  sInf_le := by
    sorry

  le_sInf := by
    sorry
