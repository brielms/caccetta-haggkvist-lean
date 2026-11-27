import checkpoints.shen_extension.PairPowerOrder

namespace LeanCH.BR.PairPowerReservoir
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay PairPowerOrder

/-- Parents of a specified label reaching every specified target at the same radius. -/
noncomputable def parentsTo (D : CH.Digraph) (V : Finset ℕ) (p : ℕ) (Y : Finset ℕ) (k : ℕ) :
    Finset ℕ := by
  classical
  exact (inN D V p).filter (fun w => ∀ y∈Y, Walk D V w y k)

theorem parentsTo_card {D : CH.Digraph} {V Y : Finset ℕ} {q j p : ℕ}
    (free : QFree D V q) (live : V.Nonempty) (room : (j+1)+(j+1) ≤ q)
    (pair : ∀ u∈V, ∀ v∈V, ∃ w∈V, D w u=true ∧ D w v=true)
    (pv : p∈V) (ys : Y⊆V) (slots : Y.card ≤ 2^j) :
    2^(2^j-Y.card+1) ≤ (parentsTo D V p Y (j+1)).card+1 := by
  classical
  let C := parentsTo D V p Y (j+1)
  have memC (r) : r∈C ↔ r∈inN D V p ∧ ∀ y∈Y, Walk D V r y (j+1) := by
    simp only [C,parentsTo,mem_filter]
  let H : CH.Digraph := fun a b => decide (Walk D V a b (j+1))
  apply common_set_order (D:=H) (2^j-Y.card)
  · intro u _ v _ uv vu
    have go : Walk D V u v (j+1) := of_decide_eq_true uv
    have back : Walk D V v u (j+1) := of_decide_eq_true vu
    exact free u ((j+1)+(j+1)) (by omega) room (go.append back)
  · intro S sc small
    have sv : S⊆V := fun h hm => (mem_inN.mp ((memC h).mp (sc hm)).1).1
    have total := card_union_le Y S
    obtain ⟨a,av,path⟩ := binary_ancestor live pair j (union_subset ys sv)
      (show (Y ∪ S).card ≤ 2^j by omega)
    obtain ⟨r,rv,rp,ra⟩ := pair p pv a av
    refine ⟨r,(memC r).mpr ⟨mem_inN.mpr ⟨rv,rp⟩,fun y hy =>
      .step av ra (path y (mem_union_left _ hy))⟩,?_⟩
    intro h hm
    exact decide_eq_true (show Walk D V r h (j+1) from .step av ra (path h (mem_union_right _ hm)))

/-- Every member of the pool lies outside every forward ball of a listed target
whose radius can be concatenated with the prescribed approach. -/
theorem parentsTo_avoids_ball {D : CH.Digraph} {V Y : Finset ℕ} {q k p y : ℕ}
    (free : QFree D V q) (hk : 0<k) (kq : k≤q) (hy : y∈Y) :
    Disjoint (parentsTo D V p Y k) (ball D V y (q-k)) := by
  classical
  apply disjoint_left.mpr
  intro r rc rb
  obtain ⟨_,l,limit,back⟩ := mem_ball.mp rb
  have approach := (mem_filter.mp (show r∈(inN D V p).filter (fun w => ∀ z∈Y, Walk D V w z k) from rc)).2 y hy
  exact free r (k+l) (by omega) (by omega) (approach.append back)

#print axioms parentsTo_card
#print axioms parentsTo_avoids_ball
end LeanCH.BR.PairPowerReservoir
