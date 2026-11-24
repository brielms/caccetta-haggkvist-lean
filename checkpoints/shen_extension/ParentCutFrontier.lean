import checkpoints.shen_extension.PrefixOrderFrontier
import checkpoints.shen_extension.dot_tensor_research.DegreeEightParentCuts

namespace LeanCH.BR.ParentCutFrontier
open Finset BRq2 BRq3 BR45 CHRuleCatalog

def Orders (m : ℕ) :=  m=37 ∨ m=44

theorem excluded (m : ℕ) (D : CH.Digraph) (order : Orders m) : ¬Bad ⟨m,8,D⟩ := by
  intro b
  have free := qfree_of_noShort b.loopless b.missing
  have deg v (vm : v∈range m) := Compose.FloorSix.out_card b.degree (mem_range.mp vm)
  rcases order with rfl|rfl
  · change QFree D (range 37) (CH.ceilDiv 37 8) at free
    rw [show CH.ceilDiv 37 8=5 by decide] at free
    exact ParentCutPacking.order37 free (card_range _) deg
  · change QFree D (range 44) (CH.ceilDiv 44 8) at free
    rw [show CH.ceilDiv 44 8=6 by decide] at free
    exact ParentCutPacking.order44 free (card_range _) deg

/-- Any lower-order exclusion propagates to every affordable descendant.
The original cycle-length quota is respected throughout. -/
theorem prefix_excluded {d} (positive : 0<d) (closed : ℕ→Prop)
    (exclude : ∀m D,closed m → ¬Bad ⟨m,d,D⟩)
    {p : Input} (bad : Bad p) {m} (pos : 0<m) (within : m≤p.n)
    (loss : d+(p.n-m)≤p.s) (quota : CH.ceilDiv m d≤cutoff p) : ¬closed m :=
  fun h=>exclude m p.D h (bad_child bad (PrefixFrontier.prefix_child p bad pos positive within loss quota))

def Gate (n r q : ℕ) := ∃m,Orders m ∧ m≤n ∧ 8+(n-m)≤r ∧ CH.ceilDiv m 8≤q

theorem close {n r D} (hn : 0<n) (hr : 0<r) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r) (gate : Gate n r (CH.ceilDiv n r)) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  obtain ⟨m,ord,within,loss,quota⟩ := gate
  have pos : 0<m := by rcases ord with rfl|rfl <;> decide
  exact prefix_excluded (d:=8) (p:=⟨n,r,D⟩) (by decide) Orders excluded
    ⟨hn,hr,loop,degree,missing⟩ pos within loss quota ord

#print axioms excluded
#print axioms prefix_excluded
#print axioms close
end LeanCH.BR.ParentCutFrontier
