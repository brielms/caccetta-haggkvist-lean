import checkpoints.shen_extension.CenterTableTransition
import checkpoints.shen_extension.dot_tensor_research.DotFullReturnCut_20261118

/-! Apply the full last-return cut on the current graph to a two-miss table.
The missing row outside the centers pins down an actual tight donor center. -/
namespace LeanCH.BR.ShenCenterTable
open BRq2 BRq3 DotFullReturnCut

theorem noncenter_edit_misses {q D V p} (hq : 2≤q) (free : QFree D V q)
    (P : Table q V) (hp : p∈V) (outside : ∀ i<q, P.center i≠p) :
    P.misses (transition D V q p (P.center (P.label p))) = (P.misses D).erase p := by
  classical
  let w := P.center (P.label p)
  have hw := P.mem (P.label p) (P.bounded p hp)
  ext x
  by_cases xx : x=p
  · subst x
    have arc : transition D V q p w p w = true := (mem_outN.mp
      (show w ∈ outN (transition D V q p w) V p from
        (transition_receiver_row hq free hp hw) ▸ Finset.mem_insert_self _ _)).2
    simp [Table.misses,w] at arc ⊢
    exact fun _ => arc
  · by_cases hx : x∈V
    · have hy := outside _ (P.bounded x hx)
      simp [Table.misses,transition,DeleteRepair.repair,cut,xx,hy,hx]
    · simp [Table.misses,hx]

/-- With two missing nominations, fixing a noncenter forces the other source
to be an actual donor of degree exactly s. Its row after the debit contains
every other member of its own pool. The two missed heads are distinct. -/
theorem pinned_donor {q s D V p} (hq : 2≤q) (free : QFree D V q)
    (P : Table q V) (degree : ∀ i<q, s≤(outN D V (P.center i)).card)
    (caps : ∀ i<q, (P.pool i).card≤s) (two : (P.misses D).card=2)
    (miss : p∈P.misses D) (outside : ∀ i<q, P.center i≠p) :
    let w := P.center (P.label p)
    ∃ a<q, let u := P.center a
      u∈P.misses D ∧ u∈donors D V q p w ∧ (outN D V u).card=s ∧
      (P.pool ((a+1)%q)).card=s ∧ P.label p≠(a+1)%q ∧
      outN D V u=insert p ((P.pool ((a+1)%q)).erase u) := by
  classical
  let w := P.center (P.label p)
  let E := transition D V q p w
  have hp := (Finset.mem_filter.mp miss).1
  have hw := P.mem (P.label p) (P.bounded p hp)
  have ew := transition_qfree hq free hw (outside _ (P.bounded _ hp)).symm
  have after : P.misses E = (P.misses D).erase p := noncenter_edit_misses hq free P hp outside
  have one : (P.misses E).card≤1 := by
    rw [after,Finset.card_erase_of_mem miss,two]
  obtain ⟨a,ha,remaining,self,sub⟩ := sole_break hq ew P one
  let u := P.center a
  let pool := P.pool ((a+1)%q)
  have uv := P.mem a ha
  have ne : u≠p := outside _ ha
  have left : u∈P.misses D := (Finset.mem_erase.mp (after ▸ remaining)).2
  have excluded : u ∉ outN E V u := fun h => loopfree ew (by omega) uv (mem_outN.mp h).2
  have thin : outN E V u ⊆ pool.erase u :=
    fun x hx => Finset.mem_erase.mpr ⟨fun eq => excluded (eq ▸ hx),sub hx⟩
  have le := Finset.card_le_card thin
  have cap := caps ((a+1)%q) (Nat.mod_lt _ (by omega))
  have exactPool := Finset.card_erase_add_one self
  have old := degree a ha
  change pool.card ≤ s at cap
  change (pool.erase u).card + 1 = pool.card at exactPool
  change s≤(outN D V u).card at old
  obtain ⟨_,loss,same⟩ := exact_row_debits hq free hp hw
    (show D p w ≠ true by simp [w,(Finset.mem_filter.mp miss).2])
  have donor : u ∈ donors D V q p w := by
    by_contra no
    have unchanged : outN E V u=outN D V u := same u ne no
    rw [unchanged] at le
    omega
  have lost : (outN E V u).card+1=(outN D V u).card := loss u donor
  have filled := Finset.eq_of_subset_of_card_le thin (by omega)
  have edited : outN E V u = (outN D V u).erase p := by
    rw [show outN E V u = _ from transition_other_row (D:=D) (V:=V) (q:=q) (p:=p) (w:=w) ne,
      cut_donor_row donor]
  have up : p∈outN D V u := mem_outN.mpr ⟨hp,(mem_donors.mp donor).2⟩
  have shape : outN D V u=insert p (pool.erase u) := by
    rw [←filled,edited,Finset.insert_erase up]
  have diff : P.label p≠(a+1)%q := by
    intro eq
    have inPool : p∈pool.erase u := Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_filter.mpr ⟨hp,eq⟩⟩
    rw [←filled,edited] at inPool
    exact Finset.notMem_erase _ _ inPool
  exact ⟨a,ha,left,donor,show (outN D V u).card=s by omega,show pool.card=s by omega,diff,shape⟩

/-- A two-hole table closes the literal input when every genuinely returning
missed center has degree to spare or its pool has fewer than s vertices. -/
theorem cycle_of_buffered_centers {q n s D p} (hq : 2≤q) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) (P : Table q (Finset.range n))
    (caps : ∀ i<q, (P.pool i).card≤s) (two : (P.misses D).card=2)
    (miss : p∈P.misses D) (outside : ∀ i<q, P.center i≠p)
    (buffer : ∀ a<q, P.center a∈P.misses D →
      P.center a∈donors D (Finset.range n) q p (P.center (P.label p)) →
      s<(outN D (Finset.range n) (P.center a)).card ∨ (P.pool ((a+1)%q)).card<s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨a,ha,left,donor,tight,full,_,_⟩ := pinned_donor hq (qfree_of_noShort loop no) P
    (fun i hi => Compose.FloorSix.out_card degree (Finset.mem_range.mp (P.mem i hi)))
    caps two miss outside
  rcases buffer a ha left donor with extra | small
  · exact (Nat.ne_of_gt extra) tight
  · exact (Nat.ne_of_lt small) full

#print axioms noncenter_edit_misses
#print axioms pinned_donor
#print axioms cycle_of_buffered_centers
end LeanCH.BR.ShenCenterTable
