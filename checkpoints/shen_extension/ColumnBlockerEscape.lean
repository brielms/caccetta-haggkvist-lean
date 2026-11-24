import LeanCH.BR.BR45Base

namespace LeanCH.BR.Closure.ColumnBlockerEscape
open BRq2 BRq3 BR45 Finset

private theorem entry {D : CH.Digraph} {V : Finset ℕ} {p v x : ℕ}
    (col : outN D V p = inN D V v) (hx : x ∈ V) :
    D p x = true ↔ D x v = true := by
  have eq : x ∈ outN D V p ↔ x ∈ inN D V v := by rw [col]
  simpa [mem_outN,mem_inN,hx] using eq

private theorem triangle {D : CH.Digraph} {V : Finset ℕ} (safe : QFree D V 3)
    {x y z} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
    (xy : D x y=true) (yz : D y z=true) (zx : D z x=true) : False :=
  safe x 3 (by decide) (by decide) (.step hy xy (.step hz yz (.step hx zx (.refl x))))

/-- B is disjoint from both A and C. An extra vertex outside all three
forces a lower bound on the intersection of A and C. -/
private theorem overlap {V A B C : Finset ℕ} {b s : ℕ}
    (av : A ⊆ V) (bv : B ⊆ V) (cv : C ⊆ V) (hb : b ∈ V)
    (ba : b ∉ A) (bb : b ∉ B) (bc : b ∉ C) (ab : Disjoint B A) (cb : Disjoint B C)
    (manyA : s ≤ A.card) (manyB : s ≤ B.card) (manyC : s ≤ C.card) :
    3*s+1 ≤ V.card+(A ∩ C).card := by
  have sub : insert b (B ∪ (A ∪ C)) ⊆ V :=
    insert_subset hb (union_subset bv (union_subset av cv))
  have le := card_le_card sub
  have miss : b ∉ B ∪ (A ∪ C) := by simp [ba,bb,bc]
  rw [card_insert_of_notMem miss,card_union_of_disjoint (disjoint_union_right.mpr ⟨ab,cb⟩)] at le
  have count := card_union_add_card_inter A C
  omega

/-- Two successive column matches force many arcs into unmatched columns.
All neighborhoods and witnesses belong to the original graph. -/
theorem local_counts {D : CH.Digraph} {V : Finset ℕ} {s a b c : ℕ}
    (safe : QFree D V 3) (degree : ∀ v ∈ V, s ≤ (outN D V v).card) (pos : 0<s)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (ab : outN D V b = inN D V a) (bc : outN D V c = inN D V b)
    (manyC : s ≤ (inN D V c).card) :
    3*s+1 ≤ V.card+(inN D V a ∩ inN D V c).card ∧
    ∀ x ∈ inN D V a ∩ inN D V c,
      3*s+1 ≤ V.card+(inN D V a ∩ outN D V x).card ∧
      ∀ z ∈ inN D V a ∩ outN D V x, ∀ w ∈ V, outN D V w ≠ inN D V z := by
  have manyA : s ≤ (inN D V a).card := ab ▸ degree b hb
  have manyB : s ≤ (inN D V b).card := bc ▸ degree c hc
  have ba : b ∉ inN D V a := fun h =>
    loopfree safe (by decide) hb ((entry ab hb).mpr (mem_inN.mp h).2)
  have bb : b ∉ inN D V b := fun h => loopfree safe (by decide) hb (mem_inN.mp h).2
  have noC : b ∉ inN D V c := by
    intro h
    obtain ⟨p,hp⟩ := card_pos.mp (pos.trans_le manyB)
    exact triangle safe hb hc (mem_inN.mp hp).1 (mem_inN.mp h).2
      ((entry bc (mem_inN.mp hp).1).mpr (mem_inN.mp hp).2) (mem_inN.mp hp).2
  have next {j k : ℕ} (hj : j ∈ V) (hk : k ∈ V) (col : outN D V k = inN D V j) :
      Disjoint (inN D V j) (inN D V k) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact digonfree safe (by decide) hk (mem_inN.mp hx).1
      ((entry col (mem_inN.mp hx).1).mpr (mem_inN.mp hx).2) (mem_inN.mp hy).2
  have apart := (next ha hb ab).symm
  refine ⟨overlap (filter_subset _ _) (filter_subset _ _) (filter_subset _ _) hb
    ba bb noC apart (next hb hc bc) manyA manyB manyC,?_⟩
  intro x h
  obtain ⟨xa,xc⟩ := mem_inter.mp h
  have xv := (mem_inN.mp xa).1
  have bx := (entry ab xv).mpr (mem_inN.mp xa).2
  have xb : b ∉ outN D V x := fun e => digonfree safe (by decide) hb xv bx (mem_outN.mp e).2
  have free : Disjoint (inN D V b) (outN D V x) := disjoint_left.mpr (by
    intro t tb xt
    exact triangle safe hb xv (mem_inN.mp tb).1 bx (mem_outN.mp xt).2 (mem_inN.mp tb).2)
  refine ⟨overlap (filter_subset _ _) (filter_subset _ _) outN_subset hb ba bb xb apart
    free manyA manyB (degree x xv),?_⟩
  intro z hz w wv col
  obtain ⟨za,xz⟩ := mem_inter.mp hz
  have bz := (entry ab (mem_inN.mp za).1).mpr (mem_inN.mp za).2
  have wb := (entry col hb).mpr bz
  have cw := (entry bc wv).mpr wb
  have wx := (entry col xv).mpr (mem_outN.mp xz).2
  exact triangle safe xv hc wv (mem_inN.mp xc).2 cw wx

/-- At critical order there is a particular z→a with unmatched column. -/
theorem local_unmatched {D : CH.Digraph} {V : Finset ℕ} {s a b c : ℕ}
    (safe : QFree D V 3) (degree : ∀ v ∈ V, s ≤ (outN D V v).card) (pos : 0<s)
    (small : V.card ≤ 3*s) (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (ab : outN D V b = inN D V a) (bc : outN D V c = inN D V b)
    (manyC : s ≤ (inN D V c).card) :
    ∃ x ∈ inN D V a ∩ inN D V c, ∃ z ∈ inN D V a ∩ outN D V x,
      ∀ w ∈ V, outN D V w ≠ inN D V z := by
  obtain ⟨left,right⟩ := local_counts safe degree pos ha hb hc ab bc manyC
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (inN D V a ∩ inN D V c).card by omega)
  obtain ⟨le,unmatched⟩ := right x hx
  obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (inN D V a ∩ outN D V x).card by omega)
  exact ⟨x,hx,z,hz,unmatched z hz⟩

/-- A triangle-free source whose every column is some row has order at least
three times its minimum outdegree plus one. No permutation is required. -/
theorem all_columns_order {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (live : V.Nonempty) (degree : ∀ v ∈ V, s ≤ (outN D V v).card)
    (cols : ∀ v ∈ V, ∃ w ∈ V, outN D V w = inN D V v) : 3*s+1 ≤ V.card := by
  by_contra! small
  have pos : 0<s := by have := card_pos.mpr live; omega
  obtain ⟨a,ha⟩ := live
  obtain ⟨b,hb,ab⟩ := cols a ha
  obtain ⟨c,hc,bc⟩ := cols b hb
  obtain ⟨e,he,ce⟩ := cols c hc
  obtain ⟨x,hx,z,hz,no⟩ := local_unmatched safe degree pos (by omega) ha hb hc ab bc
    (ce ▸ degree e he)
  obtain ⟨w,hw,hit⟩ := cols z (mem_inN.mp (mem_inter.mp hz).1).1
  exact no w hw hit

#print axioms local_counts
#print axioms local_unmatched
#print axioms all_columns_order
end LeanCH.BR.Closure.ColumnBlockerEscape
