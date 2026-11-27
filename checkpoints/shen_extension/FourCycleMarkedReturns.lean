import checkpoints.shen_extension.CriticalReturnPool

namespace LeanCH.BR.WalkReturn
open Finset BRq2 BRq3 BR45 TripleBank

/-- K is any specified set of middles a→z→c. For every continuation a→b→c→d,
the common predecessors of a,c reserve additional places outside the
three rows at b,c,d. -/
theorem marked_return_count {D : CH.Digraph} {V K : Finset ℕ} {a b c d : ℕ}
    (safe : QFree D V 3) (av : a∈V) (cv : c∈V) (dv : d∈V)
    (sub : K ⊆ outN D V a ∩ inN D V c) (bk : b∈K) (cd : D c d=true) :
    K.card+(inN D V a ∩ inN D V c).card+(outN D V b).card+
      (outN D V c).card+(outN D V d).card ≤
    V.card+(outN D K b).card+returnOverlap D V b c d := by
  classical
  let B := outN D V b
  let C := outN D V c
  let E := outN D V d
  let P := inN D V a ∩ inN D V c
  let S := (B∪E)∪C
  have kv : K⊆V := sub.trans (inter_subset_left.trans outN_subset)
  have bv := kv bk
  have ab := (mem_outN.mp (mem_inter.mp (sub bk)).1).2
  have excl {z} (zv : z∈V) (zc : D z c=true) : z∉E ∧ z∉C := by
    exact ⟨fun h => safe z 3 (by decide) (by decide) (.step cv zc
      (.step dv cd (.step zv (mem_outN.mp h).2 (.refl _)))),
      fun h => digonfree safe (by decide) zv cv zc (mem_outN.mp h).2⟩
  have spare : (K\B)∪P ⊆ V\S := by
    intro z zm
    rcases mem_union.mp zm with h | h
    · obtain ⟨zk,off⟩ := mem_sdiff.mp h
      obtain ⟨ed,cen⟩ := excl (kv zk) (mem_inN.mp (mem_inter.mp (sub zk)).2).2
      exact mem_sdiff.mpr ⟨kv zk,by simp [S,off,ed,cen]⟩
    · obtain ⟨za,zc⟩ := mem_inter.mp h
      obtain ⟨zv,za'⟩ := mem_inN.mp za
      obtain ⟨ed,cen⟩ := excl zv (mem_inN.mp zc).2
      have off : z∉B := fun bz => safe z 3 (by decide) (by decide)
        (.step av za' (.step bv ab (.step zv (mem_outN.mp bz).2 (.refl _))))
      exact mem_sdiff.mpr ⟨zv,by simp [S,off,ed,cen]⟩
  have dis : Disjoint (K\B) P := disjoint_left.mpr (fun z zk zp =>
    digonfree safe (by decide) av (kv (mem_sdiff.mp zk).1)
      (mem_outN.mp (mem_inter.mp (sub (mem_sdiff.mp zk).1)).1).2 (mem_inN.mp (mem_inter.mp zp).1).2)
  have n := card_le_card spare
  rw [card_union_of_disjoint dis] at n
  have total := card_sdiff_add_card_eq_card (show S⊆V from union_subset (union_subset outN_subset outN_subset) outN_subset)
  have inside : K∩B=outN D K b := by
    ext z
    simp only [mem_inter,mem_outN,B]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,kv h.1,h.2⟩⟩
  have marked := card_sdiff_add_card_inter K B
  rw [inside] at marked
  have h₁ := card_union_add_card_inter B E
  have h₂ := card_union_add_card_inter (B∪E) C
  change S.card+((B∪E)∩C).card=(B∪E).card+C.card at h₂
  change K.card+P.card+B.card+C.card+E.card ≤ V.card+(outN D K b).card+
    ((B∩E).card+((B∪E)∩C).card)
  omega

/-- The lower-degree induction supplies one light middle in the marked
set. This middle works for every successor d of c simultaneously. -/
theorem light_return_middle {D : CH.Digraph} {V K : Finset ℕ} {s a c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (av : a∈V) (cv : c∈V)
    (sub : K⊆outN D V a ∩ inN D V c) (live : K.Nonempty)
    (lower : ∀ t, t<s → BypassRepair.NoHost 3 t) :
    ∃ b∈K, 3*(outN D K b).card<K.card ∧ ∀ d∈V, D c d=true →
      2*K.card+1+3*(inN D V a ∩ inN D V c).card+9*s ≤
        3*V.card+3*returnOverlap D V b c d := by
  classical
  obtain ⟨b,bk,small⟩ := K.exists_min_image (fun i => (outN D K i).card) live
  have kv : K⊆V := sub.trans (inter_subset_left.trans outN_subset)
  have inside : outN D K b ⊆ K.erase b := fun _ h => mem_erase.mpr
    ⟨fun eq => loopfree safe (by decide) (kv bk) (eq ▸ (mem_outN.mp h).2),outN_subset h⟩
  have n := card_le_card inside
  have e := card_erase_add_one bk
  have k := (card_le_card (sub.trans inter_subset_left)).trans_eq (reg a av)
  have light : 3*(outN D K b).card < K.card := by
    by_contra! fails
    exact lower _ (by omega) D K live fails (safe.mono_set kv) small
  refine ⟨b,bk,light,?_⟩
  intro d dv cd
  have count := marked_return_count safe av cv dv sub bk cd
  rw [reg b (kv bk),reg c cv,reg d dv] at count
  omega

#print axioms marked_return_count
#print axioms light_return_middle
end LeanCH.BR.WalkReturn
