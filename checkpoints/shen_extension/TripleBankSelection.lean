import checkpoints.shen_extension.TripleBankFreeRepair
import checkpoints.shen_extension.FloorInduction

/-! Selecting three deleted labels with common targets missed by every short
row. The finite matching argument takes place only on the maximizing rows. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

private theorem avoids_small {G : CH.Digraph} {W T : Finset ℕ} (safe : QFree G W 3)
    (live : W.Nonempty) (sub : T ⊆ W) (small : T.card ≤ 3) :
    ∃ a ∈ W, Disjoint (outN G W a) T := by
  classical
  by_cases ne : T.Nonempty
  · obtain ⟨a,at',sink⟩ := exists_sink (safe.mono_set sub) ne small
    exact ⟨a,sub at',disjoint_left.mpr (fun b ed bt => sink b bt (mem_outN.mp ed).2)⟩
  · obtain ⟨a,aw⟩ := live
    exact ⟨a,aw,by simp [not_nonempty_iff_eq_empty.mp ne]⟩

/-- In a sinkless triangle-free graph with maximum outdegree two, three
out-neighbourhoods are pairwise disjoint. -/
theorem three_disjoint {G : CH.Digraph} {W : Finset ℕ} (safe : QFree G W 3)
    (live : W.Nonempty) (sinkless : ∀ a ∈ W, (outN G W a).Nonempty)
    (cap : ∀ a ∈ W, (outN G W a).card ≤ 2) :
    ∃ i ∈ W, ∃ j ∈ W, ∃ k ∈ W, Disjoint (outN G W i) (outN G W j) ∧
      Disjoint (outN G W i) (outN G W k) ∧ Disjoint (outN G W j) (outN G W k) := by
  classical
  let N := outN G W
  by_contra absent
  have clash {i j k} (iw : i ∈ W) (jw : j ∈ W) (kw : k ∈ W)
      (ij : Disjoint (N i) (N j)) (ik : Disjoint (N i) (N k)) (jk : Disjoint (N j) (N k)) :=
    absent ⟨i,iw,j,jw,k,kw,ij,ik,jk⟩
  have avoid (T : Finset ℕ) (sub : T ⊆ W) (small : T.card ≤ 3) :
      ∃ a ∈ W, Disjoint (N a) T := avoids_small safe live sub small
  have full (i) (iw : i ∈ W) : (N i).card = 2 := by
    have lim : (N i).card ≤ 2 := cap i iw
    by_contra neq
    obtain ⟨j,jw,ji⟩ := avoid (N i) outN_subset (by omega)
    have jc := cap j jw
    change (N j).card ≤ 2 at jc
    have bound := card_union_le (N i) (N j)
    obtain ⟨k,kw,off⟩ := avoid (N i ∪ N j) (union_subset outN_subset outN_subset) (by omega)
    exact clash iw jw kw ji.symm (off.symm.mono_left subset_union_left)
      (off.symm.mono_left subset_union_right)
  obtain ⟨i,iw⟩ := live
  obtain ⟨j,jw,ji⟩ := avoid (N i) outN_subset (by rw [full i iw]; decide)
  let T := N i ∪ N j
  have subT : T ⊆ W := union_subset outN_subset outN_subset
  have four : T.card = 4 := by simp [T,card_union_of_disjoint ji.symm,full i iw,full j jw]
  have meets (a) (aw : a ∈ W) : ∃ b ∈ N a, b ∈ T := by
    by_contra! no
    have off : Disjoint (N a) T := disjoint_left.mpr no
    exact clash iw jw aw ji.symm (off.symm.mono_left subset_union_left)
      (off.symm.mono_left subset_union_right)
  have witness (t) (tT : t ∈ T) : ∃ a ∈ W, ∃ u ∉ T, N a = {t,u} := by
    obtain ⟨a,aw,off⟩ := avoid (T.erase t) (fun _ h => subT (mem_erase.mp h).2)
      (by rw [card_erase_of_mem tT,four])
    obtain ⟨b,bn,bt⟩ := meets a aw
    have only (x) (xn : x ∈ N a) (xt : x ∈ T) : x = t := by
      by_contra ne
      exact disjoint_left.mp off xn (mem_erase.mpr ⟨ne,xt⟩)
    have tn : t ∈ N a := only b bn bt ▸ bn
    obtain ⟨u,um⟩ := card_pos.mp (show 0 < ((N a).erase t).card by
      rw [card_erase_of_mem tn,full a aw]; decide)
    obtain ⟨ut,un⟩ := mem_erase.mp um
    have eq : ({t,u} : Finset ℕ) = N a := eq_of_subset_of_card_le
      (insert_subset tn (singleton_subset_iff.mpr un)) (by rw [full a aw,card_pair ut.symm])
    exact ⟨a,aw,u,fun h => ut (only u un h),eq.symm⟩
  have uniqueOutside {t u a b x y} (tw : t ∈ T) (uw : u ∈ T) (tu : t ≠ u)
      (aw : a ∈ W) (bw : b ∈ W) (xt : x ∉ T) (yt : y ∉ T)
      (ax : N a = {t,x}) (by' : N b = {u,y}) {o} (ow : o ∈ W)
      (ot : t ∉ N o) (ou : u ∉ N o) (os : N o ⊆ T) : x = y := by
    by_contra xy
    have ao : Disjoint (N a) (N o) := by
      rw [ax]; exact disjoint_left.mpr (fun v vm vo => by
        rcases mem_insert.mp vm with rfl | h
        · exact ot vo
        · exact xt (mem_singleton.mp h ▸ os vo))
    have bo : Disjoint (N b) (N o) := by
      rw [by']; exact disjoint_left.mpr (fun v vm vo => by
        rcases mem_insert.mp vm with rfl | h
        · exact ou vo
        · exact yt (mem_singleton.mp h ▸ os vo))
    have ab : Disjoint (N a) (N b) := by
      rw [ax,by']; simp only [disjoint_left,mem_insert,mem_singleton]
      grind
    exact clash aw bw ow ab ao bo
  have oneExtra (m o) (mw : m ∈ W) (ow : o ∈ W) (mo : Disjoint (N m) (N o))
      (ms : N m ⊆ T) (os : N o ⊆ T) :
      ∃ x ∉ T, ∀ a ∈ W, ∀ u ∈ N a, u ∉ T → (∃ t ∈ N m, t ∈ N a) → u = x := by
    obtain ⟨t,u,tu,pair⟩ := card_eq_two.mp (full m mw)
    have tm : t ∈ N m := pair ▸ mem_insert_self _ _
    have um : u ∈ N m := pair ▸ mem_insert_of_mem (mem_singleton_self _)
    have ot : t ∉ N o := disjoint_left.mp mo tm
    have ou : u ∉ N o := disjoint_left.mp mo um
    obtain ⟨a,aw,x,xt,ax⟩ := witness t (ms tm)
    obtain ⟨b,bw,y,yt,by'⟩ := witness u (ms um)
    have same := uniqueOutside (ms tm) (ms um) tu aw bw xt yt ax by' ow ot ou os
    refine ⟨x,xt,?_⟩
    intro r rw' v vr vt hit
    obtain ⟨z,zm,zr⟩ := hit
    have zv : z ≠ v := fun h => vt (h ▸ ms zm)
    have eq : N r = {z,v} := (eq_of_subset_of_card_le
      (insert_subset zr (singleton_subset_iff.mpr vr)) (by rw [full r rw',card_pair zv])).symm
    rw [pair] at zm
    rcases mem_insert.mp zm with rfl | h
    · exact (uniqueOutside (ms tm) (ms um) tu rw' bw vt yt eq by' ow ot ou os).trans same.symm
    · obtain rfl := mem_singleton.mp h
      exact uniqueOutside (ms um) (ms tm) tu.symm rw' aw vt xt eq ax ow ou ot os
  obtain ⟨x,_,coverX⟩ := oneExtra i j iw jw ji.symm subset_union_left subset_union_right
  obtain ⟨y,_,coverY⟩ := oneExtra j i jw iw ji subset_union_right subset_union_left
  let H := W ∩ (T ∪ {x,y})
  have allHeads (a) (aw : a ∈ W) : N a ⊆ H := by
    intro v vn
    refine mem_inter.mpr ⟨outN_subset vn,?_⟩
    by_cases vt : v ∈ T
    · exact mem_union_left _ vt
    obtain ⟨z,zn,zt⟩ := meets a aw
    rcases mem_union.mp zt with zi | zj
    · simp [coverX a aw v vn vt ⟨z,zi,zn⟩]
    · simp [coverY a aw v vn vt ⟨z,zj,zn⟩]
  have hw : H ⊆ W := inter_subset_left
  have minTwo (a) (ah : a ∈ H) : 2 ≤ (outN G H a).card := by
    have eq : outN G H a = N a := by
      ext v; constructor
      · intro h; exact mem_outN.mpr ⟨hw (mem_outN.mp h).1,(mem_outN.mp h).2⟩
      · intro h; exact mem_outN.mpr ⟨allHeads a (hw ah) h,(mem_outN.mp h).2⟩
    rw [eq,full a (hw ah)]
  have big := FloorInduction.triangle_degree_two (safe.mono_set hw) minTwo
    ((sinkless i iw).mono (allHeads i iw))
  have small := (card_le_card (inter_subset_right : H ⊆ T ∪ {x,y})).trans (card_union_le _ _)
  change H.card ≤ T.card + ({x,y} : Finset ℕ).card at small
  have xy := card_insert_le x {y}
  simp only [card_singleton] at xy
  omega

/-- Three labels can be chosen so that their common outgoing heads in
the reversed graph, if any, are among the deleted labels. -/
private theorem clean_three {G : CH.Digraph} {W : Finset ℕ} (safe : QFree G W 3)
    (three : 3 ≤ W.card) (cap : ∀ a ∈ W, (outN G W a).card ≤ 2) :
    ∃ B ⊆ W, B.card = 3 ∧ ∀ v ∈ W \ B, ((B.filter (fun a => G a v = true))).card ≤ 1 := by
  classical
  have mk {i j k : ℕ} (iw : i ∈ W) (jw : j ∈ W) (kw : k ∈ W)
      (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
      (one : ∀ v ∈ W, v ≠ i → v ≠ j → v ≠ k →
        ¬ (G i v = true ∧ G j v = true) ∧ ¬ (G i v = true ∧ G k v = true) ∧
          ¬ (G j v = true ∧ G k v = true)) :
      ∃ B ⊆ W, B.card = 3 ∧ ∀ v ∈ W \ B, (B.filter (fun a => G a v = true)).card ≤ 1 := by
    refine ⟨{i,j,k},insert_subset iw (insert_subset jw (singleton_subset_iff.mpr kw)),by simp [ij,ik,jk],?_⟩
    intro v vm
    obtain ⟨vw,out⟩ := mem_sdiff.mp vm
    simp only [mem_insert,mem_singleton,not_or] at out
    have test := one v vw out.1 out.2.1 out.2.2
    apply card_le_one.mpr
    intro a am b bm
    simp only [mem_filter,mem_insert,mem_singleton] at am bm
    grind
  by_cases sinkless : ∀ a ∈ W, (outN G W a).Nonempty
  · obtain ⟨i,iw,j,jw,k,kw,ij,ik,jk⟩ := three_disjoint safe (card_pos.mp (by omega)) sinkless cap
    have ne {a b} (aw : a ∈ W) (d : Disjoint (outN G W a) (outN G W b)) : a ≠ b := by
      rintro rfl
      obtain ⟨t,ht⟩ := sinkless a aw
      exact disjoint_left.mp d ht ht
    exact mk iw jw kw (ne iw ij) (ne iw ik) (ne jw jk) (fun v vw _ _ _ =>
      ⟨fun h => disjoint_left.mp ij (mem_outN.mpr ⟨vw,h.1⟩) (mem_outN.mpr ⟨vw,h.2⟩),
       fun h => disjoint_left.mp ik (mem_outN.mpr ⟨vw,h.1⟩) (mem_outN.mpr ⟨vw,h.2⟩),
       fun h => disjoint_left.mp jk (mem_outN.mpr ⟨vw,h.1⟩) (mem_outN.mpr ⟨vw,h.2⟩)⟩)
  · push Not at sinkless
    obtain ⟨i,iw,empty⟩ := sinkless
    let T := W.erase i
    have ts : T ⊆ W := erase_subset _ _
    have tc : T.card = W.card - 1 := card_erase_of_mem iw
    obtain ⟨j,jt⟩ := card_pos.mp (show 0 < T.card by omega)
    let N := outN G T j
    have capj : N.card ≤ 2 := (card_le_card (show N ⊆ outN G W j from
      fun _ h => mem_outN.mpr ⟨ts (mem_outN.mp h).1,(mem_outN.mp h).2⟩)).trans (cap j (ts jt))
    have other : ∃ k ∈ T, k ≠ j ∧ Disjoint N (outN G T k) := by
      by_cases has : N.Nonempty
      · obtain ⟨k,kn,no⟩ := exists_sink ((safe.mono_set ts).mono_set (show N ⊆ T from outN_subset))
          has (by omega)
        have kj : k ≠ j := fun eq => loopfree safe (by decide) (ts jt) (eq ▸ (mem_outN.mp kn).2)
        exact ⟨k,(mem_outN.mp kn).1,kj,disjoint_left.mpr
          (fun z zn zk => no z zn (mem_outN.mp zk).2)⟩
      · obtain ⟨k,kt⟩ := card_pos.mp (show 0 < (T.erase j).card by rw [card_erase_of_mem jt]; omega)
        exact ⟨k,(mem_erase.mp kt).2,(mem_erase.mp kt).1,by simp [not_nonempty_iff_eq_empty.mp has]⟩
    obtain ⟨k,kt,kj,d⟩ := other
    apply mk iw (ts jt) (ts kt) (mem_erase.mp jt).1.symm (mem_erase.mp kt).1.symm kj.symm
    intro v vw vi _ _
    have noEdge : G i v ≠ true := fun iv => by
      have hit := mem_outN.mpr ⟨vw,iv⟩
      rw [empty] at hit
      exact notMem_empty _ hit
    have vt : v ∈ T := mem_erase.mpr ⟨vi,vw⟩
    exact ⟨fun h => noEdge h.1,fun h => noEdge h.1,
      fun h => disjoint_left.mp d (mem_outN.mpr ⟨vt,h.1⟩) (mem_outN.mpr ⟨vt,h.2⟩)⟩

/-- Preserve any initial common target set covered by three rows in the
cardinality bound. Every short survivor of the selected triple misses a
target in the same maximizing set. -/
theorem maximal_triple {D : CH.Digraph} {V P₀ : Finset ℕ}
    (safe : QFree D V 3) (base : P₀ ⊆ V)
    (start : 3 ≤ (V.filter (fun a => P₀ ⊆ outN D V a)).card) :
    ∃ P ⊆ V, P₀ ⊆ P ∧ ∃ B ⊆ V, B.card = 3 ∧ (∀ a ∈ B, P ⊆ outN D V a) ∧
      ∀ c ∈ V \ B, 2 ≤ (outN D B c).card → ∃ z ∈ P, D c z ≠ true := by
  classical
  let W (P : Finset ℕ) := V.filter (fun a => P ⊆ outN D V a)
  let choices := V.powerset.filter (fun H => P₀ ⊆ H ∧ 3 ≤ (W H).card)
  have seed : P₀ ∈ choices := mem_filter.mpr ⟨mem_powerset.mpr base,Subset.rfl,start⟩
  obtain ⟨P,pm,top⟩ := choices.exists_max_image Finset.card ⟨P₀,seed⟩
  obtain ⟨pv,baseP,large⟩ := mem_filter.mp pm
  have sw : W P ⊆ V := filter_subset _ _
  let G : CH.Digraph := fun a b => D b a
  have cap (t) (tw : t ∈ W P) : (outN G (W P) t).card ≤ 2 := by
    by_contra! many
    have tv := sw tw
    have tp : t ∉ P := fun h => loopfree safe (by decide) tv (mem_outN.mp ((mem_filter.mp tw).2 h)).2
    have add : outN G (W P) t ⊆ W (insert t P) := by
      intro a ed
      obtain ⟨aw,ta⟩ := mem_outN.mp ed
      exact mem_filter.mpr ⟨sw aw,insert_subset_iff.mpr ⟨mem_outN.mpr ⟨tv,ta⟩,(mem_filter.mp aw).2⟩⟩
    have eligible : insert t P ∈ choices := mem_filter.mpr
      ⟨mem_powerset.mpr (insert_subset tv (mem_powerset.mp pv)),baseP.trans (subset_insert _ _),
        (show 3 ≤ (outN G (W P) t).card by omega).trans (card_le_card add)⟩
    have bound := top _ eligible
    rw [card_insert_of_notMem tp] at bound
    omega
  obtain ⟨B,bw,three,clean⟩ := clean_three (G := G) (safe.reverse.mono_set sw) large cap
  refine ⟨P,mem_powerset.mp pv,baseP,B,bw.trans sw,three,fun _ am => (mem_filter.mp (bw am)).2,?_⟩
  intro c cu hits
  by_contra! allHit
  have cw : c ∈ W P := mem_filter.mpr ⟨(mem_sdiff.mp cu).1,
    fun z zp => mem_outN.mpr ⟨mem_powerset.mp pv zp,allHit z zp⟩⟩
  have small := clean c (mem_sdiff.mpr ⟨cw,(mem_sdiff.mp cu).2⟩)
  change (outN D B c).card ≤ 1 at small
  omega

private theorem seed_pair {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (live : V.Nonempty) (reg : OutEq s D V) (dense : 2*(V.card-1) < s*(s-1)) :
    ∃ P₀ ⊆ V, P₀.card = 2 ∧ 3 ≤ (V.filter (fun a => P₀ ⊆ outN D V a)).card := by
  classical
  have high : ∃ p ∈ V, s ≤ (inN D V p).card := by
    by_contra! low
    have lt := sum_lt_sum_of_nonempty live (fun p pv => low p pv)
    have eq : (∑ a ∈ V,(outN D V a).card) = ∑ a ∈ V,(inN D V a).card :=
      Compose.ThinRigid.sum_out_eq_sum_in D V
    rw [sum_congr rfl (fun a av => reg a av)] at eq
    omega
  obtain ⟨p,pv,highP⟩ := high
  let H := V.erase p
  let I := inN D V p
  have count : (∑ h ∈ H, (inN D I h).card) = ∑ x ∈ I, (outN D H x).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun h x => D x h = true)
  have row (x) (xm : x ∈ I) : (outN D H x).card = s-1 := by
    have eq : outN D H x = (outN D V x).erase p := by ext v; simp only [H,mem_outN,mem_erase]; tauto
    rw [eq,card_erase_of_mem (mem_outN.mpr ⟨pv,(mem_inN.mp xm).2⟩),reg x (mem_inN.mp xm).1]
  have heavy : ∃ h ∈ H, 3 ≤ (inN D I h).card := by
    by_contra! light
    have bound : (∑ h ∈ H, (inN D I h).card) ≤ ∑ _h ∈ H, 2 :=
      sum_le_sum (fun h hm => by have := light h hm; omega)
    rw [count,sum_congr rfl row,sum_const,smul_eq_mul,sum_const,smul_eq_mul] at bound
    have hc : H.card = V.card-1 := card_erase_of_mem pv
    have hn := Nat.mul_le_mul_right (s-1) highP
    change s*(s-1) ≤ I.card*(s-1) at hn
    rw [hc,mul_comm (V.card-1)] at bound
    omega
  obtain ⟨h,hm,many⟩ := heavy
  have hv := (mem_erase.mp hm).2
  have ph := (mem_erase.mp hm).1.symm
  refine ⟨{p,h},insert_subset pv (singleton_subset_iff.mpr hv),card_pair ph,many.trans (card_le_card ?_)⟩
  intro a am
  obtain ⟨ap,ah⟩ := mem_inN.mp am
  exact mem_filter.mpr ⟨(mem_inN.mp ap).1,insert_subset_iff.mpr
    ⟨mem_outN.mpr ⟨pv,(mem_inN.mp ap).2⟩,singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,ah⟩)⟩⟩

theorem top_triple {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 7 ≤ s) (order : V.card = 3*s) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ ∃ B ⊆ V, B.card = 3 ∧ (∀ a ∈ B, P ⊆ outN D V a) ∧
      ∀ c ∈ V \ B, 2 ≤ (outN D B c).card → ∃ z ∈ P, D c z ≠ true := by
  have dense : 2*(V.card-1) < s*(s-1) := by
    have a : 6 ≤ s-1 := by omega
    have le := Nat.mul_le_mul_left s a
    omega
  obtain ⟨P₀,base,size,start⟩ := seed_pair (card_pos.mp (by omega)) reg dense
  obtain ⟨P,pv,includeBase,B,sub,bc,allHeads,miss⟩ := maximal_triple safe base start
  exact ⟨P,pv,size ▸ card_le_card includeBase,B,sub,bc,allHeads,miss⟩

#print axioms three_disjoint
#print axioms maximal_triple
#print axioms top_triple
end LeanCH.BR.TripleBank

