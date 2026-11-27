import checkpoints.shen_extension.TripleMomentCount
import checkpoints.shen_extension.BankFiveCommonHeads

namespace LeanCH.BR.TripleBank
open Finset

/-- With exactly five common exterior heads, their combined number of arcs
back into L is at most t-3. The two distinct source labels themselves admit
no return arcs, and at most one of their two mutual arcs exists. -/
theorem five_return_incidence {L Y : Finset ℕ} {N : ℕ → Finset ℕ} {p q t : ℕ}
    (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q) (sat : L.card + 1 = t)
    (asym : ∀ v w, w ∈ N v → v ∉ N w) (ys : Y.card ≤ L.card)
    (pfull : L.card + 2 ≤ (N p).card) (qfull : L.card + 2 ≤ (N q).card)
    (pex : N p \ L ⊆ Y) (qex : N q \ L ⊆ Y) :
    let W := (N p \ L) ∩ (N q \ L)
    W.card = 5 →
      (∀ r ∈ L, 3 + (if r ∈ N p then 1 else 0) + (if r ∈ N q then 1 else 0) ≤
        (W.filter (fun w => r ∉ N w)).card) →
      (∑ w ∈ W, (N w ∩ L).card) ≤ t - 3 ∧
        ∃ w ∈ W, (N w ∩ L).card ≤ (t - 3) / 5 := by
  classical
  intro W five paid
  let bit (v r : ℕ) : ℕ := if r ∈ N v then 1 else 0
  let g (r : ℕ) := columnDegree W N r + bit p r + bit q r
  have pg (r : ℕ) (rl : r ∈ L) : g r ≤ 2 := by
    have parts := card_filter_add_card_filter_not (s := W) (fun w => r ∈ N w)
    change columnDegree W N r + (W.filter (fun w => r ∉ N w)).card = W.card at parts
    have cost := paid r rl
    change 3 + bit p r + bit q r ≤ _ at cost
    dsimp only [g]
    omega
  have zero (v : ℕ) (hit : ∀ w ∈ W, w ∈ N v) : columnDegree W N v = 0 := by
    apply card_eq_zero.mpr
    exact filter_eq_empty_iff.mpr (fun w hw => asym v w (hit w hw))
  have pzero := zero p (fun w hw => (mem_sdiff.mp (mem_inter.mp hw).1).1)
  have qzero := zero q (fun w hw => (mem_sdiff.mp (mem_inter.mp hw).2).1)
  have emptyLoop (v) : v ∉ N v := fun h => asym v v h h
  have pair : g p + g q ≤ 1 := by
    by_cases hit : q ∈ N p
    · simp [g,bit,pzero,qzero,emptyLoop,hit,asym p q hit]
    · by_cases ret : p ∈ N q <;> simp [g,bit,pzero,qzero,emptyLoop,hit,ret]
  have qp : q ∈ L.erase p := mem_erase.mpr ⟨pq.symm, ql⟩
  let S := (L.erase p).erase q
  have subS : S ⊆ L := (erase_subset ..).trans (erase_subset ..)
  have sumS : (∑ r ∈ S, g r) ≤ S.card * 2 := by
    simpa only [sum_const, Nat.nsmul_eq_mul] using sum_le_sum (fun r hr => pg r (subS hr))
  have splitP := sum_erase_add L g pl
  have splitQ := sum_erase_add (L.erase p) g qp
  have cardP := card_erase_add_one pl
  have cardQ := card_erase_add_one qp
  change (∑ r ∈ S, g r) + g q = _ at splitQ
  change S.card + 1 = _ at cardQ
  have total : (∑ r ∈ L, g r) + 3 ≤ 2 * L.card := by omega
  have bit_sum (v : ℕ) : (∑ r ∈ L, bit v r) = (N v ∩ L).card := by
    change (∑ r ∈ L, if r ∈ N v then 1 else 0) = _
    rw [← sum_filter,filter_mem_eq_inter,inter_comm]
    simp
  simp only [g,sum_add_distrib,bit_sum,columnDegree_sum] at total
  have rowP := card_sdiff_add_card_inter (N p) L
  have rowQ := card_sdiff_add_card_inter (N q) L
  have extSum := card_union_add_card_inter (N p \ L) (N q \ L)
  have pool := (card_le_card (union_subset pex qex)).trans ys
  change _ + W.card = _ at extSum
  have bound : (∑ w ∈ W, (N w ∩ L).card) ≤ t - 3 := by omega
  refine ⟨bound, ?_⟩
  by_contra! all
  have low (w : ℕ) (wm : w ∈ W) : (t - 3) / 5 + 1 ≤ (N w ∩ L).card := all w wm
  have sumLow := sum_le_sum low
  simp only [sum_const,Nat.nsmul_eq_mul,five] at sumLow
  omega

open BRq2 BRq3 BR45

/-- Every inherited pair of the selected bank satisfies the incidence bound
on its own five exterior heads. -/
theorem bank_five_return_incidence {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 3 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (hits : (outN D B c).card = 3)
    (lone : ∀ v ∈ V \ B, v ≠ c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true)
    (eq3 : (tightParents D (V \ B) c (s-1)).card = 3) :
    ∃ z ∈ P, D c z ≠ true ∧
      let U := V \ B
      let L := insert z (outN D U c)
      let I := P ∩ outN D V c
      ∀ p ∈ I, ∀ q ∈ I, p ≠ q →
        let W := (outN D U p \ L) ∩ (outN D U q \ L)
        W.card = 5 →
          (∑ w ∈ W, (outN D U w ∩ L).card) ≤ (s-1)-3 ∧
            ∃ w ∈ W, (outN D U w ∩ L).card ≤ ((s-1)-3)/5 := by
  classical
  let U := V \ B
  let t := s-1
  let H := tightParents D U c t
  have uv : U ⊆ V := sdiff_subset
  have free := safe.mono_set uv
  have size : U.card = 3*t := by
    change (V \ B).card = 3*(s-1)
    rw [card_sdiff_of_subset sub, order, three]
    omega
  obtain ⟨z,zp,cz,sat,neutralEq,nb,rest,k,_,kl,ku,ck,spare⟩ :=
    bank_saturation safe reg hs order no sub three pv many common cu hits lone menu miss
  let L := insert z (outN D U c)
  change L.card+1=t at sat
  change neutral D U H c = L at neutralEq
  have clear := neutralEq.ge
  have loc {l} (ll : l ∈ L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear ll)).1).1
  obtain ⟨a,b,d,ab,_,_,triple,_,_,drow,al,bl,gate⟩ :=
    three_parent_structure free cu ku ck size.le no rest
      (fun w wm => by rw [spare w wm]; dsimp [t]; omega) sat clear eq3
  change H = {a,b,d} at triple
  have am : a ∈ H := triple ▸ mem_insert_self _ _
  have bm : b ∈ H := triple ▸ mem_insert_of_mem (mem_insert_self _ _)
  have dm : d ∈ H := triple ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have par {v} (vm : v ∈ H) := mem_inN.mp (mem_filter.mp vm).1
  have deg {v} (vm : v ∈ H) : (outN D U v).card = t :=
    le_antisymm (mem_filter.mp vm).2 (rest v (par vm).1
      (fun e => loopfree free (by decide) cu (e ▸ (par vm).2)))
  have neutralEdge {l h} (ll : l ∈ L) (hm : h ∈ H) : D l h ≠ true := fun e =>
    disjoint_left.mp (mem_filter.mp (clear ll)).2 (mem_outN.mpr ⟨(par hm).1,e⟩) hm
  obtain ⟨Y,ys,_,outside⟩ := exterior_pool free size sat (par am).1 (par bm).1 cu (par dm).1 ab
    (par am).2 (par bm).2 (deg am) (deg bm) drow al bl
    (fun l ll => ⟨neutralEdge ll am,neutralEdge ll bm,nb l ll⟩) gate
  obtain ⟨z',zp',cz',pair⟩ :=
    bank_five_common_heads safe reg hs order no sub three pv many common cu hits lone menu miss eq3
  have chosen (x) (xp : x ∈ P) (cx : D c x ≠ true) : x ∈ rowMenu D U P c :=
    mem_union_left _ (mem_sdiff.mpr ⟨xp,fun m => cx (mem_outN.mp m).2⟩)
  obtain rfl : z' = z := card_le_one.mp menu z' (chosen z' zp' cz') z (chosen z zp cz)
  have full {v} (vp : v ∈ P) : (outN D U v).card = s := by
    have eq : outN D U v = outN D V v := by
      ext w
      simp only [mem_outN]
      exact ⟨fun h => ⟨uv h.1,h.2⟩,fun h => ⟨mem_sdiff.mpr ⟨h.1,fun wb =>
        digonfree safe (by decide) (sub wb) (pv vp) (mem_outN.mp (common w wb vp)).2 h.2⟩,h.2⟩⟩
    rw [eq, reg v (pv vp)]
  have ps {v} (vp : v ∈ P) (cv : v ∈ outN D V c) : v ∈ L :=
    mem_insert_of_mem (mem_outN.mpr ⟨mem_sdiff.mpr ⟨pv vp,fun vb =>
      loopfree safe (by decide) (pv vp) (mem_outN.mp (common v vb vp)).2⟩,(mem_outN.mp cv).2⟩)
  refine ⟨_,zp',cz',?_⟩
  dsimp only
  intro p pm q qm pq five
  have pl := ps (mem_inter.mp pm).1 (mem_inter.mp pm).2
  have ql := ps (mem_inter.mp qm).1 (mem_inter.mp qm).2
  have pf := full (mem_inter.mp pm).1
  have qf := full (mem_inter.mp qm).1
  apply five_return_incidence (N:=outN D U) pl ql pq sat (fun v w vw wv =>
    digonfree free (by decide) (outN_subset wv) (outN_subset vw) (mem_outN.mp vw).2 (mem_outN.mp wv).2)
    (by omega : Y.card ≤ L.card) (by dsimp [t] at sat; omega) (by dsimp [t] at sat; omega)
    (outside p pl) (outside q ql) five
  intro r rl
  have pay := (pair p pm q qm pq).1 r rl
  simpa only [mem_outN,and_iff_right (loc rl).2] using pay

#print axioms five_return_incidence
#print axioms bank_five_return_incidence

end LeanCH.BR.TripleBank
