import checkpoints.shen_extension.CloneTargetPayment
import checkpoints.shen_extension.FiveCommonHeads
import checkpoints.shen_extension.SelectedMenuMoment

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- The clone credit belongs to the particular neutral label r. After
removing the exceptional row, both inherited targets retain all their heads. -/
theorem three_parent_pair_returns {D : CH.Digraph} {U L : Finset ℕ} {c p q t : ℕ}
    (free : QFree D U 3) (cu : c ∈ U) (size : U.card = 3*t) (no : BypassRepair.NoHost 3 t)
    (rest : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (sat : L.card+1=t) (clear : L ⊆ neutral D U (tightParents D U c t) c)
    (nb : ∀ l ∈ L, D l c ≠ true) (eq3 : (tightParents D U c t).card=3)
    (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q) (cp : D c p=true) (cq : D c q=true)
    (fullP : (outN D U p).card=t+1) (fullQ : (outN D U q).card=t+1)
    (spare : ∀ w ∈ outN D U p ∪ outN D U q, t < (outN D U w).card) :
    let W := (outN D U p \ L) ∩ (outN D U q \ L)
    (∀ r ∈ L, 3+(if D p r=true then 1 else 0)+(if D q r=true then 1 else 0) ≤
      (W.filter (fun w => D w r ≠ true)).card) ∧ 5 ≤ W.card := by
  classical
  let H := tightParents D U c t
  have loc {l} (ll : l ∈ L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear ll)).1).1
  obtain ⟨a,b,d,ab,ad,bd,triple,_,_,drow,al,bl,gate⟩ :=
    three_parent_structure free cu (loc pl).2 cp size.le no rest (fun w wm => spare w (mem_union_left _ wm)) sat clear eq3
  change H = {a,b,d} at triple
  have am : a ∈ H := triple ▸ mem_insert_self _ _
  have bm : b ∈ H := triple ▸ mem_insert_of_mem (mem_insert_self _ _)
  have dm : d ∈ H := triple ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have par {v} (vm : v ∈ H) := mem_inN.mp (mem_filter.mp vm).1
  have nh {v} (vm : v ∈ H) : v ≠ c := fun e => loopfree free (by decide) cu (e ▸ (par vm).2)
  have deg {v} (vm : v ∈ H) : (outN D U v).card = t :=
    le_antisymm (mem_filter.mp vm).2 (rest v (par vm).1 (nh vm))
  have neutralEdge {l h} (ll : l ∈ L) (hm : h ∈ H) : D l h ≠ true := fun e =>
    disjoint_left.mp (mem_filter.mp (clear ll)).2 (mem_outN.mpr ⟨(par hm).1,e⟩) hm
  obtain ⟨Y,ys,dis,yall⟩ := exterior_pool free size sat (par am).1 (par bm).1 cu (par dm).1 ab
    (par am).2 (par bm).2 (deg am) (deg bm) drow al bl
    (fun l ll => ⟨neutralEdge ll am,neutralEdge ll bm,nb l ll⟩) gate
  let J := U.erase c
  have cj : c ∉ J := notMem_erase _ _
  have subL : L ⊆ J := fun l ll => mem_erase.mpr (loc ll)
  have jsize := card_erase_add_one cu
  change J.card+1=U.card at jsize
  have jh {v} (m : v ∈ H) : v ∈ J := mem_erase.mpr ⟨nh m,(par m).1⟩
  have row (v) : outN D J v = (outN D U v).erase c := by
    ext w; simp only [J,mem_outN,mem_erase]; tauto
  have unc {v} (off : D v c ≠ true) : outN D J v = outN D U v := by
    rw [row,erase_eq_of_notMem (fun m => off (mem_outN.mp m).2)]
  have rp := unc (nb p pl)
  have rq := unc (nb q ql)
  have noL {v} (m : v ∈ H) : v ∉ L := fun vl => (nb _ vl) (par m).2
  have base (v) (hv : v ∈ ({a,b} : Finset ℕ)) : t ≤ (outN D J v).card+1 := by
    have vh : v ∈ H := triple ▸ ((show ({a,b} : Finset ℕ) ⊆ {a,b,d} by grind) hv)
    rw [row,card_erase_add_one (mem_outN.mpr ⟨cu,(par vh).2⟩),deg vh]
  have floor (r) (rl : r ∈ L) (v) (vj : v ∈ J) (va : v ≠ a) (vb : v ≠ b) :
      t ≤ (outN D J v).card + (if D v r=true then 1 else 0) := by
    obtain ⟨vc,vu⟩ := mem_erase.mp vj
    have fl := rest v vu vc
    by_cases ed : D v c=true
    · have one := card_erase_add_one (mem_outN.mpr ⟨cu,ed⟩)
      rw [← row] at one
      by_cases more : t < (outN D U v).card
      · omega
      · have vh : v ∈ H := mem_filter.mpr ⟨mem_inN.mpr ⟨vu,ed⟩,by omega⟩
        have vd : v=d := by simpa [triple,va,vb] using vh
        have rhead : r ∈ (outN D U d).erase c := drow ▸ rl
        have vr : D v r=true := vd ▸ (mem_outN.mp (mem_erase.mp rhead).2).2
        rw [ite_eq_left vr]; omega
    · rw [unc ed]; omega
  have rich (w) (wm : w ∈ (outN D J p \ L) ∪ (outN D J q \ L)) : t+1 ≤ (outN D J w).card := by
    rw [rp,rq] at wm
    have inRows : w ∈ outN D U p ∪ outN D U q := (mem_union.mp wm).elim
      (fun h => mem_union_left _ (mem_sdiff.mp h).1) (fun h => mem_union_right _ (mem_sdiff.mp h).1)
    have off {v} (vv : v ∈ U) (cv : D c v=true) (h : w ∈ outN D U v) : D w c ≠ true :=
      fun e => free c 3 (by decide) (by decide) (.step vv cv (.step (outN_subset h)
        (mem_outN.mp h).2 (.step cu e (.refl _))))
    have wc := (mem_union.mp inRows).elim (off (loc pl).2 cp) (off (loc ql).2 cq)
    rw [unc wc]; exact spare _ inRows
  let W := (outN D U p \ L) ∩ (outN D U q \ L)
  have paid (r) (rl : r ∈ L) : 3+(if D p r=true then 1 else 0)+(if D q r=true then 1 else 0) ≤
      (W.filter (fun w => D w r ≠ true)).card := by
    have bound := clone_payment_obstruction (free.mono_set (erase_subset ..)) cj (jsize.trans size).le no
      subL pl ql rl pq (jh am) (jh bm) ab (noL am) (noL bm)
      (fun l ll => ⟨neutralEdge ll am,neutralEdge ll bm⟩)
      (fun e => disjoint_left.mp al (mem_outN.mpr ⟨(loc pl).2,e⟩) pl)
      (fun e => disjoint_left.mp bl (mem_outN.mpr ⟨(loc ql).2,e⟩) ql)
      base (floor _ rl) (rp ▸ fullP.ge) (rq ▸ fullQ.ge) rich
    rw [rp,rq] at bound
    change _ < (W.filter (fun w => D w r ≠ true)).card at bound
    omega
  refine ⟨paid,five_common_exterior_heads (N:=outN D U) pl ql
    (fun m => loopfree free (by decide) (loc pl).2 (mem_outN.mp m).2)
    (fun m => loopfree free (by decide) (loc ql).2 (mem_outN.mp m).2)
    (fun ⟨m,n⟩ => digonfree free (by decide) (loc pl).2 (loc ql).2 (mem_outN.mp m).2 (mem_outN.mp n).2)
    (by omega : Y.card ≤ L.card) (by omega) (by omega) (yall p pl) (yall q ql) ?_⟩
  intro r rl
  have rU := (loc rl).2
  simpa only [mem_outN,and_iff_right rU] using
    (paid r rl).trans (card_le_card (filter_subset ..))

/-- A single missed label determines L for all pairs and all clone choices. -/
def PaidExteriorPairs (D : CH.Digraph) (V B P : Finset ℕ) (c : ℕ) : Prop :=
    ∃ z ∈ P, D c z ≠ true ∧
      let U := V \ B
      let L := insert z (outN D U c)
      let I := P ∩ outN D V c
      ∀ p ∈ I, ∀ q ∈ I, p ≠ q →
        let W := (outN D U p \ L) ∩ (outN D U q \ L)
        (∀ r ∈ L, 3+(if D p r=true then 1 else 0)+(if D q r=true then 1 else 0) ≤
          (W.filter (fun w => D w r ≠ true)).card) ∧ 5 ≤ W.card

/-- The inherited targets of the actual lone-three-hit bank have at least
five common exterior heads per pair, with the labelwise payment obstruction. -/
theorem bank_five_common_heads {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 3 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (hits : (outN D B c).card = 3)
    (lone : ∀ v ∈ V \ B, v ≠ c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true)
    (eq3 : (tightParents D (V \ B) c (s-1)).card = 3) :
    PaidExteriorPairs D V B P c := by
  classical
  let U := V \ B
  let t := s-1
  have uv : U ⊆ V := sdiff_subset
  have size : U.card = 3*t := by
    change (V \ B).card = 3*(s-1)
    rw [card_sdiff_of_subset sub,order,three]; omega
  obtain ⟨z,zp,cz,sat,neutralEq,nb,rest,_⟩ :=
    bank_saturation safe reg hs order no sub three pv many common cu hits lone menu miss
  let L := insert z (outN D U c)
  have inside {p} (pp : p ∈ P) : p ∈ U := mem_sdiff.mpr ⟨pv pp,fun pb =>
    loopfree safe (by decide) (pv pp) (mem_outN.mp (common p pb pp)).2⟩
  have full {v} (vu : v ∈ U) (off : ∀ b ∈ B, D v b ≠ true) : (outN D U v).card=t+1 := by
    have same : outN D U v = outN D V v := by
      ext w; simp only [mem_outN]
      exact ⟨fun h => ⟨uv h.1,h.2⟩,fun h => ⟨mem_sdiff.mpr ⟨h.1,fun wb => off w wb h.2⟩,h.2⟩⟩
    rw [same,reg v (uv vu)]; dsimp [t]; omega
  have fullP {p} (pm : p ∈ P) := full (inside pm) (fun b bb =>
    digonfree safe (by decide) (sub bb) (pv pm) (mem_outN.mp (common b bb pm)).2)
  have spare {p w} (pm : p ∈ P) (wm : w ∈ outN D U p) : t < (outN D U w).card := by
    have eq := full (outN_subset wm) (fun b bb e => safe b 3 (by decide) (by decide)
      (.step (pv pm) (mem_outN.mp (common b bb pm)).2 (.step (uv (outN_subset wm)) (mem_outN.mp wm).2
        (.step (sub bb) e (.refl _)))))
    omega
  refine ⟨z,zp,cz,?_⟩
  dsimp only
  intro p pm q qm pq
  obtain ⟨pp,pc⟩ := mem_inter.mp pm
  obtain ⟨qp,qc⟩ := mem_inter.mp qm
  exact three_parent_pair_returns (safe.mono_set uv) cu size no rest sat neutralEq.ge nb eq3
    (mem_insert_of_mem (mem_outN.mpr ⟨inside pp,(mem_outN.mp pc).2⟩))
    (mem_insert_of_mem (mem_outN.mpr ⟨inside qp,(mem_outN.mp qc).2⟩)) pq (mem_outN.mp pc).2
    (mem_outN.mp qc).2 (fullP pp) (fullP qp) (fun w m => (mem_union.mp m).elim (spare pp) (spare qp))

theorem selected_pair_frontier {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ TripleCap D V P.card ∧ ∃ B ⊆ V, B.card=3 ∧
      (∀ b ∈ B, P ⊆ outN D V b) ∧
      let U := V \ B
      let S := U.filter (fun c => 2 ≤ (outN D B c).card)
      (∀ c ∈ S, ∃ z ∈ P, D c z ≠ true) ∧
      (2 ≤ S.card ∨ ∃ c, S={c} ∧ (outN D B c).card=3 ∧ (rowMenu D U P c).card=1 ∧
        (4 ≤ (tightParents D U c (s-1)).card ∨
          (tightParents D U c (s-1)).card=3 ∧ s-1 ≤ 3*P.card ∧ 4 ≤ P.card ∧ 3 ≤ (P ∩ outN D V c).card ∧ PaidExteriorPairs D V B P c)) := by
  classical
  obtain ⟨P,pv,many,cap,B,bv,three,common,miss,front⟩ := selected_moment_frontier safe reg hs order no
  refine ⟨P,pv,many,cap,B,bv,three,common,miss,?_⟩
  rcases front with several | ⟨c,one,hits,menu,parents⟩
  · exact Or.inl several
  refine Or.inr ⟨c,one,hits,menu,?_⟩
  rcases parents with high | ⟨eq3,height,heads,inherited⟩
  · exact Or.inl high
  have cs : c ∈ (V \ B).filter (fun a => 2 ≤ (outN D B a).card) := one ▸ mem_singleton_self _
  have lone (v) (vu : v ∈ V \ B) (vc : v ≠ c) : (outN D B v).card ≤ 1 := by
    by_contra! bad
    exact vc (mem_singleton.mp (one ▸ (mem_filter.mpr ⟨vu,by omega⟩)))
  exact Or.inr ⟨eq3,height,heads,inherited,bank_five_common_heads safe reg (by omega) order no
    bv three pv many common (mem_filter.mp cs).1 hits lone menu.le (miss c cs) eq3⟩

#print axioms selected_pair_frontier
#print axioms three_parent_pair_returns
#print axioms bank_five_common_heads
end LeanCH.BR.TripleBank
