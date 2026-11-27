import checkpoints.shen_extension.RotatedPairPayment
import checkpoints.shen_extension.BankFiveCommonHeads

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- The four-label deletion used when the fresh slot is opened after the rotation. -/
theorem rotatedCore_eq_bank {V B : Finset ℕ} {k c d : ℕ} (kb : k ∈ B) (bv : B ⊆ V)
    (cu : c ∈ V \ B) (du : d ∈ V \ B) :
    rotatedCore ((V \ B).erase c) d k = (V \ insert d (B.erase k)).erase c := by
  ext w
  have kv := bv kb
  simp only [rotatedCore,mem_insert,mem_erase,mem_sdiff] at *
  grind

/-- Every previously deleted label can be returned. On the rotated core
it may itself need one unit, according to its original arcs inside the bank. -/
theorem released_row {D : CH.Digraph} {V B : Finset ℕ} {s k c d : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (bv : B ⊆ V) (kb : k ∈ B)
    (cu : c ∈ V \ B) (du : d ∈ V \ B) (ck : D c k=true) (dc : D d c=true) :
    (outN D (rotatedCore ((V \ B).erase c) d k) k).card + (outN D (B.erase k) k).card = s := by
  have cv := (mem_sdiff.mp cu).1
  have dv := (mem_sdiff.mp du).1
  have kv := bv kb
  have kc := digonfree safe (by decide) cv kv ck
  have kd : D k d ≠ true := fun e => safe k 3 (by decide) (by decide)
    (.step dv e (.step cv dc (.step kv ck (.refl _))))
  let R := rotatedCore ((V \ B).erase c) d k
  have both : outN D R k ∪ outN D (B.erase k) k = outN D V k := by
    ext w
    simp only [R,rotatedCore_eq_bank kb bv cu du,mem_union,mem_erase,mem_sdiff,mem_insert,mem_outN]
    grind
  have apart : Disjoint (outN D R k) (outN D (B.erase k) k) := by
    apply disjoint_left.mpr
    intro w u v
    have u' := outN_subset u
    change w ∈ rotatedCore ((V \ B).erase c) d k at u'
    rw [rotatedCore_eq_bank kb bv cu du] at u'
    exact (mem_sdiff.mp (mem_erase.mp u').2).2 (mem_insert_of_mem (outN_subset v))
  exact (card_union_of_disjoint apart).symm.trans (by rw [both,reg _ kv])

/-- On the selected lone-three-hit bank the same targets and blockers
satisfy the vacant-label obstruction on every bank obtained by deleting d
and returning k. The equality identifies the actual carrier for each k. -/
theorem bank_rotated_payment {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 3 ≤ s) (order : V.card=3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (bv : B ⊆ V) (three : B.card=3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (hits : (outN D B c).card=3)
    (lone : ∀ v ∈ V \ B, v ≠ c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true)
    (eq3 : (tightParents D (V \ B) c (s-1)).card=3) :
    ∃ z ∈ P, D c z ≠ true ∧
      let U := V \ B
      let J := U.erase c
      let L := insert z (outN D U c)
      let I := P ∩ outN D V c
      ∃ a b d, tightParents D U c (s-1)={a,b,d} ∧ D a d=true ∧ D b d=true ∧
        ∀ k ∈ B, ∀ p ∈ I, ∀ q ∈ I, p ≠ q →
          let R := (V \ insert d (B.erase k)).erase c
          let W := (outN D U p \ L) ∩ (outN D U q \ L)
          ∀ W₀ ⊆ W, ∀ P₀ ⊆ ({p,q} : Finset ℕ), (W \ W₀).card ≤ 2+P₀.card →
            let T := rotatedCredits D J a b d k (s-1) ∪ W₀ ∪ P₀
            ((R \ T).filter (fun v => Disjoint (outN D R v) T)).card < s-1 := by
  classical
  let U := V \ B
  let J := U.erase c
  let t := s-1
  let H := tightParents D U c t
  have uv : U ⊆ V := sdiff_subset
  have free := safe.mono_set uv
  have size : U.card=3*t := by
    change (V \ B).card=3*(s-1)
    rw [card_sdiff_of_subset bv,order,three]; omega
  obtain ⟨z,zp,cz,sat,ne,nb,rest,h,_,_,hu,ch,clean⟩ :=
    bank_saturation safe reg hs order no bv three pv many common cu hits lone menu miss
  let L := insert z (outN D U c)
  change neutral D U H c=L at ne
  have clear : L ⊆ neutral D U H c := ne.ge
  have loc {u} (ul : u∈L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear ul)).1).1
  have lj : L ⊆ J := fun _ m => mem_erase.mpr (loc m)
  obtain ⟨a,b,d,ab,ad,bd,triple,_,_,drow,al,bl,_,intoA,intoB,_⟩ :=
    saturated_three_parent_structure free cu hu ch size.le no rest
      (fun w wm => by rw [clean w wm]; dsimp [t]; omega) sat clear eq3
  change H={a,b,d} at triple
  have am : a∈H := triple ▸ mem_insert_self ..
  have bm : b∈H := triple ▸ mem_insert_of_mem (mem_insert_self ..)
  have dm : d∈H := triple ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have par {v} (vm : v∈H) := mem_inN.mp (mem_filter.mp vm).1
  have hj {v} (vm : v ∈ H) : v ∈ J := mem_erase.mpr
    ⟨fun e => loopfree free (by decide) cu (e ▸ (par vm).2),(par vm).1⟩
  have off {v} (vm : v∈H) : v∉L := fun vl => (nb _ vl) (par vm).2
  have neutral {r v} (rl : r∈L) (vh : v∈H) : D r v ≠ true := fun e =>
    disjoint_left.mp (mem_filter.mp (clear rl)).2 (mem_outN.mpr ⟨(par vh).1,e⟩) vh
  have row (v) : outN D J v = (outN D U v).erase c := by
    ext w; simp only [J,mem_outN,mem_erase]; tauto
  have same {v} (vnc : D v c ≠ true) : outN D J v=outN D U v := by
    rw [row,erase_eq_of_notMem (fun m => vnc (mem_outN.mp m).2)]
  have base (v) (vm : v∈({a,b} : Finset ℕ)) : t ≤ (outN D J v).card+1 := by
    have vh : v∈H := triple ▸ ((show ({a,b} : Finset ℕ) ⊆ {a,b,d} by grind) vm)
    rw [row,card_erase_add_one (mem_outN.mpr ⟨cu,(par vh).2⟩)]
    exact rest v (par vh).1 (mem_erase.mp (hj vh)).1
  have old (v) (vj : v∈J) (va : v≠a) (vb : v≠b) (vd : v≠d) : t ≤ (outN D J v).card := by
    obtain ⟨vc,vu⟩ := mem_erase.mp vj
    have floor := rest v vu vc
    by_cases ed : D v c=true
    · have n : (outN D J v).card+1=(outN D U v).card := by
        rw [row,card_erase_add_one (mem_outN.mpr ⟨cu,ed⟩)]
      by_contra! low
      have vh : v∈H := mem_filter.mpr ⟨mem_inN.mpr ⟨vu,ed⟩,by omega⟩
      simp [triple,va,vb,vd] at vh
    · rw [same ed]; exact floor
  have inside {p} (pp : p∈P) : p∈U := mem_sdiff.mpr ⟨pv pp,fun pb =>
    loopfree safe (by decide) (pv pp) (mem_outN.mp (common p pb pp)).2⟩
  have full {v} (vu : v∈U) (away : ∀ b ∈ B, D v b ≠ true) : (outN D U v).card=t+1 := by
    have eq : outN D U v=outN D V v := by
      ext w; simp only [mem_outN]
      exact ⟨fun h => ⟨uv h.1,h.2⟩,fun h => ⟨mem_sdiff.mpr ⟨h.1,fun m => away _ m h.2⟩,h.2⟩⟩
    rw [eq,reg _ (uv vu)]; dsimp [t]; omega
  have pf {p} (pm : p∈P) := full (inside pm) (fun b bb =>
    digonfree safe (by decide) (bv bb) (pv pm) (mem_outN.mp (common b bb pm)).2)
  have wf {p w} (pm : p∈P) (cp : D c p=true) (wm : w∈outN D U p) : (outN D J w).card=t+1 := by
    have wu := outN_subset wm
    have pw := (mem_outN.mp wm).2
    have nc : D w c ≠ true := fun e => free c 3 (by decide) (by decide)
      (.step (inside pm) cp (.step wu pw (.step cu e (.refl _))))
    rw [same nc]
    exact full wu (fun b bb e => safe b 3 (by decide) (by decide)
      (.step (pv pm) (mem_outN.mp (common b bb pm)).2 (.step (uv wu) pw (.step (bv bb) e (.refl _)))))
  refine ⟨z,zp,cz,?_⟩
  dsimp only
  refine ⟨a,b,d,triple,intoA,intoB,?_⟩
  intro k kb p pm q qm pq W₀ _ P₀ two cap
  obtain ⟨pp,pc⟩ := mem_inter.mp pm
  obtain ⟨qq,qc⟩ := mem_inter.mp qm
  have cp := (mem_outN.mp pc).2
  have cq := (mem_outN.mp qc).2
  have pl : p ∈ L := mem_insert_of_mem (mem_outN.mpr ⟨inside pp,cp⟩)
  have ql : q ∈ L := mem_insert_of_mem (mem_outN.mpr ⟨inside qq,cq⟩)
  have dr {v} (vl : v∈L) : D d v=true := (mem_outN.mp (mem_erase.mp (show v∈(outN D U d).erase c by rw [drow]; exact vl)).2).2
  have kv := bv kb
  have ku : k ∉ U := fun m => (mem_sdiff.mp m).2 kb
  have kj : k ∉ J := fun m => ku (mem_erase.mp m).2
  have cj : c ∉ insert k J := fun m => (mem_insert.mp m).elim
    (fun e => (mem_sdiff.mp cu).2 (e ▸ kb)) (notMem_erase _ _)
  have Vsub : insert k J ⊆ V := insert_subset kv ((erase_subset ..).trans uv)
  have hc : outN D B c=B := eq_of_subset_of_card_le outN_subset (by omega)
  have ck : D c k=true := (mem_outN.mp (show k∈outN D B c by rw [hc]; exact kb)).2
  have rev := released_row safe reg bv kb cu (par dm).1 ck (par dm).2
  have eb := card_erase_add_one kb
  have inB := card_le_card (outN_subset : outN D (B.erase k) k ⊆ B.erase k)
  have release : t ≤ (outN D (rotatedCore J d k) k).card+1 := by
    dsimp [t]; change (outN D (rotatedCore J d k) k).card + _ = s at rev; omega
  have Rform := rotatedCore_eq_bank kb bv cu (par dm).1
  change rotatedCore J d k = _ at Rform
  rw [←Rform]
  have rp := same (nb p pl)
  have rq := same (nb q ql)
  have rich (w) (wm : w ∈ (outN D J p \ L) ∪ (outN D J q \ L)) : t+1 ≤ (outN D J w).card := by
    rw [rp,rq] at wm
    rcases mem_union.mp wm with left | right
    · exact (wf pp cp (mem_sdiff.mp left).1).ge
    · exact (wf qq cq (mem_sdiff.mp right).1).ge
  have budget : ((((outN D J p \ L) ∩ (outN D J q \ L)) \ W₀).card ≤ 2+P₀.card) := by
    rw [rp,rq]; exact cap
  have pfloor : t+1 ≤ (outN D J p).card := by rw [rp,pf pp]
  have qfloor : t+1 ≤ (outN D J q).card := by rw [rq,pf qq]
  exact rotated_vacant_payment (W₀:=W₀) (P₀:=P₀) (safe.mono_set Vsub) cj kj (hj dm) ((card_erase_add_one cu).trans size).le no
    lj (off dm) pl ql pq (hj am) (hj bm) ab ad bd (off am) (off bm)
    (fun l ll => ⟨neutral ll am,neutral ll bm⟩)
    (fun e => disjoint_left.mp al (mem_outN.mpr ⟨(loc pl).2,e⟩) pl)
    (fun e => disjoint_left.mp bl (mem_outN.mpr ⟨(loc ql).2,e⟩) ql)
    (dr pl) (dr ql) (mem_outN.mp (common k kb pp)).2 (mem_outN.mp (common k kb qq)).2
    base old release pfloor qfloor rich two budget

#print axioms bank_rotated_payment
end LeanCH.BR.TripleBank
