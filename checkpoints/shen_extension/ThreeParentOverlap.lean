import checkpoints.shen_extension.TightParentNeutral

/-! Equality at three tight parents forces two outgoing rows to overlap.
All neighborhoods are computed on the same surviving labels. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

private theorem erased_separation {D : CH.Digraph} {U : Finset ℕ} {a c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (parent : a ∈ tightParents D U c t) (miss : D a k ≠ true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (v) (vu : v ∈ U) (vc : v ≠ c) :
    ∃ x ∈ (tightParents D U c t).erase a, D x v ≠ true := by
  obtain ⟨E,ok,floor,new,keep⟩ := promote_parent safe cu ku ck parent miss spare others
  obtain ⟨x,xu,_,xc,cap,absent⟩ := BypassCloneCover.misses_copy no small ok cu vu vc floor
  have xm : x ∈ tightParents E U c t := mem_filter.mpr ⟨mem_inN.mpr ⟨xu,xc⟩,cap.le⟩
  rw [new] at xm
  have par := (mem_filter.mp (mem_erase.mp xm).2).1
  refine ⟨x,xm,?_⟩
  intro ed
  have vm : v ∈ outN E U x := by
    rw [keep x par (mem_erase.mp xm).1]
    exact mem_outN.mpr ⟨vu,ed⟩
  exact absent (mem_outN.mp vm).2

/-- In the equality case the sink d has precisely L and c as its row.
The other two parents miss L, and their heads off c,d all point to d. -/
theorem three_parent_structure {D : CH.Digraph} {U L : Finset ℕ} {c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c)
    (three : (tightParents D U c t).card = 3) :
    let H := tightParents D U c t
    ∃ a b d, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ H = {a,b,d} ∧
      (D a k ≠ true ∧ D b k ≠ true ∧ D d k = true) ∧
      (∀ h ∈ H, D d h ≠ true) ∧ (outN D U d).erase c = L ∧
      Disjoint (outN D U a) L ∧ Disjoint (outN D U b) L ∧
      ∀ v ∈ (outN D U a ∪ outN D U b).erase c, v ≠ d → D v d = true := by
  classical
  intro H
  change H.card = 3 at three
  have hu : H ⊆ U := fun _ m => (mem_inN.mp (mem_filter.mp m).1).1
  have pc {v} (vm : v ∈ H) := (mem_inN.mp (mem_filter.mp vm).1).2
  have nc {v} (vm : v ∈ H) : v ≠ c := fun e => loopfree safe (by decide) cu (e ▸ pc vm)
  have deg {v} (vm : v ∈ H) : (outN D U v).card = t := le_antisymm
    (mem_filter.mp vm).2 (others v (hu vm) (nc vm))
  have succ {v} (vm : v ∈ H) (abs : D v k ≠ true) :=
    parent_has_successor safe cu ku ck small no others vm abs spare sat clear
  obtain ⟨d,dm,sink⟩ := exists_sink (safe.mono_set hu) (card_pos.mp (by omega : 0 < H.card)) three.le
  have dk : D d k = true := by
    by_contra abs
    obtain ⟨h,hm,dh⟩ := succ dm abs
    exact sink h (mem_erase.mp hm).2 dh
  have kc : k ≠ c := fun e => loopfree safe (by decide) cu (e ▸ ck)
  obtain ⟨a,au,_,ac,cap,ak⟩ := BypassCloneCover.misses_copy no small safe cu ku kc others
  have am : a ∈ H := mem_filter.mpr ⟨mem_inN.mpr ⟨au,ac⟩,cap.le⟩
  have ad : a ≠ d := fun e => ak (e ▸ dk)
  obtain ⟨b,bm',bk⟩ := erased_separation safe cu ku ck small no others am ak spare k ku kc
  obtain ⟨ba,bm⟩ := mem_erase.mp bm'
  have bd : b ≠ d := fun e => bk (e ▸ dk)
  have triple : H = {a,b,d} := by
    apply (eq_of_subset_of_card_le (insert_subset am (insert_subset bm (singleton_subset_iff.mpr dm))) ?_).symm
    rw [show H.card = 3 from three,card_insert_of_notMem (by simp [ba.symm,ad]),card_pair bd]
  have casesH {x} (xm : x ∈ H) : x = a ∨ x = b ∨ x = d := by simpa [triple] using xm
  have hit {u v} (um : u ∈ H) (uk : D u k ≠ true) (vu : v ∈ U) (vc : v ≠ c)
      (out : v ∉ H.erase u) (vl : v ∉ L) :
      ∃ h ∈ H.erase u, D v h = true := by
    have eq := neutral_after_promotion safe cu ku ck small no others um uk spare sat clear
    by_contra! all
    exact vl (eq ▸ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨vc,vu⟩,out⟩,
      disjoint_left.mpr (fun z zm zh => all z zh (mem_outN.mp zm).2)⟩ :
      v ∈ neutral D U (H.erase u) c))
  have intoD : D a d = true ∨ D b d = true := by
    obtain ⟨x,xm,ax⟩ := succ am ak
    obtain ⟨y,ym,by'⟩ := succ bm bk
    have cx := casesH (mem_erase.mp xm).2
    have cy := casesH (mem_erase.mp ym).2
    have xa := (mem_erase.mp xm).1
    have yb := (mem_erase.mp ym).1
    have no2 := digonfree safe (by decide) au (hu bm)
    grind
  have drow : (outN D U d).erase c = L := by
    have inc : (outN D U d).erase c ⊆ L := by
      intro v vm
      obtain ⟨vc,ed⟩ := mem_erase.mp vm
      obtain ⟨vu,dv⟩ := mem_outN.mp ed
      have vh : v ∉ H := fun m => sink v m dv
      have back := digonfree safe (by decide) (hu dm) vu dv
      by_contra vl
      have use {u j} (um : u ∈ H) (uk : D u k ≠ true) (jd : D j d = true)
          (ju : j ∈ U) (pair : ∀ x ∈ H.erase u, x = j ∨ x = d) : False := by
        obtain ⟨x,xm,vx⟩ := hit um uk vu vc (fun m => vh (mem_erase.mp m).2) vl
        rcases pair x xm with rfl | rfl
        · exact safe x 3 (by decide) (by decide) (.step (hu dm) jd (.step vu dv (.step ju vx (.refl _))))
        · exact back vx
      rcases intoD with ah | bh
      · exact use bm bk ah au (fun x xm => (casesH (mem_erase.mp xm).2).elim Or.inl
          (fun alt => Or.inr (alt.resolve_left (mem_erase.mp xm).1)))
      · exact use am ak bh (hu bm) (fun x xm => (casesH (mem_erase.mp xm).2).resolve_left (mem_erase.mp xm).1)
    have cnt := card_erase_add_one (mem_outN.mpr ⟨cu,pc dm⟩)
    rw [deg dm] at cnt
    exact eq_of_subset_of_card_le inc (by omega)
  have dis {u j} (um : u ∈ H) (uk : D u k ≠ true)
      (pair : ∀ x ∈ H.erase u, x = j ∨ x = d) : Disjoint (outN D U j) L := by
    apply disjoint_left.mpr
    intro v vm vl
    have ve : v ∈ (outN D U d).erase c := drow ▸ vl
    obtain ⟨vc,dv⟩ := mem_erase.mp ve
    obtain ⟨x,xm,abs⟩ := erased_separation safe cu ku ck small no others um uk spare v (outN_subset vm) vc
    rcases pair x xm with rfl | rfl
    · exact abs (mem_outN.mp vm).2
    · exact abs (mem_outN.mp dv).2
  have pa (x) (xm : x ∈ H.erase a) : x = b ∨ x = d :=
    (casesH (mem_erase.mp xm).2).resolve_left (mem_erase.mp xm).1
  have pb (x) (xm : x ∈ H.erase b) : x = a ∨ x = d :=
    (casesH (mem_erase.mp xm).2).elim Or.inl (fun alt => Or.inr (alt.resolve_left (mem_erase.mp xm).1))
  have da := dis bm bk pb
  have db := dis am ak pa
  refine ⟨a,b,d,ba.symm,ad,bd,triple,⟨ak,bk,dk⟩,sink,drow,da,db,?_⟩
  intro v vm vd
  obtain ⟨vc,old⟩ := mem_erase.mp vm
  have route {u j} (um : u ∈ H) (uk : D u k ≠ true) (ju : j ∈ U)
      (pair : ∀ x ∈ H.erase u, x = j ∨ x = d) (jv : v ∈ outN D U j)
      (outside : Disjoint (outN D U j) L) : D v d = true := by
    obtain ⟨vu,edge⟩ := mem_outN.mp jv
    have vj : v ≠ j := fun e => loopfree safe (by decide) ju (e ▸ edge)
    obtain ⟨x,xm,vx⟩ := hit um uk vu vc (fun m => (pair v m).elim vj vd)
      (disjoint_left.mp outside jv)
    rcases pair x xm with rfl | rfl
    · exact (digonfree safe (by decide) ju vu edge vx).elim
    · exact vx
  exact (mem_union.mp old).elim (fun h => route bm bk au pb h da) (fun h => route am ak (hu bm) pa h db)

/-- Count the positions available to a row of L after excluding the heads
of a,b and c. The overlap is counted off c on the original survivor set. -/
theorem overlap_price {D : CH.Digraph} {U L : Finset ℕ} {a b c d t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (du : d ∈ U) (size : U.card = 3*t)
    (sat : L.card + 1 = t) (noBack : ∀ l ∈ L, D l c ≠ true)
    (ac : D a c = true) (bc : D b c = true)
    (da : (outN D U a).card = t) (db : (outN D U b).card = t)
    (drow : (outN D U d).erase c = L)
    (al : Disjoint (outN D U a) L) (bl : Disjoint (outN D U b) L)
    (gate : ∀ v ∈ (outN D U a ∪ outN D U b).erase c, v ≠ d → D v d = true) :
    let A := (outN D U a).erase c
    let B := (outN D U b).erase c
    ∀ l ∈ L, (outN D U l).card ≤ (outN D L l).card + 2 + (A ∩ B).card := by
  classical
  intro A B l lm
  have ld : l ∈ (outN D U d).erase c := drow ▸ lm
  have lh := (mem_erase.mp ld).2
  have lu := outN_subset lh
  have dl := (mem_outN.mp lh).2
  have cA := card_erase_add_one (mem_outN.mpr ⟨cu,ac⟩)
  have cB := card_erase_add_one (mem_outN.mpr ⟨cu,bc⟩)
  rw [da] at cA
  rw [db] at cB
  change A.card+1=t at cA
  change B.card+1=t at cB
  let T := (A ∪ B) ∪ L
  have sub : T ⊆ U.erase c := by
    intro v vm
    rcases mem_union.mp vm with ab | vl
    · rcases mem_union.mp ab with x | x <;>
        exact mem_erase.mpr ⟨(mem_erase.mp x).1,outN_subset (mem_erase.mp x).2⟩
    · have vm : v ∈ (outN D U d).erase c := drow ▸ vl
      exact mem_erase.mpr ⟨(mem_erase.mp vm).1,outN_subset (mem_erase.mp vm).2⟩
  have dis : Disjoint (A ∪ B) L := disjoint_left.mpr (fun v vm vl =>
    (mem_union.mp vm).elim (fun h => disjoint_left.mp al (mem_erase.mp h).2 vl)
      (fun h => disjoint_left.mp bl (mem_erase.mp h).2 vl))
  have cnt : T.card = (A∪B).card + L.card := card_union_of_disjoint dis
  have count := card_union_add_card_inter A B
  have rest := card_sdiff_of_subset sub
  rw [card_erase_of_mem cu,size] at rest
  have limit : ((U.erase c) \ T).card = (A ∩ B).card+2 := by omega
  have incl : outN D U l \ L ⊆ (U.erase c) \ T := by
    intro v vm
    obtain ⟨old,vl⟩ := mem_sdiff.mp vm
    obtain ⟨vu,lv⟩ := mem_outN.mp old
    have vc : v ≠ c := fun e => noBack l lm (e ▸ lv)
    refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨vc,vu⟩,?_⟩
    intro block
    rcases mem_union.mp block with ab | inside
    · have row : v ∈ (outN D U a ∪ outN D U b).erase c := mem_erase.mpr ⟨vc,
        (mem_union.mp ab).elim (fun h => mem_union_left _ (mem_erase.mp h).2)
          (fun h => mem_union_right _ (mem_erase.mp h).2)⟩
      by_cases vd : v = d
      · exact digonfree safe (by decide) du lu dl (vd ▸ lv)
      · exact safe d 3 (by decide) (by decide) (.step lu dl (.step vu lv
          (.step du (gate _ row vd) (.refl _))))
    · exact vl inside
  have inner : outN D U l ∩ L = outN D L l := by
    ext v; simp only [mem_inter,mem_outN]
    have inside (h : v ∈ L) : v ∈ U := outN_subset (mem_erase.mp (drow ▸ h)).2
    tauto
  have add := card_sdiff_add_card_inter (outN D U l) L
  rw [inner] at add
  have bound := card_le_card incl
  omega

/-- A row with low internal degree always exists in an oriented set. -/
private theorem low_internal {D : CH.Digraph} {L : Finset ℕ}
    (safe : QFree D L 3) (live : L.Nonempty) :
    ∃ l ∈ L, 2*(outN D L l).card ≤ L.card-1 := by
  classical
  by_contra! high
  have row (l) (lm : l ∈ L) : (inN D L l).card < (outN D L l).card := by
    have dis : Disjoint (inN D L l) (outN D L l) := disjoint_left.mpr (fun w inc out =>
      digonfree safe (by decide) lm (outN_subset out) (mem_outN.mp out).2 (mem_inN.mp inc).2)
    have sub : inN D L l ∪ outN D L l ⊆ L.erase l := by
      intro w wm
      rcases mem_union.mp wm with inc | out
      · obtain ⟨wu,wl⟩ := mem_inN.mp inc
        exact mem_erase.mpr ⟨fun e => loopfree safe (by decide) lm (e ▸ wl),wu⟩
      · obtain ⟨wu,lw⟩ := mem_outN.mp out
        exact mem_erase.mpr ⟨fun e => loopfree safe (by decide) lm (e ▸ lw),wu⟩
    have bound := card_le_card sub
    rw [card_union_of_disjoint dis,card_erase_of_mem lm] at bound
    have pos := high l lm
    omega
  have less := sum_lt_sum_of_nonempty live row
  have eq : (∑ v ∈ L, (outN D L v).card) = ∑ v ∈ L, (inN D L v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D L
  omega

/-- The three-parent frontier forces overlap linear in t for a single pair
of parents. The inequality at each l also accepts any available smaller
degree induction hypothesis on L. -/
theorem three_parent_overlap {D : CH.Digraph} {U L : Finset ℕ} {c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (size : U.card = 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (kl : k ∈ L) (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c)
    (noBack : ∀ l ∈ L, D l c ≠ true) (three : (tightParents D U c t).card = 3) :
    let H := tightParents D U c t
    ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧
      let M := ((outN D U a).erase c) ∩ ((outN D U b).erase c)
      t ≤ 2*M.card+2 ∧ ∀ l ∈ L, t ≤ (outN D L l).card + 2 + M.card := by
  classical
  intro H
  obtain ⟨a,b,d,ab,_,_,triple,_,_,drow,al,bl,gate⟩ :=
    three_parent_structure safe cu ku ck size.le no others spare sat clear three
  change H = {a,b,d} at triple
  have am : a ∈ H := triple ▸ mem_insert_self _ _
  have bm : b ∈ H := triple ▸ mem_insert_of_mem (mem_insert_self _ _)
  have dm : d ∈ H := triple ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have row {v} (vm : v ∈ H) := mem_inN.mp (mem_filter.mp vm).1
  have deg {v} (vm : v ∈ H) : (outN D U v).card = t := le_antisymm (mem_filter.mp vm).2
    (others v (row vm).1 (fun e => loopfree safe (by decide) cu (e ▸ (row vm).2)))
  have bill := overlap_price safe cu (row dm).1 size sat noBack (row am).2 (row bm).2
    (deg am) (deg bm) drow al bl gate
  let M := ((outN D U a).erase c) ∩ ((outN D U b).erase c)
  have whereL {v} (vl : v ∈ L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear vl)).1).1
  have each (l) (lm : l ∈ L) : t ≤ (outN D L l).card + 2 + M.card :=
    (others l (whereL lm).2 (whereL lm).1).trans (bill l lm)
  obtain ⟨l,lm,low⟩ := low_internal (safe.mono_set (fun _ h => (whereL h).2)) ⟨k,kl⟩
  have room := each l lm
  refine ⟨a,am,b,bm,ab,?_,each⟩
  change t ≤ 2*M.card+2
  have pos := card_pos.mpr (show L.Nonempty from ⟨k,kl⟩)
  omega

/-- At the capstone's selected lone frontier the smaller-degree induction
on L strengthens the overlap bound to 2t ≤ 3|M|+4 for the same pair. -/
theorem bank_overlap {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 4 ≤ s) (order : V.card = 3*s)
    (lower : ∀ r, r < s → BypassRepair.NoHost 3 r) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (hits : (outN D B c).card = 3)
    (lone : ∀ a ∈ V \ B, a ≠ c → (outN D B a).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true)
    (equality : (tightParents D (V \ B) c (s-1)).card = 3) :
    let U := V \ B
    let H := tightParents D U c (s-1)
    ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧
      let M := ((outN D U a).erase c) ∩ ((outN D U b).erase c)
      M.Nonempty ∧ 2*(s-1) ≤ 3*M.card+4 := by
  classical
  intro U H
  let t := s-1
  have no := lower t (by dsimp [t]; omega)
  obtain ⟨z,_,_,sat,neutralEq,nb,rest,k,_,kl,ku,ck,full⟩ :=
    bank_saturation safe reg (by omega) order no sub three pv many common cu hits lone menu miss
  let L := insert z (outN D U c)
  change L.card+1 = t at sat
  change neutral D U H c = L at neutralEq
  change k ∈ L at kl
  have size : U.card = 3*t := by
    change (V \ B).card = 3*(s-1); rw [card_sdiff_of_subset sub,order,three]; omega
  have spare (w) (wm : w ∈ outN D U k) : t < (outN D U w).card := by
    rw [full w wm]; dsimp [t]; omega
  obtain ⟨a,am,b,bm,ab,_,each⟩ := three_parent_overlap (safe.mono_set (sdiff_subset : U ⊆ V))
    cu ku ck size no rest spare kl sat neutralEq.ge nb equality
  let M := ((outN D U a).erase c) ∩ ((outN D U b).erase c)
  let r := (t-2)/3+1
  have inside : L ⊆ U := fun l lm => (mem_erase.mp (mem_sdiff.mp
    (mem_filter.mp (neutralEq.ge lm)).1).1).2
  have quota := lower r (by dsimp [r,t]; omega)
  have small : L.card ≤ 3*r := by dsimp [r]; omega
  have low : ∃ l ∈ L, (outN D L l).card < r := by
    by_contra! every
    exact quota D L ⟨k,kl⟩ small (safe.mono_set (inside.trans sdiff_subset)) every
  obtain ⟨l,lm,lc⟩ := low
  have bound := each l lm
  change t ≤ (outN D L l).card + 2 + M.card at bound
  dsimp [r] at lc
  have overlap : 2*t ≤ 3*M.card+4 := by omega
  have enough : 3 ≤ t := by dsimp [t]; omega
  exact ⟨a,am,b,bm,ab,card_pos.mp (by omega : 0 < M.card),overlap⟩

#print axioms bank_overlap
#print axioms three_parent_overlap
#print axioms overlap_price
#print axioms three_parent_structure
end LeanCH.BR.TripleBank
