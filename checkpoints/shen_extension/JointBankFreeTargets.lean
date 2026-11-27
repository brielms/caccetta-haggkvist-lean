import checkpoints.shen_extension.JointBankFreshRepair

/-! Free repairs across a cut, including cuts through the set of short rows. -/
namespace LeanCH.BR.JointFreeTargets
open Finset BRq2 BRq3 BR45 JointFreshRepair

/-- A missing out-neighbour with no return of length one or two on the carrier. -/
def FreeTarget (D : CH.Digraph) (U : Finset ℕ) (c v : ℕ) : Prop :=
  v ∈ U ∧ v ≠ c ∧ D c v ≠ true ∧ D v c ≠ true ∧
    ∀ w ∈ U, D v w = true → D w c ≠ true

/-- Each selected row gains its designated head. -/
def addTargets (D : CH.Digraph) (R : Finset ℕ) (f : ℕ → ℕ) : CH.Digraph :=
  fun a b => decide (D a b = true ∨ (a ∈ R ∧ b = f a))

theorem free_repair {D : CH.Digraph} {U R : Finset ℕ} {f : ℕ → ℕ}
    (safe : QFree D U 3) (heads : ∀ c ∈ R, FreeTarget D U c (f c) ∧ f c ∉ R) :
    QFree (addTargets D R f) U 3 ∧
      ∀ a, (outN (addTargets D R f) U a).card =
        (outN D U a).card + if a ∈ R then 1 else 0 := by
  classical
  let G := addTargets D R f
  have split {a b} (ed : G a b = true) : D a b = true ∨ (a ∈ R ∧ b = f a) :=
    of_decide_eq_true ed
  have fromHead {a b} (ar : a ∈ R) (ed : G (f a) b = true) : D (f a) b = true :=
    (split ed).resolve_right (fun h => (heads a ar).2 h.1)
  have toTail {a b} (ar : a ∈ R) (ed : G b a = true) : D b a = true :=
    (split ed).resolve_right (fun h => (heads b h.1).2 (h.2 ▸ ar))
  have back {a b} (ar : a ∈ R) (bu : b ∈ U) (fb : G (f a) b = true)
      (ba : G b a = true) : False :=
    (heads a ar).1.2.2.2.2 b bu (fromHead ar fb) (toTail ar ba)
  constructor
  · apply DotOriginalStarReturn.qfree_three_of_tests
    · intro a au aa
      rcases split aa with old | ⟨ar,eq⟩
      · exact loopfree safe (by decide) au old
      · exact (heads a ar).1.2.1 eq.symm
    · intro a au b bu ab ba
      rcases split ab with old | ⟨ar,rfl⟩
      · rcases split ba with old' | ⟨br,rfl⟩
        · exact digonfree safe (by decide) au bu old old'
        · exact (heads b br).1.2.2.2.1 old
      · exact (heads a ar).1.2.2.2.1 (fromHead ar ba)
    · intro a au b bu c cu ab bc ca
      rcases split ab with old | ⟨ar,rfl⟩
      · rcases split bc with old' | ⟨br,rfl⟩
        · rcases split ca with old'' | ⟨cr,rfl⟩
          · exact safe a 3 (by decide) (by decide)
              (.step bu old (.step cu old' (.step au old'' (.refl _))))
          · exact back cr bu ab bc
        · exact back br au ca ab
      · exact back ar cu bc ca
  · intro a
    by_cases ar : a ∈ R
    · have head := (heads a ar).1
      have row : outN G U a = insert (f a) (outN D U a) := by
        ext v
        by_cases eq : v = f a <;> simp [G,addTargets,mem_outN,ar,eq,head.1]
      rw [row,card_insert_of_notMem (fun h => head.2.2.1 (mem_outN.mp h).2),ite_eq_left ar]
    · have row : outN G U a = outN D U a := by
        ext v
        simp [G,addTargets,mem_outN,ar]
      rw [row,ite_eq_right ar,Nat.add_zero]

/-- Free heads remain safe after the paid edit. A paid shortcut leaving a
free head can only go to z, and z has no edge into any short row. -/
theorem free_after_edit {D : CH.Digraph} {U J : Finset ℕ} {z e c v : ℕ}
    (head : FreeTarget D U c v) (outside : c ∉ J) (cz : c ≠ z) (zc : D z c ≠ true) :
    FreeTarget (edit D J z e) U c v := by
  have split {a b} (ed : edit D J z e a b = true) : D a b = true ∨ a ∈ J ∧ b = z := by
    rcases of_decide_eq_true ed with new | ⟨old,_,_⟩
    · exact Or.inr new
    · exact Or.inl old
  refine ⟨head.1,head.2.1,?_,?_,?_⟩
  · intro edge
    exact head.2.2.1 ((split edge).resolve_right (fun h => outside h.1))
  · intro edge
    exact head.2.2.2.1 ((split edge).resolve_right (fun h => cz h.2))
  · intro w wu vw wc
    have old := (split wc).resolve_right (fun h => cz h.2)
    rcases split vw with first | ⟨_,rfl⟩
    · exact head.2.2.2.2 w wu first old
    · exact zc old


private theorem retained_floor {D : CH.Digraph} {V : Finset ℕ} {s p h c : ℕ}
    (reg : OutEq s D V) (cv : c ∈ V) (ph : p ≠ h) :
    s-1 ≤ (outN D (V \ {p,h}) c).card + 1 := by
  let B : Finset ℕ := {p,h}
  have row : outN D (V \ B) c = outN D V c \ B := by
    ext w; simp only [mem_sdiff,mem_outN]; tauto
  have split := card_sdiff_add_card_inter (outN D V c) B
  have cap := card_le_card (inter_subset_right : outN D V c ∩ B ⊆ B)
  rw [reg c cv] at split
  rw [show B.card = 2 from card_pair ph] at cap
  change s-1 ≤ (outN D (V \ B) c).card + 1
  rw [row]
  omega

private theorem retained_target {D : CH.Digraph} {V : Finset ℕ} {p h c v : ℕ}
    (cs : c ∈ inN D V p ∩ inN D V h) (target : FreeTarget D V c v) :
    FreeTarget D (V \ {p,h}) c v := by
  obtain ⟨cp,ch⟩ := mem_inter.mp cs
  have vp : v ≠ p := fun eq => target.2.2.1 (eq ▸ (mem_inN.mp cp).2)
  have vh : v ≠ h := fun eq => target.2.2.1 (eq ▸ (mem_inN.mp ch).2)
  exact ⟨mem_sdiff.mpr ⟨target.1,by simp [vp,vh]⟩,target.2.1,target.2.2.1,
    target.2.2.2.1,fun w wu => target.2.2.2.2 w (mem_sdiff.mp wu).1⟩

private theorem survivor_size {V : Finset ℕ} {p h s : ℕ} (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (room : V.card = 3*(s-1)+2) :
    (V \ {p,h}).card = 3*(s-1) := by
  rw [card_sdiff_of_subset (insert_subset pv (singleton_subset_iff.mpr hv)),card_pair ph,room]
  omega

/-- A hypothetical source must defeat every cut through its short rows. A
free row may target a short row on the other side, including a paid row. -/
theorem remaining_obstruction {D : CH.Digraph} {V R : Finset ℕ} {s p h z : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z=true) (hz : D h z=true)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1))
    (selected : R ⊆ inN D V p ∩ inN D V h)
    (heads : ∀ c ∈ R, ∃ v, FreeTarget D V c v ∧ v ∉ R) :
    let U := V \ {p,h}
    let J := (inN D V p ∩ inN D V h) \ R
    (∃ c ∈ J, D c z = true) ∨
      ∃ w ∈ outN D U z, ∃ v ∈ outN D U z, w ≠ v ∧
        2 ≤ (outN D U w ∩ J).card ∧ 2 ≤ (outN D U v ∩ J).card := by
  classical
  let U := V \ {p,h}
  let S := inN D V p ∩ inN D V h
  let J := S \ R
  change (∃ c ∈ J, D c z = true) ∨ _
  by_cases direct : ∃ c ∈ J, D c z = true
  · exact Or.inl direct
  right
  by_contra absent
  change (¬∃ w ∈ outN D U z, ∃ v ∈ outN D U z, w ≠ v ∧
    2 ≤ (outN D U w ∩ J).card ∧ 2 ≤ (outN D U v ∩ J).card) at absent
  have except : ∃ e, ∀ w ∈ outN D U z, w ≠ e → (outN D U w ∩ J).card ≤ 1 := by
    by_cases bad : ∃ v ∈ outN D U z, 2 ≤ (outN D U v ∩ J).card
    · obtain ⟨v,vz,debt⟩ := bad
      refine ⟨v,fun w wz wv => ?_⟩
      by_contra! excess
      exact absent ⟨w,wz,v,vz,wv,by omega,debt⟩
    · exact ⟨z,fun w wz _ => by
        by_contra! excess
        exact bad ⟨w,wz,by omega⟩⟩
  obtain ⟨e,cost⟩ := except
  let E := edit D J z e
  obtain ⟨safe,short⟩ := repair_deleted_pair (J := J) free reg hs pv hv ph zv pz hz
    sdiff_subset (fun c cj ed => direct ⟨c,cj,ed⟩) cost
  change U.filter (fun u => (outN E U u).card < s-1) = S \ J at short
  let f (c : ℕ) := if cr : c ∈ R then (heads c cr).choose else z
  have chosen (c) (cr : c ∈ R) : FreeTarget D V c (f c) ∧ f c ∉ R := by
    simpa [f,cr] using (heads c cr).choose_spec
  have untouched (c) (cr : c ∈ R) : c ∉ J ∧ c ≠ z ∧ D z c ≠ true := by
    obtain ⟨cv,cp⟩ := mem_inN.mp (mem_inter.mp (selected cr)).1
    refine ⟨fun cj => (mem_sdiff.mp cj).2 cr,
      fun eq => digonfree free (by decide) pv zv pz (eq ▸ cp),?_⟩
    intro zc
    exact free c 3 (by decide) (by decide) (.step pv cp (.step zv pz (.step cv zc (.refl _))))
  obtain ⟨ok,rows⟩ := free_repair (f := f) safe (fun c cr => by
    obtain ⟨cj,cz,zc⟩ := untouched c cr
    exact ⟨free_after_edit (retained_target (selected cr) (chosen c cr).1) cj cz zc,
      (chosen c cr).2⟩)
  have size : U.card = 3*(s-1) := survivor_size pv hv ph room
  apply none (addTargets E R f) U (card_pos.mp (by omega)) size.le ok
  intro c cu
  rw [rows]
  by_cases cr : c ∈ R
  · obtain ⟨cj,cz,zc⟩ := untouched c cr
    have eq : outN E U c = outN D U c := by
      ext w; simp [E,edit,mem_outN,cj,cz,zc]
    rw [ite_eq_left cr,eq]
    exact retained_floor reg (mem_sdiff.mp cu).1 ph
  · rw [ite_eq_right cr,Nat.add_zero]
    by_contra! low
    have shortRow : c ∈ U.filter (fun a => (outN E U a).card < s-1) := mem_filter.mpr ⟨cu,low⟩
    rw [short] at shortRow
    obtain ⟨cs,cj⟩ := mem_sdiff.mp shortRow
    exact cj (mem_sdiff.mpr ⟨cs,cr⟩)



/-- With precisely two short rows, a free head anywhere for one row forces
the other row to see every common target of the deleted labels. -/
theorem other_row_hits_target {D : CH.Digraph} {V : Finset ℕ} {s p h z c d : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z=true) (hz : D h z=true)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1))
    (rows : inN D V p ∩ inN D V h = {c,d}) (cd : c ≠ d)
    (head : ∃ v, FreeTarget D V c v) : D d z = true := by
  classical
  obtain ⟨v,fv⟩ := head
  have candidates (a) (ac : a ∈ ({c} : Finset ℕ)) : ∃ w, FreeTarget D V a w ∧ w ∉ ({c} : Finset ℕ) := by
    obtain rfl := mem_singleton.mp ac
    exact ⟨v,fv,fun vc => fv.2.1 (mem_singleton.mp vc)⟩
  have selected : ({c} : Finset ℕ) ⊆ inN D V p ∩ inN D V h := by simp [rows]
  have obs := remaining_obstruction free reg hs pv hv ph zv pz hz room none selected candidates
  have rest : (inN D V p ∩ inN D V h) \ {c} = {d} := by
    rw [rows]
    ext w
    simp only [mem_sdiff,mem_insert,mem_singleton]
    grind
  dsimp only at obs
  rw [rest] at obs
  rcases obs with ⟨a,ad,az⟩ | ⟨w,_,_,_,_,debt,_⟩
  · rwa [mem_singleton.mp ad] at az
  · have small := card_le_card (inter_subset_right : outN D (V \ {p,h}) w ∩ {d} ⊆ {d})
    simp only [card_singleton] at small
    omega

#print axioms other_row_hits_target

/-- Intrinsic locked rows for the deleted pair. The common target z plays
no role in this set. -/
noncomputable def lockedRows (D : CH.Digraph) (V S : Finset ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun c => ∀ v, FreeTarget D V c v → v ∈ S)

theorem locked_obstruction {D : CH.Digraph} {V : Finset ℕ} {s p h z : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z=true) (hz : D h z=true)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    let U := V \ {p,h}
    let L := lockedRows D V (inN D V p ∩ inN D V h)
    (∃ c ∈ L, D c z = true) ∨
      ∃ w ∈ outN D U z, ∃ v ∈ outN D U z, w ≠ v ∧
        2 ≤ (outN D U w ∩ L).card ∧ 2 ≤ (outN D U v ∩ L).card := by
  classical
  let S := inN D V p ∩ inN D V h
  let L := lockedRows D V S
  let R := S \ L
  have choice (c) (cr : c ∈ R) : ∃ v, FreeTarget D V c v ∧ v ∉ R := by
    obtain ⟨cs,off⟩ := mem_sdiff.mp cr
    have bad : ¬ ∀ v, FreeTarget D V c v → v ∈ S := fun h => off (mem_filter.mpr ⟨cs,h⟩)
    push Not at bad
    obtain ⟨v,fv,vs⟩ := bad
    exact ⟨v,fv,fun vr => vs (mem_sdiff.mp vr).1⟩
  have obs := remaining_obstruction free reg hs pv hv ph zv pz hz room none
    (show R ⊆ S from sdiff_subset) choice
  have eq : S \ R = L := by
    ext c
    have sub : L ⊆ S := filter_subset _ _
    simp only [R,mem_sdiff]
    constructor
    · rintro ⟨cs,off⟩; by_contra cl; exact off ⟨cs,cl⟩
    · exact fun cl => ⟨sub cl,fun h => h.2 cl⟩
  dsimp only at obs ⊢
  have labels : (inN D V p ∩ inN D V h) \ R = L := eq
  simpa only [labels] using obs

/-- Heads shared by c and every free target of c, before any labels are deleted. -/
noncomputable def sharedHeads (D : CH.Digraph) (V : Finset ℕ) (c : ℕ) : Finset ℕ := by
  classical
  exact (outN D V c).filter (fun p => ∀ v, FreeTarget D V c v → D v p = true)

/-- Every pair of labels lies together in one shared-head set. The witnessing
row and all of its free targets point to both labels. No choice of z is needed. -/
theorem pair_covered {D : CH.Digraph} {V : Finset ℕ} {s p h : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ c ∈ V, p ∈ sharedHeads D V c ∧ h ∈ sharedHeads D V c := by
  classical
  let U := V \ {p,h}
  let S := inN D V p ∩ inN D V h
  have locked : ∃ c ∈ S, ∀ v, FreeTarget D V c v → v ∈ S := by
    by_contra! fail
    let f (c : ℕ) := if cs : c ∈ S then (fail c cs).choose else p
    have heads (c) (cs : c ∈ S) : FreeTarget D U c (f c) ∧ f c ∉ S := by
      have spec := (fail c cs).choose_spec
      rw [show f c = (fail c cs).choose by simp [f,cs]]
      exact ⟨retained_target cs spec.1,spec.2⟩
    obtain ⟨safe,rows⟩ := free_repair (free.mono_set (show U ⊆ V from sdiff_subset)) heads
    have size : U.card = 3*(s-1) := survivor_size pv hv ph room
    apply none _ U (card_pos.mp (by omega)) size.le safe
    intro c cu
    rw [rows]
    by_cases cs : c ∈ S
    · rw [ite_eq_left cs]
      exact retained_floor reg (mem_sdiff.mp cu).1 ph
    · rw [ite_eq_right cs,Nat.add_zero]
      by_contra! low
      have shorts := BypassBankReplay.short_rows_eq_jointParents free (by decide) reg pv hv ph hs
      have hit : c ∈ U.filter (fun u => (outN D U u).card < s-1) := mem_filter.mpr ⟨cu,low⟩
      rw [shorts] at hit
      obtain ⟨cp,ch⟩ := mem_inN.mp hit
      exact cs (mem_inter.mpr ⟨cp,mem_inN.mpr ⟨(mem_inN.mp cp).1,ch⟩⟩)
  obtain ⟨c,cs,allHeads⟩ := locked
  obtain ⟨cp,ch⟩ := mem_inter.mp cs
  refine ⟨c,(mem_inN.mp cp).1,mem_filter.mpr ⟨mem_outN.mpr ⟨pv,(mem_inN.mp cp).2⟩,?_⟩,
    mem_filter.mpr ⟨mem_outN.mpr ⟨hv,(mem_inN.mp ch).2⟩,?_⟩⟩
  · exact fun v fv => (mem_inN.mp (mem_inter.mp (allHeads v fv)).1).2
  · exact fun v fv => (mem_inN.mp (mem_inter.mp (allHeads v fv)).2).2

/-- If the pair has a unique common predecessor, that vertex has no free target
anywhere on the original carrier, including when the pair has no common successor. -/
theorem singleton_saturated {D : CH.Digraph} {V : Finset ℕ} {s p h c : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1))
    (single : inN D V p ∩ inN D V h = {c}) : ∀ v, ¬FreeTarget D V c v := by
  classical
  obtain ⟨a,av,ap,ah⟩ := pair_covered free reg hs pv hv ph room none
  have unique (b) (bv : b ∈ V) (bp : D b p = true) (bh : D b h = true) : b = c := by
    have joint := mem_inter.mpr ⟨mem_inN.mpr ⟨bv,bp⟩,mem_inN.mpr ⟨bv,bh⟩⟩
    rw [single] at joint
    exact mem_singleton.mp joint
  obtain ⟨edgeP,allP⟩ := mem_filter.mp ap
  obtain ⟨edgeH,allH⟩ := mem_filter.mp ah
  obtain rfl := unique a av (mem_outN.mp edgeP).2 (mem_outN.mp edgeH).2
  intro v fv
  exact fv.2.1 (unique v fv.1 (allP v fv) (allH v fv))

/-- Summing the number of ordered distinct pairs in the shared-head sets
gives a necessary bound before any bank is chosen. -/
theorem pair_count {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    V.card * (V.card-1) ≤
      ∑ c ∈ V, (sharedHeads D V c).card * ((sharedHeads D V c).card-1) := by
  classical
  have cover : V.offDiag ⊆ V.biUnion (fun c => (sharedHeads D V c).offDiag) := by
    intro ⟨p,h⟩ pair
    obtain ⟨pv,hv,ph⟩ := mem_offDiag.mp pair
    obtain ⟨c,cv,cp,ch⟩ := pair_covered free reg hs pv hv ph room none
    exact mem_biUnion.mpr ⟨c,cv,mem_offDiag.mpr ⟨cp,ch,ph⟩⟩
  have count := (card_le_card cover).trans (card_biUnion_le)
  simpa only [offDiag_card,Nat.mul_sub,Nat.mul_one] using count

/-- For each label p, at least four rows have two or more shared heads,
one of which is p. Each such row covers at most s-1 partners of p. -/
theorem four_rows_through {D : CH.Digraph} {V : Finset ℕ} {s p : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    4 ≤ (V.filter (fun c => p ∈ sharedHeads D V c ∧ 2 ≤ (sharedHeads D V c).card)).card := by
  classical
  let K := sharedHeads D V
  let rows := V.filter (fun c => p ∈ K c ∧ 2 ≤ (K c).card)
  have cover : V.erase p ⊆ rows.biUnion (fun c => (K c).erase p) := by
    intro h hm
    obtain ⟨hp,hv⟩ := mem_erase.mp hm
    obtain ⟨c,cv,cp,ch⟩ := pair_covered free reg hs pv hv hp.symm room none
    have two : 2 ≤ (K c).card := one_lt_card.mpr ⟨p,cp,h,ch,hp.symm⟩
    exact mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨cv,cp,two⟩,mem_erase.mpr ⟨hp,ch⟩⟩
  have small (c) (cr : c ∈ rows) : ((K c).erase p).card ≤ s-1 := by
    obtain ⟨cv,cp,_⟩ := mem_filter.mp cr
    have sub : K c ⊆ outN D V c := filter_subset _ _
    have bound := card_le_card sub
    rw [reg c cv] at bound
    rw [card_erase_of_mem cp]
    omega
  have bound := ((card_le_card cover).trans card_biUnion_le).trans (sum_le_sum small)
  rw [card_erase_of_mem pv,sum_const,smul_eq_mul] at bound
  change 4 ≤ rows.card
  by_contra! few
  have lim := Nat.mul_le_mul_right (s-1) (show rows.card ≤ 3 by omega)
  omega

#print axioms four_rows_through
#print axioms locked_obstruction
#print axioms singleton_saturated
#print axioms pair_count
#print axioms free_repair
#print axioms free_after_edit
#print axioms remaining_obstruction
#print axioms pair_covered

end LeanCH.BR.JointFreeTargets

