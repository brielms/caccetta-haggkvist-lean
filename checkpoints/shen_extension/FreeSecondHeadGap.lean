import checkpoints.shen_extension.SponsoredHeadPool

/-! A pool of second heads that need no cuts into their own parent bank. -/
namespace LeanCH.BR.Closure.FreeSecondHead
open Finset BRq2 BRq3 TwoReplacement TwoReplacement.NearMiss DeficitLevels

def invisible (D : CH.Digraph) (W J : Finset ℕ) : Finset ℕ :=
  (W \ J).filter (fun h => Disjoint (outN D W h) J)

/-- The usual sponsored-head reduction also holds for any d rows invisible to J. -/
theorem free_second {D : CH.Digraph} {W P J : Finset ℕ} {d : ℕ}
    (base : ∀ x ∈ W, d ≤ (outN D W x).card + credit P J x)
    (second : d ≤ (invisible D W J).card) :
    Feasible D W P J d ↔ d ≤ (pool D W P J P d).card := by
  constructor
  · exact fun t => t.2.1
  intro first
  let H := invisible D W J
  have extend {x} (hx : x ∈ H) {K : Finset ℕ} (mem : x ∈ pool D W P J K d) :
      x ∈ pool D W P J (K ∪ J) d := by
    obtain ⟨xj,cut⟩ := mem_filter.mp hx
    obtain ⟨xw,noJ⟩ := mem_sdiff.mp xj
    obtain ⟨xk,paid⟩ := mem_filter.mp mem
    have keep : outN D (W \ K) x ⊆ outN D (W \ (K ∪ J)) x := by
      intro v h
      obtain ⟨vk,e⟩ := mem_outN.mp h
      obtain ⟨vw,noK⟩ := mem_sdiff.mp vk
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨vw,fun vkj => (mem_union.mp vkj).elim noK
        (disjoint_left.mp cut (mem_outN.mpr ⟨vw,e⟩))⟩,e⟩
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨xw,fun h => (mem_union.mp h).elim (mem_sdiff.mp xk).2 noJ⟩,
      paid.trans (Nat.add_le_add_right (card_le_card keep) _)⟩
  refine ⟨base,(assign_heads (pool_anti (R:=P) subset_union_left) (pool_anti (R:=J) subset_union_right)).mp ?_⟩
  refine ⟨_,Subset.rfl,H,?_,first,second,?_⟩
  · intro x hx
    have xw := (mem_sdiff.mp (mem_filter.mp hx).1).1
    have p0 : x ∈ pool D W P J ∅ d := by simp [pool,xw,base x xw]
    simpa using extend hx p0
  · intro x h
    exact extend (mem_inter.mp h).2 (mem_inter.mp h).1

private theorem sponsor_heads {D : CH.Digraph} {W J : Finset ℕ} {q : ℕ}
    (safe : QFree D W 3) (qw : q ∈ W) (jw : J ⊆ W)
    (point : ∀ t ∈ J, t=q ∨ D t q = true) : outN D W q ⊆ invisible D W J := by
  intro h hit
  obtain ⟨hw,qh⟩ := mem_outN.mp hit
  have hj : h ∉ J := by
    intro hJ
    rcases point h hJ with eq | hq
    · exact loopfree safe (by decide) qw (eq ▸ qh)
    · exact digonfree safe (by decide) qw hw qh hq
  refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨hw,hj⟩,disjoint_left.mpr ?_⟩
  intro t ht tj
  have ht' := (mem_outN.mp ht).2
  rcases point t tj with rfl | tq
  · exact digonfree safe (by decide) qw hw qh ht'
  · exact safe q 3 (by decide) (by decide)
      (.step hw qh (.step (jw tj) ht' (.step qw tq (.refl q))))

/-- Two heads of y with d-1 surviving heads each provide d second-head candidates
for the bank {y,r}, where r is one of the two underfull rows. -/
theorem two_short_heads {D : CH.Digraph} {W : Finset ℕ} {y r t d : ℕ}
    (safe : QFree D W 3) (yw : y ∈ W) (rw' : r ∈ W) (tw : t ∈ W)
    (yr : D y r = true) (yt : D y t = true) (rt : r ≠ t) (no : D t r ≠ true)
    (dr : (outN D W r).card+1=d) (dt : (outN D W t).card+1=d) :
    d ≤ (invisible D W {y,r}).card := by
  let J : Finset ℕ := {y,r}
  let H := invisible D W J
  have jw : J ⊆ W := insert_subset yw (singleton_subset_iff.mpr rw')
  have rsub : outN D W r ⊆ H := sponsor_heads safe rw' jw (by
    intro x hx
    rcases mem_insert.mp hx with rfl | eq
    · exact Or.inr yr
    · exact Or.inl (mem_singleton.mp eq))
  by_contra! small
  change H.card < d at small
  have equal : outN D W r = H := eq_of_subset_of_card_le rsub (by omega)
  by_cases edge : D r t = true
  · have tsub : outN D W t ⊆ H := sponsor_heads safe tw jw (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact Or.inr yt
      · rw [mem_singleton.mp hx]; exact Or.inr edge)
    have eqt : outN D W t = H := eq_of_subset_of_card_le tsub (by omega)
    have tt : t ∈ outN D W t := eqt.symm ▸ (rsub (mem_outN.mpr ⟨tw,edge⟩))
    exact loopfree safe (by decide) tw (mem_outN.mp tt).2
  · have ty : t ≠ y := fun e => loopfree safe (by decide) yw (e ▸ yt)
    have noY := digonfree safe (by decide) yw tw yt
    have mem : t ∈ H := mem_filter.mpr ⟨mem_sdiff.mpr ⟨tw,by simp [J,ty,rt.symm]⟩,
      disjoint_left.mpr (by
        intro x h xj
        rcases mem_insert.mp xj with rfl|xj
        · exact noY (mem_outN.mp h).2
        · exact no ((mem_singleton.mp xj) ▸ (mem_outN.mp h).2))⟩
    exact edge (mem_outN.mp (equal.symm ▸ mem)).2

private theorem pay_base {D : CH.Digraph} {W R : Finset ℕ} {d : ℕ}
    (base : ∀ x ∈ W, d ≤ (outN D W x).card + share R ∅ x) (J : Finset ℕ) :
    ∀ x ∈ W, d ≤ (outN D W x).card + credit (R \ J) J x := by
  intro x xw
  have old := base x xw
  by_cases xr : x ∈ R <;> by_cases xj : x ∈ J <;>
    simp [share,credit,xr,xj] at old ⊢ <;> omega

/-- If the ordinary common bank is one short, an otherwise paid row two
heads short after removing R still forces an actual two-copy repair. -/
theorem repair_gap {D : CH.Digraph} {W R : Finset ℕ} {d y : ℕ}
    (safe : QFree D W 3) (sub : R ⊆ W)
    (low : ∀ r ∈ R, (outN D W r).card+1=d)
    (base : ∀ x ∈ W, d ≤ (outN D W x).card + share R ∅ x)
    (near : d ≤ (commonBank D W R ∅ d).card+1)
    (yw : y ∈ W) (notR : y ∉ R) (notB : y ∉ commonBank D W R ∅ d)
    (gap : d ≤ (outN D (W \ R) y).card+2) :
    ∃ J ⊆ W, Feasible D W (R \ J) J d := by
  let E := W \ R
  let B := commonBank D W R ∅ d
  have yE : y ∈ E := mem_sdiff.mpr ⟨yw,notR⟩
  have ydeg := base y yw
  simp [share,notR] at ydeg
  have finish (J : Finset ℕ) (jw : J ⊆ W) (yj : y ∈ J)
      (enough : d ≤ (outN D (W \ (R \ J)) y).card+1) (freeHeads : d ≤ (invisible D W J).card) :
      ∃ J ⊆ W, Feasible D W (R \ J) J d := by
    let P := R \ J
    have eSub : E ⊆ W \ P := fun z hz => mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,
      fun h => (mem_sdiff.mp hz).2 (mem_sdiff.mp h).1⟩
    have Bsub : B ⊆ pool D W P J P d := by
      intro x h
      have old : x ∈ E ∧ d ≤ (outN D E x).card := by simpa [B,E,commonBank] using h
      have subRow : outN D E x ⊆ outN D (W \ P) x := fun _ hz =>
        mem_outN.mpr ⟨eSub (outN_subset hz),(mem_outN.mp hz).2⟩
      exact mem_filter.mpr ⟨eSub old.1,(old.2.trans (card_le_card subRow)).trans (Nat.le_add_right _ _)⟩
    have yp : y ∉ P := fun h => (mem_sdiff.mp h).2 yj
    have one : credit P J y = 1 := by simp [credit,yp,yj]
    have yh : y ∈ pool D W P J P d := mem_filter.mpr ⟨mem_sdiff.mpr ⟨yw,yp⟩,by simpa [one,P] using enough⟩
    have bound := card_le_card (insert_subset yh Bsub)
    rw [card_insert_of_notMem notB] at bound
    exact ⟨J,jw,(free_second (pay_base base J) freeHeads).mpr (near.trans bound)⟩
  by_cases small : d ≤ (outN D E y).card+1
  · apply finish {y} (singleton_subset_iff.mpr yw) (mem_singleton_self _) _ (ydeg.trans (card_le_card
      (sponsor_heads safe yw (singleton_subset_iff.mpr yw) (fun _ h => Or.inl (mem_singleton.mp h)))))
    have eq : R \ {y} = R := sdiff_eq_self_of_disjoint (disjoint_singleton_right.mpr notR)
    simpa [eq,E] using small
  have rowSplit : (outN D E y).card+(outN D R y).card=(outN D W y).card := by
    have e : outN D E y = outN D W y \ outN D R y := by
      ext z; simp only [E,mem_outN,mem_sdiff]; tauto
    have i : outN D R y ⊆ outN D W y := fun z hz => mem_outN.mpr ⟨sub (outN_subset hz),(mem_outN.mp hz).2⟩
    rw [e,card_sdiff_add_card_eq_card i]
  obtain ⟨r,hr,t,ht,rt⟩ := one_lt_card.mp (show 1 < (outN D R y).card by omega)
  have ordered : ∃ r ∈ outN D R y, ∃ t ∈ outN D R y, r ≠ t ∧ D t r ≠ true := by
    by_cases back : D t r = true
    · exact ⟨t,ht,r,hr,rt.symm,digonfree safe (by decide) (sub (outN_subset ht)) (sub (outN_subset hr)) back⟩
    · exact ⟨r,hr,t,ht,rt,back⟩
  obtain ⟨r,hr,t,ht,rt,noback⟩ := ordered
  let J : Finset ℕ := {y,r}
  have rr := outN_subset hr
  have tr := outN_subset ht
  have rfree := two_short_heads safe yw (sub rr) (sub tr) (mem_outN.mp hr).2 (mem_outN.mp ht).2 rt noback
    (low r rr) (low t tr)
  apply finish J (insert_subset yw (singleton_subset_iff.mpr (sub rr))) (mem_insert_self _ _) _ rfree
  have rgood : r ∈ W \ (R \ J) := mem_sdiff.mpr ⟨sub rr,fun h => (mem_sdiff.mp h).2 (by simp [J])⟩
  have keep : insert r (outN D E y) ⊆ outN D (W \ (R \ J)) y := by
    apply insert_subset (mem_outN.mpr ⟨rgood,(mem_outN.mp hr).2⟩)
    intro v h
    obtain ⟨ve,edge⟩ := mem_outN.mp h
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp ve).1,fun bad =>
      (mem_sdiff.mp ve).2 (mem_sdiff.mp bad).1⟩,edge⟩
  have cnt := card_le_card keep
  rw [card_insert_of_notMem (fun h => (mem_sdiff.mp (outN_subset h)).2 rr)] at cnt
  change d ≤ (outN D E y).card+2 at gap
  exact gap.trans (Nat.add_le_add_right cnt 1)

/-- At the critical order, with at most two deleted heads per row and the common
bank at most one short of target, surviving rows outside the double-loss set
have either at least d heads outside that set or at most d-3. -/
theorem native_gap {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2)
    (sub : S ⊆ U) (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card = d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2) :
    let W := U \ S
    let R := doubleRows D U S
    d ≤ (commonBank D W R ∅ d).card+1 → ∀ y ∈ W \ R,
      d ≤ (outN D (W \ R) y).card ∨ (outN D (W \ R) y).card+3 ≤ d := by
  intro W R near y hy
  have subR : R ⊆ W := filter_subset _ _
  have sum (x) (hx : x ∈ W) : (outN D W x).card+(outN D S x).card=d+1 := by
    have row : outN D W x = outN D U x \ outN D S x := by
      ext z; simp only [W,mem_outN,mem_sdiff]; tauto
    have incl : outN D S x ⊆ outN D U x := fun z h =>
      mem_outN.mpr ⟨sub (outN_subset h),(mem_outN.mp h).2⟩
    rw [row,card_sdiff_add_card_eq_card incl,exactRows x hx]
  have low (r) (hr : r ∈ R) : (outN D W r).card+1=d := by
    have h := sum r (subR hr)
    have lost : (outN D S r).card=2 := (mem_filter.mp hr).2
    omega
  have base (x) (hx : x ∈ W) : d ≤ (outN D W x).card+share R ∅ x := by
    by_cases hr : x ∈ R
    · simpa [share,hr] using (low x hr).ge
    · have ne : (outN D S x).card ≠ 2 := fun e => hr (mem_filter.mpr ⟨hx,e⟩)
      have bound := two x hx
      have h := sum x hx
      simp [share,hr]; omega
  by_cases paid : d ≤ (outN D (W \ R) y).card
  · exact Or.inl paid
  right
  by_contra! close
  have notB : y ∉ commonBank D W R ∅ d := by simp [commonBank,paid]
  have gap : d ≤ (outN D (W \ R) y).card+2 := by omega
  obtain ⟨J,jw,h⟩ := repair_gap (W:=W) safe subR low base near (mem_sdiff.mp hy).1
    (mem_sdiff.mp hy).2 notB gap
  exact critical_obstruction law size sub four safe (R \ J) (sdiff_subset.trans subR) J jw h

#print axioms free_second
#print axioms two_short_heads
#print axioms repair_gap
#print axioms native_gap
end LeanCH.BR.Closure.FreeSecondHead
