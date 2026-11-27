import checkpoints.shen_extension.ThreeParentVacantPayment

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- One selected extra predecessor consumes at most its own position and
its incidence column in any candidate successor pool. -/
theorem vacant_pool_budget {D : CH.Digraph} {J T A : Finset ℕ} {w t : ℕ}
    (base : A ⊆ (J \ T).filter (fun v => Disjoint (outN D J v) T))
    (bound : ((J \ insert w T).filter (fun v => Disjoint (outN D J v) (insert w T))).card < t) :
    A.card+1 ≤ t + (if w∈A then 1 else 0) + (inN D A w).card := by
  classical
  let R := inN D A w ∪ ({w} ∩ A)
  have inside : A \ R ⊆ (J \ insert w T).filter
      (fun v => Disjoint (outN D J v) (insert w T)) := by
    intro v vR
    obtain ⟨va,vr⟩ := mem_sdiff.mp vR
    obtain ⟨vj,clear⟩ := mem_filter.mp (base va)
    have vw : v ≠ w := fun h => vr (mem_union_right _ (mem_inter.mpr ⟨mem_singleton.mpr h,va⟩))
    have off : D v w ≠ true := fun e => vr (mem_union_left _ (mem_inN.mpr ⟨va,e⟩))
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp vj).1,by simpa [vw] using (mem_sdiff.mp vj).2⟩,
      disjoint_left.mpr (fun u uh um => (mem_insert.mp um).elim
        (fun e => off (e ▸ (mem_outN.mp uh).2)) (disjoint_left.mp clear uh))⟩
  have sent := (card_le_card inside).trans_lt bound
  have priced := card_le_card_sdiff_add_card (s := A) (t := R)
  have bills := card_union_le (inN D A w) ({w}∩A)
  have singleton : ({w}∩A).card = (if w∈A then 1 else 0) := by
    by_cases wa : w∈A
    · have h : ({w} : Finset ℕ) ∩ A = {w} := inter_eq_left.mpr (singleton_subset_iff.mpr wa)
      simp [h,wa]
    · have h : ({w} : Finset ℕ) ∩ A = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v m
        obtain ⟨p,q⟩ := mem_inter.mp m
        exact wa ((mem_singleton.mp p) ▸ q)
      simp [h,wa]
  rw [singleton] at bills
  change R.card ≤ _ at bills
  omega

/-- At exact five, one common exterior head can be selected as an extra
predecessor with both inherited targets. -/
theorem exact_five_vacant_pool {D : CH.Digraph} {U L A : Finset ℕ}
    {c a b d p q w t : ℕ}
    (free : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (clear : L ⊆ neutral D U (tightParents D U c t) c) (nb : ∀ l ∈ L, D l c ≠ true)
    (triple : tightParents D U c t = {a,b,d}) (ab : a ≠ b)
    (ad : D a d = true) (bd : D b d = true)
    (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q) (cp : D c p = true) (cq : D c q = true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (fullP : t+1 ≤ (outN D U p).card) (fullQ : t+1 ≤ (outN D U q).card)
    (spare : ∀ w ∈ outN D U p ∪ outN D U q, t+1 ≤ (outN D U w).card)
    (both : w ∈ (outN D U p \ L) ∩ (outN D U q \ L))
    (five : ((outN D U p \ L) ∩ (outN D U q \ L)).card = 5)
    (candidate : A ⊆ ((U.erase c) \ {d,p,q}).filter
      (fun v => Disjoint (outN D (U.erase c) v) {d,p,q})) :
    A.card+1 ≤ t + (if w∈A then 1 else 0) + (inN D A w).card := by
  classical
  have budget : (((outN D U p \ L) ∩ (outN D U q \ L)) \ {w}).card ≤ 2+({p,q} : Finset ℕ).card := by
    rw [← erase_eq,card_erase_of_mem both,five,card_pair pq]
  have bound := three_parent_vacant_bound free cu small none floor clear nb triple ab ad bd pl ql pq cp cq
    ap bq fullP fullQ spare (singleton_subset_iff.mpr both) Subset.rfl budget
  have eq : (insert d ({w} ∪ {p,q}) : Finset ℕ) = insert w {d,p,q} := by
    ext v
    simp only [mem_insert,mem_union,mem_singleton]
    tauto
  dsimp only at bound
  rw [eq] at bound
  exact vacant_pool_budget candidate bound

/-- A common head of the credited rows and every successor of that head
can be used as potential replacement successors. -/
theorem common_head_candidate {D : CH.Digraph} {J T : Finset ℕ} {r : ℕ}
    (free : QFree D J 3) (sub : T ⊆ J) (rj : r ∈ J)
    (heads : ∀ h ∈ T, D h r=true) :
    insert r (outN D J r) ⊆ (J \ T).filter (fun v => Disjoint (outN D J v) T) := by
  intro v vv
  have vj : v ∈ J := (mem_insert.mp vv).elim (fun eq => eq.symm ▸ rj) (fun h => outN_subset h)
  have apart (h) (ht : h ∈ T) : v ≠ h := by
    rcases mem_insert.mp vv with e | vr
    · exact fun eq => loopfree free (by decide) rj ((eq.symm.trans e) ▸ heads h ht)
    · exact fun eq => digonfree free (by decide) rj vj (mem_outN.mp vr).2 (eq.symm ▸ heads h ht)
  have noEdge (h) (ht : h ∈ T) : D v h ≠ true := by
    intro e
    rcases mem_insert.mp vv with eq | vr
    · exact digonfree free (by decide) rj (sub ht) (eq ▸ e) (heads h ht)
    · exact free r 3 (by decide) (by decide)
        (.step vj (mem_outN.mp vr).2 (.step (sub ht) e (.step rj (heads h ht) (.refl _))))
  exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨vj,fun vt => apart v vt rfl⟩,
    disjoint_left.mpr (fun h hOut ht => noEdge h ht (mem_outN.mp hOut).2)⟩

/-- The loss budget of the candidate set formed by one full row and its heads. -/
theorem full_vacant_row_budget {D : CH.Digraph} {J : Finset ℕ} {r w t : ℕ}
    (free : QFree D J 3) (rj : r ∈ J) (wj : w ∈ J) (wr : w ≠ r)
    (full : t+1 ≤ (outN D J r).card)
    (budget : let A := insert r (outN D J r)
      A.card+1 ≤ t + (if w∈A then 1 else 0) + (inN D A w).card) :
    3 ≤ ((outN D J r) ∩ (inN D J w)).card + 2*(if D r w=true then 1 else 0) := by
  classical
  let N := outN D J r
  let A := insert r N
  let C := N ∩ inN D J w
  have noSelf : r ∉ N := fun h => loopfree free (by decide) rj (mem_outN.mp h).2
  have ac : A.card = N.card+1 := card_insert_of_notMem noSelf
  have nw : w ∈ A ↔ D r w=true := by simp [A,N,wr,mem_outN,wj]
  have column : inN D A w = C ∪ (if D r w=true then {r} else ∅) := by
    ext v
    by_cases vr : v=r
    · subst v
      by_cases hit : D r w=true <;> simp [C,A,mem_inN,noSelf,hit]
    · have nested : v ∈ N → v ∈ J := fun h => outN_subset h
      by_cases hit : D r w=true <;> simp [C,A,mem_inN,vr,hit]
      all_goals tauto
  have colCount : (inN D A w).card = C.card + (if D r w=true then 1 else 0) := by
    rw [column]
    by_cases hit : D r w=true
    · rw [ite_eq_left hit,ite_eq_left hit,union_singleton,card_insert_of_notMem]
      exact fun h => noSelf (mem_inter.mp h).1
    · simp [hit]
  change A.card+1 ≤ t + (if w∈A then 1 else 0) + (inN D A w).card at budget
  rw [ac,colCount] at budget
  simp only [nw] at budget
  change t+1 ≤ N.card at full
  change 3 ≤ C.card + 2*(if D r w=true then 1 else 0)
  omega

/-- Every common neutral head r of d and the two inherited targets has
a large return column to each of the five shared exterior blockers. -/
theorem exact_five_common_row_budget {D : CH.Digraph} {U L : Finset ℕ}
    {c a b d p q r w t : ℕ}
    (free : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (clear : L ⊆ neutral D U (tightParents D U c t) c) (nb : ∀ l ∈ L, D l c ≠ true)
    (triple : tightParents D U c t = {a,b,d}) (ab : a ≠ b)
    (ad : D a d = true) (bd : D b d = true)
    (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q) (cp : D c p = true) (cq : D c q = true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (fullP : t+1 ≤ (outN D U p).card) (fullQ : t+1 ≤ (outN D U q).card)
    (spare : ∀ w ∈ outN D U p ∪ outN D U q, t+1 ≤ (outN D U w).card)
    (both : w ∈ (outN D U p \ L) ∩ (outN D U q \ L))
    (five : ((outN D U p \ L) ∩ (outN D U q \ L)).card = 5)
    (rl : r ∈ L) (dr : D d r=true) (pr : D p r=true) (qr : D q r=true) :
    let J := U.erase c
    3 ≤ (outN D J r ∩ inN D J w).card + 2*(if D r w=true then 1 else 0) := by
  classical
  let J := U.erase c
  have sub : J ⊆ U := erase_subset ..
  have loc {l} (ll : l ∈ L) : l ∈ J :=
    (mem_sdiff.mp (mem_filter.mp (clear ll)).1).1
  have dj : d ∈ J := by
    have dm : d ∈ tightParents D U c t := by simp [triple]
    obtain ⟨du,dc⟩ := mem_inN.mp (mem_filter.mp dm).1
    exact mem_erase.mpr ⟨fun e => loopfree free (by decide) cu (e ▸ dc),du⟩
  have toJ : ({d,p,q} : Finset ℕ) ⊆ J :=
    insert_subset dj (insert_subset (loc pl) (singleton_subset_iff.mpr (loc ql)))
  have candidate := common_head_candidate (free.mono_set sub) toJ (loc rl)
    (show ∀ h ∈ ({d,p,q} : Finset ℕ), D h r=true by
      intro h hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> assumption)
  have result := exact_five_vacant_pool free cu small none floor clear nb triple ab ad bd
    pl ql pq cp cq ap bq fullP fullQ spare both five candidate
  obtain ⟨wp,wl⟩ := mem_sdiff.mp (mem_inter.mp both).1
  have wj : w ∈ J :=
    mem_erase.mpr ⟨fun eq => (nb p pl) (eq ▸ (mem_outN.mp wp).2),outN_subset wp⟩
  have rFull := spare r (mem_union_left _ (mem_outN.mpr ⟨sub (loc rl),pr⟩))
  have row : outN D J r = outN D U r := by
    ext v
    simp only [J,mem_outN,mem_erase]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨fun e => nb r rl (e ▸ h.2),h.1⟩,h.2⟩⟩
  exact full_vacant_row_budget (free.mono_set sub) (loc rl) wj (fun e => wl (e.symm ▸ rl))
    (row ▸ rFull) result

#print axioms vacant_pool_budget
#print axioms exact_five_vacant_pool
#print axioms common_head_candidate
#print axioms full_vacant_row_budget
#print axioms exact_five_common_row_budget
end LeanCH.BR.TripleBank
