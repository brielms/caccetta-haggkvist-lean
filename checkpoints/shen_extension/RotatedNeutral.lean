import checkpoints.shen_extension.TightParentNeutral

/-! Releasing a different bank vertex changes the row available to take the
vacant position. It does not change the underlying deficient rows. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

def slotHeads (D : CH.Digraph) (J H : Finset ℕ) (t : ℕ) : Finset ℕ :=
  J.filter (fun v => t ≤ (outN D J v \ H).card)

/-- The same vacant position has exactly L affordable heads under arbitrary
cuts from those heads to the required incoming rows. -/
theorem slot_saturation {D : CH.Digraph} {U L : Finset ℕ} {c t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c) :
    slotHeads D (U.erase c) (tightParents D U c t) t = L := by
  classical
  let H := tightParents D U c t
  have row (v) : outN D (U.erase c) v \ H = outN D U v \ insert c H := by
    ext w; simp only [mem_outN,mem_erase,mem_sdiff,mem_insert]; tauto
  have eq : slotHeads D (U.erase c) H t = (U.erase c).filter
      (fun v => t ≤ (outN D U v \ insert c H).card) := by
    ext v; simp only [slotHeads,mem_filter,row]
  have lim := affordable_bound safe cu small no others
  change ((U.erase c).filter (fun v => t ≤ (outN D U v \ insert c H).card)).card < t at lim
  apply eq_of_superset_of_card_ge
  · intro v vl
    obtain ⟨base,dis⟩ := mem_filter.mp (clear vl)
    obtain ⟨ve,vh⟩ := mem_sdiff.mp base
    obtain ⟨vc,vu⟩ := mem_erase.mp ve
    have red : outN D (U.erase c) v \ H = (outN D U v).erase c := by
      ext w
      simp only [mem_outN,mem_erase,mem_sdiff]
      have h (wu : w ∈ U) (vw : D v w = true) : w ∉ H := disjoint_left.mp dis (mem_outN.mpr ⟨wu,vw⟩)
      tauto
    refine mem_filter.mpr ⟨ve,?_⟩
    rw [red]
    by_cases ed : c ∈ outN D U v
    · have slack : t < (outN D U v).card := by
        by_contra! low
        exact vh (mem_filter.mpr ⟨mem_inN.mpr ⟨vu,(mem_outN.mp ed).2⟩,low⟩)
      rw [card_erase_of_mem ed]; omega
    · rw [erase_eq_of_notMem ed]; exact others v vu vc
  · change (slotHeads D (U.erase c) H t).card ≤ L.card
    rw [eq]; omega

/-- Restoring k to the common core pays precisely those deficient rows
that already point to k. The affordable successors of k are the heads
it has in the fixed set of affordable slot heads. -/
theorem released_retainable {D : CH.Digraph} {J H : Finset ℕ} {k t : ℕ}
    (safe : QFree D (insert k J) 3) (sub : H ⊆ J) :
    let R := H.filter (fun h => D h k ≠ true)
    retainable D (insert k J) R k t = outN D J k ∩ slotHeads D J H t := by
  classical
  intro R
  have ku : k ∈ insert k J := mem_insert_self _ _
  have heads : outN D (insert k J) k = outN D J k := by
    ext v
    simp only [mem_outN,mem_insert]
    have kk := loopfree safe (by decide) ku
    constructor
    · rintro ⟨rfl | h,ed⟩
      · exact (kk ed).elim
      · exact ⟨h,ed⟩
    · exact fun h => ⟨Or.inr h.1,h.2⟩
  have row {w} (wm : w ∈ outN D J k) : outN D (insert k J) w \ R = outN D J w \ H := by
    obtain ⟨wj,kw⟩ := mem_outN.mp wm
    have wu : w ∈ insert k J := mem_insert_of_mem wj
    have wk := digonfree safe (by decide) ku wu kw
    ext v
    simp only [mem_sdiff,mem_outN,mem_insert,R,mem_filter]
    constructor
    · rintro ⟨⟨vk | vj,wv⟩,off⟩
      · exact (wk (vk ▸ wv)).elim
      · refine ⟨⟨vj,wv⟩,fun vh => off ⟨vh,fun vk => safe k 3 (by decide) (by decide)
          (.step wu kw (.step (mem_insert_of_mem (sub vh)) wv (.step ku vk (.refl _))))⟩⟩
    · exact fun h => ⟨⟨Or.inr h.1.1,h.1.2⟩,fun rh => h.2 rh.1⟩
  ext w
  simp only [retainable,heads,mem_filter,slotHeads,mem_inter]
  constructor
  · rintro ⟨wm,budget⟩
    exact ⟨wm,outN_subset wm,by rwa [row wm] at budget⟩
  · rintro ⟨wm,_,budget⟩
    exact ⟨wm,by rwa [row wm]⟩

/-- On a lone-deficit carrier the rows below quota after removing c are
exactly its tight predecessors. This identifies H before any rotation. -/
theorem vacant_deficits {D : CH.Digraph} {U : Finset ℕ} {c t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    (U.erase c).filter (fun v => (outN D (U.erase c) v).card < t) = tightParents D U c t := by
  classical
  ext v
  have row : outN D (U.erase c) v = (outN D U v).erase c := by
    ext w; simp only [mem_outN,mem_erase]; tauto
  simp only [mem_filter,mem_erase,tightParents,mem_inN,row]
  by_cases vu : v ∈ U
  · by_cases vc : v = c
    · subst v; simp [loopfree safe (by decide) cu]
    · have floor := others v vu vc
      by_cases ed : D v c = true
      · rw [card_erase_of_mem (mem_outN.mpr ⟨cu,ed⟩)]
        have pos := card_pos.mpr (show (outN D U v).Nonempty from ⟨c,mem_outN.mpr ⟨cu,ed⟩⟩)
        exact ⟨fun h => ⟨⟨vu,ed⟩,by omega⟩,fun h => ⟨⟨vc,vu⟩,by omega⟩⟩
      · rw [erase_eq_of_notMem (fun h => ed (mem_outN.mp h).2)]
        exact ⟨fun h => (Nat.not_lt_of_ge floor h.2).elim,fun h => (ed h.1.2).elim⟩
  · tauto

/-- Inserting k into a core of at most unit deficits leaves precisely the
old deficient vertices missing k below quota, if k itself meets quota. -/
theorem released_deficits {D : CH.Digraph} {J : Finset ℕ} {k t : ℕ}
    (fresh : k ∉ J) (room : ∀ v ∈ J, t ≤ (outN D J v).card + 1)
    (floor : t ≤ (outN D (insert k J) k).card) :
    let H := J.filter (fun h => (outN D J h).card < t)
    (insert k J).filter (fun v => (outN D (insert k J) v).card < t) =
      H.filter (fun h => D h k ≠ true) := by
  classical
  intro H
  ext v
  by_cases vk : v = k
  · subst v; simp [H,fresh,Nat.not_lt_of_ge floor]
  by_cases vj : v ∈ J
  · have lim := room v vj
    by_cases ed : D v k = true
    · have row : outN D (insert k J) v = insert k (outN D J v) := by
        ext w; simp only [mem_outN,mem_insert]; constructor
        · rintro ⟨rfl | h,old⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h,old⟩
        · rintro (rfl | h)
          · exact ⟨Or.inl rfl,ed⟩
          · exact ⟨Or.inr h.1,h.2⟩
      simp [H,row,card_insert_of_notMem (fun h => fresh (outN_subset h)),Nat.not_lt_of_ge lim,ed]
    · have row : outN D (insert k J) v = outN D J v := by
        ext w; simp only [mem_outN,mem_insert]; constructor
        · rintro ⟨rfl | h,old⟩
          · exact (ed old).elim
          · exact ⟨h,old⟩
        · exact fun h => ⟨Or.inr h.1,h.2⟩
      simp [H,row,vj,ed]
  · simp [H,vj,vk]

/-- The exact excess of forced cuts over k's spare is one plus the number
of its missed heads in L, independently of the count of short rows. -/
theorem excess_identity {D : CH.Digraph} {J H L : Finset ℕ} {k t : ℕ}
    (safe : QFree D (insert k J) 3) (sub : H ⊆ J)
    (fixed : slotHeads D J H t = L) (sat : L.card+1 = t)
    (floor : t ≤ (outN D J k).card) :
    let O := outN D J k
    let R := H.filter (fun h => D h k ≠ true)
    (O \ retainable D (insert k J) R k t).card =
      (O.card-t) + 1 + (L \ O).card := by
  classical
  intro O R
  have eq := released_retainable (t := t) safe sub
  change retainable D (insert k J) R k t = O ∩ slotHeads D J H t at eq
  rw [eq,fixed]
  have diff : O \ (O ∩ L) = O \ L := by ext v; simp only [mem_sdiff,mem_inter]; tauto
  rw [diff]
  have left := card_sdiff_add_card_inter O L
  have right := card_sdiff_add_card_inter L O
  rw [inter_comm L O] at right
  change t ≤ O.card at floor
  omega

/-- For a surviving head p of c with a full row and full successors, at
least three distinct successors each point to two or more tight parents. -/
theorem three_double_returns {D : CH.Digraph} {U L : Finset ℕ} {c p t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (pu : p ∈ U) (cp : D c p = true)
    (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c)
    (pl : p ∈ L) (row : (outN D U p).card = t+1)
    (spare : ∀ w ∈ outN D U p, t < (outN D U w).card) :
    let H := tightParents D U c t
    3 ≤ ((outN D U p).filter (fun w => 2 ≤ (outN D U w ∩ H).card)).card := by
  classical
  intro H
  have eq := slot_saturation safe cu small no others sat clear
  let O := outN D U p
  have inside : O ∩ L ⊆ L.erase p := fun w m => mem_erase.mpr
    ⟨fun e => loopfree safe (by decide) pu (e ▸ (mem_outN.mp (mem_inter.mp m).1).2),(mem_inter.mp m).2⟩
  have cap := card_le_card inside
  rw [card_erase_of_mem pl] at cap
  have count := card_sdiff_add_card_inter O L
  change O.card = t+1 at row
  have paid : O \ L ⊆ O.filter (fun w => 2 ≤ (outN D U w ∩ H).card) := by
    intro w wm
    obtain ⟨op,off⟩ := mem_sdiff.mp wm
    obtain ⟨wu,pw⟩ := mem_outN.mp op
    have wc : D w c ≠ true := fun ed => safe c 3 (by decide) (by decide)
      (.step pu cp (.step wu pw (.step cu ed (.refl _))))
    have wnc : w ≠ c := fun e => digonfree safe (by decide) cu pu cp (e ▸ pw)
    have same : outN D (U.erase c) w = outN D U w := by
      ext x; simp only [mem_outN,mem_erase]
      exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨fun e => wc (e ▸ h.2),h.1⟩,h.2⟩⟩
    have gap : (outN D U w \ H).card < t := by
      by_contra! enough
      apply off
      rw [←eq]
      apply mem_filter.mpr
      exact ⟨mem_erase.mpr ⟨wnc,wu⟩,same ▸ enough⟩
    have split := card_sdiff_add_card_inter (outN D U w) H
    have full := spare w op
    exact mem_filter.mpr ⟨op,by omega⟩
  have pos := card_pos.mpr (show L.Nonempty from ⟨p,pl⟩)
  exact (show 3 ≤ (O \ L).card by omega).trans (card_le_card paid)

/-- Rotate the vacant position from c to k. Both the short rows and the
overload bill below are computed from the degrees of the rotated graph. -/
theorem rotated_bill {D : CH.Digraph} {U L : Finset ℕ} {c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c)
    (fresh : k ∉ U.erase c) (safe' : QFree D (insert k (U.erase c)) 3)
    (budget : t ≤ (outN D (U.erase c) k).card) :
    let J := U.erase c
    let U' := insert k J
    let R := U'.filter (fun h => (outN D U' h).card < t)
    let O := outN D J k
    retainable D U' R k t = O ∩ L ∧
      (O \ retainable D U' R k t).card = (O.card-t) + 1 + (L \ O).card := by
  classical
  intro J U' R O
  let H := tightParents D U c t
  have core := vacant_deficits safe cu others
  change J.filter (fun v => (outN D J v).card < t) = H at core
  have sub : H ⊆ J := core ▸ filter_subset _ _
  have floor : t ≤ (outN D U' k).card := budget.trans (card_le_card (fun v vm =>
    mem_outN.mpr ⟨mem_insert_of_mem (outN_subset vm),(mem_outN.mp vm).2⟩))
  have room (v) (vj : v ∈ J) : t ≤ (outN D J v).card+1 := by
    obtain ⟨vc,vu⟩ := mem_erase.mp vj
    have lim := others v vu vc
    have eq : outN D J v = (outN D U v).erase c := by
      ext w; simp only [J,mem_outN,mem_erase]; tauto
    rw [eq]
    by_cases ed : c ∈ outN D U v
    · rw [card_erase_add_one ed]; exact lim
    · rw [erase_eq_of_notMem ed]; omega
  have rows := released_deficits fresh room floor
  change R = (J.filter (fun v => (outN D J v).card < t)).filter _ at rows
  rw [core] at rows
  have fixed := slot_saturation safe cu small no others sat clear
  rw [rows]
  exact ⟨(released_retainable safe' sub).trans (congrArg (fun X => O ∩ X) fixed),
    excess_identity safe' sub fixed sat budget⟩

#print axioms rotated_bill
#print axioms three_double_returns
#print axioms excess_identity
#print axioms released_deficits
#print axioms slot_saturation
#print axioms released_retainable
#print axioms vacant_deficits
end LeanCH.BR.TripleBank
