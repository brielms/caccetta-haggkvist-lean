import checkpoints.shen_extension.VacantTargetPayment

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Law R′ on the labeled three-parent bank. The same sink d receives
both promotions' old back edges and gets the replacement credit. -/
theorem three_parent_vacant_bound {D : CH.Digraph} {U L W₀ P₀ : Finset ℕ}
    {c a b d p q t : ℕ}
    (free : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (clear : L ⊆ neutral D U (tightParents D U c t) c) (nb : ∀ l ∈ L, D l c ≠ true)
    (triple : tightParents D U c t = {a,b,d}) (ab : a ≠ b)
    (ad : D a d = true) (bd : D b d = true)
    (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q) (cp : D c p = true) (cq : D c q = true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (fullP : t+1 ≤ (outN D U p).card) (fullQ : t+1 ≤ (outN D U q).card)
    (spare : ∀ w ∈ outN D U p ∪ outN D U q, t+1 ≤ (outN D U w).card)
    (wsub : W₀ ⊆ (outN D U p \ L) ∩ (outN D U q \ L)) (targets : P₀ ⊆ {p,q})
    (budget : (((outN D U p \ L) ∩ (outN D U q \ L)) \ W₀).card ≤ 2+P₀.card) :
    let J := U.erase c
    let T := insert d (W₀ ∪ P₀)
    ((J \ T).filter (fun v => Disjoint (outN D J v) T)).card < t := by
  classical
  let H := tightParents D U c t
  let J := U.erase c
  let T := insert d (W₀ ∪ P₀)
  let W := (outN D U p \ L) ∩ (outN D U q \ L)
  change H = {a,b,d} at triple
  have am : a ∈ H := by simp [triple]
  have bm : b ∈ H := by simp [triple]
  have dm : d ∈ H := by simp [triple]
  have par {v} (m : v ∈ H) := mem_inN.mp (mem_filter.mp m).1
  have nc {v} (m : v ∈ H) : v ≠ c := fun e => loopfree free (by decide) cu (e ▸ (par m).2)
  have jh {v} (m : v ∈ H) : v ∈ J := mem_erase.mpr ⟨nc m,(par m).1⟩
  have loc {l} (ll : l ∈ L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear ll)).1).1
  have sub : L ⊆ J := fun _ ll => mem_erase.mpr (loc ll)
  have nL {v} (m : v ∈ H) : v ∉ L := fun l => (nb _ l) (par m).2
  have neutralEdge {l h} (ll : l ∈ L) (hm : h ∈ H) : D l h ≠ true := fun e =>
    disjoint_left.mp (mem_filter.mp (clear ll)).2 (mem_outN.mpr ⟨(par hm).1,e⟩) hm
  have size := card_erase_add_one cu
  change J.card+1 = U.card at size
  have row (v) : outN D J v = (outN D U v).erase c := by
    ext w
    simp only [J,mem_outN,mem_erase]
    tauto
  have unc {v} (off : D v c ≠ true) : outN D J v = outN D U v := by
    rw [row,erase_eq_of_notMem (fun m => off (mem_outN.mp m).2)]
  have rp := unc (nb p pl)
  have rq := unc (nb q ql)
  have base (v) (hv : v ∈ ({a,b} : Finset ℕ)) :
      t ≤ (outN D J v).card+1 + (if v∈T then 1 else 0) := by
    have vh : v ∈ H := triple ▸ ((show ({a,b} : Finset ℕ) ⊆ {a,b,d} by grind) hv)
    have bill := card_erase_add_one (mem_outN.mpr ⟨cu,(par vh).2⟩)
    rw [← row] at bill
    have old := floor v (par vh).1 (nc vh)
    omega
  have lower (v) (vj : v ∈ J) (va : v ≠ a) (vb : v ≠ b) :
      t ≤ (outN D J v).card + (if v∈T then 1 else 0) := by
    obtain ⟨vc,vu⟩ := mem_erase.mp vj
    have fl := floor v vu vc
    by_cases ed : D v c=true
    · have one := card_erase_add_one (mem_outN.mpr ⟨cu,ed⟩)
      rw [← row] at one
      by_cases more : t < (outN D U v).card
      · omega
      · have vh : v ∈ H := mem_filter.mpr ⟨mem_inN.mpr ⟨vu,ed⟩,by omega⟩
        have vd : v=d := by simpa [triple,va,vb] using vh
        subst v
        simp [T]
        omega
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
  have pd : p ≠ d := fun e => nL dm (e ▸ pl)
  have qd : q ≠ d := fun e => nL dm (e ▸ ql)
  have pPaid : p ∈ T ↔ p ∈ P₀ := by
    have off : p ∉ W₀ := fun h => (mem_sdiff.mp (mem_inter.mp (wsub h)).1).2 pl
    simp [T,pd,off]
  have qPaid : q ∈ T ↔ q ∈ P₀ := by
    have off : q ∉ W₀ := fun h => (mem_sdiff.mp (mem_inter.mp (wsub h)).1).2 ql
    simp [T,qd,off]
  have cardPi : P₀.card = (if p∈P₀ then 1 else 0) + (if q∈P₀ then 1 else 0) := by
    by_cases pm : p ∈ P₀ <;> by_cases qm : q ∈ P₀
    · rw [show P₀ = {p,q} from Subset.antisymm targets (insert_subset pm (singleton_subset_iff.mpr qm))]
      simp [pq]
    · have eq : P₀ = {p} := by
        apply Subset.antisymm _ (singleton_subset_iff.mpr pm)
        intro x xm
        rcases mem_insert.mp (targets xm) with e | h
        · exact mem_singleton.mpr e
        · exact (qm ((mem_singleton.mp h) ▸ xm)).elim
      rw [eq]
      simp [pq.symm]
    · have eq : P₀ = {q} := by
        apply Subset.antisymm _ (singleton_subset_iff.mpr qm)
        intro x xm
        rcases mem_insert.mp (targets xm) with e | h
        · exact (pm (e ▸ xm)).elim
        · exact h
      rw [eq]
      simp [pq]
    · have eq : P₀ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x xm
        rcases mem_insert.mp (targets xm) with e | h
        · exact pm (e ▸ xm)
        · exact qm ((mem_singleton.mp h) ▸ xm)
      simp [eq]
  have spend : (((outN D J p \ L) ∩ (outN D J q \ L)) \ T).card ≤
      (1 + (if p∈T then 1 else 0)) + (1 + (if q∈T then 1 else 0)) := by
    rw [rp,rq]
    have subset : W \ T ⊆ W \ W₀ := by
      intro w wh
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp wh).1,
        fun h => (mem_sdiff.mp wh).2 (mem_insert_of_mem (mem_union_left _ h))⟩
    have bound := (card_le_card subset).trans budget
    rw [cardPi] at bound
    change (W \ T).card ≤ _
    simp only [pPaid,qPaid]
    omega
  exact vacant_payment_bound (free.mono_set (erase_subset ..)) (notMem_erase _ _) (size.trans_le small) none
    sub pl ql pq (jh am) (jh bm) ab (nL am) (nL bm)
    (fun _ ll => ⟨neutralEdge ll am,neutralEdge ll bm⟩) ap bq base lower (rp ▸ fullP) (rq ▸ fullQ)
    rich spend (Or.inr ⟨d,mem_inter.mpr ⟨mem_insert_self ..,jh dm⟩,ad⟩)
    (Or.inr ⟨d,mem_inter.mpr ⟨mem_insert_self ..,jh dm⟩,bd⟩)

#print axioms three_parent_vacant_bound
end LeanCH.BR.TripleBank
