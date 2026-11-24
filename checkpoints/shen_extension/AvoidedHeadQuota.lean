import checkpoints.shen_extension.CompromiseQuotaReplay
import checkpoints.shen_extension.SharedHeadSuppliers

namespace LeanCH.BR.AvoidedHeadQuota
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog FragmentScoreEquality

/-- If none of the rows in S can use a column of H, any m of those
same rows pay a quota whenever their exterior room is small enough. -/
theorem avoided {D V H S : _} {q r m d : ℕ} (free : QFree D V q) (none : NoHost q d)
    (degree : ∀v∈V,r≤(outN D V v).card) (hv : H⊆V) (sv : S⊆V)
    (dis : Disjoint H S) (off : ∀v∈S,∀h∈H,D v h≠true)
    (pos : 0<m) (fit : m≤q*d) (room : V.card+d≤r+H.card+m) : S.card<m := by
  classical
  by_contra! large
  obtain ⟨W,ws,size⟩ := exists_subset_card_eq large
  have wv := ws.trans sv
  have both := union_subset hv wv
  have dw := dis.mono_right ws
  have card := card_sdiff_of_subset both
  rw [card_union_of_disjoint dw,size] at card
  have inV := card_le_card both
  rw [card_union_of_disjoint dw,size] at inV
  apply none D W (card_pos.mp (size ▸ pos)) (size ▸ fit) (free.mono_set wv)
  intro v vm
  have sub : outN D V v ⊆ outN D W v ∪ (V \ (H∪W)) := by
    intro a am
    obtain ⟨av,va⟩ := mem_outN.mp am
    by_cases aw : a∈W
    · exact mem_union_left _ (mem_outN.mpr ⟨aw,va⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨av,fun h=> (mem_union.mp h).elim (fun ah=>off v (ws vm) a ah va) aw⟩)
  have count := (card_le_card sub).trans (card_union_le _ _)
  have := degree v (wv vm)
  omega

/-- For a complete directed rectangle H→Y, retain Y and all heads of
one actual sparse row of Y. Neither kind of row can send an arc to H. -/
theorem rectangle {D V H Y : _} {q r a d m : ℕ} (free : QFree D V q) (cut : 3≤q)
    (small : NoHost q a) (none : NoHost q d) (degree : ∀v∈V,r≤(outN D V v).card)
    (hv : H⊆V) (yv : Y⊆V) (live : Y.Nonempty) (size : Y.card≤q*a)
    (full : ∀h∈H,∀y∈Y,D h y=true)
    (need : m+a≤Y.card+r+1) (pos : 0<m) (fit : m≤q*d)
    (room : V.card+d≤r+H.card+m) : False := by
  classical
  obtain ⟨y,ym,low⟩ : ∃y∈Y,(outN D Y y).card<a := by
    by_contra! all
    exact small D Y live size (free.mono_set yv) all
  let S := Y ∪ outN D V y
  have sv : S⊆V := union_subset yv outN_subset
  have dis : Disjoint H S := disjoint_left.mpr fun h hm mem=>by
    rcases mem_union.mp mem with hy | yh
    · exact loopfree free (by omega) (hv hm) (full h hm h hy)
    · exact digonfree free (by omega) (hv hm) (yv ym) (full h hm y ym) (mem_outN.mp yh).2
  have off v (vm : v∈S) h (hm : h∈H) (vh : D v h=true) : False := by
    rcases mem_union.mp vm with vy | yv'
    · exact digonfree free (by omega) (hv hm) (yv vy) (full h hm v vy) vh
    · exact free h 3 (by decide) cut (.step (yv ym) (full h hm y ym)
        (.step (mem_outN.mp yv').1 (mem_outN.mp yv').2 (.step (hv hm) vh (.refl _))))
  have cap := avoided free none degree hv sv dis off pos fit room
  have eq : Y ∩ outN D V y=outN D Y y := by
    ext z
    simp only [mem_inter,mem_outN]
    exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,yv h.1,h.2⟩⟩
  have bill := card_union_add_card_inter Y (outN D V y)
  rw [eq] at bill
  change (Y∪outN D V y).card<m at cap
  have := degree y (yv ym)
  omega

attribute [aesop safe forward (immediate := [free,none,degree,hv,sv,dis,off,pos,fit,room])
  (rule_sets := [CHGraphFamilies])] avoided
attribute [aesop safe forward (immediate := [free,cut,small,none,degree,hv,yv,live,size,full,need,pos,fit,room])
  (rule_sets := [CHGraphFamilies])] rectangle
#print axioms avoided
#print axioms rectangle
end LeanCH.BR.AvoidedHeadQuota
