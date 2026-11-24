import checkpoints.shen_extension.SinkTransit

namespace LeanCH.BR.EqualLayerTransit
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- Follow actual full sinks through any number of complete boundaries. -/
theorem from_sink {D V q a} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (sub : ∀ (i : ℕ), L i⊆V) (b : ℕ) (small : ∀ (i : ℕ), a ≤ i → i < b → (L i).card ≤ q)
    (live : ∀ (i : ℕ), a ≤ i → i < b → (L i).Nonempty)
    (full : ∀ (i : ℕ), a ≤ i → i < b → ∀s∈L i,Sink D (L i) s → L (i+1)⊆outN D V s)
    (lt : a < b) {s z} (start : s∈L a) (sink : Sink D (L a) s) (goal : z∈L b) :
    Walk D V s z (b-a) := by
  induction b generalizing z with
  | zero => omega
  | succ b ih =>
    by_cases eq : a=b
    · subst b
      have head := full a le_rfl (Nat.lt_succ_self _) s start sink goal
      simpa only [Nat.add_sub_cancel_left] using
        (Walk.step (sub _ goal) (mem_outN.mp head).2 (.refl z) : Walk D V s z 1)
    have ab : a < b := by omega
    obtain ⟨y,ym,stop⟩ := exists_sink (free.mono_set (sub b)) (live b ab.le (by omega)) (small b ab.le (by omega))
    have p := ih (fun i ai ib=>small i ai (by omega)) (fun i ai ib=>live i ai (by omega))
      (fun i ai ib=>full i ai (by omega)) ab (z:=y) ym
    have arc := full b ab.le (by omega) y ym stop goal
    simpa only [show b+1-a=b-a+1 by omega] using p.snoc (sub _ goal) (mem_outN.mp arc).2

/-- The next layer after a run of full layers must fit the entire quota.
The height of the run is a parameter. Heads are allowed initially to
return to any earlier layer; the proof excludes those returns in order. -/
theorem end_capacity {D V q r h} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r < q) (height : r/2+h ≤ q) (depth : 0 < h)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < h → (L i).card=r)
    (apart : ∀ (i : ℕ),  i+1 < h → Disjoint (L i) (L (i+1)))
    (quota : ∀ (i : ℕ), i < h → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i < h → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j) : r ≤ (L h).card := by
  classical
  have sinks {i} (hi : i < h) (hi' : i+1 < h)
      (keep : ∀v∈L i,outN D V v⊆L i∪L (i+1)) (s) (sm : s∈L i) (last : Sink D (L i) s) :
      L (i+1)⊆outN D V s := by
    apply (eq_of_subset_of_card_le (s:=outN D V s) (t:=L (i+1)) ?_ ?_).symm.subset
    · exact fun x xm=>(mem_union.mp (keep s sm xm)).resolve_left (fun a=>last x a (mem_outN.mp xm).2)
    · rw [size _ hi']; exact quota i hi s sm
  have keep (i) (hi : i < h) : ∀v∈L i,outN D V v⊆L i∪L (i+1) := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro v vm x xm
      obtain ⟨j,le,xj⟩ := step i hi v vm x xm
      by_cases eq : j=i+1
      · exact mem_union_right _ (eq ▸ xj)
      by_cases same : j=i
      · exact mem_union_left _ (same ▸ xj)
      have ji : j < i := by omega
      have qj : (L j).card ≤ q := (size j (by omega)).le.trans hq.le
      obtain ⟨s,sm,last,k,kl,path⟩ := reach_sink_of_card (free.mono_set (sub j)) qj xj
      have endJ := sinks (by omega : j < h) (by omega : j+1 < h) (ih j ji (by omega)) s sm last
      have xV := sub j xj
      have arc := (mem_outN.mp xm).2
      rw [size j (by omega)] at kl
      by_cases next : j+1=i
      · have e : v∈outN D V s := endJ (next.symm ▸ vm)
        exact (free x _ (by omega) (by omega) (((path.mono (sub j)).snoc (sub i vm) (mem_outN.mp e).2).snoc xV arc)).elim
      have menu := ih j ji (by omega) x xj
      have rank : r ≤ (outN D (L j∪L (j+1)) x).card := (quota j (by omega) x xj).trans
        (card_le_card (fun y ym=>mem_outN.mpr ⟨menu ym,(mem_outN.mp ym).2⟩))
      have pos : (outN D (L (j+1)) x).Nonempty := by
        have internal : outN D (L j) x⊆(L j).erase x := fun y ym=>mem_erase.mpr
          ⟨fun e=>loopfree free (by omega) xV (e ▸ (mem_outN.mp ym).2),outN_subset ym⟩
        have cap := card_le_card internal
        rw [card_erase_of_mem xj,size j (by omega)] at cap
        rw [card_outN_union (apart j (by omega))] at rank
        exact card_pos.mp (by omega)
      obtain ⟨b,bm,bs,l,len,road⟩ := SinkTransit.two_routes free (sub j) (sub (j+1))
        qj ((size _ (by omega)).le.trans hq.le) xj (apart _ (by omega)) rank pos
        (sinks (by omega) (by omega) (ih j ji (by omega)))
      have plus := len.trans (Nat.min_le_left _ _)
      have minus := len.trans (Nat.min_le_right _ _)
      rw [size j (by omega)] at plus
      rw [size (j+1) (by omega)] at minus
      have internal := card_le_card (outN_subset : outN D (L j) x⊆L j)
      rw [size j (by omega)] at internal
      have tail := from_sink L free sub i
        (fun k _ ki=>(size k (by omega)).le.trans hq.le)
        (fun k _ ki=>card_pos.mp (by rw [size k (by omega)]; exact hr))
        (fun k _ ki=>sinks (by omega) (by omega) (ih k ki (by omega))) (by omega : j+1 < i) bm bs vm
      exact (free x _ (by omega) (by omega) ((road.append tail).snoc xV arc)).elim
  obtain ⟨s,sm,stop⟩ := exists_sink (free.mono_set (sub (h-1)))
    (card_pos.mp (by rw [size _ (by omega)]; exact hr)) ((size _ (by omega)).le.trans hq.le)
  have bound : outN D V s⊆L h := by
    intro v vm
    have hit := (mem_union.mp (keep (h-1) (by omega) s sm vm)).resolve_left (fun old=>stop v old (mem_outN.mp vm).2)
    rwa [Nat.sub_add_cancel depth] at hit
  exact (quota _ (by omega) s sm).trans (card_le_card bound)

attribute [aesop safe forward (immediate := [free,hr,hq,height,depth,sub,size,apart,quota,step])
  (rule_sets := [CHGraphFamilies])] end_capacity
#print axioms from_sink
#print axioms end_capacity
end LeanCH.BR.EqualLayerTransit
