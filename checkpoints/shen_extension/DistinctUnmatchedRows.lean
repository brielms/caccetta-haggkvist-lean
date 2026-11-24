import checkpoints.shen_extension.ColumnBlockerEscape

namespace LeanCH.BR.Closure.ColumnBlockerEscape
open Finset BRq2 BRq3 BR45

def Unmatched (D : CH.Digraph) (V : Finset ℕ) (a : ℕ) : Prop :=
  ∀ w∈V, outN D V w ≠ inN D V a

/-- Two different outgoing sets occur on the unmatched columns, already on
the original counterexample. No regularity or least-order hypothesis. -/
theorem distinct_unmatched {D V s} (safe : QFree D V 3) (live : V.Nonempty)
    (degree : ∀v∈V, s≤(outN D V v).card) (small : V.card≤3*s) :
    ∃ u∈V, ∃ v∈V, Unmatched D V u ∧ Unmatched D V v ∧ outN D V u≠outN D V v := by
  classical
  let U := V.filter (Unmatched D V)
  have uv : U⊆V := filter_subset _ _
  have matched {a} (av : a∈V) (au : a∉U) : ∃ b∈V, outN D V b=inN D V a := by
    by_contra no
    exact au (mem_filter.mpr ⟨av,fun b bv e => no ⟨b,bv,e⟩⟩)
  have present : U.Nonempty := by
    by_contra none
    have := all_columns_order safe live degree (fun _ av => matched av (fun h => none ⟨_,h⟩))
    omega
  obtain ⟨u,uu⟩ := present
  let H := outN D V u
  have hV : H⊆V := outN_subset
  have pos : 0<s := by have := card_pos.mpr live; omega
  obtain ⟨h,hh⟩ := card_pos.mp (pos.trans_le (degree u (uv uu)))
  change h∈H at hh
  by_contra noPair
  have uniform {v} (vu : v∈U) : outN D V v=H := by
    by_contra ne
    exact noPair ⟨u,uv uu,v,uv vu,(mem_filter.mp uu).2,(mem_filter.mp vu).2,Ne.symm ne⟩
  have apart {v} (vu : v∈U) : v∉H := fun vh =>
    loopfree safe (by decide) (uv vu) (mem_outN.mp ((uniform vu).symm ▸ vh)).2
  let T := V.filter (fun a => inN D V a=H)
  have Tedge {a} (ta : a∈T) {x} (hx : x∈H) : D x a=true :=
    (mem_inN.mp ((mem_filter.mp ta).2.symm ▸ hx)).2
  have notH {a} (ta : a∈T) : a∉H := fun hit =>
    loopfree safe (by decide) (mem_filter.mp ta).1 (Tedge ta hit)
  have avoid {t a} (tt : t∈T) (ta : a∈outN D V t) : a∉U ∧ a∉H ∧ a∉T := by
    have tv := (mem_filter.mp tt).1
    have ⟨av,edge⟩ := mem_outN.mp ta
    refine ⟨fun au => safe a 3 (by decide) (by decide)
      (.step (hV hh) (mem_outN.mp ((uniform au).symm ▸ hh)).2
        (.step tv (Tedge tt hh) (.step av edge (.refl _)))),?_,?_⟩
    · exact fun ah => digonfree safe (by decide) tv av edge (Tedge tt ah)
    · intro at'
      have ht : t∈inN D V a := mem_inN.mpr ⟨tv,edge⟩
      rw [(mem_filter.mp at').2] at ht
      exact notH tt ht
  have outside {a} (av : a∈V) (au : a∉U) (ah : a∉H) (at' : a∉T) :
      ∃ b∈T, outN D V b=inN D V a := by
    obtain ⟨b,bv,ab⟩ := matched av au
    have bu : b∉U := fun hit => at' (mem_filter.mpr ⟨av,ab.symm.trans (uniform hit)⟩)
    obtain ⟨c,cv,bc⟩ := matched bv bu
    by_cases cu : c∈U
    · exact ⟨b,mem_filter.mpr ⟨bv,bc.symm.trans (uniform cu)⟩,ab⟩
    obtain ⟨e,ev,ce⟩ := matched cv cu
    obtain ⟨_,_,z,hz,un⟩ := local_unmatched safe degree pos small av bv cv ab bc (ce ▸ degree e ev)
    have ⟨zv,za⟩ := mem_inN.mp (mem_inter.mp hz).1
    have zu : z∈U := mem_filter.mpr ⟨zv,un⟩
    exact False.elim (ah ((uniform zu) ▸ mem_outN.mpr ⟨av,za⟩))
  have noT (t) (tt : t∈T) : False := by
    obtain ⟨a,ta⟩ := card_pos.mp (pos.trans_le (degree t (mem_filter.mp tt).1))
    obtain ⟨au,ah,at'⟩ := avoid tt ta
    obtain ⟨b,bt,ab⟩ := outside (mem_outN.mp ta).1 au ah at'
    have tIn : t∈inN D V a := mem_inN.mpr ⟨(mem_filter.mp tt).1,(mem_outN.mp ta).2⟩
    exact (avoid bt (ab.symm ▸ tIn)).2.2 tt
  have cover {a} (av : a∈V) (au : a∉U) : a∈H := by
    by_contra ah
    obtain ⟨b,bt,_⟩ := outside av au ah (noT a)
    exact noT b bt
  obtain ⟨b,bv,bh⟩ := matched (hV hh) (fun hu => apart hu hh)
  have buEdge : D b u=true := (mem_outN.mp (bh.symm ▸
    (mem_inN.mpr ⟨uv uu,(mem_outN.mp hh).2⟩ : u∈inN D V h))).2
  by_cases bu : b∈U
  · exact apart uu ((uniform bu) ▸ mem_outN.mpr ⟨uv uu,buEdge⟩)
  · exact digonfree safe (by decide) (uv uu) bv (mem_outN.mp (cover bv bu)).2 buEdge

#print axioms distinct_unmatched
end LeanCH.BR.Closure.ColumnBlockerEscape
