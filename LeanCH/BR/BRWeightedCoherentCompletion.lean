import LeanCH.BR.BRCoherentCompletionGeometry
import LeanCH.BR.BRWeightedSaturatedCompletion

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

theorem arc_count_outdegree (D : CH.Digraph) (V : Finset ℕ) :
    (arcSet D V).card=∑x∈V,(outN D V x).card := by
  simp only [arcSet,card_eq_sum_ones,sum_filter,sum_product,outN]

/-- Two additions and one deletion, with exact degrees. The two insertions need not be individually specified
as distinct labels: only the ordered arcs are distinct. The cut head is arbitrary. -/
theorem regular_two_completion_endpoint {q d : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (i j k l h : V)
    (hn : V.card=q*d+1) (hout : ∀x:V,(outN D V x).card=d)
    (hin : ∀x:V,(inN D V x).card=d)
    (h1 : ¬D i j=true) (h2 : ¬D k l=true) (hdist : i≠k ∨ j≠l)
    (hhj : h≠j) (hhl : h≠l) (hcut : D i h=true)
    (hjoint : QFree (insertArc (insertArc D i j) k l) V q) :
    let T := insertArc (eraseArc (insertArc D i j) i h) k l
    QFree T V q ∧ ¬SmallRow q T V ∧
      (∀x:V,(outN T V x).card=d+(if x=k then 1 else 0)) ∧
      (inN T V h).card=d-1 ∧ (arcSet T V).card=V.card*d+1 := by
  dsimp only
  have heq (a b:V) : a.val=b.val ↔ a=b := Subtype.ext_iff.symm
  have hnew : ¬insertArc D i j k l=true := by
    have hnij : ¬(k.val=i.val ∧ l.val=j.val) := by
      simp only [heq]
      rintro ⟨e,f⟩
      exact hdist.elim (fun n=>n e.symm) (fun n=>n f.symm)
    simpa only [insertArc,hnij,ite_false] using h2
  have hold := insertArc_mono D i j i h hcut
  have ho : ∀x:V,(outN (insertArc D i j) V x).card=d+(if x=i then 1 else 0) := by
    intro x
    simp only [outdegree_insert_missing i j h1,hout x,heq]
  have hi : ∀x:V,(inN (insertArc D i j) V x).card=d+(if x=j then 1 else 0) := by
    intro x
    have hh := outdegree_insert_missing (D:=fun a b=>D b a) j i h1 x
    have he : (inN (insertArc D i j) V x).card=(inN D V x).card+(if x=j then 1 else 0) := by
      simpa only [outN,inN,insertArc,and_comm,heq] using hh
    simpa only [hin x] using he
  have ho1 : (outN (insertArc D i j) V i).card=d+1 := by simpa using ho i
  have ho0 : ∀x:V,x≠i→(outN (insertArc D i j) V x).card=d := by
    intro x hx; simpa [hx] using ho x
  have hfresh : ¬eraseArc (insertArc D i j) i h k l=true :=
    fun e=>hnew (eraseArc_sub _ i h k l e)
  have hh1 : (inN (insertArc D i j) V j).card=d+1 := by simpa using hi j
  have hh0 : ∀x:V,x≠j→(inN (insertArc D i j) V x).card=d := by
    intro x hx; simpa [hx] using hi x
  have hp := single_excess_exchange_degrees i j h k l hold hfresh hhj hhl ho1 ho0 hh1 hh0
  refine ⟨?_,single_excess_fresh_completion_bad hq i h k l hn ho1 ho0 hold hnew,
    hp.1,by simpa using hp.2 h,?_⟩
  · apply qfree_sub (E:=insertArc (insertArc D i j) k l) ?_
      hjoint
    intro a b e
    by_cases hab : a=k.val ∧ b=l.val
    · simp [insertArc,hab]
    · have hh : eraseArc (insertArc D i j) i h a b=true := by
        simpa only [insertArc,hab,ite_false] using e
      exact insertArc_mono _ k l a b (eraseArc_sub _ i h a b hh)
  · rw [arcSet_exchange_card i h k l hold hfresh,arcSet_insert i.property j.property]
    have hnot : (i.val,j.val)∉arcSet D V := fun he=>h1 (mem_filter.mp he).2
    rw [card_insert_of_notMem hnot,arc_count_outdegree]
    congr 1
    calc
      ∑x∈V,(outN D V x).card = ∑_x∈V,d := sum_congr rfl (fun x hx=>hout ⟨x,hx⟩)
      _ = V.card*d := by simp

/-- Coherence supplies joint safety and makes EVERY old first-tail head usable. -/
theorem regular_coherent_completion {q d : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (i j k l h : V)
    (hn : V.card=q*d+1) (hout : ∀x:V,(outN D V x).card=d)
    (hin : ∀x:V,(inN D V x).card=d)
    (h1 : ¬D i j=true) (h2 : ¬D k l=true) (hdist : i≠k ∨ j≠l)
    (hshare : i=k ∨ j=l) (hcut : D i h=true)
    (hs1 : QFree (insertArc D i j) V q) (hs2 : QFree (insertArc D k l) V q) :
    let T := insertArc (eraseArc (insertArc D i j) i h) k l
    QFree T V q ∧ ¬SmallRow q T V ∧
      (∀x:V,(outN T V x).card=d+(if x=k then 1 else 0)) ∧
      (inN T V h).card=d-1 ∧ (arcSet T V).card=V.card*d+1 := by
  have hsh : i.val=k.val ∨ j.val=l.val := hshare.elim
    (fun e=>Or.inl (congrArg Subtype.val e)) (fun e=>Or.inr (congrArg Subtype.val e))
  have hav := old_head_avoids_shared_insertions hsh h1 h2 hcut
  exact regular_two_completion_endpoint hq i j k l h hn hout hin h1 h2 hdist
    (fun e=>hav.1 (congrArg Subtype.val e)) (fun e=>hav.2 (congrArg Subtype.val e)) hcut
    (qfree_two_insertions_shared_endpoint i j k l hsh hs1 hs2)

/-- Global minimum is retained by the ACTUAL coherent endpoint and its reverse.
The source F need not be saturated or equalized; only its global arc minimum and
the exact count are used. Normal forms follow from the existing own-law API. -/
theorem NativeArcMinimum.coherent_regular_completion_negative {q d : ℕ} (hq : 2≤q)
    (hd : 1≤d) {F D : CH.Digraph} {V : Finset ℕ}
    (hF : NativeArcMinimum q F V) (hsmall : SmallerSmallRow q V.card)
    (hn : V.card=q*d+1) (hcF : (arcSet F V).card=V.card*d+1)
    (hout : ∀x:V,(outN D V x).card=d) (hin : ∀x:V,(inN D V x).card=d)
    (i j k l : V) (h1 : ¬D i j=true) (h2 : ¬D k l=true)
    (hdist : i≠k ∨ j≠l) (hshare : i=k ∨ j=l)
    (hs1 : QFree (insertArc D i j) V q) (hs2 : QFree (insertArc D k l) V q) :
    ∃h:V,D i h=true ∧
      let T := insertArc (eraseArc (insertArc D i j) i h) k l
      NativeArcMinimum q T V ∧ NativeArcMinimum q (fun x y=>T y x) V ∧
      (arcSet T V).card=(arcSet F V).card ∧
      (outN (fun x y=>T y x) V h).card=d-1 ∧
      1+q*(outN (fun x y=>T y x) V h).card<V.card := by
  obtain ⟨h,hh⟩ := card_pos.mp (show 0<(outN D V i).card by rw [hout i]; omega)
  let hV : V := ⟨h,(mem_outN.mp hh).1⟩
  have hed : D i hV=true := (mem_outN.mp hh).2
  obtain ⟨hf,hbad,_,hi,hc⟩ := regular_coherent_completion hq i j k l hV hn hout hin
    h1 h2 hdist hshare hed hs1 hs2
  have hmin := hF.same_count hf hbad (hc.trans hcF.symm)
  refine ⟨hV,hed,hmin,hmin.reverse hsmall,hc.trans hcF.symm,hi,?_⟩
  change 1+q*(inN (insertArc (eraseArc (insertArc D i j) i hV) k l) V hV).card<V.card
  rw [hi,hn]
  have hd' : d-1+1=d := by omega
  nlinarith

end LeanCH.BR.WeightedSD

