import LeanCH.BR.BRWeightedGlobalArcMinimum
import LeanCH.BR.BRWeightedNativePressureReduction

/-! Exact degrees of the actual same-count repair, without reminimization. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

theorem outdegree_insert_missing {D : CH.Digraph} {V : Finset ℕ}
    (t b : V) (hnew : ¬D t b=true) (x : ℕ) :
    (outN (insertArc D t b) V x).card=(outN D V x).card+(if x=t.val then 1 else 0) := by
  by_cases hx : x=t.val
  · subst x
    have he : outN (insertArc D t b) V t=insert b.val (outN D V t) := by
      ext y
      by_cases hy : y=b.val
      · subst y; simp [outN,insertArc,b.property]
      · simp [outN,insertArc,hy]
    have hn : b.val∉outN D V t := fun hh => hnew (mem_outN.mp hh).2
    rw [he,card_insert_of_notMem hn]
    simp
  · have he : outN (insertArc D t b) V x=outN D V x := by
      ext y
      simp [outN,insertArc,hx]
    rw [he]
    simp [hx]

theorem outdegree_erase_actual {D : CH.Digraph} {V : Finset ℕ}
    (h w : V) (hhw : D h w=true) (x : ℕ) :
    (outN (eraseArc D h w) V x).card+(if x=h.val then 1 else 0)=(outN D V x).card := by
  by_cases hx : x=h.val
  · subst x
    have he : outN (eraseArc D h w) V h=(outN D V h).erase w := by
      ext y
      simp [outN,eraseArc,and_comm,and_left_comm,and_assoc]
    have hw : w.val∈outN D V h := mem_outN.mpr ⟨w.property,hhw⟩
    have hp : 0<(outN D V h).card := card_pos.mpr ⟨w,hw⟩
    rw [he,card_erase_of_mem hw]
    simp only [ite_true]
    omega
  · have he : outN (eraseArc D h w) V x=outN D V x := by
      ext y
      simp [outN,eraseArc,hx]
    rw [he]
    simp [hx]

theorem outdegree_exchange {D : CH.Digraph} {V : Finset ℕ}
    (h w t b : V) (hhw : D h w=true) (hnew : ¬eraseArc D h w t b=true) (x : ℕ) :
    (outN (insertArc (eraseArc D h w) t b) V x).card+(if x=h.val then 1 else 0)=
      (outN D V x).card+(if x=t.val then 1 else 0) := by
  rw [outdegree_insert_missing t b hnew]
  have he := outdegree_erase_actual h w hhw x
  omega

theorem indegree_exchange {D : CH.Digraph} {V : Finset ℕ}
    (h w t b : V) (hhw : D h w=true) (hnew : ¬eraseArc D h w t b=true) (x : ℕ) :
    (inN (insertArc (eraseArc D h w) t b) V x).card+(if x=w.val then 1 else 0)=
      (inN D V x).card+(if x=b.val then 1 else 0) := by
  have hh := outdegree_exchange (D := fun i j => D j i) w h b t hhw
    (by simpa only [eraseArc_reverse] using hnew) x
  simpa [outN,inN,insertArc,eraseArc,and_comm] using hh

theorem single_excess_exchange_degrees {D : CH.Digraph} {V : Finset ℕ} {r : ℕ}
    (h g w t b : V) (hhw : D h w=true) (hnew : ¬eraseArc D h w t b=true)
    (hwg : w≠g) (hwb : w≠b)
    (hdh : (outN D V h).card=r+1) (hout : ∀i:V,i≠h → (outN D V i).card=r)
    (hdg : (inN D V g).card=r+1) (hin : ∀i:V,i≠g → (inN D V i).card=r) :
    (∀ i:V,(outN (insertArc (eraseArc D h w) t b) V i).card=r+(if i=t then 1 else 0)) ∧
    (∀ i:V,(inN (insertArc (eraseArc D h w) t b) V i).card=
      if i=w then r-1 else r+(if i=g then 1 else 0)+(if i=b then 1 else 0)) := by
  have heq (i j : V) : i.val=j.val ↔ i=j := Subtype.ext_iff.symm
  constructor
  · intro i
    have he := outdegree_exchange h w t b hhw hnew i
    simp only [heq] at he
    by_cases hh : i=h
    · subst i
      rw [hdh] at he
      simp only [ite_true] at he
      omega
    · rw [hout i hh] at he
      simp only [hh,ite_false,add_zero] at he
      exact he
  · intro i
    have he := indegree_exchange h w t b hhw hnew i
    simp only [heq] at he
    by_cases hiw : i=w
    · subst i
      rw [hin w hwg] at he
      simp only [hwb,ite_false,ite_true,add_zero] at he
      simp only [ite_true]
      omega
    · simp only [hiw,ite_false,add_zero] at he ⊢
      by_cases hig : i=g
      · subst i
        rw [hdg] at he
        simpa using he
      · rw [hin i hig] at he
        simpa [hig] using he

theorem NativeArcMinimum.single_excess_repair {q r : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hmin : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card)
    (hH : CommonInverse (realMatrix q D V) H) (h g w t b : V)
    (hhw : D h w=true) (ht : (q:ℝ)*H w h=1) (hnew : ¬eraseArc D h w t b=true)
    (hwg : w≠g) (hwb : w≠b) (hn : V.card=q*r+1)
    (hdh : (outN D V h).card=r+1) (hout : ∀i:V,i≠h → (outN D V i).card=r)
    (hdg : (inN D V g).card=r+1) (hin : ∀i:V,i≠g → (inN D V i).card=r)
    (hf : QFree (insertArc (eraseArc D h w) t b) V q) :
    let E := fun x y => insertArc (eraseArc D h w) t b y x
    NativeArcMinimum q E V ∧ (arcSet E V).card=(arcSet D V).card ∧
      (∀ i:V,(outN E V i).card=if i=w then r-1 else r+(if i=g then 1 else 0)+(if i=b then 1 else 0)) ∧
      (∀ i:V,(inN E V i).card=r+(if i=t then 1 else 0)) ∧
      1+q*(outN E V w).card<V.card := by
  dsimp only
  obtain ⟨_,he⟩ := hmin.threshold_exchange hq hsmall hH h w t b hhw ht hnew hf
  obtain ⟨ho,hi⟩ := single_excess_exchange_degrees h g w t b hhw hnew hwg hwb hdh hout hdg hin
  have hneg := (threshold_deletion_add_negative_reverse hq hH h w t b hhw ht hn
    (hin w hwg) hwb hnew hf).2.2
  exact ⟨he,(arcSet_reverse_card _ V).trans (arcSet_exchange_card h w t b hhw hnew),hi,ho,hneg⟩

theorem NativeArcMinimum.nonsaturated_single_excess_repair {q r : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hmin : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card)
    (hH : CommonInverse (realMatrix q D V) H) (hr : 2≤r) (h g : V)
    (hn : V.card=q*r+1)
    (hdh : (outN D V h).card=r+1) (hout : ∀i:V,i≠h → (outN D V i).card=r)
    (hdg : (inN D V g).card=r+1) (hin : ∀i:V,i≠g → (inN D V i).card=r)
    (hcol : ∀i:V,H i h=1/(q:ℝ)) (hns : ¬Sat q D V) :
    ∃ w t b : V, D h w=true ∧ w≠g ∧ w≠b ∧ ¬D t b=true ∧
      let E := fun x y => insertArc (eraseArc D h w) t b y x
      NativeArcMinimum q E V ∧ (arcSet E V).card=(arcSet D V).card ∧
        (∀ i:V,(outN E V i).card=if i=w then r-1 else r+(if i=g then 1 else 0)+(if i=b then 1 else 0)) ∧
        (∀ i:V,(inN E V i).card=r+(if i=t then 1 else 0)) ∧
        1+q*(outN E V w).card<V.card := by
  classical
  unfold BRsub.Sat at hns
  push Not at hns
  obtain ⟨b,hb,t,ht,htb,hsafe⟩ := hns
  have hnot : ¬outN D V h⊆{g.val,b} := by
    intro hs
    have hh := (card_le_card hs).trans (card_insert_le g.val {b})
    simp only [card_singleton] at hh
    omega
  obtain ⟨w,hw,hex⟩ := not_subset.mp hnot
  have hwV := (mem_outN.mp hw).1
  have hhw := (mem_outN.mp hw).2
  have hex' : w≠g.val ∧ w≠b := by simpa only [mem_insert,mem_singleton,not_or] using hex
  let wV : V := ⟨w,hwV⟩
  let tV : V := ⟨t,ht⟩
  let bV : V := ⟨b,hb⟩
  have hnew : ¬eraseArc D h w t b=true := fun he => htb (eraseArc_sub D h w t b he)
  have hK : QFree (insertArc (eraseArc D h w) t b) V q := by
    apply qfree_sub ?_ (qfree_insertArc hmin.free tV bV hsafe)
    intro x y he
    by_cases hh : x=t ∧ y=b
    · simp [insertArc,hh,tV,bV]
    · have heG : eraseArc D h w x y=true := by simpa only [insertArc,hh,ite_false] using he
      exact insertArc_mono D t b x y (eraseArc_sub D h w x y heG)
  have hthreshold : (q:ℝ)*H wV h=1 := by
    rw [hcol]
    have hq0 : (q:ℝ)≠0 := by exact_mod_cast (show q≠0 by omega)
    field_simp
  have hwg : wV≠g := fun he => hex'.1 (congrArg Subtype.val he)
  have hwb : wV≠bV := fun he => hex'.2 (congrArg Subtype.val he)
  exact ⟨wV,tV,bV,hhw,hwg,hwb,htb,hmin.single_excess_repair hq hsmall hH
    h g wV tV bV hhw hthreshold hnew hwg hwb hn hdh hout hdg hin hK⟩

end LeanCH.BR.WeightedSD
