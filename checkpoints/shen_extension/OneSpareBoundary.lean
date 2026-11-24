import checkpoints.shen_extension.SharedSuccessorEquality
import checkpoints.shen_extension.OneSpareTightRow
import checkpoints.shen_extension.PrivateHeadClone

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion

/-- The order-32 argument at arbitrary cutoff and degree. The only
numerical restrictions come from degree-two CH and the fragment capacity. -/
theorem above_four_times {D V q r} (free : QFree D V q) (hq : 4≤q)
    (live : V.Nonempty) (degree : ∀v∈V,r≤(outN D V v).card) (pos : 3≤r) (room : r≤2*q)
    (deficit : (r+(r-1))*(r+(r-1)+1)<2*(r*(r+3)+(r-1)*7)) : 4*r<V.card := by
  classical
  have atLeast := below_four_times free hq live degree (by omega) room deficit
  by_contra! low
  have order : V.card=2*(2*r) := by omega
  obtain ⟨G,sub,reg⟩ := exists_outEq degree
  have gf := qfree_sub sub free
  have f4 := gf.mono_bound hq
  let S := V.filter (fun v=>(ball G V v 2).card=2*r)
  let T := V\S
  have bs v (vv : v∈V) (eq : (ball G V v 2).card=2*r) :
      (N2 G V v).card+1=r := by rw [card_B2,card_B1 f4 vv,reg v vv] at eq; omega
  have floor v (vv : v∈V) : 2*r≤(ball G V v 2).card := by
    have count := reg v vv
    have yy := second_layer gf hq vv (fun w wm=>(reg w wm).ge) (by omega) (by omega)
    rw [card_B2,card_B1 f4 vv,count]
    omega
  let full := fun u w => w∈outN G V u ∧ (outN G (outN G V u) w).card=1
  have supplier (u : ℕ) : ∃w,u∈S → full u w ∧ w∈T := by
    by_cases us : u∈S
    · obtain ⟨uv,small⟩ := mem_filter.mp us
      have short := bs u uv small
      obtain ⟨w,wm,tall,one⟩ := tall_successor gf hq uv reg (by omega) room short
        (third_layer gf hq uv reg room short deficit)
      exact ⟨w,fun _=>⟨⟨wm,one⟩,mem_sdiff.mpr ⟨outN_subset wm,fun ss=>
        (Nat.ne_of_gt tall) (mem_filter.mp ss).2⟩⟩⟩
    · exact ⟨0,fun h=>(us h).elim⟩
  choose f info using supplier
  have clash {u v w} (us : u∈S) (vs : v∈S) (ne : u≠v)
      (uw : full u w) (vw : full v w) : v∉ball G V u 2 := by
    obtain ⟨uv,ue⟩ := mem_filter.mp us
    obtain ⟨vv,ve⟩ := mem_filter.mp vs
    have su := bs u uv ue
    have sv := bs v vv ve
    exact shared_full_misses gf hq uv vv ne reg su sv uw.1 vw.1
      (sends_layer gf hq uv reg su uw.1 uw.2) (sends_layer gf hq vv reg sv vw.1 vw.2)
  have tall u (uv : u∈V) (small : (ball G V u 2).card=2*r) :
      f u∈V ∧ 2*r<(ball G V (f u) 2).card := by
    have ht := (info u (mem_filter.mpr ⟨uv,small⟩)).2
    obtain ⟨wv,off⟩ := mem_sdiff.mp ht
    exact ⟨wv,lt_of_le_of_ne (floor _ wv) (fun eq=>off (mem_filter.mpr ⟨wv,eq.symm⟩))⟩
  have packet := shared_successor_equality gf (by omega : 2+2≤q) order floor f tall
    (fun u uv v vv ue ve ne same=>by
      have us : u∈S := mem_filter.mpr ⟨uv,ue⟩
      have vs : v∈S := mem_filter.mpr ⟨vv,ve⟩
      exact clash us vs ne (info u us).1 (same.symm ▸ (info v vs).1))
  obtain ⟨sc,tc,empty,scores⟩ := packet
  have only {u v w} (us : u∈S) (vs : v∈S) (uw : full u w) (vw : full v w) : u=v := by
    by_contra ne
    have hit : (u,v)∈orderedIncomparable G V 2 := mem_filter.mpr
      ⟨mem_offDiag.mpr ⟨(mem_filter.mp us).1,(mem_filter.mp vs).1,ne⟩,
        clash us vs ne uw vw,clash vs us (Ne.symm ne) vw uw⟩
    rw [empty] at hit
    exact notMem_empty _ hit
  have inj : Set.InjOn f (↑S) := fun u us v vs eq=>only us vs (info u us).1 (eq.symm ▸ (info v vs).1)
  have onto : S.image f=T := by
    apply eq_of_subset_of_card_le (image_subset_iff.mpr (fun u us=>(info u us).2))
    rw [card_image_of_injOn inj]
    change T.card≤S.card
    exact tc.le.trans sc.ge
  have all v (vv : v∈V) : (ball G V v 2).card≤2*r+1 := by
    by_cases vs : v∈S
    · exact (mem_filter.mp vs).2.le.trans (Nat.le_succ _)
    · exact (scores v (mem_sdiff.mpr ⟨vv,vs⟩)).le
  obtain ⟨u,us⟩ := card_pos.mp (show 0<S.card by change S.card=2*r at sc; omega)
  obtain ⟨uv,ue⟩ := mem_filter.mp us
  have short := bs u uv ue
  let X := outN G V u
  let a := f u
  obtain ⟨⟨ax,one⟩,_⟩ := info u us
  obtain ⟨b,ab⟩ := card_eq_one.mp one
  have bm : b∈outN G X a := ab.symm ▸ mem_singleton_self b
  have other (v) (vm : v∈X) (ne : v≠a) : 2≤(outN G X v).card := by
    by_contra! small
    have positive : 0<(outN G X v).card := internal_positive gf hq uv reg short vm
    have vo : (outN G X v).card=1 := by omega
    have big := every_full_tall gf hq uv reg pos room vm vo short (third_layer gf hq uv reg room short deficit) all
    have vt : v∈T := mem_sdiff.mpr ⟨outN_subset vm,fun ss=>(Nat.ne_of_gt big) (mem_filter.mp ss).2⟩
    rw [←onto] at vt
    obtain ⟨w,ws,eq⟩ := mem_image.mp vt
    have same := only us ws ⟨vm,vo⟩ (eq ▸ (info w ws).1)
    exact ne (show v=f u from eq.symm.trans (congrArg f same.symm))
  exact PrivateHeadClone.degree_two_obstruction (gf.mono_set (outN_subset : X⊆V)) (by omega)
    (by change (outN G V u).card≤_; rw [reg u uv]; exact room) ax (outN_subset bm)
    (mem_outN.mp bm).2 (by
      intro eq
      have edge : G a b=true := (mem_outN.mp bm).2
      rw [eq] at edge
      exact n1 f4 (outN_subset ax) edge) other

#print axioms above_four_times
end LeanCH.BR.OneSpareGrowth
