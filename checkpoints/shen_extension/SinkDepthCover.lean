import checkpoints.shen_extension.UniqueSinkReturnCapacity
import checkpoints.shen_extension.OneOmissionSinkBank
import checkpoints.shen_extension.RecipientUnionReplay

namespace LeanCH.BR.SinkDepthCover
open Finset BRq2 BRq3 BR45 BRsGen OneOmissionSinkBank ProfileSinkReturns

/-- First-layer labels without a route to any sink in fewer than j steps. -/
noncomputable def deep (D : CH.Digraph) (X : Finset ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact X.filter (fun v=>∀s∈sinks D X,∀k,k<j → ¬Walk D X v s k)

theorem depth_slots {D X j} (dag : QFree D X X.card) (pos : 0<j)
    (live : (deep D X j).Nonempty) :
    (deep D X j).card+(sinks D X).card+(j-1)≤X.card := by
  classical
  let R := deep D X j
  let S := sinks D X
  have rx : R⊆X := filter_subset _ _
  have sx : S⊆X := filter_subset _ _
  have apart : Disjoint R S := by
    apply disjoint_left.mpr
    intro v vm sm
    exact (mem_filter.mp vm).2 v sm 0 pos (.refl v)
  obtain ⟨v,vm⟩ := live
  obtain ⟨p⟩ := exists_shortest_sink_path dag le_rfl (rx vm)
  have ends : p.vertex p.len∈S := mem_filter.mpr ⟨p.mem _ le_rfl,p.sink⟩
  have long : j≤p.len := by
    by_contra! h
    apply (mem_filter.mp vm).2 _ ends _ h
    simpa only [p.start,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
  let I := Ico (p.len-(j-1)) p.len
  have ci : I.card=j-1 := by dsimp [I]; rw [Nat.card_Ico]; omega
  have sub : I.image p.vertex ⊆ X\(R∪S) := by
    intro a am
    obtain ⟨i,im,rfl⟩ := mem_image.mp am
    obtain ⟨lo,hi⟩ := mem_Ico.mp im
    refine mem_sdiff.mpr ⟨p.mem _ hi.le,?_⟩
    intro h
    rcases mem_union.mp h with d|s
    · exact (mem_filter.mp d).2 _ ends _ (by omega) (p.walk hi.le le_rfl)
    · exact (mem_filter.mp s).2 _ (p.mem _ hi) (p.edge i hi)
  have incl : (↑I : Set ℕ)⊆range (p.len+1) := by
    intro i im
    exact mem_range.mpr (by have := (mem_Ico.mp im).2; omega)
  have bound := card_le_card sub
  have cap := card_le_card (union_subset rx sx)
  rw [card_image_of_injOn ((p.injective dag le_rfl).mono incl),ci,card_sdiff_of_subset (union_subset rx sx)] at bound
  rw [card_union_of_disjoint apart] at bound cap
  change R.card+S.card+(j-1)≤X.card
  omega

/-- The outgoing row of a late recipient fits one level earlier. Its own
label also consumes one slot at that level. -/
theorem head_slots {D X j v} (dag : QFree D X X.card) (pos : 2≤j) (vm : v∈deep D X j) :
    (outN D X v).card+(sinks D X).card+(j-1)≤X.card := by
  classical
  have vx := (mem_filter.mp vm).1
  have earlier : v∈deep D X (j-1) :=
    mem_filter.mpr ⟨vx,fun s sm k h=>(mem_filter.mp vm).2 s sm k (by omega)⟩
  have sub : insert v (outN D X v)⊆deep D X (j-1) := by
    apply insert_subset earlier
    intro a am
    refine mem_filter.mpr ⟨outN_subset am,?_⟩
    intro s sm k h walk
    exact (mem_filter.mp vm).2 _ sm _ (by omega : k+1<j) (.step (outN_subset am) (mem_outN.mp am).2 walk)
  have no : v∉outN D X v := fun h=>loopfree dag (card_pos.mpr ⟨v,vx⟩) vx (mem_outN.mp h).2
  have bound := card_le_card sub
  rw [card_insert_of_notMem no] at bound
  have lim := depth_slots dag (by omega : 0<j-1) ⟨v,earlier⟩
  omega

/-- A late recipient can omit only the spare second-layer labels and
as many further labels as it has heads inside the first layer. -/
theorem omitted_heads {D V X Y v r k} (degree : r≤(outN D V v).card)
    (menu : outN D V v⊆X∪Y) (slots : (outN D X v).card≤k) :
    (Y\outN D V v).card+r≤Y.card+k := by
  have sub : outN D V v⊆(Y∩outN D V v)∪outN D X v := by
    intro a am
    by_cases ay : a∈Y
    · exact mem_union_left _ (mem_inter.mpr ⟨ay,am⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨(mem_union.mp (menu am)).resolve_right ay,(mem_outN.mp am).2⟩)
  have := (card_le_card sub).trans (card_union_le _ _)
  have := card_sdiff_add_card_inter Y (outN D V v)
  omega

/-- For any marked sink whose bank returns, a cover by actual omissions
forces a numerical bill indexed by the *number of sinks*, regardless of
which of the sinks carry the omitted labels. -/
theorem cover_bill {D V X Y q r s} (free : QFree D V q) (hq : 4≤q)
    (xv : X⊆V) (yv : Y⊆V) (dag : QFree D X X.card) (sm : s∈sinks D X)
    (om : ℕ→ℕ) (rows : ∀t∈sinks D X,outN D V t=Y.erase (om t))
    (acyclic : QFree D (Y.erase (om s)) (Y.erase (om s)).card)
    (returns : ∀b∈Y.erase (om s),Sink D (Y.erase (om s)) b → ∃v∈X,D b v=true)
    (menu : ∀v∈X,outN D V v⊆X∪Y) (rank : ∀v∈X,r≤(outN D V v).card)
    (short : X.card-((sinks D X).card+(q-3))+(Y.card-r)<q-1) :
    (Y.erase (om s)).card ≤
      (X.card-((sinks D X).card+(q-3)))*(X.card-((sinks D X).card+(q-3))+(Y.card-r))+
      ((sinks D X).card-1) := by
  classical
  let S := sinks D X
  let R := deep D X (q-2)
  let K := X.card-(S.card+(q-3))
  have rx : R⊆X := filter_subset _ _
  have count : R.card≤K := by
    by_cases h : R.Nonempty
    · have := depth_slots dag (by omega : 0<q-2) h
      dsimp [R,K,S] at *
      omega
    · rw [not_nonempty_iff_eq_empty.mp h,card_empty]; omega
  have bound v (vm : v∈R) : (Y\outN D V v).card≤K+(Y.card-r) := by
    have a := head_slots dag (by omega : 2≤q-2) vm
    have cap : (outN D X v).card≤K := by dsimp [K,S]; omega
    have := omitted_heads (rank v (rx vm)) (menu v (rx vm)) cap
    omega
  have near v (vm : v∈X) (miss : v∉R) : ∃t∈S,∃k,k+3≤q ∧ Walk D X v t k := by
    by_contra! h
    exact miss (mem_filter.mpr ⟨vm,fun t tm k hk=>h t tm k (by omega)⟩)
  have cov := RecipientUnionAudit.paid_omissions free (by omega) xv yv (rx.trans xv) (Subset.rfl : R⊆R)
    om rows acyclic returns near (fun v vm miss=>by obtain ⟨t,tm,k,lim,w⟩ := near v vm miss; exact ⟨t,tm,k,by omega,w⟩)
    (fun v vm=>(bound v vm).trans_lt short)
  have total := (card_le_card cov).trans (card_union_le _ _)
  have cap := card_biUnion_le_card_mul R (fun v=>Y\outN D V v) (K+(Y.card-r)) bound
  have extra := card_image_le (s:=S.erase s) (f:=om)
  rw [card_erase_of_mem sm] at extra
  have pay := Nat.mul_le_mul_right (K+(Y.card-r)) count
  change _≤K*(K+(Y.card-r))+(S.card-1)
  exact total.trans (Nat.add_le_add (cap.trans pay) extra)

/-- Use the marked sink that actually returns. Every obstructed sink supplies
one via its physical destination. -/
theorem flat_impossible {D V q r u} (free : QFree D V q) (hq : 7≤q) (hr : 8≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (flat : Flat D V r) (uv : u∈V)
    (routing : Routing D V u) : False := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let S := sinks D X
  have cx : X.card=r := reg u uv
  have cy : Y.card=r+1 := (layers free (by omega) reg flat uv).1
  have caps : r-(q-1)≤2 := by omega
  have lc : r-(q-1)+(Y.card-r)≤3 := by omega
  have six := Nat.mul_le_mul caps lc
  obtain ⟨a,am,b,bm,diff,sa,sb⟩ := UniqueSinkReturnCapacity.two_sinks free (by omega) reg uv routing
    (by change r-(q-1)+(Y.card-r)<q-1; omega) (by change (r-(q-1))*(r-(q-1)+(Y.card-r))<r; omega)
  have ma : a∈S := mem_filter.mpr ⟨am,sa⟩
  have mb : b∈S := mem_filter.mpr ⟨bm,sb⟩
  have low : 2≤S.card := by
    have sub : ({b,a} : Finset ℕ)⊆S := insert_subset mb (singleton_subset_iff.mpr ma)
    simpa [card_pair diff] using card_le_card sub
  have high : S.card≤r := (card_le_card (filter_subset _ _ : S⊆X)).trans_eq cx
  have steady : ∃s∈S,¬Deflects D V X s := by
    by_cases h : Deflects D V X a
    · obtain ⟨t,tm,ts,st,_⟩ := routing.send a am sa h
      exact ⟨t,mem_filter.mpr ⟨tm,ts⟩,st⟩
    · exact ⟨a,ma,h⟩
  obtain ⟨s,sm,stead⟩ := steady
  have supply t (tm : t∈S) : ∃b∈Y,outN D V t=Y.erase b ∧ QFree D (Y.erase b) (Y.erase b).card := by
    obtain ⟨o,oo,eq,ac,_⟩ := routing.layers.at_sink t (mem_filter.mp tm).1 (mem_filter.mp tm).2
    exact ⟨o,oo,eq,ac⟩
  let om t := if h:t∈S then (supply t h).choose else 0
  have marks t (tm : t∈S) : om t∈Y ∧ outN D V t=Y.erase (om t) ∧ QFree D (Y.erase (om t)) (Y.erase (om t)).card := by
    simpa only [om,dite_eq_left tm] using (supply t tm).choose_spec
  have row := (marks s sm).2.1
  have need b (bm : b∈Y.erase (om s)) (sink : Sink D (Y.erase (om s)) b) : ∃v∈X,D b v=true := by
    by_contra h
    exact stead ⟨b,row.symm ▸ bm,row.symm ▸ sink,fun v vm arc=>h ⟨v,vm,arc⟩⟩
  let K := X.card-(S.card+(q-3))
  have small : K≤2 := by dsimp [K]; omega
  have bound := cover_bill (r:=r) free (by omega) (outN_subset : X⊆V) (fun _ m=>N2_subV m) routing.layers.acyclic sm
    om (fun t tm=>(marks t tm).2.1) (marks s sm).2.2 need
    (fun v vm z zm=>headX (free.mono_bound (by omega : 4≤q)) uv vm (outN_subset zm) (mem_outN.mp zm).2)
    (fun v vm=>(reg v (outN_subset vm)).ge)
    (by change K+(Y.card-r)<q-1; omega)
  change (Y.erase (om s)).card≤K*(K+(Y.card-r))+(S.card-1) at bound
  rw [card_erase_of_mem (marks s sm).1,cy] at bound
  by_cases empty : K=0
  · simp only [empty,Nat.zero_mul,Nat.zero_add] at bound
    omega
  by_cases one : K=1
  · have few : S.card≤3 := by dsimp [K] at one; omega
    simp only [one,Nat.one_mul] at bound
    omega
  · have two : K=2 := by omega
    have few : S.card=2 := by dsimp [K] at two; omega
    rw [two] at bound
    omega

theorem carrier {D V q r} (free : QFree D V q) (live : V.Nonempty)
    (degree : ∀v∈V,r≤(outN D V v).card) (hq : 7≤q) (hr : 8≤r) (fit : r≤q+1)
    (prev : RetainedLayerCapacity.FourthRoom r) (cap : MixedBankScore.Capacity r)
    (room : MixedBankProfile.Room r) (exactRoom : EqualMixedShells.Room r) :
    7*r<V.card := by
  by_contra! size
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have shells := MixedBankProfile.uniform ff reg hq (by omega) fit prev cap room size
  have second := EqualMixedShells.exact_second ff hq (by omega) fit reg exactRoom shells
  have flat : Flat F V r := fun v vm=>⟨second v vm,(shells v vm).2⟩
  have left := fun x (xm : x∈V)=>(flat x xm).2.1.ge
  have right := fun x (xm : x∈V)=>(flat x xm).2.2.ge
  have time : 3+4≤q := by omega
  obtain ⟨u,uv⟩ := live
  have lower := card_ge_of_two_balls ff time left right ⟨u,uv⟩
  have routes := ProfileSinkReturns.routing ff (by omega) (by omega) fit reg flat uv
    (fun _ sm _ vm ne=>separated ff time left right (by omega) sm vm ne)
  exact flat_impossible ff hq hr fit reg flat uv routes

/-- Apply the carrier theorem at any retained quota paid by the original graph. -/
-- `FourthRoom d` holds only for d ≤ 11, so this window covers the degrees 8 to 11.
@[ch_numeric_guard] def Fits (n r q : ℕ) : Prop :=
  7≤q ∧ ∃d∈Icc 8 r,d≤q+1 ∧ n+d≤7*d+r ∧ RetainedLayerCapacity.FourthRoom d ∧
    MixedBankScore.Capacity d ∧ MixedBankProfile.Room d ∧ EqualMixedShells.Room d

instance {n r q} : Decidable (Fits n r q) := by unfold Fits; infer_instance

theorem exclude {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) :
    ¬Fits p.n p.s (CHRuleCatalog.cutoff p) := by
  rintro ⟨hq,d,dm,fit,order,prev,cap,room,exactRoom⟩
  obtain ⟨hr,dr⟩ := mem_Icc.mp dm
  have bound : GuardedFamilyRules.OrderBound (CHRuleCatalog.cutoff p) d (7*d) :=
    ⟨by omega,fun _ _ f live deg=>carrier f live deg hq hr fit prev cap room exactRoom⟩
  exact GuardedFamilyRules.forbidden bad bound ⟨le_rfl,dr,order⟩

theorem literal {D n r} (hn : 0<n) (hr : 0<r) (simple : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r) (inside : Fits n r (CH.ceilDiv n r)) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  exact exclude (p:=⟨n,r,D⟩) ⟨hn,hr,simple,degree,missing⟩ inside

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] exclude
#print axioms exclude
#print axioms literal
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,flat,uv,routing]) (rule_sets := [CHGraphFamilies])] flat_impossible
attribute [aesop safe forward (immediate := [free,live,degree,hq,hr,fit,prev,cap,room,exactRoom]) (rule_sets := [CHGraphFamilies])] carrier
#print axioms carrier
#print axioms flat_impossible
#print axioms cover_bill
#print axioms depth_slots
#print axioms head_slots
end LeanCH.BR.SinkDepthCover
