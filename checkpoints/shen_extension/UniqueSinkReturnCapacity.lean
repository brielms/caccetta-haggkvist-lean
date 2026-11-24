import checkpoints.shen_extension.ProfileSinkReturns
import checkpoints.shen_extension.RecipientUnionAudit
import checkpoints.shen_extension.SinkTransit

namespace LeanCH.BR.UniqueSinkReturnCapacity
open Finset BRq2 BRq3 BR45 BRsGen ProfileSinkReturns

/-- Late recipients share a finite space. A single shortest path to the
unique sink reserves its final q−1 labels against *every* recipient. -/
theorem late_capacity {D X U q s} (hq : 2≤q)
    (acyclic : QFree D X X.card) (ux : U⊆X) (live : U.Nonempty)
    (unique : ∀t∈X,Sink D X t → t=s)
    (late : ∀v∈U,∀k,k+2≤q → ¬Walk D X v s k) :
    U.card+(q-1)≤X.card ∧ ∀v∈U,(outN D X v).card+(q-1)≤X.card := by
  classical
  have far v (vm : v∈U) (p : ShortestSinkPath D X v) : q-1≤p.len := by
    have ends := unique _ (p.mem _ le_rfl) p.sink
    by_contra! near
    apply late v vm p.len (by omega)
    simpa only [p.start,ends,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
  obtain ⟨x,xm⟩ := live
  obtain ⟨p⟩ := exists_shortest_sink_path acyclic le_rfl (ux xm)
  let I := Icc (p.len-(q-2)) p.len
  have d := far x xm p
  have cI : I.card=q-1 := by dsimp [I]; rw [Nat.card_Icc]; omega
  have sub : I.image p.vertex⊆X\U := by
    intro z zm
    obtain ⟨i,im,rfl⟩ := mem_image.mp zm
    obtain ⟨lo,hi⟩ := mem_Icc.mp im
    refine mem_sdiff.mpr ⟨p.mem i hi,fun inside=>late _ inside (p.len-i) (by omega) ?_⟩
    simpa only [unique _ (p.mem _ le_rfl) p.sink] using p.walk hi le_rfl
  have inj : Set.InjOn p.vertex ↑I := (p.injective acyclic le_rfl).mono (by
    intro i im
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp im).2))
  have count := card_le_card sub
  rw [card_image_of_injOn inj,cI,card_sdiff_of_subset ux] at count
  refine ⟨by have := card_le_card ux; omega,?_⟩
  intro v vm
  obtain ⟨p⟩ := exists_shortest_sink_path acyclic le_rfl (ux vm)
  have := far v vm p
  have := SinkTransit.internal_depth acyclic le_rfl p
  omega

/-- When every sink of the head bank returns, its whole carrier is
covered by omissions of the *actual* recipients. -/
theorem omission_capacity {D V A U q k} (free : QFree D V q) (hq : 2≤q)
    (av : A⊆V) (uv : U⊆V) (acyclic : QFree D A A.card)
    (returns : ∀b∈A,Sink D A b → ∃v∈U,D b v=true)
    (omits : ∀v∈U,(A\outN D V v).card≤k) (short : k<q-1) :
    A.card≤U.card*k := by
  classical
  have sub : A⊆U.biUnion (fun v=>A\outN D V v) := by
    intro a am
    obtain ⟨p⟩ := exists_shortest_sink_path acyclic le_rfl am
    obtain ⟨v,vm,edge⟩ := returns _ (p.mem _ le_rfl) p.sink
    exact mem_biUnion.mpr ⟨v,vm,RecipientUnionAudit.ancestor_omitted free hq av Subset.rfl acyclic
      (uv vm) p edge (lt_of_le_of_lt (omits v vm) short)⟩
  exact (card_le_card sub).trans ((card_biUnion_le).trans ((sum_le_sum omits).trans (by simp)))

/-- A shortage of eligible recipients excludes the unique-sink family.
The widths, quota, and number of spare labels are arbitrary. -/
theorem unique_impossible {D V X A Y q s} (free : QFree D V q) (hq : 2≤q)
    (xv : X⊆V) (heads : A=outN D V s) (ay : A⊆Y)
    (first : QFree D X X.card) (second : QFree D A A.card) (an : A.Nonempty)
    (returns : ∀y∈A,Sink D A y → ∃x∈X,D y x=true)
    (menu : ∀x∈X,outN D V x⊆X∪Y) (rank : ∀x∈X,A.card≤(outN D V x).card)
    (short : X.card-(q-1)+(Y.card-A.card)<q-1)
    (bill : (X.card-(q-1))*(X.card-(q-1)+(Y.card-A.card))<A.card)
    (unique : ∀t∈X,Sink D X t → t=s) : False := by
  classical
  let U := X∩A.biUnion (outN D V)
  have ux : U⊆X := inter_subset_left
  have av : A⊆V := heads ▸ outN_subset
  have turn a (am : a∈A) (sa : Sink D A a) : ∃v∈U,D a v=true := by
    obtain ⟨v,vm,arc⟩ := returns a am sa
    exact ⟨v,mem_inter.mpr ⟨vm,mem_biUnion.mpr ⟨a,am,mem_outN.mpr ⟨xv vm,arc⟩⟩⟩,arc⟩
  obtain ⟨a,am,sa⟩ := BRq3.exists_sink second an le_rfl
  obtain ⟨v,vm,_⟩ := turn a am sa
  have late v (vm : v∈U) k (room : k+2≤q) (walk : Walk D X v s k) : False := by
    obtain ⟨a,am,arc⟩ := mem_biUnion.mp (mem_inter.mp vm).2
    exact free v _ (by omega) (by omega)
      (((walk.mono xv).snoc (av am) (mem_outN.mp (heads ▸ am)).2).snoc (xv (ux vm)) (mem_outN.mp arc).2)
  obtain ⟨slots,per⟩ := late_capacity hq first ux ⟨v,vm⟩ unique late
  have omits v (vm : v∈U) : (A\outN D V v).card≤X.card-(q-1)+(Y.card-A.card) := by
    have sub : outN D V v⊆(A∩outN D V v)∪(outN D X v∪(Y\A)) := by
      intro z zm
      by_cases az : z∈A
      · exact mem_union_left _ (mem_inter.mpr ⟨az,zm⟩)
      · rcases mem_union.mp (menu v (ux vm) zm) with x|y
        · exact mem_union_right _ (mem_union_left _ (mem_outN.mpr ⟨x,(mem_outN.mp zm).2⟩))
        · exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨y,az⟩))
    have lim := (rank v (ux vm)).trans ((card_le_card sub).trans (card_union_le _ _))
    have sub2 := card_union_le (outN D X v) (Y\A)
    have diff := card_sdiff_add_card_inter A (outN D V v)
    rw [card_sdiff_of_subset ay] at sub2
    have := per v vm
    omega
  have cap := omission_capacity free hq av (ux.trans xv) second turn omits short
  exact bill.not_ge (cap.trans (Nat.mul_le_mul_right _ (by omega)))

/-- Every prescribed first-layer sink has a different sink on the same labelled row. -/
theorem other_sink {D V u s q r} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (uv : u∈V) (routing : Routing D V u)
    (sm : s∈outN D V u) (ss : Sink D (outN D V u) s)
    (short : r-(q-1)+((N2 D V u).card-r)<q-1)
    (bill : (r-(q-1))*(r-(q-1)+((N2 D V u).card-r))<r) :
    ∃t∈outN D V u,t≠s ∧ Sink D (outN D V u) t := by
  classical
  by_contra none
  have unique t (tm : t∈outN D V u) (ts : Sink D (outN D V u) t) : t=s := by
    by_contra ne
    exact none ⟨t,tm,ne,ts⟩
  have steady : ¬Deflects D V (outN D V u) s := by
    intro d
    obtain ⟨t,tm,ts,no,_⟩ := routing.send s sm ss d
    exact no ((unique t tm ts).symm ▸ d)
  obtain ⟨b,_,row,acyclic,_⟩ := routing.layers.at_sink s sm ss
  have sv := outN_subset sm
  have as := reg s sv
  refine unique_impossible free (by omega) outN_subset rfl (row ▸ erase_subset ..)
    routing.layers.acyclic (row ▸ acyclic) (card_pos.mp (by omega)) ?_ ?_ ?_ ?_ ?_ unique
  · intro y ym sy
    by_contra h
    exact steady ⟨y,ym,sy,fun v vm e=>h ⟨v,vm,e⟩⟩
  · intro x xm z zm
    exact headX (free.mono_bound hq) uv xm (outN_subset zm) (mem_outN.mp zm).2
  · intro v vm
    rw [as,reg v (outN_subset vm)]
  · simpa only [reg u uv,as] using short
  · simpa only [reg u uv,as] using bill

def TwoSinks (D : CH.Digraph) (X : Finset ℕ) : Prop :=
  ∃s∈X,∃t∈X,t≠s ∧ Sink D X s ∧ Sink D X t

theorem two_sinks {D V q r u} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (routes : Routing D V u)
    (short : r-(q-1)+((N2 D V u).card-r)<q-1)
    (bill : (r-(q-1))*(r-(q-1)+((N2 D V u).card-r))<r) :
    TwoSinks D (outN D V u) := by
  obtain ⟨s,sm,ss⟩ := BRq3.exists_sink routes.layers.acyclic (card_pos.mp (by rw [reg u uv]; omega)) le_rfl
  obtain ⟨t,tm,d,ts⟩ := other_sink free hq reg uv routes sm ss short bill
  exact ⟨s,sm,t,tm,d,ss,ts⟩

structure OnFamily (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀{q},q≤CHRuleCatalog.cutoff p → 7≤q → 7≤p.s → p.s≤q+1 →
    RetainedLayerCapacity.FourthRoom p.s → MixedBankScore.Capacity p.s → MixedBankProfile.Room p.s → EqualMixedShells.Room p.s →
    p.n≤7*p.s → ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀u∈range p.n,TwoSinks F (outN F (range p.n) u)

theorem native {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p)
    (profile : EqualMixedShells.OnFamily p) (routes : ProfileSinkReturns.OnFamily p) : OnFamily p := by
  constructor
  intro q cut hq hr fit prev cap more room size F sub reg u uv
  have free := qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)
  have flat := profile.on_graph cut hq hr fit prev cap more room size F sub reg
  have routing := routes.on_graph cut hq hr fit prev cap more room size F sub reg u uv
  have width := (layers free (by omega) reg flat uv).1
  have small : p.s-(q-1)≤2 := by omega
  have slack : p.s-(q-1)+((N2 F (range p.n) u).card-p.s)≤3 := by omega
  have := Nat.mul_le_mul small slack
  exact two_sinks free (by omega) reg uv routing (by omega) (by omega)

attribute [aesop safe forward (immediate := [bad,profile,routes]) (rule_sets := [CHGraphFamilies])] native
attribute [aesop safe forward (immediate := [free,hq,reg,uv,routes,short,bill]) (rule_sets := [CHGraphFamilies])] two_sinks
#print axioms native
#print axioms two_sinks
#print axioms unique_impossible
end LeanCH.BR.UniqueSinkReturnCapacity
