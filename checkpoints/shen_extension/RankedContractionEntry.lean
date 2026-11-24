import checkpoints.shen_extension.RankedNativeContraction
import checkpoints.shen_extension.RankedMenuThreshold
import LeanCH.BR.CH.Side.ScFinsetEnumeration

namespace LeanCH.BR.RankedContractionEntry
open Finset BRq2 BRq3 BR45 WeightedSD Closure CHRuleCatalog

/-- A paid native deletion, with the actual vertices reserved to head the
    replacement. Its hypotheses use only the original graph and degree. -/
structure Proposal (p : Input) (W H : Finset ℕ) (z : ℕ) : Prop where
  inside : W⊆range p.n
  size : 2≤W.card
  rep : z∈W
  heads : H⊆range p.n\W
  quota : p.s≤H.card
  one : ∀i∈range p.n\W,p.s≤(outN p.D (range p.n\W) i).card+1
  safe : ∀h∈H,∀i∈RankedNativeContraction.shortRows p.s p.D (range p.n\W),
    i∉ball p.D (range p.n\W) h (cutoff p-2)

structure Contracted (p : Input) (W H : Finset ℕ) (z : ℕ) : Prop where
  witness :
    let U := range p.n\W
    let C := insert z U
    let E := coreTwoSidedExtension p.D U (RankedNativeContraction.shortRows p.s p.D U) H z
    ∃c : Input,∃e : ℕ→ℕ,Child p c ∧ Bad c ∧ c.s=p.s ∧ c.n=C.card ∧ c.n<p.n ∧ cutoff c≤cutoff p ∧
      (∀i<c.n,e i∈C) ∧ (∀v∈C,∃i<c.n,e i=v) ∧ (∀i<c.n,∀j<c.n,e i=e j → i=j) ∧
      (∀i<c.n,∀j<c.n,c.D i j=E (e i) (e j)) ∧ (∀i∈U,∀j∈U,E i j=p.D i j)

theorem contract_bad {p : Input} (bad : Bad p) (hq : 2≤cutoff p) {W H z} (pick : Proposal p W H z) :
    Contracted p W H z := by
  classical
  constructor
  intro U C E
  obtain ⟨smaller,free,degree,old⟩ := RankedNativeContraction.contract (qfree_of_noShort bad.loopless bad.missing)
    pick.inside pick.size pick.rep pick.heads pick.quota pick.one pick.safe
  have cv : C⊆range p.n := insert_subset (pick.inside pick.rep) sdiff_subset
  obtain ⟨e,_,inject,into,onto⟩ := CH.Side.sc_finset_enumeration cv
  let c : Input := ⟨C.card,p.s,fun i j=>E (e i) (e j)⟩
  have cn : c.n<p.n := by simpa only [card_range] using smaller
  have qle : cutoff c ≤ cutoff p := by
    change (C.card+p.s-1)/p.s ≤ (p.n+p.s-1)/p.s
    apply Nat.div_le_div_right
    change C.card<p.n at cn
    omega
  have walk {i j k} (w : Walk c.D (range c.n) i j k) : Walk E C (e i) (e j) k := by
    induction w with
    | refl => exact .refl _
    | step mb hit rest ih => exact .step (into _ (mem_range.mp mb)) hit ih
  have safe : QFree c.D (range c.n) (cutoff c) := fun i k hp limit w=>
    free (e i) k hp (limit.trans qle) (walk w)
  have missing := ShenReachTransition.no_cycle_of_free safe
  have positive : 0<c.n := card_pos.mpr (insert_nonempty _ _)
  have ll : CH.Loopless c.D c.n := by
    intro i iv
    change E (e i) (e i)=false
    exact Bool.eq_false_iff.mpr (loopfree (D:=E) (W:=C) (q:=cutoff p) free (by omega) (into i iv))
  have minDegree : CH.MinOutdegreeAtLeast c.D c.n c.s := by
    intro i iv
    let B := outN c.D (range c.n) i
    have eq : B.image e=outN E C (e i) := by
      ext y
      constructor
      · rintro hy
        obtain ⟨j,jb,rfl⟩ := mem_image.mp hy
        exact mem_outN.mpr ⟨into j (mem_range.mp (outN_subset jb)),(mem_outN.mp jb).2⟩
      · intro hy
        obtain ⟨j,jb,eq⟩ := onto y (outN_subset hy)
        exact mem_image.mpr ⟨j,mem_outN.mpr ⟨mem_range.mpr jb,show E (e i) (e j)=true by
          rw [eq]; exact (mem_outN.mp hy).2⟩,eq⟩
    have count : (outN E C (e i)).card≤B.card := by rw [←eq]; exact card_image_le
    have quota : c.s≤B.card := (degree (e i) (into i iv)).trans count
    obtain ⟨T,ts,card⟩ := exists_subset_card_eq quota
    refine ⟨T.toList,by simpa using card,T.nodup_toList,fun j jt=>?_⟩
    obtain ⟨jv,edge⟩ := mem_outN.mp (ts (mem_toList.mp jt))
    exact ⟨mem_range.mp jv,edge⟩
  have child : Child p c := ⟨positive,bad.degree_pos,ll,minDegree,fun hit=>(missing hit).elim⟩
  exact ⟨c,e,child,bad_child bad child,rfl,rfl,cn,qle,into,onto,fun i hi j hj=>inject i j hi hj,fun _ _ _ _=>rfl,old⟩

structure RootContractions (p : Input) : Prop where
  apply_to : ∀W H z,Proposal p W H z → Contracted p W H z

@[aesop safe forward (immediate := [bad,sub,two,rep,rich,one]) (rule_sets := [CHGraphFamilies])]
theorem bank_proposal {p : Input} (bad : Bad p) {W : Finset ℕ} {z : ℕ}
    (sub : W⊆range p.n) (two : 2≤W.card) (rep : z∈W)
    (rich : p.s≤(FlatPeelReach.interior p.D (range p.n) (range p.n\W) (cutoff p-1)).card)
    (one : ∀i∈range p.n\W,p.s≤(outN p.D (range p.n\W) i).card+1) :
    Proposal p W (FlatPeelReach.interior p.D (range p.n) (range p.n\W) (cutoff p-1)) z := by
  have hq := (remaining_from_run p bad).1
  exact ⟨sub,two,rep,fun h hh=>(mem_filter.mp hh).2 (self_mem_ball (mem_filter.mp hh).1),rich,one,
    RankedNativeContraction.interior_safe (by omega) sub (fun _ iv=>Compose.FloorSix.out_card bad.degree (mem_range.mp iv))⟩

/-- Supply a repair directly from the two physical labels. A surviving row
    can lose two heads only by pointing to both of them. -/
@[aesop safe forward (immediate := [bad,hq,av,dv,ad,rich,spare]) (rule_sets := [CHGraphFamilies])]
theorem pair_proposal {p : Input} (bad : Bad p) (hq : 2≤cutoff p) {a d : ℕ}
    (av : a∈range p.n) (dv : d∈range p.n) (ad : a≠d)
    (rich : p.s≤(FlatPeelReach.interior p.D (range p.n) (range p.n\{a,d}) (cutoff p-1)).card)
    (spare : ∀i∈range p.n\{a,d},p.D i a=true → p.D i d=true → p.s<(outN p.D (range p.n) i).card) :
    Proposal p {a,d} (FlatPeelReach.interior p.D (range p.n) (range p.n\{a,d}) (cutoff p-1)) a := by
  let V := range p.n
  let U := V\{a,d}
  have ws : {a,d}⊆V := insert_subset av (singleton_subset_iff.mpr dv)
  have deg (i) (iv : i∈V) := Compose.FloorSix.out_card bad.degree (mem_range.mp iv)
  refine ⟨ws,by rw [card_pair ad],mem_insert_self ..,
    fun h hh=>(mem_filter.mp hh).2 (self_mem_ball (mem_filter.mp hh).1),rich,?_,
    RankedNativeContraction.interior_safe hq ws deg⟩
  intro i iu
  change i∈U at iu
  have quota : p.s≤(outN p.D V i).card := deg i (mem_sdiff.mp iu).1
  have cover : outN p.D V i ⊆ outN p.D U i ∪ outN p.D {a,d} i := by
    intro j jj
    obtain ⟨jv,ij⟩ := mem_outN.mp jj
    by_cases cut : j∈({a,d}:Finset ℕ)
    · exact mem_union_right _ (mem_outN.mpr ⟨cut,ij⟩)
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,cut⟩,ij⟩)
  have cap := (card_le_card cover).trans (card_union_le _ _)
  change p.s≤(outN p.D U i).card+1
  by_cases both : outN p.D {a,d} i={a,d}
  · have ia := (mem_outN.mp (show a∈outN p.D {a,d} i by rw [both]; exact mem_insert_self ..)).2
    have id' := (mem_outN.mp (show d∈outN p.D {a,d} i by rw [both]; exact mem_insert_of_mem (mem_singleton_self d))).2
    have more : p.s<(outN p.D V i).card := spare i iu ia id'
    rw [both,card_pair ad] at cap
    omega
  · have lt := card_lt_card (ssubset_of_subset_of_ne outN_subset both)
    rw [card_pair ad] at lt
    omega

@[aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
theorem root_rule {p : Input} (bad : Bad p) : RootContractions p :=
  ⟨fun _ _ _ pick=>contract_bad bad ((show 2≤3 by decide).trans (remaining_from_run p bad).1) pick⟩

@[aesop safe forward (immediate := [root,pick]) (rule_sets := [CHGraphFamilies])]
theorem apply_proposal {p W H z} (root : RootContractions p) (pick : Proposal p W H z) :
    Contracted p W H z := root.apply_to W H z pick

/-- Keep one actual child fixed across all subsequent catalogue calls. The
    witness stores the enumeration between the child and the original labels. -/
noncomputable def next {p W H z} (made : Contracted p W H z) : Input :=
  Classical.choose made.witness

@[aesop safe forward (immediate := [made]) (rule_sets := [CHGraphFamilies])]
theorem next_edge {p W H z} (made : Contracted p W H z) : Child p (next made) :=
  (Classical.choose_spec (Classical.choose_spec made.witness)).1

@[aesop safe forward (immediate := [made]) (rule_sets := [CHGraphFamilies])]
theorem next_bad {p W H z} (made : Contracted p W H z) : Bad (next made) :=
  (Classical.choose_spec (Classical.choose_spec made.witness)).2.1

theorem next_size {p W H z} (made : Contracted p W H z) :
    (next made).s=p.s ∧ (next made).n=(insert z (range p.n\W)).card ∧
    (next made).n<p.n ∧ cutoff (next made)≤cutoff p := by
  have facts := Classical.choose_spec (Classical.choose_spec made.witness)
  exact ⟨facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2.1⟩

#print axioms contract_bad
#print axioms root_rule
#print axioms pair_proposal
#print axioms next_size
end LeanCH.BR.RankedContractionEntry
