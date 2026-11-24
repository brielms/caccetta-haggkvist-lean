import checkpoints.shen_extension.FlatCycleFamilyCompletion

namespace LeanCH.BR.Closure.FlatPairCover
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FirstPacketBarrier MarkedCyclePeeling
open FlatOverlapDescent

/-- If two shortest cycles are disjoint and every overlapping pair differs
by at most one label, overlap is transitive. Its classes have no arcs
between them, contradicting strictness on a least support. -/
private theorem no_disjoint {D V q x} {G : Family} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (cycles : ∀M∈G,Cycle D V q M)
    (wit : ∀u∈V,∀v∈V,D u v=true → ∃M∈G,u∈M ∧ v∈M)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q D V x i)
    (near : ∀A∈G,∀B∈G,(A∩B).Nonempty → (A\B).card≤1) {A N} (ag : A∈G) (ng : N∈G) : (A∩N).Nonempty := by
  classical
  by_contra absent
  have trans {L M K} (lf : L∈G) (mf : M∈G) (kf : K∈G) (lm : (L∩M).Nonempty) (mk : (M∩K).Nonempty) :
      (L∩K).Nonempty := by
    by_contra no
    have sub : M⊆(M\L)∪(M\K) := by
      intro i ii
      by_cases il : i∈L
      · exact mem_union_right _ (mem_sdiff.mpr ⟨ii,fun ik => no ⟨i,mem_inter.mpr ⟨il,ik⟩⟩⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨ii,il⟩)
    have cap := (card_le_card sub).trans (card_union_le _ _)
    have a := near M mf L lf (inter_comm L M ▸ lm)
    have b := near M mf K kf mk
    rw [(cycles M mf).size] at cap
    omega
  let S := (G.filter (fun M => (A∩M).Nonempty)).biUnion id
  have aLive : A.Nonempty := card_pos.mp (by rw [(cycles A ag).size]; omega)
  have nLive : N.Nonempty := card_pos.mp (by rw [(cycles N ng).size]; omega)
  have asub : A⊆S := fun i ia => mem_biUnion.mpr ⟨A,mem_filter.mpr ⟨ag,by simpa using aLive⟩,ia⟩
  have sv : S⊆V := by
    intro i ih
    obtain ⟨M,mf,im⟩ := mem_biUnion.mp ih
    exact (cycles _ (mem_filter.mp mf).1).sub im
  have prop : S≠V := by
    intro eq
    obtain ⟨i,ni⟩ := nLive
    have si : i∈S := eq.symm ▸ (cycles N ng).sub ni
    obtain ⟨M,mf,im⟩ := mem_biUnion.mp si
    exact absent (trans ag (mem_filter.mp mf).1 ng (mem_filter.mp mf).2 ⟨i,mem_inter.mpr ⟨im,ni⟩⟩)
  obtain ⟨u,us,low⟩ := small.induced free S sv prop x (fun i hi => xp i (sv hi)) (aLive.mono asub)
  have same : outN D V u=outN D S u := by
    ext v
    simp only [mem_outN]
    constructor
    · rintro ⟨vv,arc⟩
      obtain ⟨M,mf,um,vm⟩ := wit u (sv us) v vv arc
      obtain ⟨K,kf,uk⟩ := mem_biUnion.mp us
      exact ⟨mem_biUnion.mpr ⟨M,mem_filter.mpr ⟨mf,trans ag (mem_filter.mp kf).1 mf
        (mem_filter.mp kf).2 ⟨u,mem_inter.mpr ⟨uk,um⟩⟩⟩,vm⟩,arc⟩
    · exact fun a => ⟨sv a.1,a.2⟩
  have hi := strict u (sv us)
  have ml : mass S x≤mass V x := sum_le_sum_of_subset_of_nonneg sv (fun i hi _ => xp i hi)
  rw [WeightedSD.row,outW_eq_mass,same] at hi
  rw [WeightedSD.row,outW_eq_mass] at low
  linarith

/-- Either an actual normalized pair child has unavoidable slack, or
every two distinct shortest cycles intersect and cover the entire source. -/
theorem alternatives {D V q x} {G : Family} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (complete : ∀M,M∈G ↔ Cycle D V q M)
    (wit : ∀u∈V,∀v∈V,D u v=true → ∃M∈G,u∈M ∧ v∈M)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q D V x i) :
    (∃A∈G,∃B∈G,A≠B ∧ ForcedSlack q D (V\(A\B))) ∨
    ∀A∈G,∀B∈G,A≠B → (A∩B).Nonempty ∧ V=A∪B := by
  classical
  by_cases stopped : ∃A∈G,∃B∈G,A≠B ∧ ForcedSlack q D (V\(A\B))
  · exact Or.inl stopped
  right
  have cycles (M) (mg : M∈G) := (complete M).mp mg
  have retained {A B} (ag : A∈G) (bg : B∈G) (ne : A≠B) : ((V\(A\B)).card : ZMod q)=1 := by
    by_contra no
    exact stopped ⟨A,ag,B,bg,ne,fun p hp => by
      by_contra! high
      exact no ((CanonicalCycleLaw.unit_columns hq (fun z hz => le_antisymm (hp.columns z hz) (high z hz))).1 hp.normalized)⟩
  have size {A B} (af : A∈G) (bf : B∈G) (ne : A≠B) : (1:ZMod q)+((A\B).card : ZMod q)=V.card := by
    have total := card_sdiff_add_card_eq_card (sdiff_subset.trans (cycles A af).sub : A\B⊆V)
    rw [←retained af bf ne,←Nat.cast_add,total]
  have meet {A B} (af : A∈G) (bf : B∈G) : (A∩B).Nonempty := by
    by_contra no
    have live : A.Nonempty := card_pos.mp (by rw [(cycles A af).size]; omega)
    have neq : A≠B := by rintro rfl; exact no (by simpa using live)
    have all : A\B=A := by
      apply Subset.antisymm sdiff_subset
      exact fun i ia => mem_sdiff.mpr ⟨ia,fun ib => no ⟨i,mem_inter.mpr ⟨ia,ib⟩⟩⟩
    have base := size af bf neq
    rw [all,(cycles A af).size] at base
    apply no
    apply no_disjoint hq free small cycles wit xp strict _ af bf
    intro L lf M mf lm
    by_cases eq : L=M
    · simp [eq]
    have cmp := add_left_cancel ((size lf mf eq).trans base.symm)
    have rem := (ZMod.natCast_eq_natCast_iff _ _ _).mp cmp
    change (L\M).card%q=(q+1)%q at rem
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1<q)] at rem
    have sum := card_sdiff_add_card_inter L M
    rw [(cycles L lf).size] at sum
    have positive := card_pos.mpr lm
    by_cases less : (L\M).card<q
    · rw [Nat.mod_eq_of_lt less] at rem; omega
    · have same : (L\M).card=q := by omega
      rw [same,Nat.mod_self] at rem
      omega
  intro A ag B bg ne
  have both := meet ag bg
  refine ⟨both,?_⟩
  rcases transition hq free small (cycles A ag) (cycles B bg) ne with cover|slack|step
  · exact cover
  · exact (stopped ⟨A,ag,B,bg,ne,slack⟩).elim
  · obtain ⟨h,hh⟩ := both
    obtain ⟨M,cy,_,absent,_,_,outcome⟩ := step h hh
    have mg := (complete M).mpr cy
    have am : A≠M := fun eq => absent (eq ▸ (mem_inter.mp hh).1)
    rcases outcome with slack|⟨empty,_,_⟩
    · exact (stopped ⟨A,ag,M,mg,am,slack⟩).elim
    · exact ((meet ag mg).ne_empty empty).elim

#print axioms alternatives
end LeanCH.BR.Closure.FlatPairCover
