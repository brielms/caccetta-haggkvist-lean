import checkpoints.shen_extension.QuotaBankPromotion

namespace LeanCH.BR.ProjectedQuotaTransfer
open Finset BRq2 BRq3 BR45 BRsGen CHRuleCatalog BypassRepair

/-- After deleting a specified bank, the surviving debtor has a labelled
set of lost heads. The applicable threshold uses its actual degree. -/
theorem mixed_bank_witness {D V B q d} (free : QFree D V q) (nohost : NoHost q d)
    (sub : B⊆V) (live : B.card<V.card) (size : V.card-B.card≤q*d) :
    ∃v∈V\B, (outN D (V\B) v).card<d ∧ (outN D V v).card<(outN D B v).card+d := by
  classical
  have left := card_sdiff_of_subset sub
  obtain ⟨v,vm,short⟩ : ∃v∈V\B,(outN D (V\B) v).card<d := by
    by_contra! paid
    exact nohost D _ (card_pos.mp (by omega)) (by omega) (free.mono_set sdiff_subset) paid
  have split := card_outN_union (D:=D) (show Disjoint B (V\B) from disjoint_sdiff) v
  rw [union_sdiff_of_subset sub] at split
  exact ⟨v,vm,short,by omega⟩

/-- Count separately the banks using exactly j heads of a row. The debtor
itself cannot be in the bank. A bank with more than the required number of
heads appears in just one summand for this particular row. -/
def bankChoices (n r k threshold : ℕ) :=
  ∑j∈Icc threshold k,r.choose j*(n-1-r).choose (k-j)

theorem mixed_bank_count {D V q d r k} (free : QFree D V q) (hq : 1≤q)
    (reg : OutEq r D V) (nohost : NoHost q d)
    (rank : d≤r) (live : k<V.card) (afford : V.card-k≤q*d) :
    V.card.choose k ≤ V.card*bankChoices V.card r k (r-d+1) := by
  classical
  let A v := outN D V v
  let O v := (V.erase v)\A v
  let parts v j := ((A v).powersetCard j ×ˢ (O v).powersetCard (k-j)).image
    (fun pair : Finset ℕ × Finset ℕ=>pair.1∪pair.2)
  let banks v := (Icc (r-d+1) k).biUnion (parts v)
  have charge : V.powersetCard k⊆V.biUnion banks := by
    intro B bm
    obtain ⟨sub,card⟩ := mem_powersetCard.mp bm
    obtain ⟨v,kept,_,loss⟩ := mixed_bank_witness free nohost sub (by omega) (by omega)
    obtain ⟨vm,vB⟩ := mem_sdiff.mp kept
    have hinside : outN D B v=B∩A v := by
      ext x
      simp only [mem_outN,mem_inter,A]
      exact ⟨fun h=>⟨h.1,sub h.1,h.2⟩,fun h=>⟨h.1,h.2.2⟩⟩
    rw [hinside,reg v vm] at loss
    let H := B∩A v
    have subH : H⊆B := inter_subset_left
    have lim := card_le_card subH
    have eligible : H.card∈Icc (r-d+1) k := mem_Icc.mpr ⟨by dsimp [H]; omega,by omega⟩
    refine mem_biUnion.mpr ⟨v,vm,mem_biUnion.mpr ⟨H.card,eligible,mem_image.mpr
      ⟨(H,B\H),mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right,rfl⟩,mem_powersetCard.mpr ⟨?_,?_⟩⟩,?_⟩⟩⟩
    · intro x xm
      obtain ⟨xb,off⟩ := mem_sdiff.mp xm
      exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun eq=>vB (eq ▸ xb),sub xb⟩,fun a=>off (mem_inter.mpr ⟨xb,a⟩)⟩
    · rw [card_sdiff_of_subset subH,card]
    · exact union_sdiff_of_subset subH
  have per v (vm : v∈V) : (banks v).card ≤ bankChoices V.card r k (r-d+1) := by
    have av : A v⊆V.erase v := by
      intro x xm
      exact mem_erase.mpr ⟨fun eq=>loopfree free hq vm (eq ▸ (mem_outN.mp xm).2),outN_subset xm⟩
    have oc : (O v).card = V.card-1-r := by
      change ((V.erase v)\A v).card=_
      rw [card_sdiff_of_subset av,card_erase_of_mem vm,show (A v).card=r from reg v vm]
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro j _
    apply card_image_le.trans
    rw [card_product,card_powersetCard,card_powersetCard,oc,show (A v).card=r from reg v vm]
  have sum := (card_le_card charge).trans (card_biUnion_le.trans (sum_le_sum per))
  simpa [card_powersetCard] using sum

attribute [aesop safe forward (immediate := [free,nohost,sub,live,size]) (rule_sets := [CHGraphFamilies])] mixed_bank_witness
attribute [aesop safe forward (immediate := [free,hq,reg,nohost,rank,live,afford]) (rule_sets := [CHGraphFamilies])] mixed_bank_count
@[ch_numeric_guard] def MixedBankWindow (n r q floor : ℕ) : Prop :=
  ∃d∈Icc 1 (min r (floor-1)), let k := n-q*d
    k<n ∧ n*bankChoices n r k (r-d+1)<n.choose k
instance {n r q floor} : Decidable (MixedBankWindow n r q floor) := by unfold MixedBankWindow; infer_instance

theorem mixed_after_prefix {p : Input} {floor} (bad : Bad p) (positive : 0<floor)
    (lower : ∀t,t<floor → NoHost (cutoff p) t) : ¬MixedBankWindow p.n p.s (cutoff p) floor := by
  rintro ⟨d,dm,live,excess⟩
  have le := (mem_Icc.mp dm).2
  have rank := le.trans (min_le_left ..)
  have low := le.trans (min_le_right ..)
  have hq := (remaining_from_run p bad).1
  obtain ⟨F,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  let k := p.n-cutoff p*d
  have bound := mixed_bank_count (k:=k) free (by omega) reg (lower d (by omega)) rank
    (by rw [card_range]; exact live) (by rw [card_range]; dsimp [k]; omega)
  rw [card_range] at bound
  exact (Nat.not_lt_of_ge bound) excess

theorem promoted_mixed {p : Input} (bad : Bad p) : ¬MixedBankWindow p.n p.s (cutoff p) projectionFloor :=
  mixed_after_prefix bad (Nat.zero_lt_succ _) (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,positive,lower]) (rule_sets := [CHGraphFamilies])] mixed_after_prefix
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] promoted_mixed
attribute [aesop safe forward (immediate := [reg,live,roots,inside,bound]) (rule_sets := [CHGraphFamilies])]
  LowShellCycleSelection.exhaust_successor
attribute [aesop safe forward (immediate := [free,hq,uv,vv,ne,liveC,liveE,first,second,third,first',second',ce,ew,dC,fE,wb,df,degreeD,degreeF]) (rule_sets := [CHGraphFamilies])]
  LowShellCycleSelection.full_bank_separates
attribute [aesop safe forward (immediate := [free,hq,reg,hr,uv,vv,ne,live,width,common,common',ce,eWidth,roots,bE,fE,second,second',small,small']) (rule_sets := [CHGraphFamilies])]
  LowShellCycleSelection.priced_origins_separate
#print axioms promoted_mixed
#print axioms mixed_bank_witness
#print axioms mixed_bank_count
end LeanCH.BR.ProjectedQuotaTransfer
