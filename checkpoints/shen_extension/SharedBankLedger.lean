import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace LeanCH.BR.SharedBankLedger
open Finset

/-- Disjoint representatives with a physical witness wherever a row was
left out. A representative is selected from the actual source labels. -/
theorem representatives {α β : Type*} [DecidableEq α] [DecidableEq β]
    (bank : α→Finset β) (S : Finset α) :
    ∃I⊆S,(I : Set α).PairwiseDisjoint bank ∧
      ∀u∈S\I,∃v∈I,∃w∈bank u,w∈bank v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,Subset.rfl,by simp,by simp⟩
  | @insert u S fresh ih =>
    obtain ⟨I,sub,apart,caught⟩ := ih
    by_cases overlap : ∃v∈I,∃w∈bank u,w∈bank v
    · refine ⟨I,sub.trans (subset_insert _ _),apart,?_⟩
      intro x xm
      obtain ⟨xs,off⟩ := mem_sdiff.mp xm
      rcases mem_insert.mp xs with rfl|old
      · exact overlap
      · exact caught x (mem_sdiff.mpr ⟨old,off⟩)
    · refine ⟨insert u I,insert_subset_insert u sub,?_,?_⟩
      · intro x xm y ym ne
        rcases mem_insert.mp xm with rfl|xi <;> rcases mem_insert.mp ym with eq|yi
        · exact (ne eq.symm).elim
        · exact disjoint_left.mpr (fun w wx wy=>overlap ⟨y,yi,w,wx,wy⟩)
        · subst y
          exact disjoint_left.mpr (fun w wx wy=>overlap ⟨x,xi,w,wy,wx⟩)
        · exact apart xi yi ne
      · intro x xm
        obtain ⟨xs,off⟩ := mem_sdiff.mp xm
        have old := ((mem_insert.mp xs).resolve_left (fun eq=>off (mem_insert.mpr (.inl eq))))
        obtain ⟨v,vi,w,wx,wv⟩ := caught x (mem_sdiff.mpr ⟨old,fun xi=>off (mem_insert.mpr (.inr xi))⟩)
        exact ⟨v,mem_insert.mpr (.inr vi),w,wx,wv⟩

/-- Each omitted source accounts for two different ordered source pairs.
Each representative accounts for at least d distinct target labels.
Both bills can be used simultaneously at any degree and cutoff. -/
theorem witness_budget {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {T : Finset β} (B : α→Finset β) {d : ℕ}
    (paid : ∀u∈S,d≤(B u).card) (inT : ∀u∈S,B u⊆T)
    {M : Finset (α×α)}
    (miss : ∀u∈S,∀v∈S,u≠v → ∀w∈B u,w∈B v → (u,v)∈M) :
    ∃g,g≤S.card ∧ (S.Nonempty → 0<g) ∧ g*d≤T.card ∧ 2*(S.card-g)≤M.card := by
  classical
  obtain ⟨I,sub,apart,caught⟩ := representatives B S
  have ne (sn : S.Nonempty) : I.Nonempty := by
    obtain ⟨u,us⟩ := sn
    by_cases ui : u∈I
    · exact ⟨u,ui⟩
    · obtain ⟨v,vi,_⟩ := caught u (mem_sdiff.mpr ⟨us,ui⟩)
      exact ⟨v,vi⟩
  have targets : I.biUnion B ⊆ T := by
    intro w wm
    obtain ⟨u,ui,hit⟩ := mem_biUnion.mp wm
    exact inT u (sub ui) hit
  have cap := card_le_card targets
  rw [card_biUnion apart] at cap
  have lo := sum_le_sum (fun u (ui : u∈I)=>paid u (sub ui))
  rw [sum_const_nat (fun _ _=>rfl)] at lo
  refine ⟨I.card,card_le_card sub,fun sn=>card_pos.mpr (ne sn),lo.trans cap,?_⟩
  by_cases sn : S.Nonempty
  · let f : α→α := fun u=>if h : u∈S\I then (caught u h).choose else sn.choose
    have hf (u) (um : u∈S\I) : f u∈I ∧ ∃w∈B u,w∈B (f u) := by
      simpa only [f,dif_pos um] using (caught u um).choose_spec
    let left := (S\I).image (fun u=>(u,f u))
    let right := (S\I).image (fun u=>(f u,u))
    have dis : Disjoint left right := by
      apply disjoint_left.mpr
      intro e em rm
      obtain ⟨u,um,rfl⟩ := mem_image.mp em
      obtain ⟨v,vm,eq⟩ := mem_image.mp rm
      have vu : f v=u := congrArg Prod.fst eq
      exact (mem_sdiff.mp um).2 (vu ▸ (hf v vm).1)
    have push (u) (um : u∈S\I) : (u,f u)∈M ∧ (f u,u)∈M := by
      obtain ⟨us,off⟩ := mem_sdiff.mp um
      obtain ⟨fi,w,wu,wf⟩ := hf u um
      have neq : u≠f u := fun eq=>off (eq.symm ▸ fi)
      exact ⟨miss u us _ (sub fi) neq w wu wf,miss _ (sub fi) u us (Ne.symm neq) w wf wu⟩
    have both : left∪right⊆M := by
      intro e em
      rcases mem_union.mp em with l|r
      · obtain ⟨u,um,rfl⟩ := mem_image.mp l
        exact (push u um).1
      · obtain ⟨u,um,rfl⟩ := mem_image.mp r
        exact (push u um).2
    have bill := card_le_card both
    rw [card_union_of_disjoint dis] at bill
    have lsize : left.card=(S\I).card := card_image_of_injective _ (fun _ _ eq=>congrArg Prod.fst eq)
    have rsize : right.card=(S\I).card := card_image_of_injective _ (fun _ _ eq=>congrArg Prod.snd eq)
    rw [lsize,rsize,card_sdiff_of_subset sub] at bill
    omega
  · rw [not_nonempty_iff_eq_empty.mp sn]
    simp

#print axioms witness_budget
end LeanCH.BR.SharedBankLedger
