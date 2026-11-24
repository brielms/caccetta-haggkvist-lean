import checkpoints.shen_extension.DotClonePairCompletion_20261118
import checkpoints.shen_extension.dot_tensor_research.PhysicalBankRouting

namespace LeanCH.BR.PrivateHeadClone
open Finset BRq2 BRq3 BR45 DotClonePairCompletion

/-- Duplicate a specified head and give the duplicate a single parent.
Folding the child onto the original graph preserves the length of each walk. -/
theorem clone {D V q d a b} (free : QFree D V q) (av : a∈V) (bv : b∈V)
    (ab : D a b=true) (paid : d≤(outN D V b).card)
    (gap : d≤(outN D V a).card+1) (other : ∀v∈V,v≠a → d≤(outN D V v).card) :
    ∃(F : CH.Digraph) (t : ℕ), t∉V ∧ QFree F (insert t V) q ∧
      (∀v∈insert t V,d≤(outN F (insert t V) v).card) ∧ inN F (insert t V) t={a} := by
  classical
  obtain ⟨t,off⟩ := Infinite.exists_notMem_finset V
  let p := fun v=>if v=t then b else v
  let F : CH.Digraph := fun v w=>if w=t then decide (v=a) else D (p v) w
  have nt {v} (vm : v∈V) : v≠t := fun eq=>off (eq ▸ vm)
  have old {v} (vm : v∈V) : p v=v := if_neg (nt vm)
  have fold (x y) (edge : F x y=true) : D (p x) (p y)=true := by
    by_cases eq : y=t
    · subst y
      have xa : x=a := by simpa [F] using edge
      subst x
      simpa [p,nt av] using ab
    · simpa [F,p,eq] using edge
  have live v (vm : v∈insert t V) : p v∈V := by
    rcases mem_insert.mp vm with eq|vv
    · subst v; simpa [p] using bv
    · rwa [old vv]
  have stay (v) : outN D V (p v)⊆outN F (insert t V) v := by
    intro y ym
    obtain ⟨yv,xy⟩ := mem_outN.mp ym
    exact mem_outN.mpr ⟨mem_insert_of_mem yv,by simpa [F,nt yv] using xy⟩
  refine ⟨F,t,off,qfree_project free live fold,?_,?_⟩
  · intro v vm
    rcases mem_insert.mp vm with eq|vv
    · subst v; exact paid.trans (by simpa [p] using card_le_card (stay t))
    have saved := stay v
    rw [old vv] at saved
    by_cases va : v=a
    · subst v
      have extra : t∈outN F (insert t V) a := mem_outN.mpr ⟨mem_insert_self _ _,by simp [F]⟩
      have count := card_le_card (insert_subset extra saved)
      rw [card_insert_of_notMem (fun h=>off (outN_subset h))] at count
      exact gap.trans count
    · exact (other v vv va).trans (card_le_card saved)
  · ext v
    simp only [mem_inN,mem_insert,mem_singleton,F,ite_true,decide_eq_true_eq]
    exact ⟨fun h=>h.2,fun eq=>⟨Or.inr (eq ▸ av),eq⟩⟩

theorem degree_two_obstruction {D V q a b} (free : QFree D V q) (hq : 1≤q) (small : V.card≤2*q)
    (av : a∈V) (bv : b∈V) (ab : D a b=true) (ne : b≠a)
    (other : ∀v∈V,v≠a → 2≤(outN D V v).card) : False := by
  have edge : b∈outN D V a := mem_outN.mpr ⟨bv,ab⟩
  obtain ⟨F,t,off,hf,deg,one⟩ := clone free av bv ab (other b bv ne)
    (by have := card_pos.mpr ⟨b,edge⟩; omega) other
  let W := insert t V
  have wcard : W.card=V.card+1 := card_insert_of_notMem off
  have upper (v) (vm : v∈W) : (inN F W v).card≤2 := by
    have limit := ExclusiveBankRouting.parent_room hq hf vm
    have growth := ball_growth q hq F W hf deg v vm (q-1) (by omega)
    change (inN F W v).card≤W.card-(ball F W v (q-1)).card at limit
    omega
  have sum := sum_out_in F W
  have lower := sum_le_sum deg
  have higher := sum_le_sum upper
  change (∑_v∈W,2)≤∑v∈W,(outN F W v).card at lower
  have all := (sum_eq_sum_iff_of_le upper).mp (le_antisymm higher (sum ▸ lower))
  have atT := all t (mem_insert_self t V)
  change (inN F (insert t V) t).card=2 at atT
  rw [one,card_singleton] at atT
  omega

#print axioms clone
#print axioms degree_two_obstruction
end LeanCH.BR.PrivateHeadClone
