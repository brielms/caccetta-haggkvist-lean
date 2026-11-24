import checkpoints.shen_extension.BoundaryParentQuota

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45 LabelledCompromiseRecipe

/-- A single missing but reachable-by-repair column determines the total
arc count on H. The omissions and the neutral labels have one exact budget. -/
theorem omission_balance {D H q t g b} (missCount : ℕ→ℕ)
    (free : QFree D H q) (cut : 2≤q) (gm : g∈H) (bh : b∈H.erase g)
    (short : (outN D H g).card+1=t)
    (rows : ∀a∈H,missCount a+t=(outN D H a).card+1)
    (cols : ∀a∈H,a≠g → (inN D H a).card+(if a=b then 1 else 0)=t) :
    (∑a∈H,missCount a)+(neutral D H g).card+2*t+1=2*H.card := by
  classical
  have count := sum_congr (s₁:=H) rfl rows
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at count
  have sumIn : (∑a∈H,(outN D H a).card)=∑a∈H,(inN D H a).card := Compose.ThinRigid.sum_out_eq_sum_in D H
  rw [sumIn] at count
  have rem := sum_congr (s₁:=H.erase g) rfl (fun a am=>cols a (mem_erase.mp am).2 (mem_erase.mp am).1)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at rem
  have single : (∑a∈H.erase g,if a=b then 1 else 0)=1 := by simp [bh]
  rw [single] at rem
  have ins := sum_erase_add H (fun a=>(inN D H a).card) gm
  have sz := card_erase_add_one gm
  have times := congrArg (fun k=>k*t) sz
  have part := partition_card free cut gm
  nlinarith

/-- If an exceptional remote column exists, the original parents must
fit the exact budget and also support the reversed lower-quota test. -/
theorem remote_budget {D H q t g b} (missCount : ℕ→ℕ)
    (free : QFree D H q) (cut : 3≤q) (gm : g∈H)
    (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (short : (outN D H g).card+1=t) (other : ∀a∈H,a≠g → t≤(outN D H a).card)
    (rows : ∀a∈H,missCount a+t=(outN D H a).card+1)
    (fresh : b∈remote D H q t g) (off : D g b≠true) :
    (∑a∈H,missCount a)+(neutral D H g).card+2*t+1=2*H.card ∧
    ∀k,k+(neutral D H g).card≤t → BypassRepair.NoHost q k → LoneRow.NoNearHost q k →
      q*k+(neutral D H g).card+t<H.card := by
  obtain ⟨_,tightCount,cols⟩ := fresh_profile free (by omega) gm size br short other fresh off
  have live : (inN D H g).Nonempty := by
    have sub : tight D H t g⊆inN D H g := fun _ m=>mem_inN.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.1⟩
    have bound := card_le_card sub
    exact card_pos.mp (by omega)
  refine ⟨omission_balance missCount free (by omega) gm (mem_filter.mp fresh).1 short rows cols,?_⟩
  intro k fund none near
  have big := parent_order free cut gm live (fun a am=>by
    have ne : a≠g := fun e=>loopfree free (by omega) gm (e ▸ (mem_inN.mp am).2)
    exact (cols a (mem_inN.mp am).1 ne).ge) fund none near
  have part := partition_card free (by omega) gm
  omega

/-- The cap on omissions bounds all neutral labels. Checking the smallest
remaining quota suffices for the order inequality throughout the interval. -/
theorem remote_exact {D H q t g M} (missCount : ℕ→ℕ)
    (free : QFree D H q) (cut : 3≤q) (gm : g∈H)
    (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (short : (outN D H g).card+1=t) (other : ∀a∈H,a≠g → t≤(outN D H a).card)
    (rows : ∀a∈H,missCount a+t=(outN D H a).card+1) (floor : M≤∑a∈H,missCount a)
    (small : let c:=2*H.card-(M+2*t+1); c+2≤t ∧ H.card≤q*(t-c)+c+t)
    (lower : ∀k,2≤k → k≤t → BypassRepair.NoHost q k ∧ LoneRow.NoNearHost q k) :
    remote D H q t g=outN D H g := by
  apply Subset.antisymm _ (old_heads_remote free (by omega) gm)
  intro b bm
  have bh := (mem_erase.mp (mem_filter.mp bm).1).2
  apply mem_outN.mpr
  refine ⟨bh,?_⟩
  by_contra off
  let c:=2*H.card-(M+2*t+1)
  change c+2≤t ∧ H.card≤q*(t-c)+c+t at small
  obtain ⟨balance,above⟩ := remote_budget missCount free cut gm size br short other rows bm off
  let o:=(neutral D H g).card
  have oc : o≤c := by dsimp [o,c]; omega
  let k:=t-o
  have fund : k+o=t := by dsimp [k]; omega
  obtain ⟨none,near⟩ := lower k (by omega) (by omega)
  have high := above k fund.le none near
  change q*k+o+t<H.card at high
  have step : t-c+(c-o)=k := by omega
  have gain : c-o≤q*(c-o) := Nat.le_mul_of_pos_left _ (by omega)
  have prod := congrArg (fun j=>q*j) step
  simp only [Nat.mul_add] at prod
  omega

#print axioms omission_balance
#print axioms remote_budget
#print axioms remote_exact
end LeanCH.BR.BoundaryTightParentReach
