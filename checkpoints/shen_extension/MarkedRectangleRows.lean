import checkpoints.shen_extension.RectangleMissingHeads

namespace LeanCH.BR.AvoidedHeadQuota
open Finset BRq2 BRq3 BypassRepair CHRuleCatalog

/-- The missing rows in the cost bound are precisely those spending
extra degree inside the first head set. Each such row retains an actual
omitted label of the second shell, usable in later rules. -/
theorem excess_rows {D V q v r a d m} (free : QFree D V q) (cut : 3≤q) (vm : v∈V)
    (reg : OutEq r D V) (small : NoHost q a) (none : NoHost q d)
    (live : (ball D V v 2 \ ball D V v 1).Nonempty)
    (size : (ball D V v 2 \ ball D V v 1).card≤q*a)
    (need : m+a≤(ball D V v 2 \ ball D V v 1).card+r+1) (pos : 0<m) (fit : m≤q*d) :
    ∃M⊆outN D V v, 2*r+m<V.card+d+M.card ∧
      ∀h∈outN D V v,(h∈M ↔ r<(outN D (outN D V v) h).card+(ball D V v 2 \ ball D V v 1).card) ∧
        (h∈M → ∃y∈ball D V v 2 \ ball D V v 1,D h y≠true) := by
  classical
  let Y := ball D V v 2 \ ball D V v 1
  have yv : Y⊆V := sdiff_subset.trans ball_subset
  obtain ⟨M,sub,wit,cap⟩ := missing_parents (H:=outN D V v) free cut small none
    (fun x xm=>(reg x xm).ge) outN_subset yv live size need pos fit
  rw [reg v vm] at cap
  refine ⟨M,sub,by omega,?_⟩
  intro h hm
  have id := missing_count free (by omega) vm hm (reg h (mem_outN.mp hm).1)
  change (Y \ outN D V h).card+r=Y.card+(outN D (outN D V v) h).card at id
  refine ⟨?_,(wit h hm).mp⟩
  constructor
  · intro mem
    obtain ⟨y,ym,off⟩ := (wit h hm).mp mem
    have positive : 0<(Y \ outN D V h).card :=
      card_pos.mpr ⟨y,mem_sdiff.mpr ⟨ym,fun p=>off (mem_outN.mp p).2⟩⟩
    change r<(_ : ℕ)+Y.card
    omega
  · intro hi
    change r<(_ : ℕ)+Y.card at hi
    obtain ⟨y,ym⟩ := card_pos.mp (show 0<(Y \ outN D V h).card by omega)
    obtain ⟨inY,miss⟩ := mem_sdiff.mp ym
    exact (wit h hm).mpr ⟨y,inY,fun hit=>miss (mem_outN.mpr ⟨yv inY,hit⟩)⟩

attribute [aesop safe forward (immediate := [free,cut,vm,reg,small,none,live,size,need,pos,fit])
  (rule_sets := [CHGraphFamilies])] excess_rows
ch_family_split_result excess_rows
ch_family_split_result opposite_profile
#print axioms excess_rows
end LeanCH.BR.AvoidedHeadQuota
