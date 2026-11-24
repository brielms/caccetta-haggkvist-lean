import checkpoints.shen_extension.PhysicalReceiverRows

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota FragmentScoreEquality

/-- Count the same physical omissions by rows and columns. -/
theorem omitted_entries {D : CH.Digraph} {V H Y : Finset ℕ} (hv : H⊆V) (yv : Y⊆V) :
    ∑z∈Y,(H \ inN D V z).card = ∑h∈H,(Y \ outN D V h).card := by
  classical
  have left z : H \ inN D V z = H.filter (fun h=>D h z≠true) := by
    ext h
    simp only [mem_sdiff,mem_inN,mem_filter]
    exact ⟨fun ⟨hm,neg⟩=>⟨hm,fun hit=>neg ⟨hv hm,hit⟩⟩,fun ⟨hm,neg⟩=>⟨hm,fun hit=>neg hit.2⟩⟩
  have right h : Y \ outN D V h = Y.filter (fun z=>D h z≠true) := by
    ext z
    simp only [mem_sdiff,mem_outN,mem_filter]
    exact ⟨fun ⟨zm,neg⟩=>⟨zm,fun hit=>neg ⟨yv zm,hit⟩⟩,fun ⟨zm,neg⟩=>⟨zm,fun hit=>neg hit.2⟩⟩
  simp only [left,right,card_eq_sum_ones,sum_filter]
  exact sum_comm

/-- When the exceptional columns exceed the total permitted by a regular
head bank, one actual head must spend fewer than t arcs in that bank. -/
theorem light_head {D V q r t v} {X : Finset ℕ} {k : ℕ} (free : QFree D V q)
    (cut : 2≤q) (vm : v∈V) (reg : OutEq r D V) (mult : r=q*t+1)
    (boundary : Compose.Boundary.BoundaryRegular q t)
    (inside : X⊆ball D V v 2 \ ball D V v 1)
    (miss : ∀z∈X,k≤(outN D V v \ inN D V z).card)
    (overbook : r*((ball D V v 2 \ ball D V v 1).card+t-r)<X.card*k) :
    ∃h∈outN D V v,(outN D (outN D V v) h).card<t := by
  classical
  by_contra! all
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  have hs : H.card=r := reg v vm
  have hv : H⊆V := outN_subset
  have yv : Y⊆V := sdiff_subset.trans ball_subset
  have eq := WeightedSD.boundary_regular_out_on_set boundary (free.mono_set hv)
    (fun h hm=>loopfree free (by omega) (hv hm)) (hs.trans mult) all
  have rows h (hm : h∈H) : (Y\outN D V h).card=Y.card+t-r := by
    have cost := missing_count free cut vm hm (reg h (hv hm))
    change (Y\outN D V h).card+r=Y.card+(outN D H h).card at cost
    rw [eq h hm] at cost
    omega
  have enough := sum_le_sum miss
  rw [sum_const_nat (fun _ _=>rfl)] at enough
  have subset := sum_le_sum_of_subset (f:=fun z=>(H\inN D V z).card) inside
  have bill := omitted_entries (D:=D) hv yv
  rw [sum_const_nat rows,hs] at bill
  exact (Nat.not_lt_of_ge (enough.trans (subset.trans bill.le))) overbook

attribute [aesop safe forward (immediate := [free,cut,vm,reg,mult,boundary,inside,miss,overbook])
  (rule_sets := [CHGraphFamilies])] light_head
#print axioms omitted_entries
#print axioms light_head
end LeanCH.BR.LabelledCompromiseRecipe
