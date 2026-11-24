import checkpoints.shen_extension.ShortCycleBalance
import checkpoints.shen_extension.ShellProfileCapacity

namespace LeanCH.BR.BalancedShellOrder
open Finset BRq2 BRq3 BR45 BRsGen ShellCycleSupply RetainedLayerCapacity
open GuardedLayerGrowth ConsecutiveShellBanks ExteriorPacking

/-- Every low-scoring root supplies a physical cycle on its own first
shell. The same labels give the extra third-ball slots. -/
theorem low_support {D V q r u} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (uv : u∈V)
    (base : ∀v∈V,3*r≤(ball D V v 3).card)
    (third : (ball D V u 3).card=3*r) (fourth : (ball D V u 4).card=4*r-1) :
    (N2 D V u).card≤r ∧ ∀v∈outN D V u,
      Rooted D V v (outN D V u) ∧ 3*r+2≤(ball D V v 3).card := by
  have lo := second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) uv
  have hi := ShellProfileCapacity.short_second free hq hr fit reg uv third.le
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  have ru := reg u uv
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  refine ⟨by omega,?_⟩
  by_cases small : (ball D V u 2).card=2*r
  · intro v vm
    have ⟨cr,grow⟩ := narrow_supply free (by omega) reg uv fit (by omega) v vm
    have h := grow 2 (by omega)
    simp only [Nat.reduceAdd] at h
    exact ⟨cr,by omega⟩
  obtain ⟨s,sm,_,cap⟩|high := equal_rows free (by omega) (by omega) fit reg uv (by omega) (by omega)
  · have := base s (outN_subset sm)
    omega
  intro v vm
  have ⟨cr,atV⟩ := high v vm
  exact ⟨cr,by omega⟩

/-- Equality in the global two-ball budget gives a constant score. Every
low root first spends a physical cycle or an ordered missing pair. -/
theorem flat_score {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (reg : OutEq r D V)
    (third : ∀v∈V,3*r≤(ball D V v 3).card)
    (fourth : ∀v∈V,4*r-1≤(ball D V v 4).card) (small : V.card<7*r) :
    ∀v∈V,(ball D V v 3).card+(ball D V v 4).card=7*r := by
  classical
  let score := fun v=>(ball D V v 3).card+(ball D V v 4).card
  let S := V.filter (fun v=>score v<7*r)
  let T := V.filter (fun v=>7*r+1≤score v)
  have sv : S⊆V := filter_subset _ _
  have tv : T⊆V := filter_subset _ _
  have supp u (us : u∈S) := by
    have h : (ball D V u 3).card+(ball D V u 4).card<7*r := (mem_filter.mp us).2
    have := third u (sv us)
    have := fourth u (sv us)
    exact low_support free hq hr fit reg (sv us) third (by omega) (by omega)
  have bill := ShortCycleBalance.count (c:=1) free (by omega) reg sv tv
    (fun u us x xm=>by
      have ⟨cr,extra⟩ := (supp u us).2 x xm
      have := fourth x (outN_subset xm)
      exact ⟨cr,mem_filter.mpr ⟨outN_subset xm,show 7*r+1≤_+_ by omega⟩⟩)
    (fun u us=>by have := (supp u us).1; omega)
  have cap := (remote_capacity free (by omega : 3+4≤q)).trans
    (Nat.mul_le_mul_left V.card (by omega : V.card+1≤7*r))
  have emp := ShortCycleBalance.positive_balance (score:=score) sv tv
    (disjoint_left.mpr (fun x sm tm=>by
      have a : score x<7*r := (mem_filter.mp sm).2
      have b : 7*r+1≤score x := (mem_filter.mp tm).2
      omega))
    (fun x sm=>by change 7*r≤_+_+1; have := third x (sv sm); have := fourth x (sv sm); omega)
    (fun x xm=>le_of_not_gt (fun low=>(mem_sdiff.mp xm).2 (mem_filter.mpr ⟨(mem_sdiff.mp xm).1,low⟩)))
    (fun x xm=>(mem_filter.mp xm).2) cap bill (by omega)
  have lower x (xv : x∈V) : 7*r≤score x := by
    by_contra! no
    have xs : x∈S := mem_filter.mpr ⟨xv,no⟩
    rw [emp] at xs
    exact notMem_empty _ xs
  have eq : (∑_x∈V,7*r)=∑x∈V,score x := by
    apply le_antisymm (sum_le_sum lower)
    rw [sum_const_nat (fun _ _=>rfl)]
    exact (Nat.le_add_left _ _).trans cap
  intro v vm
  exact ((sum_eq_sum_iff_of_le lower).mp eq v vm).symm

theorem order_floor {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (room : FourthRoom r) (extra : ShellProfileCapacity.Capacity r)
    (live : V.Nonempty) (degree : ∀v∈V,r≤(outN D V v).card) : 7*r≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have third x (xm : x∈V) := diagonal_third (k:=q-2) ff xm reg hq (by omega) fit
    (by omega) (by omega) room.1
  have fourth x (xm : x∈V) := diagonal_fourth ff hq hr fit room reg xm
  by_contra! small
  have score := flat_score ff hq hr fit reg third fourth small
  have ceiling x (xm : x∈V) : (ball F V x 3).card≤3*r+1 := by
    have := score x xm
    have := fourth x xm
    omega
  have sec x (xm : x∈V) : 2*r+1≤(ball F V x 2).card := by
    have base := second_floor ff (by omega : 4≤q) reg (by omega : 0<r) (by omega) xm
    by_contra! low
    have one := card_B1 (ff.mono_bound (by omega : 4≤q)) xm
    have two := @card_B2 F V x
    have dr := reg x xm
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<(outN F V x).card by omega)
    have gain := (narrow_supply ff (by omega) reg xm fit (by omega) v vm).2 2 (by omega)
    simp only [Nat.reduceAdd] at gain
    have := ceiling v (outN_subset vm)
    have := fourth x xm
    omega
  have flat x (xm : x∈V) : (ball F V x 3).card=3*r+1 := by
    have cap := ceiling x xm
    have lo := third x xm
    by_contra ne
    have two := ShellProfileCapacity.short_second ff hq hr fit reg xm (by omega)
    have := sec x xm
    have one := card_B1 (ff.mono_bound (by omega : 4≤q)) xm
    have b2 := @card_B2 F V x
    have b3 := @card_B3 F V x
    have dr := reg x xm
    obtain ⟨s,sm,small,_⟩|tall := equal_rows ff (by omega) (by omega) fit reg xm (by omega) (by omega)
    · have := sec s (outN_subset sm)
      omega
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<(outN F V x).card by omega)
    have gain := (tall v vm).2
    have := ceiling v (outN_subset vm)
    have := fourth x xm
    omega
  obtain ⟨x,xm⟩ := live
  have th := flat x xm
  have sum := score x xm
  have b4 : (ball F V x 4).card≤4*r-1 := by omega
  have tip := ShellProfileCapacity.second_upper ff hq hr fit extra reg xm sec th b4
  exact ShellProfileCapacity.triple_excess ff hr fit reg xm (Nat.le_antisymm tip (sec x xm)) th b4

attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,uv,base,third,fourth])
  (rule_sets := [CHGraphFamilies])] low_support
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,third,fourth,small])
  (rule_sets := [CHGraphFamilies])] flat_score
#print axioms low_support
#print axioms flat_score
#print axioms order_floor
end LeanCH.BR.BalancedShellOrder
