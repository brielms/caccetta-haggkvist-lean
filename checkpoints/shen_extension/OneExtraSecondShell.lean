import checkpoints.shen_extension.StrongDirectBudget
import checkpoints.shen_extension.PrefixReturnSize

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- A single low labelled cycle row excludes every short primary and every
narrow middle primary on that same cycle. The surviving second shell keeps
the actual exterior and its one additional label. -/
theorem one_extra_from_measured_shells {D V q r C Y a} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (hq : 6≤q) (hr : 4≤r) (fit : r≤q+2)
    (width : (exterior D V C).card=r-1) (paid : ∀v∈C,exterior D V C⊆outN D V v)
    (two : (N2 D V (t.rep Y)).card≤r) (three : 3*r≤(ball D V (t.rep Y) 3).card+1) (claim : Y∈claims t C) (first : C⊆outN D V (t.rep Y))
    (size : C.card+1=r) (long : q<C.card) (am : a∈C) (low : (ball D V a 3).card≤3*r+1)
    (next : ∀e∈exterior D V C,Rooted D V e (exterior D V C))
    (narrowSupply : (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14 ∨
      ((N2 D V (t.rep Y)).card=r-1 → r-1≤(ball D V (t.rep Y) 4\ball D V (t.rep Y) 3).card)) :
    (ball D V (t.rep Y) 3).card=3*r ∧ (N3 D V (t.rep Y)).card=r-1 ∧
    ∃b∈Y\exterior D V C,Y=insert b (exterior D V C) := by
  classical
  obtain ⟨key,id⟩ := mem_filter.mp claim
  have y := rep_key t key
  have uv := rep_native t key
  have root := t.rooted _ (t.assigned _ key)
  rw [id] at root
  have slot := card_sdiff_of_subset first
  rw [reg _ uv] at slot
  have upper := (mem_filter.mp (mem_filter.mp (t.represents Y key)).1).2
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have b2 := @card_B2 D V (t.rep Y)
  have b3 := @card_B3 D V (t.rep Y)
  have gate := sparse_gate free (by omega) uv first paid
    (fun w (wm : w∈outN D V (t.rep Y))=>(reg w (outN_subset wm)).ge)
    (fun e em=>((next e em).one e em).le) (by omega)
  have medium : (ball D V (t.rep Y) 3).card=3*r := by
    by_contra neq
    have short : (ball D V (t.rep Y) 3).card<3*r := by omega
    have ys := card_le_card gate.2
    by_cases narrow : (N2 D V (t.rep Y)).card=r-1
    · have third : (N3 D V (t.rep Y)).card=r-1 := by omega
      have narrowY := (congrArg card y).symm.trans narrow
      have kept : Y∉shortSwitches t := by
        intro moved
        have eq := (policy.secondary Y moved).symm.trans id
        exact (mem_N2.mp (y.symm ▸ (eq.symm ▸ am))).2 (X_B1 (first am))
      have four : r≤(ball D V (t.rep Y) 4\ball D V (t.rep Y) 3).card := by
        by_contra! small; exact kept (mem_filter.mpr ⟨key,narrowY,third,small⟩)
      have strong := (policy.strong Y key ⟨narrowY,third,four⟩).2 a (id.symm ▸ am)
      omega
    · exact short_large_second_escape free hq reg uv fit long root first size (by omega) (by omega)
  have full : (N2 D V (t.rep Y)).card=r := by
    by_contra notFull
    have inc := card_le_card gate.2
    have narrow : (N2 D V (t.rep Y)).card=r-1 := by omega
    rcases narrowSupply with capacity|growth
    case inr =>
      have whole := eq_of_subset_of_card_le gate.2 (by omega)
      have seen : N2 D V (t.rep Y)⊆ball D V a 1 := fun e em=>
        X_B1 (paid a am (whole.symm ▸ em))
      have cap := BankReachTransfer.prefix_return_size (j:=1) (d:=1) (k:=2) free uv am
        (fun _ cm=>X_B1 (first cm)) (fun c cm=>((root c cm).one c cm).ge) (by omega) seen
      have fourth := card_sdiff_add_card_eq_card
        (ball_mono_radius (D:=D) (W:=V) (u:=t.rep Y) (by decide : 3≤4))
      have rich := growth narrow
      simp only [Nat.reduceAdd] at cap
      omega
    have rows := (actual_narrow_middle free hq reg uv fit hr (by omega) narrow (by omega) capacity first long root).2
    have cell : outN D (outN D V (t.rep Y)) a⊆outN D C a := by
      intro d dm
      have dx := outN_subset dm
      have dv := outN_subset dx
      have ad := (mem_outN.mp dm).2
      by_cases dc : d∈C
      · exact mem_outN.mpr ⟨dc,ad⟩
      have de : d∈exterior D V C := mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,am,mem_outN.mpr ⟨dv,ad⟩⟩,dc⟩
      exact (disjoint_left.mp gate.1 dx de).elim
    have only := congrArg card (Subset.antisymm cell (outN_mono first _))
    have strong := rows a am (only.trans ((root a am).one a am))
    omega
  have diff := card_sdiff_of_subset (y ▸ gate.2 : exterior D V C⊆Y)
  have cy := congrArg card y
  obtain ⟨b,single⟩ := card_eq_one.mp (show (Y\exterior D V C).card=1 by omega)
  refine ⟨medium,by omega,b,single.symm ▸ mem_singleton_self b,?_⟩
  calc Y=(Y\exterior D V C)∪exterior D V C := (sdiff_union_of_subset (y ▸ gate.2)).symm
       _=insert b (exterior D V C) := by rw [single,singleton_union]

/-- The existing root growth data supply both measured shell bounds. -/
theorem primary_one_extra {D V q r C Y a target A} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (account : CompleteAccount t C A) (claim : Y∈claims t C) (first : C⊆outN D V (t.rep Y))
    (size : C.card+1=r) (long : q<C.card) (am : a∈C) (low : (ball D V a 3).card≤3*r+1)
    (next : ∀e∈exterior D V C,Rooted D V e (exterior D V C))
    (narrowSupply : (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14 ∨
      ((N2 D V (t.rep Y)).card=r-1 → r-1≤(ball D V (t.rep Y) 4\ball D V (t.rep Y) 3).card)) :
    (ball D V (t.rep Y) 3).card=3*r ∧ (N3 D V (t.rep Y)).card=r-1 ∧
    ∃b∈Y\exterior D V C,Y=insert b (exterior D V C) := by
  have key := (mem_filter.mp claim).1
  have uv := rep_native t key
  have upper := (mem_filter.mp (mem_filter.mp (t.represents Y key)).1).2
  obtain ⟨hq,h1,h2,h3,h4,_⟩ := ready.cycle
  have lim := low_third_second free hq reg uv h1 h2 h3 h4 upper
  change (ball D V (t.rep Y) 2).card≤2*r+1 at lim
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have b2 := @card_B2 D V (t.rep Y)
  have floor := ShellBankOrders.mixed_third free ready.growth reg uv
  exact one_extra_from_measured_shells free reg t policy hq ready.growth.2.1 ready.close account.width
    account.allHeads (by omega) (by omega) claim first size long am low next narrowSupply

attribute [aesop safe forward (immediate := [free,reg,policy,hq,hr,fit,width,paid,two,three,claim,first,size,long,am,low,next,narrowSupply]) (rule_sets := [CHGraphFamilies])] one_extra_from_measured_shells
#print axioms one_extra_from_measured_shells
attribute [aesop safe forward (immediate := [free,reg,policy,ready,account,claim,first,size,long,am,low,next,narrowSupply]) (rule_sets := [CHGraphFamilies])] primary_one_extra
#print axioms primary_one_extra
end LeanCH.BR.LowShellCycleSelection
