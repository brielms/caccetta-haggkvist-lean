import checkpoints.shen_extension.LowShellCycleSelection
import checkpoints.shen_extension.ShellBankOrders

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- If every low class assigns its entire shell as a cycle, the literal shells
index the accounting. A complete exterior gives at most one successor per
row across this whole family. More than four high labels then pay each
class's entire residual debt, strictly. -/
theorem whole_cycle_exit {D V q r k b} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (live : V.Nonempty) (time : k+k≤q) (order : V.card≤2*b)
    (floor : ∀v∈V,b≤(ball D V v k).card+1)
    (sel : Selection D V q r k b)
    (whole : ∀Y∈(shellOrigins D V k b).image (N2 D V),sel.pay Y=Y)
    (loss : ∀Y∈(shellOrigins D V k b).image (N2 D V),omissions D V Y r=0)
    (high : ∀Y∈(shellOrigins D V k b).image (N2 D V),
      4<(Y.filter (fun v=>b<(ball D V v k).card)).card) : False := by
  classical
  let F := (shellOrigins D V k b).image (N2 D V)
  have installed Y (ym : Y∈F) : Y∈sel.family := whole Y ym ▸ sel.assigned Y ym
  have rooted Y (ym : Y∈F) := sel.rooted _ (installed Y ym)
  let price := fun a=>(surplus b (ball D V a k).card : ℚ)
  have stock Y (ym : Y∈F) v (vm : v∈Y) : share D V F r price Y v=price v := by
    have bound := turns_bound (v:=v) free (by omega : 0+2≤q) rooted reg (fun C cm=>(loss C cm).le)
    have occ : Y∈through F v := mem_filter.mpr ⟨ym,vm⟩
    have pos := card_pos.mpr (show (turns D F v).Nonempty from
      ⟨internalHead D Y v,mem_image_of_mem _ occ⟩)
    simp [share,show (turns D F v).card=1 by omega,loss Y ym]
  have rich Y (ym : Y∈F) : (4:ℚ)<∑v∈Y,share D V F r price Y v := by
    let G := Y.filter (fun v=>b<(ball D V v k).card)
    have lower v (vm : v∈G) : (1:ℚ)≤price v := by
      have hi := (mem_filter.mp vm).2
      have unit : 1≤surplus b (ball D V v k).card := by simp [surplus,hi]; omega
      dsimp [price]
      exact_mod_cast unit
    have cost := sum_le_sum lower
    simp only [sum_const,nsmul_eq_mul,mul_one] at cost
    have sub : ∑v∈G,price v≤∑v∈Y,price v :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _=>by dsimp [price]; positivity)
    have more : (4:ℚ)<G.card := by exact_mod_cast high Y ym
    calc
      4 < (G.card:ℚ) := more
      _ ≤ ∑v∈G,price v := by simpa using cost
      _ ≤ ∑v∈Y,price v := sub
      _ = _ := sum_congr rfl (fun v vm=>(stock Y ym v vm).symm)
  have residual Y : shellDebt D V k b Y≤4 := by
    apply (class_residual (m:=3) _).trans (by decide)
    intro v _
    unfold debit
    split_ifs <;> omega
  have has : F.Nonempty := by
    by_contra! none
    have large v (vm : v∈V) : b+1≤(ball D V v k).card := by
      by_contra! small
      have inU : v∈shellOrigins D V k b := mem_filter.mpr ⟨vm,by omega⟩
      exact (not_nonempty_iff_eq_empty.mpr none) ⟨N2 D V v,mem_image_of_mem _ inU⟩
    have bound := card_ge_of_two_balls free time large large live
    omega
  obtain ⟨Y,ym⟩ := has
  have pays C (cm : C∈F) : (shellDebt D V k b C : ℚ)<∑v∈C,share D V F r price C v :=
    lt_of_le_of_lt (by exact_mod_cast residual C) (rich C cm)
  have total := sum_lt_sum (fun C cm=>(pays C cm).le) ⟨Y,ym,pays Y ym⟩
  apply ledger_from_shell_classes (F:=F) (extra:=∅) free hq time floor order rooted
    (fun C cm=>sel.sub _ (installed C cm)) reg (empty_subset _) (by simp)
  simpa using total

/-- Every surviving selection has a representative whose first layer is
cyclic or whose assigned cycle uses a proper part of the second shell,
when all acyclic representatives supply at least five high rows on a
whole shell. -/
theorem hard_representative {D V q r target} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (regime : Room q r) (mixed : ShellBankOrders.MixedRoom q r)
    (size : V.card≤2*(3*r)) (hr : 4<r)
    (fit : r+(r-(q+1))<2*(q-1)) (dist : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) (pay : 3*r<4+target)
    (sel : Selection D V q r 3 (3*r)) :
    ∃Y∈(shellOrigins D V 3 (3*r)).image (N2 D V),
      ¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card ∨ sel.pay Y≠Y := by
  classical
  by_contra! easy
  have hq := regime.1
  have labels Y (ym : Y∈(shellOrigins D V 3 (3*r)).image (N2 D V)) := by
    have data := selected_stock free reg (by omega) sel ym regime (easy Y ym).1 fit dist guard
    dsimp only at data
    rw [(easy Y ym).2] at data
    exact data
  have width Y (ym : Y∈(shellOrigins D V 3 (3*r)).image (N2 D V)) : Y.card=r := by
    have entry := mem_filter.mp (sel.represents Y ym)
    have lm := mem_filter.mp entry.1
    obtain ⟨f,roomA,roomB,roomC,roomD,_⟩ := regime
    have cap := low_third_second free f reg lm.1 roomA roomB roomC roomD lm.2
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) lm.1
    rw [reg _ lm.1] at one
    have two := @card_B2 D V (sel.rep Y)
    rw [entry.2] at two
    have cx := reg _ lm.1
    obtain ⟨s,sm,ss⟩ := exists_sink (easy Y ym).1 (card_pos.mp (by omega)) le_rfl
    have sy : outN D V s⊆N2 D V (sel.rep Y) := fun z hm=>(mem_union.mp (headX (free.mono_bound (by omega : 4≤q))
      lm.1 sm (outN_subset hm) (mem_outN.mp hm).2)).resolve_left (fun xm=>ss z xm (mem_outN.mp hm).2)
    rw [entry.2] at sy
    have low := card_le_card sy
    rw [reg _ (outN_subset sm)] at low
    omega
  have full Y (ym : Y∈(shellOrigins D V 3 (3*r)).image (N2 D V)) :
      ∀v∈Y,N3 D V (sel.rep Y)⊆outN D V v := by
    have n := (labels Y ym).2.2.1
    rw [width Y ym,Nat.sub_self,Nat.zero_mul,Nat.add_zero] at n
    have eq := eq_of_subset_of_card_le (filter_subset (fun a=>N3 D V (sel.rep Y)⊆outN D V a) Y)
      (by simpa only [width Y ym] using n)
    intro v vm
    have filtered : v∈Y.filter (fun a=>N3 D V (sel.rep Y)⊆outN D V a) := eq.symm ▸ vm
    exact (mem_filter.mp filtered).2
  apply whole_cycle_exit free (by omega) reg live (by omega) size
    (fun v vm=>by have := ShellBankOrders.mixed_third free mixed reg vm; omega)
    sel (fun Y ym=>(easy Y ym).2)
  · intro Y ym
    have entry := mem_filter.mp (sel.represents Y ym)
    have lm := mem_filter.mp entry.1
    have used : Y∈sel.family := (easy Y ym).2 ▸ sel.assigned Y ym
    have cv := sel.sub Y used
    have zSize := (labels Y ym).2.1
    let Z := N3 D V (sel.rep Y)
    have Zlen : Z.card+1=r := zSize
    have outer : exterior D V Y⊆Z := by
      intro z zm
      obtain ⟨seen,off⟩ := mem_sdiff.mp zm
      obtain ⟨v,vm,arc⟩ := mem_biUnion.mp seen
      have dis : Disjoint Y Z := by
        rw [←entry.2]
        exact disjoint_left.mpr (fun _ h1 h2=>(mem_N3.mp h2).2 (mem_N2.mp h1).1)
      have heads : outN D Y v ∪ Z ⊆ outN D V v := union_subset (outN_mono cv v) (full Y ym v vm)
      have eq := eq_of_subset_of_card_le heads (by rw [card_union_of_disjoint (dis.mono_left outN_subset),
        (sel.rooted Y used v vm).one v vm,reg v (cv vm)]; omega)
      obtain old|zz := mem_union.mp (eq.symm ▸ arc)
      · exact (off (outN_subset old)).elim
      · exact zz
    have lim := card_le_card outer
    unfold omissions
    omega
  · intro Y ym
    have data := (labels Y ym).2.2.2
    have subset : Y⊆Y.filter (fun v=>3*r<(ball D V v 3).card) := by
      intro a am
      exact mem_filter.mpr ⟨am,lt_of_lt_of_le pay (data a (mem_filter.mpr ⟨am,full Y ym a am⟩))⟩
    have := card_le_card subset
    rw [width Y ym] at this
    omega

/-- The actual labelled class survives under any exact thinning of the input.
The structural alternative is conditional only on the indicated arithmetic
and retains the caller's chosen selection. -/
structure OnHardFamily (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀q≤CHRuleCatalog.cutoff p,∀target,
    Room q p.s → ShellBankOrders.MixedRoom q p.s → p.n≤2*(3*p.s) → 4<p.s →
    p.s+(p.s-(q+1))<2*(q-1) → (p.s-(q+1))*(p.s-q)+3≤q →
    ScoreRoom q p.s (p.s-1) target → 3*p.s<4+target →
    ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀sel : Selection F (range p.n) q p.s 3 (3*p.s),
        ∃Y∈(shellOrigins F (range p.n) 3 (3*p.s)).image (N2 F (range p.n)),
          ¬QFree F (outN F (range p.n) (sel.rep Y)) (outN F (range p.n) (sel.rep Y)).card ∨ sel.pay Y≠Y

theorem hard_on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : OnHardFamily p := by
  constructor
  intro q cut target room mixed size hr fit dist guard pay F sub reg sel
  have free := qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)
  exact hard_representative free reg ⟨0,mem_range.mpr bad.order⟩ room mixed (by simpa using size)
    hr fit dist guard pay sel

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] hard_on_bad

#print axioms hard_on_bad

#print axioms whole_cycle_exit
#print axioms hard_representative
end LeanCH.BR.LowShellCycleSelection
