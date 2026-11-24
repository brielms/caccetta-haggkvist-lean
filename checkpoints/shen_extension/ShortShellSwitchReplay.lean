import checkpoints.shen_extension.SecondShellTransfer
import checkpoints.shen_extension.CompleteBankScore
import checkpoints.shen_extension.MeasuredCycleBudget

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen PhysicalCycleStock ExteriorPacking
open scoped Classical

noncomputable def shortSwitches {D V q r} (sel : Selection D V q r 3 (3*r)) :=
  (classes D V 3 (3*r)).filter (fun Y=>Y.card=r-1 ∧ (N3 D V (sel.rep Y)).card=r-1 ∧
    (ball D V (sel.rep Y) 4\ball D V (sel.rep Y) 3).card<r)

def NeedsStrong {D V q r} (sel : Selection D V q r 3 (3*r)) (Y : Finset ℕ) : Prop :=
  Y.card=r-1 ∧ (N3 D V (sel.rep Y)).card=r-1 ∧ r≤(ball D V (sel.rep Y) 4\ball D V (sel.rep Y) 3).card

def StrongChoice {D V q r} (sel : Selection D V q r 3 (3*r)) (Y C : Finset ℕ) : Prop :=
  C⊆outN D V (sel.rep Y) ∧ ∀v∈C,3*r+2≤(ball D V v 3).card

structure SwitchStep {D V q r} (s t : Selection D V q r 3 (3*r)) : Prop where
  same : t.rep=s.rep
  valid : ∀Y∈classes D V 3 (3*r),NeedsStrong t Y → StrongChoice t Y (t.pay Y)
  keep : ∀Y∈classes D V 3 (3*r),(NeedsStrong s Y → StrongChoice s Y (s.pay Y)) → t.pay Y=s.pay Y

/-- Every repeat on an already repaired selection keeps all the used labels. -/
theorem stable_switch {D V q r} {s t v : Selection D V q r 3 (3*r)}
    (first : SwitchStep s t) (again : SwitchStep t v) :
    v.rep=t.rep ∧ ∀Y∈classes D V 3 (3*r),v.pay Y=t.pay Y :=
  ⟨again.same,fun Y ym=>again.keep Y ym (first.valid Y ym)⟩

/-- Match the first-cycle choice to its actual rows whenever the fourth
layer has room. All other classes retain their designated cycle. -/
theorem choose_strong_first {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (sel : Selection D V q r 3 (3*r)) (hq : 4≤q) (hr : 4≤r) (fit : r≤q+2) :
    ∃t : Selection D V q r 3 (3*r),SwitchStep sel t := by
  classical
  let P := fun Y C=>(NeedsStrong sel Y → StrongChoice sel Y C) ∧
    ((NeedsStrong sel Y → StrongChoice sel Y (sel.pay Y)) → C=sel.pay Y)
  obtain ⟨t,same,choose⟩ := rebook sel P (by
    intro Y ym
    dsimp only [P]
    by_cases settled : NeedsStrong sel Y → StrongChoice sel Y (sel.pay Y)
    · have used := sel.assigned Y ym
      exact ⟨_,sel.located Y ym,sel.length _ used,sel.rooted _ used,sel.loss _ used,settled,fun _=>rfl⟩
    · have guard : NeedsStrong sel Y := by by_contra no; exact settled (fun h=>(no h).elim)
      obtain ⟨h₂,h₃,h₄⟩ := guard
      have uv := rep_native sel ym
      have s₂ := (congrArg card (rep_key sel ym)).trans h₂
      obtain good|bad := short_shell_payer free hq reg uv fit hr s₂ h₃
      · obtain ⟨_,C,first,len,root,width,strong⟩ := good
        have fr := (card_le_card first).trans_eq (reg _ uv)
        exact ⟨C,.inl first,len,root,by unfold omissions; omega,fun _=>⟨first,strong⟩,fun h=>(settled h).elim⟩
      · have := bad.1; omega)
  refine ⟨t,same,?_,fun Y ym=>(choose Y ym).2⟩
  intro Y ym
  simpa only [NeedsStrong,StrongChoice,same] using (choose Y ym).1

/-- The geometry and the strength test for a switch are both supplied from
the three actual layer sizes. No independent growth or payment premise. -/
theorem switched_shell_paid {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (sel : Selection D V q r 3 (3*r)) (hq : 4≤q) (hr : 4≤r) (fit : r≤q+2)
    {Y} (ym : Y∈shortSwitches sel) :
    CompletePayer D V r 1 Y ∧ (shellDebt D V 3 (3*r) Y:ℚ)<∑v∈Y,(surplus (3*r) (ball D V v 3).card:ℚ) := by
  classical
  obtain ⟨key,yw,zw,ww⟩ := mem_filter.mp ym
  let u := sel.rep Y
  have ey : N2 D V u=Y := rep_key sel key
  obtain good|paid := short_shell_payer free hq reg (rep_native sel key) fit hr ((congrArg card ey).trans yw) zw
  · have := good.1; omega
  obtain ⟨width,yz,rest,payer⟩ := paid
  rw [ey] at payer yz
  change (N3 D V u).card=r-1 at zw
  have zv : N3 D V u⊆V := fun _ m=>N3_subV m
  have wsize : (exterior D V (N3 D V u)).card=r-1 := (congrArg card rest).trans width
  have zr := (short_exterior free (by omega) reg zv (by omega : (N3 D V u).card≤q+1)
    (card_pos.mp (by omega : 0<(N3 D V u).card)) wsize.le (by omega)).2
  have high := double_bank_high free hq reg (by omega) fit payer.rooted payer.width (yz.symm ▸ zr) (yz.symm ▸ wsize)
  have force : q<Y.card := by
    by_contra! small
    obtain ⟨x,xm,sink⟩ := exists_sink (free.mono_set (show Y⊆V from ey ▸ (fun _ m=>N2_subV m)))
      (card_pos.mp (by omega : 0<Y.card)) small
    obtain ⟨a,am⟩ := card_pos.mp (show 0<(outN D Y x).card by rw [(payer.rooted x xm).one x xm]; decide)
    exact sink a (outN_subset am) (mem_outN.mp am).2
  have units : Y.card≤∑v∈Y,surplus (3*r) (ball D V v 3).card := by
    have per v (vm : v∈Y) : 1≤surplus (3*r) (ball D V v 3).card := by
      have h := high v vm
      simp only [surplus,ite_eq_left h]; omega
    simpa only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] using sum_le_sum per
  have owed : shellDebt D V 3 (3*r) Y≤4 := by
    apply (class_residual (m:=3) _).trans (by decide)
    intro v _; unfold debit; split_ifs <;> omega
  refine ⟨payer,?_⟩
  exact_mod_cast (show shellDebt D V 3 (3*r) Y<∑v∈Y,surplus (3*r) (ball D V v 3).card by omega)

structure SwitchedDeficit {D V q r} (t : Selection D V q r 3 (3*r)) (Y : Finset ℕ) : Prop where
  key : Y∈classes D V 3 (3*r)
  kept : Y∉shortSwitches t
  unpaid : rowStock t (booked t) (t.pay Y)≤switchedBill t (shortSwitches t) (t.pay Y)
  strong_if_narrow : Y.card=r-1 → (N3 D V (t.rep Y)).card=r-1 →
    t.pay Y⊆outN D V (t.rep Y) ∧ ∀v∈t.pay Y,3*r+2≤(ball D V v 3).card

theorem switch_frontier {D V q r} (sel : Selection D V q r 3 (3*r)) (free : QFree D V q)
    (reg : OutEq r D V) (hq : 6≤q) (hr : 4≤r) (fit : r≤q+2) (gap : r-q+1<r-1)
    (floor : MeasuredFloor D V 3 (3*r)) (size : V.card≤2*(3*r)) (live : V.Nonempty) :
    ∃t : Selection D V q r 3 (3*r),SwitchStep sel t ∧ ∃Y,SwitchedDeficit t Y := by
  classical
  obtain ⟨t,step⟩ := choose_strong_first free reg sel (by omega) hr fit
  have facts Y (ym : Y∈shortSwitches t) := switched_shell_paid free reg t (by omega) hr fit ym
  obtain ⟨Y,key,kept,due⟩ := old_payer_after_switch t free reg (by omega) (by omega)
    floor.every size live (fun _ h=>(mem_filter.mp (show _∈shortSwitches t from h)).1)
    (fun _ h=>(facts _ h).1) (fun C cm=>by obtain ⟨W,wm,rfl⟩:=mem_image.mp cm; exact t.loss _ (t.assigned _ wm))
    gap (fun _ h=>(facts _ h).2)
  refine ⟨t,step,Y,key,kept,due,?_⟩
  intro y z
  have large : r≤(ball D V (t.rep Y) 4\ball D V (t.rep Y) 3).card := by
    by_contra! small; exact kept (mem_filter.mpr ⟨key,y,z,small⟩)
  exact step.valid Y key ⟨y,z,large⟩

attribute [aesop safe forward (immediate := [sel,free,reg,hq,hr,fit,gap,floor,size,live]) (rule_sets := [CHGraphFamilies])] switch_frontier

#print axioms stable_switch
#print axioms choose_strong_first
#print axioms switched_shell_paid
#print axioms switch_frontier
end LeanCH.BR.LowShellCycleSelection
