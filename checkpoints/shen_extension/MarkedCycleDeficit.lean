import checkpoints.shen_extension.UnpaidCycleClaims

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- Choose cycles subject to an additional property while preserving every
labelled representative and its minimum-score certificate. -/
theorem rebook {D V q r k b} (sel : Selection D V q r k b) (P : Finset ℕ → Finset ℕ → Prop)
    (supply : ∀Y∈classes D V k b,∃C,(C⊆outN D V (sel.rep Y) ∨ C⊆Y) ∧
      q<C.card ∧ (∀v∈C,Rooted D V v C) ∧ omissions D V C r≤r-q ∧ P Y C) :
    ∃t : Selection D V q r k b,t.rep=sel.rep ∧ ∀Y∈classes D V k b,P Y (t.pay Y) := by
  classical
  let K := classes D V k b
  let pay Y := if h:Y∈K then (supply Y h).choose else ∅
  have props Y (ym : Y∈K) :
      (pay Y⊆outN D V (sel.rep Y) ∨ pay Y⊆Y) ∧ q<(pay Y).card ∧
      (∀v∈pay Y,Rooted D V v (pay Y)) ∧ omissions D V (pay Y) r≤r-q ∧ P Y (pay Y) := by
    simpa only [pay,dite_eq_left ym] using (supply Y ym).choose_spec
  let other : Selection D V q r k b := {
    rep := sel.rep, pay := pay, family := K.image pay
    represents := sel.represents, least := sel.least
    assigned := fun Y ym=>mem_image_of_mem _ ym, located := fun Y ym=>(props Y ym).1
    rooted := by rintro C cm; obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact (props Y ym).2.2.1
    sub := by rintro C cm x xm; obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact ((props Y ym).2.2.1 x xm).sub xm
    length := by rintro C cm; obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact (props Y ym).2.1
    loss := by rintro C cm; obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact (props Y ym).2.2.2.1 }
  exact ⟨other,rfl,fun Y ym=>(props Y ym).2.2.2.2⟩

/-- Select the actual first-layer cycle whenever that layer contains one. -/
theorem primary_selection {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (sel : Selection D V q r 3 (3*r)) (room : Room q r) :
    ∃t : Selection D V q r 3 (3*r),t.rep=sel.rep ∧ ∀Y∈classes D V 3 (3*r),
      ¬QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card → t.pay Y⊆outN D V (t.rep Y) := by
  classical
  let P Y C := ¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card → C⊆outN D V (sel.rep Y)
  obtain ⟨t,eq,prop⟩ := rebook sel P (by
    intro Y ym
    let X := outN D V (sel.rep Y)
    by_cases dag : QFree D X X.card
    · have used := sel.assigned Y ym
      exact ⟨_,sel.located Y ym,sel.length _ used,sel.rooted _ used,sel.loss _ used,fun no=>(no dag).elim⟩
    have hq := room.1
    have uv := rep_native sel ym
    obtain ⟨C,inX,len,roots⟩ := actual_cycle free (by omega) (outN_subset : X⊆V) dag
    obtain ⟨_,h1,h2,h3,h4,_⟩ := room
    have low := (mem_filter.mp (mem_filter.mp (sel.represents Y ym)).1).2
    have two := low_third_second free hq reg uv h1 h2 h3 h4 low
    have shell := @card_B2 D V (sel.rep Y)
    have initial := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    have order := reg _ uv
    have ext := (card_le_card (exterior_subset_menu free (by omega) uv inX)).trans (card_union_le _ _)
    rw [card_sdiff_of_subset inX] at ext
    change (ball D V (sel.rep Y) 2).card≤2*r+1 at two
    have rr := card_le_card inX
    change C.card≤(outN D V (sel.rep Y)).card at rr
    refine ⟨C,Or.inl inX,len,roots,?_,fun _=>inX⟩
    unfold omissions
    omega)
  refine ⟨t,eq,?_⟩
  rw [eq]
  exact prop

/-- The cyclic-side alternative is at the *unpaid* cycle, on the same graph
as both the incoming claims and all the measured row scores. -/
theorem marked_unpaid {D V q r target} (free : QFree D V q) (reg : OutEq r D V)
    (hr : 0<r) (live : V.Nonempty) (sel : Selection D V q r 3 (3*r))
    (regime : Room q r) (mixed : ShellBankOrders.MixedRoom q r) (size : V.card≤2*(3*r))
    (one : r≤q+2) (fit : r+1<2*(q-1)) (dist : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) (pay : 3*r<4+target) :
    ∃t : Selection D V q r 3 (3*r),t.rep=sel.rep ∧ ∃C∈booked t,shortfall t C (r-q) ∧
    ((∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ ¬QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card) ∨
     ∃Y,claims t C={Y} ∧ QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card ∧ t.pay Y=C ∧ omissions D V C r≤1 ∧
      C.card≤(C.filter (fun v=>3*r<(ball D V v 3).card)).card+(r-C.card)*(r-q) ∧
      (C.filter (fun v=>3*r<(ball D V v 3).card)).card+
        2*(C.filter (fun v=>3*r+1<(ball D V v 3).card)).card≤(r-q+1)*2^(omissions D V C r)) := by
  classical
  obtain ⟨t,eq,primary⟩ := primary_selection free reg sel regime
  have hq := regime.1
  have cap C (cm : C∈booked t) : omissions D V C r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact t.loss _ (t.assigned Y ym)
  obtain ⟨C,cm,bill⟩ := unpaid_stock free (by omega) reg (by omega) (by omega)
    (fun v vm=>by have := ShellBankOrders.mixed_third free mixed reg vm; omega) size live t cap
  refine ⟨t,eq,C,cm,bill,?_⟩
  by_cases primaryUsed : ∃Y∈claims t C,¬QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card
  · obtain ⟨Y,ym,cy⟩ := primaryUsed
    obtain ⟨key,mark⟩ := mem_filter.mp ym
    exact .inl ⟨Y,ym,mark ▸ primary Y key cy,cy⟩
  · push Not at primaryUsed
    obtain ⟨Y,only,more⟩ := unpaid_acyclic free reg hr t cm bill primaryUsed regime one fit dist guard pay
    exact .inr ⟨Y,only,primaryUsed Y (only.symm ▸ mem_singleton_self Y),more⟩

#print axioms marked_unpaid
end LeanCH.BR.LowShellCycleSelection
