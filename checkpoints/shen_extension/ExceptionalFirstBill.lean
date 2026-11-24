import checkpoints.shen_extension.ShortFirstRecovery

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Allow an arbitrary labelled exceptional class to carry extra debt.
Every other first-layer claim costs one unit. The price includes all
secondary classes and uses the actual cross-class receipts. -/
theorem first_exception_budget {D V q r target C special extra} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (policy : ShellBooking t) (off : C∉shortSwitches t)
    (width : r≤(exterior D V C).card) (long : r≤C.card+1)
    (excess : shellDebt D V 3 (3*r) special≤1+extra)
    (single : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → Y≠special → shellDebt D V 3 (3*r) Y≤1) :
    netDebt t C≤3+(extra:ℚ) := by
  classical
  let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
  let J := claims t C\K
  let U := K.image t.rep
  have keys : K⊆claims t C := filter_subset _ _
  have other : J⊆claims t C := sdiff_subset
  have away : Disjoint K J := disjoint_left.mpr (fun _ a b=>(mem_sdiff.mp b).2 a)
  have union : K∪J=claims t C := by
    ext x; simp only [J,mem_union,mem_sdiff]
    exact ⟨fun h=>h.elim (fun k=>keys k) And.left,fun h=>by by_cases m : x∈K; exact .inl m; exact .inr ⟨h,m⟩⟩
  have dag Z (zm : Z∈J) : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card := by
    by_contra cyclic
    have mark := (mem_filter.mp (other zm)).2
    have no : Z∉shortSwitches t := fun z=>off (((policy.secondary Z z).symm.trans mark) ▸ z)
    exact (mem_sdiff.mp zm).2 (mem_filter.mpr ⟨other zm,mark ▸ policy.primary Z (mem_filter.mp (other zm)).1 no cyclic⟩)
  have jbill := cohort_unit_bill free reg t ready other dag
  have combine {i m : ℕ} (ik : ∑Y∈K,shellDebt D V 3 (3*r) Y≤(credits t K).card+i)
      (jm : ∑Y∈J,shellDebt D V 3 (3*r) Y≤(credits t J).card+m) :
      netDebt t C≤(i:ℚ)+m := by simpa [union] using split_bill t keys other away ik jm
  have key Y (ym : Y∈K) := (mem_filter.mp (keys ym)).1
  have data u (um : u∈U) : u∈V ∧ C⊆outN D V u ∧ (outN D V u\C).card≤1 ∧
      (N2 D V u).card≤(exterior D V C).card := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp um
    have uv := rep_native t (key _ ym)
    have f := (mem_filter.mp ym).2
    have size := card_sdiff_of_subset f
    rw [reg _ uv] at size
    have ⟨hq,a,b,c,d,_⟩ := ready.cycle
    have low := (mem_filter.mp (mem_filter.mp (t.represents Y (key _ ym))).1).2
    have next := low_third_second free hq reg uv a b c d low
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at one
    have two := @card_B2 D V (t.rep Y)
    change (ball D V (t.rep Y) 2).card≤2*r+1 at next
    exact ⟨uv,f,by omega,by omega⟩
  have inj : Set.InjOn (N2 D V) (U:Set ℕ) := by
    intro a am b bm eq
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp am
    obtain ⟨Z,zm,rfl⟩ := mem_image.mp bm
    exact congrArg t.rep ((rep_key t (key Y ym)).symm.trans (eq.trans (rep_key t (key Z zm))))
  have count : U.card=K.card := card_image_of_injOn (fun Y ym Z zm eq=>
    (rep_key t (key _ ym)).symm.trans ((congrArg (N2 D V) eq).trans (rep_key t (key _ zm))))
  have ordinary Y (ym : Y∈K.erase special) := single Y (keys (mem_of_mem_erase ym))
    (mem_filter.mp (mem_of_mem_erase ym)).2 (mem_erase.mp ym).1
  have costs := sum_le_sum ordinary
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at costs
  have summed : ∑Y∈K,shellDebt D V 3 (3*r) Y≤U.card+extra := by
    by_cases mem : special∈K
    · have := sum_erase_add K (fun Y=>shellDebt D V 3 (3*r) Y) mem
      rw [card_erase_of_mem mem] at costs
      have := card_pos.mpr (show K.Nonempty from ⟨_,mem⟩)
      omega
    rw [erase_eq_of_notMem mem] at costs
    omega
  have hq := ready.cycle.1
  have alternative := one_slot_price (D:=D) (k:=3) free (by omega) (by omega) (fun u (um : u∈U)=>(data u um).1) inj
    (fun u um=>(data u um).2.1) (fun u um=>(data u um).2.2.1) (fun u um=>(data u um).2.2.2)
  have capU : U.card≤(credits t K).card+2 := by
    rcases alternative with cheap|⟨two,_⟩
    · change U.card≤(credits t K).card+1 at cheap
      omega
    · omega
  have bill := combine (i:=2+extra) (by omega) jbill
  push_cast at bill
  linarith

#print axioms first_exception_budget
end LeanCH.BR.LowShellCycleSelection
