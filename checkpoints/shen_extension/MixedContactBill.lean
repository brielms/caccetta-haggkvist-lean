import checkpoints.shen_extension.CohortBalance

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- The two-unit exceptional bill in a class of unit claims needs exactly
two origins, with one actually the unique private head of the other. -/
theorem one_slot_price {D V q k C U} (free : QFree D V q) (hq : 4≤q) (time : k+1≤q)
    (sub : U⊆V) (unique : Set.InjOn (N2 D V) (U : Set ℕ)) (first : ∀u∈U,C⊆outN D V u)
    (slots : ∀u∈U,(outN D V u\C).card≤1)
    (width : ∀u∈U,(N2 D V u).card≤(exterior D V C).card) :
    let H := U.offDiag∩DotClonePairCompletion.orderedIncomparable D V k
    U.card≤H.card+1 ∨ (U.card=2 ∧ H=∅ ∧ ∃a∈U,∃b∈U,a≠b ∧
      privateHeads D V C a={b} ∧ N2 D V a=exterior D V C) := by
  classical
  dsimp only
  let H := U.offDiag∩DotClonePairCompletion.orderedIncomparable D V k
  by_cases ordinary : U.card≤H.card+1
  · exact .inl ordinary
  have bound := at_most_one_contact free hq sub unique first slots width time
  have holes := holes_of_contacts (D:=D) (k:=k) sub
  change U.offDiag.card ≤ H.card+2*(contacts D V U k).card at holes
  rw [offDiag_card] at holes
  have two : U.card=2 := by
    by_contra no
    have m := Nat.mul_le_mul_left U.card (show 3≤U.card by omega)
    omega
  rw [two] at holes
  have zero : H=∅ := card_eq_zero.mp (by omega)
  obtain ⟨⟨a,b⟩,pair⟩ := card_pos.mp (show 0<(contacts D V U k).card by omega)
  obtain ⟨ab,hit⟩ := mem_filter.mp pair
  obtain ⟨am,bm,ne⟩ := mem_offDiag.mp ab
  exact .inr ⟨two,zero,a,am,b,bm,ne,single_slot_collision free hq (sub am) ne (first a am) (first b bm)
    (slots _ am) (width _ am) time hit⟩

/-- Combine primary and secondary receipts on the same booking. Above the
ordinary two-unit bill there is a named directed contact on precisely two
first-layer representatives and an additional acyclic claimant. -/
theorem mixed_contact_bill {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (policy : ShellBooking t) (off : C∉shortSwitches t)
    (width : r≤(exterior D V C).card) (long : r≤C.card+1)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card) :
    let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
    netDebt t C≤3 ∧ (netDebt t C≤2 ∨
      ((K.image t.rep).card=2 ∧ ∃a∈K.image t.rep,∃b∈K.image t.rep,a≠b ∧
        privateHeads D V C a={b} ∧ N2 D V a=exterior D V C ∧
        ∃Z∈claims t C\K,QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)) := by
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
  have individual Y (ym : Y∈K) : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := t.least Y (key Y ym) v vm
    have hi := medium Y (keys ym) (mem_filter.mp ym).2
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have summed := sum_le_sum individual
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one,←count] at summed
  have hq := ready.cycle.1
  have alternative := one_slot_price (D:=D) (k:=3) free (by omega) (by omega) (fun u (um : u∈U)=>(data u um).1) inj
    (fun u um=>(data u um).2.1) (fun u um=>(data u um).2.2.1) (fun u um=>(data u um).2.2.2)
  rcases alternative with ordinary|⟨two,_empty,a,am,b,bm,ne,privateArc,same⟩
  · have v := combine (summed.trans ordinary) jbill
    norm_num at v
    exact ⟨by linarith,Or.inl v⟩
  · have ik : (∑Y∈K,shellDebt D V 3 (3*r) Y)≤(credits t K).card+2 := by omega
    have v := combine ik jbill
    norm_num at v
    refine ⟨v,?_⟩
    rcases J.eq_empty_or_nonempty with empty|⟨Z,zm⟩
    · have paid := combine ik (m:=0) (by simp [empty])
      norm_num at paid
      exact .inl paid
    · exact .inr ⟨two,a,am,b,bm,ne,privateArc,same,Z,zm,dag Z zm⟩

#print axioms one_slot_price
#print axioms mixed_contact_bill
end LeanCH.BR.LowShellCycleSelection
