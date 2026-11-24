import checkpoints.shen_extension.ExteriorSinkClaims

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

theorem direct_bill_of_one_contact {D V q r C target} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (off : C∉shortSwitches t)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card)
    (excess : 2<netDebt t C) :
    let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
    (contacts D V (K.image t.rep) 3).card≤1 →
      netDebt t C≤3 ∧ (contacts D V (K.image t.rep) 3).Nonempty := by
  classical
  let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
  let J := claims t C\K
  let U := K.image t.rep
  change (contacts D V U 3).card≤1 → netDebt t C≤3 ∧ (contacts D V U 3).Nonempty
  intro one
  have keys : K⊆claims t C := filter_subset _ _
  have other : J⊆claims t C := sdiff_subset
  have apart : Disjoint K J := disjoint_left.mpr (fun _ a b=>(mem_sdiff.mp b).2 a)
  have union : K∪J=claims t C := by
    ext x; simp only [J,mem_union,mem_sdiff]
    exact ⟨fun h=>h.elim (fun k=>keys k) And.left,fun h=>by by_cases m : x∈K; exact .inl m; exact .inr ⟨h,m⟩⟩
  have dag Z (zm : Z∈J) : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card := by
    by_contra cyclic
    have mark := (mem_filter.mp (other zm)).2
    have no : Z∉shortSwitches t := fun z=>off (((policy.secondary Z z).symm.trans mark) ▸ z)
    exact (mem_sdiff.mp zm).2 (mem_filter.mpr ⟨other zm,mark ▸ policy.primary Z (mem_filter.mp (other zm)).1 no cyclic⟩)
  have jbill := cohort_unit_bill free reg t ready other dag
  have key Y (ym : Y∈K) := (mem_filter.mp (keys ym)).1
  have size : U.card=K.card := card_image_of_injOn (fun Y ym Z zm eq=>
    (rep_key t (key Y ym)).symm.trans ((congrArg (N2 D V) eq).trans (rep_key t (key Z zm))))
  have individual Y (ym : Y∈K) : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := t.least Y (key Y ym) v vm
    have hi := medium Y (keys ym) (mem_filter.mp ym).2
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have summed := sum_le_sum individual
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one,←size] at summed
  have uv : U⊆V := by intro u um; obtain ⟨Y,ym,rfl⟩ := mem_image.mp um; exact rep_native t (key Y ym)
  have count := holes_of_contacts (D:=D) (k:=3) uv
  change U.offDiag.card≤(credits t K).card+2*(contacts D V U 3).card at count
  rw [offDiag_card] at count
  have pay (i : ℕ) (room : U.card≤(credits t K).card+i) : netDebt t C≤(i:ℚ)+1 := by
    simpa [union] using split_bill t keys other apart (summed.trans room) jbill
  have enough : U.card≤(credits t K).card+2 := by
    by_cases few : U.card≤2
    · omega
    have := Nat.mul_le_mul_left U.card (show 3≤U.card by omega)
    omega
  refine ⟨by convert pay 2 enough using 1; norm_num,?_⟩
  by_contra! empty
  have zero : (contacts D V U 3).card=0 := by simp [empty]
  have cap : U.card≤(credits t K).card+1 := by
    by_cases few : U.card≤1
    · omega
    have := Nat.mul_le_mul_left U.card (show 2≤U.card by omega)
    omega
  have limit := pay 1 cap
  norm_num at limit
  exact excess.not_ge limit

/-- A complete, direct, unpaid physical cycle has no sink in its exterior
under the displayed narrow-middle capacity and stock comparison. -/
theorem direct_exterior_no_sink {D V q r C target δ cap} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap ∅) (account : CompleteAccount t C ∅)
    (length : C.card+1=r) (long : q<C.card) (enough : 2*(r-q+1)<C.card)
    (capacity : (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14)
    (reserve : r-q+1<3*q+3-2*r) : ∀e∈exterior D V C,∃a∈exterior D V C,D e a=true := by
  classical
  intro e ee
  by_contra! sink
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have roots : ∀v∈C,Rooted D V v C := by
    obtain ⟨Y,ym,eq⟩ := mem_image.mp mark.bookedHere
    exact eq ▸ t.rooted _ (t.assigned _ ym)
  have noarc a (am : a∈exterior D V C) : D e a≠true := by simpa using sink a am
  obtain ⟨off,medium⟩ := sink_claim_shapes free reg t ready account length long roots ee noarc
  obtain ⟨one,id⟩ := sink_account_contacts free reg t ready account length ee noarc
  obtain ⟨bill,edge,em⟩ := direct_bill_of_one_contact free reg t policy ready off medium (account.direct rfl 2 enough) one
  have matchY := id edge em
  have source := (mem_offDiag.mp (mem_filter.mp em).1).1
  obtain ⟨Y,ym,eq⟩ := mem_image.mp source
  rw [←eq] at matchY
  obtain ⟨claim,first⟩ := mem_filter.mp ym
  have key := (mem_filter.mp claim).1
  have uv := rep_native t key
  have low := (mem_filter.mp (mem_filter.mp (t.represents Y key)).1).2
  have hi := medium Y claim first
  have width := account.width
  have ys : (N2 D V (t.rep Y)).card=r-1 := (congrArg card matchY).trans width
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have b2 := @card_B2 D V (t.rep Y)
  have b3 := @card_B3 D V (t.rep Y)
  have zs : (N3 D V (t.rep Y)).card=r := by omega
  have room := ready.space
  obtain ⟨rows,paid⟩ := actual_narrow_middle free hq reg uv fit hr (by omega) ys zs capacity first long roots
  let L := C.filter (fun x=>(outN D (outN D V (t.rep Y)) x).card=1)
  have per x (xm : x∈L) : 3≤surplus (3*r) (ball D V x 3).card := by
    have := paid x (mem_filter.mp xm).1 (mem_filter.mp xm).2
    simp [surplus,show 3*r<(ball D V x 3).card by omega]; omega
  have summed := sum_le_sum per
  simp only [sum_const_nat (fun _ _=>rfl)] at summed
  have sub : ∑v∈L,surplus (3*r) (ball D V v 3).card≤∑v∈C,surplus (3*r) (ball D V v 3).card :=
    sum_le_sum_of_subset (filter_subset _ _)
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Z,zk,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ zk)
  have due := mark.due
  rw [sum_empty,add_zero] at due
  have cap' := booked_score_cap free reg (by omega : r-q+2≤q) t scale mark.bookedHere (allowance:=3) (due.trans bill)
  have om : omissions D V C r=0 := by unfold omissions; rw [width]; omega
  rw [om,pow_zero,Nat.mul_one] at cap'
  change 3*q+3-2*r≤L.card at rows
  omega

attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,account,length,long,enough,capacity,reserve]) (rule_sets := [CHGraphFamilies])] direct_exterior_no_sink
#print axioms direct_bill_of_one_contact
#print axioms direct_exterior_no_sink
end LeanCH.BR.LowShellCycleSelection
