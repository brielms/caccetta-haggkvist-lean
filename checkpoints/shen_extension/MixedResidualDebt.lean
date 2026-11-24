import checkpoints.shen_extension.MixedClaimTransfer

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Once the individual secondary charge is withdrawn, at most one
unit remains at the physical source cycle. An acyclic claimant identifies
every other secondary class by its literal second shell, even when its own
charge is zero. -/
theorem residual_after_transfer {D V q r target C Z} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (policy : ShellBooking t) (width : (exterior D V C).card=r) (size : C.card+1=r)
    (zm : Z∈claims t C) (dag : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card) :
    netDebt t C-(shellDebt D V 3 (3*r) Z:ℚ)≤1 := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have off : C∉shortSwitches t := by
    intro sw; have := (switched_shell_paid free reg t (by omega) hr fit sw).1.width; omega
  let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
  let U := ((claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))).image t.rep
  have info v (vm : v∈U) : v∈V ∧ C⊆outN D V v ∧ (outN D V v\C).card≤1 ∧
      (N2 D V v).card≤r ∧ (ball D V v 3).card=3*r := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp vm
    obtain ⟨ycl,first⟩ := mem_filter.mp ym
    have key := (mem_filter.mp ycl).1
    have uv := rep_native t key
    have debt := (mem_filter.mp (mem_filter.mp (t.represents _ key)).1).2
    have med := medium Y ycl first
    have ⟨hq,a,b,c,d,_⟩ := ready.cycle
    have bound := low_third_second free hq reg uv a b c d debt
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at one
    have two := @card_B2 D V (t.rep Y)
    change (ball D V (t.rep Y) 2).card≤2*r+1 at bound
    have rest := card_sdiff_of_subset first
    rw [reg _ uv] at rest
    exact ⟨uv,first,by omega,by omega,le_antisymm debt med⟩

  obtain ⟨d,de,_,sealed,guard⟩ := guarded_exception free reg t ready zm dag size width
  have noContact : contacts D V U 3=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨a,b⟩ pair
    obtain ⟨ab,hit⟩ := mem_filter.mp pair
    obtain ⟨am,bm,ne⟩ := mem_offDiag.mp ab
    have ⟨av,first,slots,_,eqA⟩ := info a am
    have ⟨bv,also,other,b2,eqB⟩ := info b bm
    obtain ⟨privateB,same⟩ := single_slot_collision free (by omega) av ne first also slots
      ((info a am).2.2.2.1.trans_eq width.symm) (by omega) hit
    have := contact_through_exception free (by omega) reg av bv first also privateB same slots other b2 de
      sealed guard (by decide : 2≤3) (by omega)
    omega
  have other Y (ym : Y∈claims t C) (cy : QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card) :
      Y=C∪mutualExterior D V C := by
    have fact := claim_data free reg (by omega) t (mem_filter.mp ym).1 ready.cycle cy ready.close
      ready.space ready.distance ready.score
    rw [(mem_filter.mp ym).2] at fact
    rcases fact.single with eq|⟨d,ex,wide|narrow⟩
    · have := fact.width; rw [eq] at size; omega
    · exact wide.2
    · have := narrow.1; omega
  have diff : claims t C\K={Z} := by
    apply eq_singleton_iff_unique_mem.mpr
    have zc := (claim_data free reg (by omega) t (mem_filter.mp zm).1 ready.cycle dag ready.close
      ready.space ready.distance ready.score).inside
    rw [(mem_filter.mp zm).2] at zc
    have notFirst : Z∉K := by
      intro first
      obtain ⟨x,xm⟩ := card_pos.mp (by omega : 0<C.card)
      have y := (rep_key t (mem_filter.mp zm).1).symm ▸ zc xm
      exact (mem_N2.mp y).2 (X_B1 ((mem_filter.mp first).2 xm))
    refine ⟨mem_sdiff.mpr ⟨zm,notFirst⟩,?_⟩
    intro Y ym
    have key := (mem_filter.mp (mem_sdiff.mp ym).1).1
    have id := (mem_filter.mp (mem_sdiff.mp ym).1).2
    have never : Y∉shortSwitches t := fun sw=>off (((policy.secondary Y sw).symm.trans id) ▸ sw)
    have acyclic : QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card := by
      by_contra cy
      exact (mem_sdiff.mp ym).2 (mem_filter.mpr ⟨(mem_sdiff.mp ym).1,id ▸ policy.primary Y key never cy⟩)
    exact (other Y (mem_sdiff.mp ym).1 acyclic).trans (other Z zm dag).symm
  have keys : K⊆claims t C := filter_subset _ _
  have cards : U.card=K.card := card_image_of_injOn (fun a am b bm eq=>
    (rep_key t (mem_filter.mp (keys am)).1).symm.trans ((congrArg (N2 D V) eq).trans (rep_key t (mem_filter.mp (keys bm)).1)))
  have holes := holes_of_contacts (D:=D) (k:=3) (fun u (um : u∈U)=>(info u um).1)
  simp only [noContact,card_empty,mul_zero,add_zero] at holes
  have payable : K.card≤(credits t K).card+1 := by
    change U.offDiag.card≤(credits t K).card at holes
    rw [offDiag_card,cards] at holes
    by_cases little : K.card≤1
    · omega
    have := Nat.mul_le_mul_left K.card (show 2≤K.card by omega)
    omega
  have belongs : credits t K⊆receipts t C := by
    intro e em
    obtain ⟨ab,missing⟩ := mem_inter.mp em
    obtain ⟨a,b,ne⟩ := mem_offDiag.mp ab
    exact mem_inter.mpr ⟨mem_offDiag.mpr ⟨image_subset_image keys a,image_subset_image keys b,ne⟩,missing⟩
  have individual Y (ym : Y∈K) : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := t.least Y (mem_filter.mp (keys ym)).1 v vm
    have med := medium Y (keys ym) (mem_filter.mp ym).2
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have total := sum_le_sum individual
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at total
  have limit := card_le_card belongs
  have bound : ∑Y∈K,(shellDebt D V 3 (3*r) Y:ℚ)≤(receipts t C).card+1 := by
    exact_mod_cast (show ∑Y∈K,shellDebt D V 3 (3*r) Y≤(receipts t C).card+1 by omega)
  have combined := sum_sdiff keys (f:=fun Y=>(shellDebt D V 3 (3*r) Y:ℚ))
  rw [diff,sum_singleton] at combined
  unfold netDebt
  linarith only [bound,combined]

#print axioms residual_after_transfer
end LeanCH.BR.LowShellCycleSelection
