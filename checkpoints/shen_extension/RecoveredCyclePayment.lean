import checkpoints.shen_extension.RecoverRoutedStock

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

theorem booked_score_cap {D V q r k b c C allowance} (free : QFree D V q) (reg : OutEq r D V)
    (cut : c+2≤q) (sel : Selection D V q r k b) (cap : ∀H∈booked sel,omissions D V H r≤c)
    (cm : C∈booked sel) (low : rowStock sel (booked sel) C≤(allowance:ℕ)) :
    (∑v∈C,surplus b (ball D V v k).card)≤allowance*((c+1)*2^(omissions D V C r)) := by
  classical
  let d := (c+1)*2^(omissions D V C r)
  let P v := surplus b (ball D V v k).card
  have positive : 0<(d:ℚ) := by dsimp [d]; positivity
  have rooted H (hm : H∈booked sel) : ∀v∈H,Rooted D V v H := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp hm
    exact sel.rooted _ (sel.assigned Y ym)
  have row v (vm : v∈C) : (P v:ℚ)/(d:ℚ) ≤ share D V (booked sel) r (fun a=>(P a:ℚ)) C v := by
    have tc := turns_bound (v:=v) free cut rooted reg cap
    have occ : C∈through (booked sel) v := mem_filter.mpr ⟨cm,vm⟩
    have nz : 0<(turns D (booked sel) v).card := card_pos.mpr ⟨_,mem_image_of_mem _ occ⟩
    unfold share
    rw [←div_eq_mul_one_div,div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    dsimp [d]
    push_cast
    gcongr
    exact_mod_cast tc
  have rsum := sum_le_sum row
  rw [←sum_div] at rsum
  have raw : (∑v∈C,(P v:ℚ))≤(allowance:ℚ)*(d:ℚ) :=
    (div_le_iff₀ positive).mp (rsum.trans low)
  exact_mod_cast raw

/-- A complete secondary bank and its immediate successor give every row of
the old cycle a positive surplus on the original graph. -/
theorem booking_recovers_rows {D V q r target C Y} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target)
    (claim : Y∈claims t C) (dag : QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card)
    (size : C.card+1=r) (ew : (exterior D V C).card=r)
    (zroot : ∀z∈N3 D V (t.rep Y),Rooted D V z (N3 D V (t.rep Y)))
    (outer : (exterior D V (N3 D V (t.rep Y))).card=r-1) :
    ∀c∈C,3*r<(ball D V c 3).card := by
  classical
  let u := t.rep Y
  let Z := N3 D V u
  let E := exterior D V C
  let G := C.filter (fun a=>Z⊆outN D V a)
  obtain ⟨key,id⟩ := mem_filter.mp claim
  have hq := room.cycle.1
  have hr := room.growth.2.1
  have fit := room.close
  have space := room.space
  have uv := rep_native t key
  have ey : N2 D V u=Y := rep_key t key
  have rc := t.rooted _ (t.assigned Y key)
  have len := t.length _ (t.assigned Y key)
  rw [id] at rc len
  have data := claim_data free reg (by omega) t key room.cycle dag fit space room.distance room.score
  rw [id] at data
  have chosen := selected_stock free reg (by omega) t key room.cycle dag (by omega) room.distance room.score
  dsimp only at chosen
  rw [id] at chosen
  obtain ⟨_,zw,rows,_⟩ := chosen
  change Z.card+1=r at zw
  change C.card≤G.card+(r-C.card)*(r-q) at rows
  have diff : r-C.card=1 := by omega
  rw [diff,Nat.one_mul] at rows
  obtain equal|⟨d,except,wide|narrow⟩ := data.single
  · have := data.width; rw [equal] at size; omega
  case inr.inr =>
    have := narrow.1; omega
  have yv : Y⊆V := ey ▸ (fun _ h=>N2_subV h)
  have cv := data.inside.trans yv
  have dm : d∈Y\C := except.symm ▸ mem_singleton_self d
  have back : d∈mutualExterior D V C := (mem_union.mp (wide.2 ▸ (mem_sdiff.mp dm).1)).resolve_left (mem_sdiff.mp dm).2
  obtain ⟨de,⟨c,ce⟩⟩ := mem_filter.mp back
  have ds : d∉Z := fun h=>(mem_N3.mp h).2 (mem_N2.mp (ey.symm ▸ (mem_sdiff.mp dm).1)).1
  obtain ⟨a,am⟩ := card_pos.mp (show 0<G.card by omega)
  have zsub : Z⊆E := by
    intro z zm
    have arc := (mem_filter.mp am).2 zm
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,(mem_filter.mp am).1,arc⟩,fun cm=>
      (mem_N3.mp zm).2 (mem_N2.mp (ey.symm ▸ data.inside cm)).1⟩
  have bank : insert d Z=E := eq_of_subset_of_card_le (insert_subset de zsub)
    (by rw [card_insert_of_notMem ds]; change (exterior D V C).card≤Z.card+1; omega)
  apply restored_rows free (by omega) reg (by omega) fit rc (Z:=Z) (fun _ m=>N3_subV m) (by omega) zroot outer
  · intro a am
    by_contra! miss
    let H := (outN D V a).erase (internalHead D C a)
    have sub : H⊆{d} := by
      intro z hz
      change z∈(outN D V a).erase (internalHead D C a) at hz
      have ze : z∈E := (mem_inter.mp ((row_exterior (rc a am)) ▸ hz)).1
      rcases mem_insert.mp (bank.symm ▸ ze) with eq|zz
      · exact mem_singleton.mpr eq
      · exact False.elim (miss z zz (mem_outN.mp (mem_of_mem_erase hz)).2)
    have small := card_le_card sub
    dsimp only [H] at small
    rw [card_singleton,card_erase_of_mem (outN_mono cv a (successor_mem (rc a am))),reg a (cv am)] at small
    omega
  · intro x xe miss
    have eq := (mem_insert.mp (bank.symm ▸ (show x∈E from xe))).resolve_right miss
    exact ⟨c,(mem_outN.mp ce).1,eq ▸ (mem_outN.mp ce).2⟩

/-- The original cycle can keep and strictly pay one whole unit after its
secondary class is transferred. Its labels and all sharing denominators
come from the original booking. -/
theorem stock_after_secondary {D V q r target C Y} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target)
    (claim : Y∈claims t C) (dag : QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card)
    (size : C.card+1=r) (ew : (exterior D V C).card=r)
    (enough : 2*(r-q+1)<C.card) (afford : 2*(r-q+1)<3*fullRowFloor q r) :
    1<rowStock t (booked t) C := by
  classical
  by_contra! low
  obtain ⟨key,id⟩ := mem_filter.mp claim
  have hr := room.growth.2.1
  have hq := room.cycle.1
  have fit := room.close
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨X,xm,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ xm)
  have cm : C∈booked t := id ▸ mem_image_of_mem t.pay key
  have bound := booked_score_cap free reg (by omega : r-q+2≤q) t scale cm (allowance:=1) (by simpa using low)
  have om : omissions D V C r=1 := by unfold omissions; rw [ew]; omega
  simp only [om,pow_one,Nat.one_mul] at bound
  have tier := tier_stock D V C 3 (3*r)
  have chain := weak_row_chain free reg (by omega) t key dag room.cycle fit room.space room.distance room.score
    room.high room.squeeze room.finite (2*(r-q+1)) (by rw [id]; omega) afford
  rw [id] at chain
  obtain ⟨_,_,_,_,k,_,valid,_⟩ := chain
  have allRows := booking_recovers_rows free reg t room claim dag size ew (valid 0 (by omega)).2 (valid 1 (by omega)).1
  have allCount : C.filter (fun v=>3*r<(ball D V v 3).card)=C := filter_eq_self.mpr allRows
  rw [allCount] at tier
  omega

#print axioms booked_score_cap
#print axioms booking_recovers_rows
#print axioms stock_after_secondary
end LeanCH.BR.LowShellCycleSelection
