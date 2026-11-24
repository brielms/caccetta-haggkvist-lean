import checkpoints.shen_extension.MarkedCycleDeficit
import checkpoints.shen_extension.PhysicalCycleStockChain

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- Exclude every proposed first-neighborhood size at or above lo from an
upper bound on the next neighborhood. Both sizes and the marked bank are free. -/
def CompressionRoom (q r z lo top : ℕ) : Prop :=
  ∀h∈Icc lo top,(∃d∈Icc 2 5,h≤q*d ∧ top+d≤r+h) ∨
    (top+2≤r+h ∧ h*(h+1)<z*(2*(r+4))+(h-z)*14)

instance {q r z lo top} : Decidable (CompressionRoom q r z lo top) := by
  unfold CompressionRoom; infer_instance

theorem compressed_first {D V q r Z lo top} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (zv : Z⊆V) (live : Z.Nonempty) (fit : r+2≤2*q)
    (tight : (neighborhood D V Z 2).card≤top) (room : CompressionRoom q r Z.card lo top) :
    (neighborhood D V Z 1).card<lo := by
  classical
  let H := neighborhood D V Z 1
  let T := neighborhood D V Z 2
  have zh : Z⊆H := fun a am=>mem_biUnion.mpr ⟨a,am,self_mem_ball (zv am)⟩
  have ht : H⊆T := by
    intro x xm; obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm
    exact mem_biUnion.mpr ⟨a,am,ball_mono_radius (by decide : 1≤2) hit⟩
  have hv : H⊆V := by intro x xm; obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm; exact ball_subset hit
  have heads x (xm : x∈H) : outN D V x⊆outN D H x∪(T\H) := by
    intro v vm
    by_cases inside : v∈H
    · exact mem_union_left _ (mem_outN.mpr ⟨inside,(mem_outN.mp vm).2⟩)
    obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm
    exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,am,ball_step hit (outN_subset vm) (mem_outN.mp vm).2⟩,inside⟩)
  have retained x (xm : x∈H) : r≤(outN D H x).card+(T.card-H.card) := by
    have cap := (card_le_card (heads x xm)).trans (card_union_le _ _)
    rwa [reg x (hv xm),card_sdiff_of_subset ht] at cap
  have full z (zm : z∈Z) : r≤(outN D H z).card := by
    rw [←reg z (zv zm)]
    exact card_le_card (fun v vm=>mem_outN.mpr ⟨mem_biUnion.mpr ⟨z,zm,ball_of_adj (outN_subset vm) (mem_outN.mp vm).2⟩,
      (mem_outN.mp vm).2⟩)
  have limit : T.card≤top := tight
  have subset := card_le_card ht
  by_contra! failed
  rcases room H.card (mem_Icc.mpr ⟨failed,by omega⟩) with ⟨d,mem,demand,inc⟩|⟨inc,demand⟩
  · obtain ⟨low,high⟩ := mem_Icc.mp mem
    have := BRq6.lower_order (by omega : 5≤q) low (by omega : d<6) (free.mono_set hv)
      (fun x xm=>by have := retained x xm; omega) (live.mono zh)
    omega
  · have quota x (xm : x∈H) : 2≤(outN D H x).card := by have := retained x xm; omega
    have bill := RetainedMixedCapacity.mixed_capacity (i:=3) (j:=3) (base:=14) (high:=2*(r+4))
      (free.mono_set hv) (by omega) zh
      (fun x xm=>by have := ball_growth q (by omega) D H (free.mono_set hv) quota x xm 3 (by omega); omega)
      (fun x xm=>by have := FullRowEscape.high_third (free.mono_set hv) (by omega) quota (zh xm) (full x xm) fit; omega)
    omega

theorem first_neighborhood {D V Z} (zv : Z⊆V) :
    neighborhood D V Z 1=Z∪exterior D V Z := by
  classical
  ext v
  constructor
  · intro vm
    obtain ⟨a,am,hit⟩ := mem_biUnion.mp vm
    obtain eq|arc := (mem_ball_one (zv am)).mp hit
    · exact mem_union_left _ (eq ▸ am)
    · by_cases old : v∈Z
      · exact mem_union_left _ old
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,am,arc⟩,old⟩)
  · intro vm
    rcases mem_union.mp vm with am|om
    · exact mem_biUnion.mpr ⟨v,am,self_mem_ball (zv am)⟩
    obtain ⟨a,am,arc⟩ := mem_biUnion.mp (mem_sdiff.mp om).1
    exact mem_biUnion.mpr ⟨a,am,ball_of_adj (outN_subset arc) (mem_outN.mp arc).2⟩

theorem short_exterior {D V q r Z} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (zv : Z⊆V) (small : Z.card≤q+1) (live : Z.Nonempty) (cap : (exterior D V Z).card≤r-1)
    (hr : 1≤r) :
    (exterior D V Z).card=r-1 ∧ ∀z∈Z,Rooted D V z Z := by
  have row z (zm : z∈Z) : r≤(outN D Z z).card+(exterior D V Z).card := by
    rw [←reg z (zv zm)]
    apply le_trans (card_le_card ?_) (card_union_le _ _)
    intro a am
    by_cases inside : a∈Z
    · exact mem_union_left _ (mem_outN.mpr ⟨inside,(mem_outN.mp am).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨z,zm,am⟩,inside⟩)
  have rooted a (am : a∈Z) := ShellCycleSupply.rooted_on_small_set free (by omega) zv small
    (fun z zm=>by have := row z zm; omega) am
  obtain ⟨z,zm⟩ := live
  have bill := row z zm
  rw [(rooted z zm).one z zm] at bill
  exact ⟨by omega,rooted⟩

theorem bank_chain {D V q r Z} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V) (hr : 2≤r)
    (fit : r≤q+2) (zv : Z⊆V) (size : Z.card=r-1)
    (tight : (neighborhood D V Z 2).card≤3*Z.card)
    (guard : CompressionRoom q r Z.card (2*Z.card+1) (3*Z.card)) :
    (exterior D V Z).card=r-1 ∧ (exterior D V (exterior D V Z)).card=r-1 ∧
    (∀z∈Z,Rooted D V z Z) ∧ ∀w∈exterior D V Z,Rooted D V w (exterior D V Z) := by
  classical
  let W := exterior D V Z
  let T := exterior D V W
  have live : Z.Nonempty := card_pos.mp (by omega)
  have c := compressed_first free hq reg zv live (by omega) tight guard
  rw [first_neighborhood zv,card_union_of_disjoint (show Disjoint Z W from
    disjoint_left.mpr (fun _ a b=>(mem_sdiff.mp b).2 a))] at c
  have ⟨wNum,zz⟩ := short_exterior free (by omega) reg zv (by omega) live (by change W.card≤r-1; omega) (by omega)
  have wn : W.card=r-1 := wNum
  have edge z (zm : z∈Z) w (wm : w∈W) : D z w=true := by
    have m := (complete_row (zz z zm) (reg z (zv zm)) wNum).symm ▸ (show w∈exterior D V Z from wm)
    exact (mem_outN.mp (mem_of_mem_erase m)).2
  have wv : W⊆V := by intro w wm; obtain ⟨a,am,aw⟩ := mem_biUnion.mp (mem_sdiff.mp wm).1; exact outN_subset aw
  have dis : Disjoint (Z∪W) T := by
    apply disjoint_left.mpr
    intro a old ext
    obtain ⟨w,wm,wa⟩ := mem_biUnion.mp (mem_sdiff.mp ext).1
    rcases mem_union.mp old with za|wa'
    · exact digonfree free (by omega) (zv za) (wv wm) (edge a za w wm) (mem_outN.mp wa).2
    · exact (mem_sdiff.mp ext).2 wa'
  have seen : Z∪W∪T⊆neighborhood D V Z 2 := by
    intro x xm
    obtain ⟨z,zm⟩ := live
    rcases mem_union.mp xm with prev|far
    · rcases mem_union.mp prev with xz|xw
      · exact mem_biUnion.mpr ⟨x,xz,self_mem_ball (zv xz)⟩
      · exact mem_biUnion.mpr ⟨z,zm,ball_mono_radius (by decide : 1≤2) (ball_of_adj (wv xw) (edge z zm x xw))⟩
    obtain ⟨w,wm,wx⟩ := mem_biUnion.mp (mem_sdiff.mp far).1
    exact mem_biUnion.mpr ⟨z,zm,ball_step (ball_of_adj (wv wm) (edge z zm w wm)) (outN_subset wx) (mem_outN.mp wx).2⟩
  have lim := (card_le_card seen).trans tight
  rw [card_union_of_disjoint dis,card_union_of_disjoint (show Disjoint Z W from
    disjoint_left.mpr (fun _ a b=>(mem_sdiff.mp b).2 a))] at lim
  have ⟨tn,ww⟩ := short_exterior free (by omega) reg wv (by omega) (card_pos.mp (by omega)) (by change T.card≤r-1; omega) (by omega)
  exact ⟨wNum,tn,zz,ww⟩


/-- A weak row of the unpaid secondary cycle sees the entire third shell in
one step. Its own three-ball caps the two-step neighborhood of that shell. -/
theorem weak_row_chain {D V q r target Y} (free : QFree D V q) (reg : OutEq r D V)
    (hr : 2≤r) (sel : Selection D V q r 3 (3*r)) (ym : Y∈classes D V 3 (3*r))
    (dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (room : Room q r) (fit : r≤q+2) (close : r+1<2*(q-1)) (dist : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) (way : 3*r<4+target)
    (squeeze : CompressionRoom q r (r-1) (2*(r-1)+1) (3*(r-1)))
    (order : V.card<(q+1)*(r-1)) (budget : ℕ)
    (price : let C := sel.pay Y
             (C.filter (fun v=>3*r<(ball D V v 3).card)).card+
             2*(C.filter (fun v=>3*r+1<(ball D V v 3).card)).card≤budget)
    (afford : budget<3*((q+1)-(r-(q+1))*(r-q))) :
    let C := sel.pay Y
    let Z := N3 D V (sel.rep Y)
    let B := bankIteration D V Z
    ∃v∈C,Z⊆outN D V v ∧ (ball D V v 3).card=3*r+1 ∧ ∃k,k+2≤q ∧
      (∀j≤k+1,(B j).card=r-1 ∧ ∀x∈B j,Rooted D V x (B j)) ∧
      ∀x∈B k,3*r+2≤(ball D V x 3).card := by
  classical
  let C := sel.pay Y
  let Z := N3 D V (sel.rep Y)
  let G := C.filter (fun v=>Z⊆outN D V v)
  let H := C.filter (fun v=>3*r<(ball D V v 3).card)
  let S := C.filter (fun v=>3*r+1<(ball D V v 3).card)
  have props := selected_stock free reg (by omega) sel ym room dag (by omega) dist guard
  dsimp only at props
  obtain ⟨_,sz,nfull,high⟩ := props
  change C.card≤G.card+(r-C.card)*(r-q) at nfull
  change ∀v∈G,4+target≤(ball D V v 3).card at high
  change H.card+2*S.card≤budget at price
  have root := sel.rooted _ (sel.assigned Y ym)
  have cc : q<C.card := sel.length _ (sel.assigned Y ym)
  have delta := Nat.mul_le_mul_right (r-q) (show r-C.card≤r-(q+1) by omega)
  have gh : G⊆H := fun v vm=>mem_filter.mpr ⟨(mem_filter.mp vm).1,way.trans_le (high v vm)⟩
  have low : ∃v∈G,v∉S := by
    by_contra! no
    have s := card_le_card (show G⊆S from fun v vm=>no v vm)
    have h := card_le_card gh
    omega
  obtain ⟨v,vm,weak⟩ := low
  have exactScore : (ball D V v 3).card=3*r+1 := by
    have too : ¬3*r+1<(ball D V v 3).card := fun h=>weak (mem_filter.mpr ⟨(mem_filter.mp vm).1,h⟩)
    have hi := (mem_filter.mp (gh vm)).2
    omega
  have hq := room.1
  have cap := score_from_bank (m:=(r-C.card)*(r-q)) free (sel.sub _ (sel.assigned Y ym))
    (fun _ m=>N3_subV m) (fun x xm=>(root x xm).one x xm |>.ge)
    (by omega) (by omega) (mem_filter.mp vm).1 (mem_filter.mp vm).2 nfull (le_refl (neighborhood D V Z 2).card)
  have size : Z.card=r-1 := by change Z.card+1=r at sz; omega
  have guard' : CompressionRoom q r Z.card (2*Z.card+1) (3*Z.card) := size ▸ squeeze
  have ⟨b,c,rz,rw⟩ := bank_chain (Z:=Z) free hq reg hr fit (fun _ m=>N3_subV m) size (by omega) guard'
  exact ⟨v,(mem_filter.mp vm).1,(mem_filter.mp vm).2,exactScore,
    exclusive_terminal free (by omega) hr fit reg order size b c rz rw⟩

#print axioms weak_row_chain

#print axioms bank_chain
end LeanCH.BR.LowShellCycleSelection
