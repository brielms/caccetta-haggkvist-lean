import checkpoints.shen_extension.RemainingPayerEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Count the actual first-layer labels a marked row reaches by the scoring
radius, in addition to the second layer and the later transferred shells. -/
theorem prefix_price {D V u v d k} {A : Finset ℕ} (uv : u∈V)
    (early : A⊆outN D V u) (reached : A⊆ball D V v (d+k))
    (second : N2 D V u⊆ball D V v (d+k)) (third : N3 D V u⊆ball D V v d) :
    A.card+(ball D V u (3+k)).card-(ball D V u 1).card≤(ball D V v (d+k)).card := by
  have prior : A∪N2 D V u⊆ball D V u 2 := union_subset
    (fun _ am=>ball_mono_radius (by decide : 1≤2) (X_B1 (early am))) (fun _ ym=>(mem_N2.mp ym).1)
  have bill := BankReachTransfer.count_with_prefix (j:=2) uv prior (union_subset reached second) third
  rw [card_union_of_disjoint (disjXY.mono_left early)] at bill
  simp only [Nat.reduceAdd] at bill
  have := @card_B2 D V u
  have := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : 2≤3+k))
  omega

/-- On the labelled cycle chosen for the claim, every row can include its
internal ball. A row that reaches a first-layer label outside the cycle
adds that label to the very same count. -/
theorem actual_first_price {D V q r u C} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (hr : 4≤r) (fit : r≤q+2) (first : C⊆outN D V u)
    (len : q<C.card) (roots : ∀v∈C,Rooted D V v C)
    (two : (N2 D V u).card=r-1) (three : (N3 D V u).card=r-1) :
    ∀v∈C, ∀A⊆outN D V u,A⊆ball D V v 3 →
      A.card+(ball D V u 4).card-(ball D V u 1).card≤(ball D V v 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have native v (vm : v∈V) := reg v vm
  have allY := BankReachTransfer.reaches_bank (k:=1) free (by omega) (outN_subset : X⊆V)
    (fun _ (ym : _∈Y)=>N2_subV ym) disjXY (fun v vm=>by rw [reg v vm]; omega)
    (fun v vm=>by rw [←outN_X_eq (free.mono_bound hq) uv vm,reg v (outN_subset vm)]; exact Nat.succ_le_of_lt (by dsimp [Y]; omega))
    (by rw [reg u uv]; omega) (by omega) (by rw [reg u uv]; omega)
  obtain ⟨_,_,_,_,_,_,_,bank,_⟩ := narrow_cycle free hq reg uv fit hr two three
  intro v vm A ax reached
  have outX : (outN D X v).card≤1+(X.card-C.card) := by
    have h : outN D X v⊆outN D C v∪(X\C) := by
      intro a am
      by_cases ac : a∈C
      · exact mem_union_left _ (mem_outN.mpr ⟨ac,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset am,ac⟩)
    exact (card_le_card h).trans ((card_union_le _ _).trans_eq (by rw [(roots v vm).one v vm,card_sdiff_of_subset first]))
  have sizeX : X.card=r := reg u uv
  have n := reg v (outN_subset (first vm))
  rw [outN_X_eq (free.mono_bound hq) uv (first vm),card_outN_union disjXY] at n
  change (outN D X v).card+(outN D Y v).card=r at n
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(outN D Y v).card by omega)
  apply prefix_price (d:=2) (k:=1) uv ax reached
  · intro w wm
    obtain ⟨j,_,jlim,path⟩ := allY v (first vm) w wm
    exact mem_ball.mpr ⟨N2_subV wm,j,by omega,path⟩
  · intro z zm
    have yz : z∈outN D Z y := (bank y (outN_subset ym)).2.symm ▸ zm
    exact ball_step (ball_of_adj (N2_subV (outN_subset ym)) (mem_outN.mp ym).2) (N3_subV zm) (mem_outN.mp yz).2

#print axioms actual_first_price
end LeanCH.BR.LowShellCycleSelection
