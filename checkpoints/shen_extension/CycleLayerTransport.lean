import checkpoints.shen_extension.SecondaryCycleCohort
import checkpoints.shen_extension.PhysicalCycleStockAnchors
import checkpoints.shen_extension.RetainedLayerOrders
namespace LeanCH.BR.CycleLayerTransport
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking ShellCycleSupply BankReachTransfer RetainedLayerCapacity

/-- At a cyclic first layer, its marked row reaches both whole later banks in
two steps. Its cycle vertices and the second bank are disjoint, and its
later reach contains each actual subsequent layer of the original root. -/
theorem transfer {D V q r u w k} (free : QFree D V q) (hq : 4≤q) (hr : 5≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (uv : u∈V)
    (ys : (N2 D V u).card=r) (zs : (N3 D V u).card+1=r)
    (cr : Rooted D V w (outN D V u)) (time : k+3≤q) :
    (k+3)+r+((ball D V u (k+3)).card-(ball D V u 2).card)≤(ball D V w (k+2)).card := by
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have wm : w∈X := cr.root
  have bank := EqualShellEscape.flat_exit free hq hr fit reg uv ys zs
  have sumY : (outN D Y w).card+1=r := by
    have degree := reg w (xv wm)
    rw [outN_X_eq (free.mono_bound hq) uv wm,card_outN_union disjXY,cr.one w wm] at degree
    change 1+(outN D Y w).card=r at degree
    omega
  have pos y (ym : y∈Y) : 1≤(outN D Y y).card := by
    have sub : outN D V y⊆outN D Y y∪Z := by
      intro a am
      rcases mem_union.mp ((bank y ym).1 am) with first|second
      · exact mem_union_left _ (mem_outN.mpr ⟨first,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ second
    have h := (card_le_card sub).trans (card_union_le _ _)
    rw [reg y (yv ym)] at h
    change Z.card+1=r at zs
    omega
  have size : Y.card=q+1 := by
    have hi : Y.card≤q+1 := ys.le.trans fit
    by_contra! ne
    obtain ⟨y,ym,sink⟩ := exists_sink (free.mono_set yv) (card_pos.mp (show 0<Y.card by change Y.card=r at ys; omega)) (by omega)
    obtain ⟨a,am⟩ := card_pos.mp (pos y ym)
    exact sink a (outN_subset am) (mem_outN.mp am).2
  have inward := (dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (free.mono_set yv) pos
    (show Y.card=q*1+1 by omega)).2
  have reachY : Y⊆ball D V w 2 := by
    intro y ym
    by_cases seen : y∈outN D Y w
    · exact ball_mono_radius (by decide : 1≤2) (ball_of_adj (yv ym) (mem_outN.mp seen).2)
    have row : outN D Y w=Y.erase y := eq_of_subset_of_card_le (fun a am=>mem_erase.mpr
      ⟨fun eq=>seen (eq ▸ am),outN_subset am⟩) (by rw [card_erase_of_mem ym]; change Y.card=r at ys; omega)
    obtain ⟨a,am⟩ := card_pos.mp (show 0<(inN D Y y).card by rw [inward y ym]; decide)
    obtain ⟨ay,arc⟩ := mem_inN.mp am
    have ne : a≠y := by rintro rfl; exact loopfree free (by omega) (yv ay) arc
    have hit : a∈outN D Y w := row.symm ▸ mem_erase.mpr ⟨ne,ay⟩
    exact ball_step (ball_of_adj (yv ay) (mem_outN.mp hit).2) (yv ym) arc
  obtain ⟨y,hit⟩ := card_pos.mp (show 0<(outN D Y w).card by omega)
  have reachZ : Z⊆ball D V w 2 := fun z zm=>ball_step (ball_of_adj (yv (outN_subset hit)) (mem_outN.mp hit).2)
    (N3_subV zm) ((bank y (outN_subset hit)).2 z zm)
  let A := ball D X w (2+k) ∪ Y
  have sub : A⊆ball D V u 2 := union_subset
    (fun _ h=>ball_mono_radius (by decide : 1≤2) (X_B1 (ball_subset h))) (fun _ h=>(mem_N2.mp h).1)
  have inside : A⊆ball D V w (2+k) := union_subset (lift_ball xv) (reachY.trans (ball_mono_radius (by omega)))
  have result := count_with_prefix (j:=2) (d:=2) (k:=k) uv sub inside reachZ
  have card : A.card=(ball D X w (2+k)).card+Y.card := card_union_of_disjoint (disjXY.mono_left ball_subset)
  have growth := ball_one_growth (free.mono_set xv) (fun a am=>(cr.one a am).ge) wm (2+k) (show 2+k+1≤q by omega)
  change Y.card=r at ys
  rw [show 2+1+k=k+3 by omega,show 2+k=k+2 by omega] at result
  omega

/-- If the fifth ball misses the requested threshold, its complement inside
the fifth shell leaves rank d in the punctured fourth ball. The same first
heads are fully credited with their native third balls. -/
theorem fifth {D V q r u d target bound} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (root : u∈V) (smallRank : d=2 ∨ d=3) (cut : r-1≤q)
    (pos : 2*d≤r) (room : target+d≤(ball D V u 4).card+r+1)
    (near : ∀x∈V,2*r≤(ball D V x 2).card)
    (first : ∀x∈outN D V u,bound≤(ball D V x 3).card)
    (capacity :
      let a := (ball D V u 2).card-1
      let b := (ball D V u 3).card-1
      let m := (ball D V u 4).card-1
      m*(m+1)<(m-b)*(2*(3*d+1))+(b-a)*(2*(r+2*d))+(a-r)*(4*r)+r*(2*bound)) :
    target≤(ball D V u 5).card := by
  by_contra! bad
  have count := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 4≤5))
  have firstBall := erase_ball_one_eq_outN free (by omega) root
  have sum : r*(2*bound)≤∑x∈(ball D V u 1).erase u, 2*(ball D V x 3).card := by
    rw [firstBall, ←reg u root]
    simpa only [sum_const_nat (fun _ _=>rfl)] using (sum_le_sum (s:=outN D V u)
      (fun x xm=>Nat.mul_le_mul_left 2 (first x xm)))
  have bill := PhysicalCycleStock.fifth_prefix_budget (d:=d) (base:=2*(3*d+1)) (full:=2*(r+2*d))
    free hq root (fun x xm=>(reg x xm).ge) (by omega) (fun x xm=>near x (ball_subset (mem_of_mem_erase xm))) sum
    (fun W ff ranks x xm=>by
      have base : 3*d+1≤(ball D W x 3).card := by
        rcases smallRank with rfl|rfl
        · have := ball_growth q (by omega) D W ff ranks x xm 3 (by omega); omega
        · exact ball_of_min (BRq3.ball_all 4 (by decide)) (ff.mono_bound (by omega)) ranks x xm
      refine ⟨by omega,?_⟩
      intro full
      have high := high_row_ball_three_min (by omega : 2≤d) (show 2*d≤(r-1)+1 by omega)
        (ff.mono_bound cut) ranks xm (show r-1+1≤(outN D W x).card by omega)
      omega)
  dsimp only at bill capacity
  simp only [card_erase_of_mem (self_mem_ball root)] at bill
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) root
  rw [reg u root] at one
  rw [one] at bill
  simp only [Nat.add_sub_cancel] at bill
  have same : 2*(2*r)=4*r := by omega
  rw [same] at bill
  omega
theorem fourth {D V q r u d target} (free : QFree D V q) (hq : 7≤q)
    (reg : OutEq r D V) (root : u∈V) (smallRank : d=2 ∨ d=3) (cut : r-1≤q)
    (enough : 6≤r) (room : target+d≤(ball D V u 3).card+r+1)
    (near : ∀x∈V,2*r≤(ball D V x 2).card)
    (capacity :
      let a := (ball D V u 2).card-1
      let m := (ball D V u 3).card-1
      let full := if d=2 then 2*r+10 else 2*(r+2*d)
      m*(m+1)<(m-a)*(7*d+2)+(a-r)*full+r*(4*r)) :
    target≤(ball D V u 4).card := by
  by_contra! missing
  let full := if d=2 then 2*r+10 else 2*(r+2*d)
  have delta := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  have cap := prefix_three_scores (k:=3) (a:=2) (b:=1) (j:=2) (i:=3) (l:=4)
    (h:=2*r) (near:=4*r) (base:=7*d+2) (high:=full) free root (by omega) (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun v vm=>(reg v vm).ge)
    (show d+(ball D V u 4\ball D V u 3).card≤r by omega)
    (fun x xm=>near x (ball_subset (mem_of_mem_erase xm))) (by omega) (fun W ff rr x xm=>by
      rcases smallRank with rfl|rfl
      · have grow := ball_growth q (by omega) D W ff rr x xm
        refine ⟨by have := grow 3 (by omega); have := grow 4 (by omega); omega,?_⟩
        intro hx
        have a := high_row_ball_three_min (by decide : 2≤2) (show 2*2≤(r-1)+1 by omega)
          (ff.mono_bound cut) rr xm (show r-1+1≤_ by omega)
        have b := high_two_ball_four (show 5≤r-1 by omega) (ff.mono_bound cut) rr xm (show r-1+1≤_ by omega)
        simp only [full,ite_true] 
        omega
      · have a := ball_of_min (BRq3.ball_all 4 (by decide)) (ff.mono_bound (by omega)) rr x xm
        have b := ball_of_min (BRq3.ball_all 5 (by decide)) (ff.mono_bound (by omega)) rr x xm
        change 10≤(ball D W x 3).card at a
        change 13≤(ball D W x 4).card at b
        refine ⟨by omega,?_⟩
        intro hx
        have grow := high_row_ball_three_min (by decide : 2≤3) (show 2*3≤(r-1)+1 by omega)
          (ff.mono_bound cut) rr xm (show r-1+1≤_ by omega)
        have mono := card_le_card (ball_mono_radius (D:=D) (W:=W) (u:=x) (by decide : 3≤4))
        simp only [full, Nat.reduceEqDiff,ite_false]
        omega)
  dsimp only at cap capacity
  simp only [card_erase_of_mem (self_mem_ball root)] at cap
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) root
  rw [reg u root,add_comm] at one
  rw [one,Nat.add_sub_cancel_left] at cap
  exact (Nat.not_lt_of_ge cap) capacity

#print axioms fourth

#print axioms transfer
#print axioms fifth
end LeanCH.BR.CycleLayerTransport




