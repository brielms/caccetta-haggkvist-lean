import checkpoints.shen_extension.MixedBankProfile
namespace LeanCH.BR.WideBankEscape
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking ShellCycleSupply

/-- Two steps from a marked bank. A sink of the bank puts a full native
row outside it in the first step. If too few labels are reached altogether,
the first neighbourhood either violates degree-three CH or saturates the
degree-two boundary with a row of degree greater than two. -/
theorem expansion {D V W q r} (free : QFree D V q) (hq : 5≤q) (hr : 3≤r) (fit : r≤q+1)
    (wv : W⊆V) (width : W.card+1=r) (min : ∀v∈V,r≤(outN D V v).card) :
    3*r-2≤(W.biUnion (fun w=>ball D V w 2)).card := by
  let A := W.biUnion (fun w=>ball D V w 1)
  let B := W.biUnion (fun w=>ball D V w 2)
  have wa : W⊆A := fun x xm=>mem_biUnion.mpr ⟨x,xm,self_mem_ball (wv xm)⟩
  have ab : A⊆B := by
    intro x xm
    obtain ⟨w,wm,xh⟩ := mem_biUnion.mp xm
    exact mem_biUnion.mpr ⟨w,wm,ball_mono_radius (by decide : 1≤2) xh⟩
  have bv : B⊆V := by intro x xm; obtain ⟨w,wm,xh⟩ := mem_biUnion.mp xm; exact ball_subset xh
  have av := ab.trans bv
  obtain ⟨s,sm,sink⟩ := exists_sink (free.mono_set wv) (card_pos.mp (show 0<W.card by omega)) (by omega)
  have outer : outN D V s⊆A\W := by
    intro x xm
    obtain ⟨xv,arc⟩ := mem_outN.mp xm
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨s,sm,ball_of_adj xv arc⟩,fun xw=>sink x xw arc⟩
  have first := (min s (wv sm)).trans (card_le_card outer)
  have firstCount := card_sdiff_add_card_eq_card wa
  have secondCount := card_sdiff_add_card_eq_card ab
  have retained u (um : u∈A) : r≤(outN D A u).card+(B\A).card := by
    obtain ⟨w,wm,hit⟩ := mem_biUnion.mp um
    have sub : outN D V u⊆outN D A u ∪ (B\A) := by
      intro x xm
      obtain ⟨xv,arc⟩ := mem_outN.mp xm
      by_cases inside : x∈A
      · exact mem_union_left _ (mem_outN.mpr ⟨inside,arc⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨w,wm,ball_step hit xv arc⟩,inside⟩)
    exact (min u (av (mem_biUnion.mpr ⟨w,wm,hit⟩))).trans ((card_le_card sub).trans (card_union_le _ _))
  change 3*r-2≤B.card
  by_contra! tiny
  have live : A.Nonempty := ⟨s,wa sm⟩
  by_cases big : 2*r≤A.card
  · have three (v) (vm : v∈A) : 3≤(outN D A v).card := by have := retained v vm; omega
    have := BRq6.lower_order hq (by decide : 2≤3) (by decide : 3<6) (free.mono_set av) three live
    have := card_le_card ab
    omega
  have two (v) (vm : v∈A) : 2≤(outN D A v).card := by have := retained v vm; omega
  have size := BRq6.lower_order hq (by decide : 2≤2) (by decide : 2<6) (free.mono_set av) two live
  have regular : Ball q 2 := by
    intro G U guard rr u um
    exact ball_growth q (by omega) G U guard (fun x xm=>(rr x xm).ge) u um (q-1) (by omega)
  have eq := (dt_reg (by omega : 1≤q) regular (free.mono_set av) two (by omega)).1 s (wa sm)
  have full : outN D V s⊆outN D A s := by
    intro x xm
    exact mem_outN.mpr ⟨(mem_sdiff.mp (outer xm)).1,(mem_outN.mp xm).2⟩
  have := (min s (wv sm)).trans (card_le_card full)
  omega

/-- The complete bank plus its cyclic successors pays for four distinct
additional labels. Short returns exclude every overlap with the bank's
second neighbourhood. -/
theorem on_cycle {D V C W q r z} (free : QFree D V q) (hq : 5≤q) (hr : 3≤r) (fit : r≤q+1)
    (wv : W⊆V) (width : W.card+1=r) (min : ∀v∈V,r≤(outN D V v).card)
    (cycle : Rooted D V z C) (complete : ∀c∈C,∀w∈W,D c w=true) :
    3*r+2≤(ball D V z 3).card := by
  let B := W.biUnion (fun w=>ball D V w 2)
  have high := expansion free hq hr fit wv width min
  have disj : Disjoint (ball D C z 3) B := by
    refine disjoint_left.mpr ?_
    intro c cm bm
    obtain ⟨w,wm,reaches⟩ := mem_biUnion.mp bm
    obtain ⟨_,k,dt,path⟩ := mem_ball.mp reaches
    exact free w _ (by omega) (by omega) (path.snoc (wv wm) (complete c (ball_subset cm) w wm))
  have inside : B⊆ball D V z 3 := by
    intro c cm
    obtain ⟨w,wm,reaches⟩ := mem_biUnion.mp cm
    obtain ⟨cv,k,dt,path⟩ := mem_ball.mp reaches
    exact mem_ball.mpr ⟨cv,k+1,by omega,Walk.step (wv wm) (complete z cycle.root w wm) path⟩
  have full := card_le_card (union_subset (lift_ball cycle.sub : ball D C z 3⊆ball D V z 3) inside)
  rw [card_union_of_disjoint disj] at full
  have reach := ball_one_growth (free.mono_set cycle.sub) (fun a am=>(cycle.one a am).ge) cycle.root 3 (by omega)
  change 3*r-2≤B.card at high
  omega
#print axioms expansion
#print axioms on_cycle
end LeanCH.BR.WideBankEscape


