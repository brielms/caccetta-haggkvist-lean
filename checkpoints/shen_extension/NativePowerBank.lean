import checkpoints.shen_extension.OpposedPowerRows

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair CHRuleCatalog ProjectedQuotaTransfer

/-- The measured degree of the cheap row improves the quota on its
actual first heads. No thinning or relabelling is required. -/
theorem native_bank {D V q r} (free : QFree D V q) (live : V.Nonempty)
    (degree : ∀u∈V,r≤(outN D V u).card) (radius : 3≤q) (order : V.card≤3*r) :
    ∃x∈V,∃y∈V,x≠y ∧ 2*r+1≤(ball D V x 2).card ∧ (ball D V y 2).card<V.card-r ∧
      ∀z∈outN D V y,2*r+(outN D V y).card+2≤V.card+(outN D (outN D V y) z).card := by
  have first v (vm : v∈V) := ReachLedger.ball_one free (by omega) vm
  have base v (vm : v∈V) : r+1≤(ball D V v 1).card := by rw [first v vm]; have := degree v vm; omega
  obtain ⟨v,vm⟩ := live
  have size := card_le_card (ball_subset (D:=D) (W:=V) (u:=v) (k:=1))
  have := base v vm
  obtain ⟨x,xm,y,ym,ne,high,low⟩ := opposed_rows (k:=1) (b:=V.card-r) free
    ⟨v,vm⟩ (by omega) base (by omega) (by omega)
  change 2*(ball D V x 1).card≤(ball D V x 2).card+1 at high
  change (ball D V y 2).card<V.card-r at low
  have := base x xm
  refine ⟨x,xm,y,ym,ne,by omega,low,?_⟩
  have order2 := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=y) (by decide : 1≤2))
  have y1 := first y ym
  have yr := degree y ym
  let d := 2*r+(outN D V y).card+2-V.card
  have internal : ∀z∈(ball D V y 1).erase y,d≤(outN D ((ball D V y 1).erase y) z).card := by
    apply minOut_prefix_erase free ym (by omega : 1+1≤q) degree
    rw [card_sdiff_of_subset (ball_mono_radius (Nat.le_succ _))]
    change d+((ball D V y 2).card-(ball D V y 1).card)≤r
    dsimp [d]
    omega
  rw [erase_ball_one_eq_outN free (by omega) ym] at internal
  intro z zm
  have paid := internal z zm
  dsimp [d] at paid
  omega

/-- Reapply the minimum-degree argument in the unthinned power child.
The bank named in the answer is an actual punctured two-ball of the
parent, and the rows counted inside it are the child's physical arcs. -/
theorem inherited_native_bank {p : Input} (bad : Bad p)
    (win : UniformReduction p.n p.s (cutoff p) projectionFloor)
    (triangle : 3≤CH.ceilDiv p.n (2*p.s)) (density : p.n≤3*(2*p.s)) :
    ∃c : Input,Child p c ∧ Bad c ∧ c.n=p.n ∧ c.s=2*p.s ∧ cutoff c<cutoff p ∧
      ∃x∈range p.n,∃y∈range p.n,x≠y ∧ 2*c.s+1≤(ball c.D (range p.n) x 2).card ∧
      (ball c.D (range p.n) y 2).card<p.n-c.s ∧
      let H := (ball p.D (range p.n) y 2).erase y
      H=outN c.D (range p.n) y ∧ ∀z∈H,2*c.s+H.card+2≤p.n+(outN c.D H z).card := by
  obtain ⟨c,edge,bc,n,s,smaller,rows⟩ := original_edge bad win
  have q3 : 3≤cutoff c := by unfold cutoff; rwa [n,s]
  have free := qfree_of_noShort bc.loopless bc.missing
  have degree v (vm : v∈range c.n) := Compose.FloorSix.out_card bc.degree (mem_range.mp vm)
  obtain ⟨x,xm,y,ym,ne,high,low,bank⟩ := native_bank free (nonempty_range_iff.mpr bc.order.ne') degree q3
    (by rw [card_range,n,s]; exact density)
  rw [card_range] at low bank
  rw [n] at xm ym high low bank
  refine ⟨c,edge,bc,n,s,smaller,x,xm,y,ym,ne,high,low,(rows y ym).symm,?_⟩
  simpa only [←rows y ym] using bank

attribute [aesop safe forward (immediate := [free,live,degree,radius,order]) (rule_sets := [CHGraphFamilies])] native_bank
attribute [aesop safe forward (immediate := [bad,win,triangle,density]) (rule_sets := [CHGraphFamilies])] inherited_native_bank
#print axioms native_bank
#print axioms inherited_native_bank
end LeanCH.BR.FragmentScoreEquality