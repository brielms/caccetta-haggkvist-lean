import checkpoints.shen_extension.WideBankEscape
namespace LeanCH.BR.EqualMixedShells
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking ShellCycleSupply RetainedLayerCapacity

def Room (r : ℕ) : Prop := (2*r+2)*(2*r+3)<(r+2)*16 + r*(2*r+10)
instance (r : ℕ) : Decidable (Room r) := by unfold Room; infer_instance

/-- Uniform middle balls exclude both the triple of equal layers and the
overfull second ball. This leaves the same three cardinalities at every
root on the same exact-degree graph. -/
theorem exact_second {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 7≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (room : Room r)
    (flat : ∀v∈V,2*r+1≤(ball D V v 2).card ∧ (ball D V v 3).card=3*r+1 ∧
      (ball D V v 4).card=4*r) : ∀u∈V,(ball D V u 2).card=2*r+2 := by
  intro u uv
  obtain ⟨base,mid,last⟩ := flat u uv
  have degree v (vm : v∈V) := (reg v vm).ge
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg u uv] at one
  have sizes k := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k≤k+1 by omega))
  have a := sizes 1
  have b := sizes 2
  have c := sizes 3
  simp only [Nat.reduceAdd] at a b c
  by_cases small : (ball D V u 2).card=2*r+1
  · let Z := ball D V u 3\ball D V u 2
    let W := ball D V u 4\ball D V u 3
    have zv : Z⊆V := fun _ hm=>ball_subset (mem_sdiff.mp hm).1
    have wv : W⊆V := fun _ hm=>ball_subset (mem_sdiff.mp hm).1
    have cardZ : Z.card=r := by dsimp [Z]; omega
    have cardW : W.card+1=r := by dsimp [W]; omega
    have no := BRsub.equal_triple_layers_no_back (by omega : 6≤r) (free.mono_bound (by omega : r-1≤q)) uv
      degree (reg u uv) (by omega) cardZ (by dsimp [W] at cardW; omega)
    have allowed (z) (zm : z∈Z) : outN D V z⊆outN D Z z∪outN D W z := by
      intro v vm
      obtain ⟨vv,arc⟩ := mem_outN.mp vm
      have seen := ball_step (mem_sdiff.mp zm).1 vv arc
      by_cases early : v∈ball D V u 3
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨early,fun hit=>no z zm v hit arc⟩,arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨seen,early⟩,arc⟩)
    have tally z (zm : z∈Z) : r≤(outN D Z z).card+(outN D W z).card :=
      (degree z (zv zm)).trans ((card_le_card (allowed z zm)).trans (card_union_le _ _))
    have live z (zm : z∈Z) : 1≤(outN D Z z).card := by
      have := tally z zm
      have cap := card_le_card (outN_subset : outN D W z⊆W)
      omega
    obtain ⟨z,zm⟩ := card_pos.mp (show 0<Z.card by omega)
    have cycle := rooted_on_small_set free (by omega) zv (cardZ.le.trans fit) live zm
    have covers x (xm : x∈Z) : W⊆outN D W x := by
      apply (eq_of_subset_of_card_le outN_subset ?_).ge
      have := tally x xm
      have := cycle.one x xm
      omega
    have growth := WideBankEscape.on_cycle free (by omega) (by omega) fit wv cardW degree cycle
      (fun x xm w wm=>(mem_outN.mp (covers x xm wm)).2)
    have fixed := (flat z (zv zm)).2.1
    omega
  by_contra! ne
  have wide : 2*r+3≤(ball D V u 2).card := by omega
  by_cases first : (ball D V u 2).card=2*r+3
  · have cap := prefix_three_scores (k:=2) (a:=1) (b:=0) (j:=2) (i:=3) (l:=4)
      (h:=0) (near:=0) (base:=16) (high:=2*r+10) free uv (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) degree
      (show 2+(ball D V u 3\ball D V u 2).card≤r by omega)
      (fun _ _=>Nat.zero_le _) (by omega) (fun G ff rank x xm=>by
        have all := ball_growth q (by omega) D G ff rank x xm
        refine ⟨by have := all 3 (by omega); have := all 4 (by omega); omega,?_⟩
        intro full
        have e := high_row_ball_three_min (by decide : 2≤2) (show 2*2≤(r-1)+1 by omega)
          (ff.mono_bound (by omega : r-1≤q)) rank xm (show r-1+1≤_ by omega)
        have f := high_two_ball_four (show 5≤r-1 by omega) (ff.mono_bound (by omega : r-1≤q)) rank xm (show r-1+1≤_ by omega)
        omega)
    have zero : ball D V u 0={u} := eq_of_subset_of_card_le
      (fun _ h=>mem_singleton.mpr (eq_of_mem_ball_zero h)) (by rw [card_singleton]; exact card_pos.mpr ⟨u,self_mem_ball uv⟩)
    dsimp only at cap
    simp only [zero,erase_singleton,card_erase_of_mem (self_mem_ball uv),card_empty,first,one,Nat.add_sub_cancel] at cap
    unfold Room at room
    have m : 2*r+3-1=2*r+2 := by omega
    have l : 2*r+2-r=r+2 := by omega
    have n : 2*r+2+1=2*r+3 := by omega
    simp only [m,l,n,Nat.sub_zero,Nat.zero_mul,Nat.add_zero] at cap
    omega
  let A := (ball D V u 2).erase u
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have cardA : A.card+1=(ball D V u 2).card := card_erase_add_one (self_mem_ball uv)
  have nonempty : A.Nonempty := card_pos.mp (by omega)
  have upper := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  by_cases m : A.card≤3*q
  · have rank := minOut_prefix_erase (k:=2) free uv (by omega) degree
      (show 3+(ball D V u 3\ball D V u 2).card≤r by omega)
    have := BRq6.lower_order (by omega : 5≤q) (by decide : 2≤3) (by decide : 3<6) (free.mono_set av) rank nonempty
    omega
  · have rank := minOut_prefix_erase (k:=2) free uv (by omega) degree
      (show 4+(ball D V u 3\ball D V u 2).card≤r by omega)
    have := BRq6.lower_order (by omega : 5≤q) (by decide : 2≤4) (by decide : 4<6) (free.mono_set av) rank nonempty
    omega

/-- All exact-degree thinnings of the same input have this labelled ball
profile whenever the two symbolic capacity tests hold. -/
structure OnFamily (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀{q},q≤CHRuleCatalog.cutoff p → 7≤q → 7≤p.s → p.s≤q+1 →
    FourthRoom p.s → MixedBankScore.Capacity p.s → MixedBankProfile.Room p.s → Room p.s →
    p.n≤7*p.s → ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀u∈range p.n,(ball F (range p.n) u 2).card=2*p.s+2 ∧ (ball F (range p.n) u 3).card=3*p.s+1 ∧
        (ball F (range p.n) u 4).card=4*p.s

theorem from_bad (p : CHRuleCatalog.Input) (bad : CHRuleCatalog.Bad p) : OnFamily p := by
  constructor
  intro q cut hq hr fit previous cap more room host F sub reg
  have packet := (MixedBankProfile.native p bad).on_graph cut hq hr fit previous cap more host F sub reg
  have ff := qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)
  have second := exact_second ff hq hr fit reg room packet
  exact fun u um=>⟨second u um,(packet u um).2⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] from_bad
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,room,flat]) (rule_sets := [CHGraphFamilies])] exact_second
attribute [aesop safe forward (immediate := [free,hq,hr,fit,wv,width,min]) (rule_sets := [CHGraphFamilies])] WideBankEscape.expansion
attribute [aesop safe forward (immediate := [free,hq,hr,fit,wv,width,min,cycle,complete]) (rule_sets := [CHGraphFamilies])] WideBankEscape.on_cycle
#print axioms from_bad

#print axioms exact_second
end LeanCH.BR.EqualMixedShells


