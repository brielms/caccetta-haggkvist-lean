import checkpoints.shen_extension.FifthStrip
import checkpoints.shen_extension.FourthStrip
import checkpoints.shen_extension.DotTwoPassShellTransport_20261117

namespace LeanCH.BR.ShenFifthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open DotTwoPassShellTransport (fullColumns shell layer full_bank_avoids)
open Classical

private theorem col_card {D : CH.Digraph} {V : Finset ℕ} {u k : ℕ} :
    (fullColumns D V (k+1) u).card =
      ((ball D V u (k+2) \ ball D V u (k+1)).filter
        (fun h => ∀ v ∈ ball D V u (k+1) \ ball D V u k, D v h=true)).card := by
  unfold fullColumns shell layer
  simp only [Nat.add_sub_cancel]
  congr 1
  ext h
  simp only [Finset.mem_filter]

private theorem erased {D : CH.Digraph} {V : Finset ℕ} {u k : ℕ} (hu : u∈V) :
    ((ball D V u k).erase u).card+1=(ball D V u k).card := by
  rw [Finset.card_erase_add_one (self_mem_ball hu)]

/-- An R-ball attaining the lowest allowed size is impossible up to order qs-4. -/
theorem tight_root_false {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u∈V)
    (hn : V.card+4≤(2*a+7)*(a+7))
    (he : (ball D V u (a+3)).card+1=(a+7)*(a+3)) : False := by
  let U := (ball D V u (a+2)).erase u
  let T := ball D V u (a+3) \ ball D V u (a+2)
  let S := ball D V u (a+2) \ ball D V u (a+1)
  let C := fullColumns D V (a+2) u
  let K := V \ U
  have hU : U.card+1=(ball D V u (a+2)).card := erased hu
  have hT : T.card+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V u (a+1)).card=(ball D V u (a+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hr := (middle_growth hf hm hu).1
  have hi := inner_growth hf hm hu (a+1) le_rfl
  have ht : T.card≤a+6 := by nlinarith only [hT,he,hr]
  let j := a+6-T.card
  have hj : T.card+j=a+6 := by dsimp [j]; omega
  have hc : S.card≤a+6+j := by nlinarith only [hT,hS,hi,he,hj]
  have budget : U.card+(a+6+j)*(T.card-1)+5≤(2*a+7)*(a+6)+T.card := by
    by_cases hz : T.card=0
    · rw [hz,Nat.zero_sub,Nat.mul_zero]; nlinarith only [hT,he,hU,hz]
    have hp : T.card-1+1=T.card := by omega
    have p1 := congrArg (fun x : ℕ => x*(a+6+j)) hj
    have p2 := congrArg (fun x : ℕ => (a+6+j)*x) hp
    nlinarith only [p1,p2,hT,he,hU,hj,Nat.le_mul_self j]
  have rect := PrefixTensor.rectangle (k:=a+1) hf hm hu (by omega : 2≤a+7)
    (fun _ _ h m n => ShenThirdStrip.order_to_top h m n) (by omega)
    (show T.card<a+7 by omega) hc budget (by decide : 2≤5)
  have hs : S.card=a+6+j := rect.1
  have hC : 5≤C.card := by
    change 5≤(fullColumns D V ((a+1)+1) u).card
    rw [col_card]; exact rect.2
  have hinner : (ball D V u (a+1)).card=(a+7)*(a+1)+1 := by
    nlinarith only [hS,hT,he,hj,hs]
  have hUV : U⊆V := (Finset.erase_subset _ _).trans ball_subset
  have hCT : C⊆T := Finset.filter_subset _ _
  have hCV : C⊆V := fun _ hh => ball_subset (Finset.mem_sdiff.mp (hCT hh)).1
  have hCK : C⊆K := by
    intro h hh
    exact Finset.mem_sdiff.mpr ⟨hCV hh, fun hu' =>
      (Finset.mem_sdiff.mp (hCT hh)).2 (Finset.mem_of_mem_erase hu')⟩
  have hballs : ∀ h ∈ C, ball D V h (a+5)⊆K := by
    apply full_bank_avoids (k:=a+1) hf hu (by omega)
    intro y hy
    have hp := erased (k:=a+1) (D:=D) hu
    have hg := inner_growth hf hm (hUV hy) (a+1) le_rfl
    omega
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have bound (y) (hy : y∈V) : (a+7)*(a+5)+1≤(ball D V y (a+5)).card+6 := by
    obtain ⟨_,h3,h4⟩ := middle_growth hf hm hy
    apply ShenStripTransfer.growth_step (k:=a+3) (s:=a+7) (d:=a+6) (j:=1)
      (L:=(2*a+7)*(a+6)) (fun _ _ h m n => ShenThirdStrip.order_to_top h m n)
      hf hm hy rfl (by omega) h3 h4 (by decide) (by decide)
    · push_cast; nlinarith
    · nlinarith
  have miss (h) (hh : h∈C) :
      (K \ ball D V h (a+5)).card + U.card + (a+7)*(a+5) ≤ V.card+5 := by
    have hg := bound h (hCV hh)
    have hx := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    omega
  by_cases ha : a=0
  · subst a
    have h2 := card_ball_two_ge_twice (by decide : 2≤7) (hf.mono_bound (by decide : 7≤2*0+7)) hm hu
    apply near_full_container_false hf (by decide : (0+5)+2≤2*0+7) hCV hCK hballs
      (fun h hh => ?_) (by omega) ((Finset.card_le_card hCT).trans (by omega))
    have hx := miss h hh
    norm_num at h2 hU hn hx
    omega
  · apply ShenFourthStrip.two_omission_container_false hf (by omega) (by omega)
      hCV hCK hballs (fun h hh => ?_) (by omega)
    have hx := miss h hh
    nlinarith only [hx,hr,hU,hn]

theorem order_to_four {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) : (2*a+7)*(a+7)≤V.card+4 := by
  by_contra! hn
  have hR (u) (hu : u∈V) : (a+7)*(a+3)≤(ball D V u (a+3)).card := by
    have h := (middle_growth hf hm hu).2.1
    by_contra! hh
    exact tight_root_false hf hm hu (by omega) (by omega)
  have h := card_ge_of_two_balls hf (by omega : (a+3)+(a+4)≤2*a+7) hR
    (b:=(a+7)*(a+4)-3)
    (fun v hv => by have := (middle_growth hf hm (u:=v) hv).2.2; omega) hne
  have h3 : 3≤(a+7)*(a+4) := by nlinarith
  have he : (2*a+7)*(a+7)=(a+7)*(a+3)+(a+7)*(a+4) := by ring
  omega

#print axioms tight_root_false
#print axioms order_to_four

/-- At order qs-4 the two middle radii would saturate the return capacity.
The resulting common container has zero omissions. -/
theorem fourth_from_top_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card+4=(2*a+7)*(a+7)) : False := by
  have hR (u) (hu : u∈V) : (a+7)*(a+3)≤(ball D V u (a+3)).card := by
    have h := (middle_growth hf hm hu).2.1
    by_contra! hh
    exact tight_root_false hf hm hu hn.le (by omega)
  have h3 : 3≤(a+7)*(a+4) := by nlinarith
  have he : (2*a+7)*(a+7)=(a+7)*(a+3)+(a+7)*(a+4) := by ring
  have rigid := two_balls_boundary_cards hf (by omega : (a+3)+(a+4)≤2*a+7) hR
    (b:=(a+7)*(a+4)-3)
    (fun v hv => by have := (middle_growth hf hm (u:=v) hv).2.2; omega) (by omega)
  obtain ⟨u,hu⟩ := hne
  let U := (ball D V u (a+3)).erase u
  let S := ball D V u (a+3) \ ball D V u (a+2)
  let T := ball D V u (a+4) \ ball D V u (a+3)
  let C := fullColumns D V (a+3) u
  let K := V \ U
  obtain ⟨huR,huNext,_⟩ := rigid u hu
  have hU : U.card+1=(ball D V u (a+3)).card := erased hu
  have hT : T.card+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hdiff : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have ht : T.card=a+4 := by omega
  have hi := (middle_growth hf hm hu).1
  have hc : S.card≤a+7 := by nlinarith only [hS,huR,hi]
  have hp : 4≤(2*a+7)*(a+7) := by nlinarith
  have budget : U.card+(a+7)*T.card+(a+1)≤(2*a+7)*(a+7)-4+T.card := by
    rw [ht]; omega
  have rect := ShenFourthStrip.same_rectangle (k:=a+2) hf hm hu (by omega : 1≤a+7)
    (fun _ _ h m n => by have := order_to_four h m n; omega)
    (by omega) (show T.card<a+7 by omega) hc budget (by omega : 1≤a+1)
  have hs : S.card=a+7 := rect.1
  have hinner : (ball D V u (a+2)).card=(a+7)*(a+2) := by nlinarith only [hS,huR,hs]
  have hC : a+1≤C.card := by
    change a+1≤(fullColumns D V ((a+2)+1) u).card
    rw [col_card]; exact rect.2
  by_cases ha : a=0
  · subst a
    have h2 := card_ball_two_ge_twice (by decide : 2≤7) (hf.mono_bound (by decide : 7≤2*0+7)) hm hu
    norm_num at h2 hinner
    omega
  have hUV : U⊆V := (Finset.erase_subset _ _).trans ball_subset
  have boxes : ∀ h ∈ C, ball D V h (a+4)⊆K := by
    apply full_bank_avoids (k:=a+2) hf hu (by omega)
    intro y hy
    have hh := erased (k:=a+2) (D:=D) hu
    have hg := (middle_growth hf hm (hUV hy)).1
    omega
  have hCT : C⊆T := Finset.filter_subset _ _
  have hCV : C⊆V := fun _ hh => ball_subset (Finset.mem_sdiff.mp (hCT hh)).1
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have eqK (h) (hh : h∈C) : ball D V h (a+4)=K := by
    apply Finset.eq_of_subset_of_card_le (boxes h hh)
    have := (rigid h (hCV hh)).2.1
    omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1<C.card by omega)
  exact hxy (DotTwoPassShellTransport.ball_root_injective_short hf (by omega)
    (hCV hx) (hCV hy) ((eqK x hx).trans (eqK y hy).symm))

theorem order_to_three {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) : (2*a+7)*(a+7)≤V.card+3 := by
  have h := order_to_four hf hm hne
  by_contra! hh
  exact fourth_from_top_false hf hm hne (by omega)

theorem cycle_below_three {s q n : ℕ} {D : CH.Digraph}
    (hs : 7≤s) (hq : q=2*s-7) (hn : 0<n) (hc : n+4≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  have he : q=2*a+7 := by omega
  rw [he] at hc ⊢
  by_contra hno
  have h := order_to_three (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h
  omega

#print axioms fourth_from_top_false
#print axioms order_to_three
#print axioms cycle_below_three
end LeanCH.BR.ShenFifthStrip
