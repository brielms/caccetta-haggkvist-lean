import checkpoints.shen_extension.ThirdStrip
import checkpoints.shen_extension.PrefixTensor

namespace LeanCH.BR.ShenThirdStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

private theorem root_budget {a j t N : ℕ}
    (hn : N+t+1=(a+6)*(a+3)) (htj : t+j=a+5) :
    N+(a+6+j)*(t-1)+5≤(2*a+7)*(a+5)+1+t := by
  by_cases ht0 : t=0
  · rw [ht0] at hn ⊢
    simp only [Nat.zero_sub,Nat.mul_zero,Nat.add_zero]
    nlinarith only [hn]
  have hloss : t-1+1=t := by omega
  have hprod := congrArg (fun z : ℕ => z*(a+6+j)) htj
  have hprod2 := congrArg (fun z : ℕ => (a+6+j)*z) hloss
  nlinarith only [hn,htj,hprod,hprod2,Nat.zero_le (j*j)]

/-- The actual tight-root rectangle supplies a labelled bank reached from U. -/
theorem tight_root_bank {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V)
    (hroot : (ball D V u (a+3)).card=(a+6)*(a+3)) :
    ∃ (U C : Finset ℕ), U ⊆ V ∧ C ⊆ V \ U ∧ 5≤C.card ∧ C.card≤2*a+7 ∧
      (a+6)*(a+3)≤U.card+(a+6) ∧
      ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y (a+2) := by
  let B := ball D V u (a+2)
  let U := B.erase u
  let S := B \ ball D V u (a+1)
  let T := ball D V u (a+3) \ B
  let j := a+5-T.card
  let C := T.filter (fun h => ∀ v ∈ S, D v h=true)
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card=(a+6)*(a+3) :=
    (Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))).trans hroot
  have hS : S.card+(ball D V u (a+1)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hprev := inner_growth hf hm hu (a+2) (by omega) (by omega)
  change (a+6)*(a+2)+1≤B.card at hprev
  have hinner := inner_growth hf hm hu (a+1) (by omega) (by omega)
  have ht : T.card≤a+5 := by nlinarith only [hT,hprev]
  have htj : T.card+j=a+5 := by dsimp [j]; omega
  have hc : S.card≤a+6+j := by nlinarith only [hT,hS,hinner,htj]
  have hn : U.card+T.card+1=(a+6)*(a+3) := by omega
  have budget := root_budget hn htj
  have hrect := PrefixTensor.rectangle hf hm hu (by omega : 2≤a+6)
    (fun F W hf' hm' hn' => previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn')
    (by omega : (a+1)+2≤2*a+7) (by change T.card<a+6; omega) hc budget (by decide : 2≤5)
  have hSc : S.card=a+6+j := hrect.1
  have hC : 5≤C.card := by
    have he : C = (ball D V u ((a+1)+2) \ ball D V u ((a+1)+1)).filter
        (fun h => ∀ v ∈ ball D V u ((a+1)+1) \ ball D V u (a+1), D v h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hexact : (ball D V u (a+1)).card=(a+6)*(a+1)+1 := by
    nlinarith only [hSc,hS,hT,htj]
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hn (Finset.mem_of_mem_erase hU)⟩
  refine ⟨U,C,hUV,hCK,hC,(Finset.card_le_card hCT).trans (by omega),by omega,?_⟩
  intro h hh y hy
  have hyV := hUV hy
  have hlarge := inner_growth hf hm hyV (a+1) (by omega) (by omega)
  have hsmall : ((ball D V u (a+1)).erase u).card=(a+6)*(a+1) := by
    have he := Finset.card_erase_of_mem (s:=ball D V u (a+1)) (self_mem_ball hu)
    rw [hexact] at he
    omega
  obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hu (by omega : (a+1)+1≤2*a+7) hy (by omega)
  have hhV := (Finset.mem_sdiff.mp (hCK hh)).1
  exact ball_step hyz hhV ((Finset.mem_filter.mp hh).2 z hz)

/-- A bank with return paths of radius r excludes forward balls of complementary radius k. -/
theorem bank_avoids {q k r : ℕ} {D : CH.Digraph} {V U C : Finset ℕ}
    (hf : QFree D V q) (hCK : C ⊆ V \ U) (hkr : k+r≤q)
    (hreach : ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y r) :
    ∀ h ∈ C, ball D V h k ⊆ V \ U := by
  intro h hh y hy
  refine Finset.mem_sdiff.mpr ⟨ball_subset hy,?_⟩
  intro hyU
  have hyh := hreach h hh y hyU
  obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hy
  obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hyh
  have hne : h ≠ y := by
    intro he; subst y
    exact (Finset.mem_sdiff.mp (hCK hh)).2 hyU
  have hip : 0<i := by
    cases i with
    | zero => cases wi; exact (hne rfl).elim
    | succ => omega
  exact hf h (i+j) (by omega) (by omega) (wi.append wj)

theorem lowest_endpoint_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card+2=(2*a+7)*(a+6)) : False := by
  let b := (a+6)*(a+3)
  have hi := fun v hv => radius_R_growth hf hm (u:=v) hv
  have hj (v) (hv : v ∈ V) : (a+6)*(a+4)-1≤(ball D V v (a+4)).card := by
    have h := radius_R1_growth hf hm hv
    omega
  have hcards := two_balls_boundary_cards hf (by omega : (a+3)+(a+4)≤2*a+7) hi hj (by
    have hsub : (a+6)*(a+4)-1+1=(a+6)*(a+4) :=
      Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
    nlinarith only [hn,hsub])
  obtain ⟨u,hu⟩ := hne
  obtain ⟨U,C,hUV,hCK,hC,hCq,hU,hreach⟩ := tight_root_bank hf hm hu (hcards u hu).1
  have hballs := bank_avoids (k:=a+5) hf hCK (by omega : (a+5)+(a+2)≤2*a+7) hreach
  let K := V \ U
  have hK : K.card+(U.card)=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hbound : K.card+2≤(a+6)*(a+5) := by
    nlinarith only [hn,hK,hU]
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+5)).card≤1 := by
    have hg := radius_R2_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+5)).card+(ball D V h (a+5)).card=K.card at he
    omega
  exact near_full_container_false hf (by omega : (a+5)+2≤2*a+7)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega) hCq

#print axioms tight_root_bank
#print axioms bank_avoids
#print axioms lowest_endpoint_false
end LeanCH.BR.ShenThirdStrip

namespace LeanCH.BR.ShenThirdStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

private theorem improvement_budget {a f t N : ℕ}
    (hn : N+2=(a+6)*(a+4)+f) (htf : t+f=a+4) :
    N+(a+5+f)*(t-1)+3≤(2*a+7)*(a+5)+1+t := by
  by_cases ht0 : t=0
  · rw [ht0] at htf ⊢
    simp only [Nat.zero_sub,Nat.mul_zero,Nat.add_zero]
    nlinarith only [hn,htf]
  have hloss : t-1+1=t := by omega
  have hprod := congrArg (fun z : ℕ => z*(a+5+f)) htf
  have hprod2 := congrArg (fun z : ℕ => (a+5+f)*z) hloss
  nlinarith only [hn,htf,hprod,hprod2,Nat.zero_le (f*f)]

/-- A second actual rectangle improves the enlarged ball under the middle-order cap. -/
theorem radius_R2_improved {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V)
    (hn : V.card+1≤(2*a+7)*(a+6)) :
    (a+6)*(a+5)≤(ball D V u (a+5)).card+2 := by
  by_contra! hbad
  have hold := radius_R2_growth hf hm hu
  have hroot : (ball D V u (a+5)).card+3=(a+6)*(a+5) := by omega
  let B := ball D V u (a+4)
  let U := B.erase u
  let S := B \ ball D V u (a+3)
  let T := ball D V u (a+5) \ B
  let base := (a+6)*(a+4)-1
  let f := B.card-base
  let C := T.filter (fun h => ∀ v ∈ S, D v h=true)
  have hbase : base+1=(a+6)*(a+4) :=
    Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
  have hprev := radius_R1_growth hf hm hu
  change (a+6)*(a+4)≤B.card+1 at hprev
  have he : B.card+1=(a+6)*(a+4)+f := by dsimp [f]; omega
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    have hp : 0<B.card := by nlinarith only [hprev]
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card=(ball D V u (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V u (a+3)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have htf : T.card+f=a+4 := by nlinarith only [he,hroot,hT]
  have hnU : U.card+2=(a+6)*(a+4)+f := by omega
  have hg := radius_R_growth hf hm hu
  have hc : S.card≤a+5+f := by nlinarith only [he,hS,hg]
  have budget := improvement_budget hnU htf
  have hrect := PrefixTensor.rectangle hf hm hu (by omega : 2≤a+6)
    (fun F W hf' hm' hn' => previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn')
    (by omega : (a+3)+2≤2*a+7) (by change T.card<a+6; omega) hc budget (by decide : 2≤3)
  have hSc : S.card=a+5+f := hrect.1
  have hC : 3≤C.card := by
    have hcset : C=(ball D V u ((a+3)+2) \ ball D V u ((a+3)+1)).filter
        (fun h => ∀ v ∈ ball D V u ((a+3)+1) \ ball D V u (a+3), D v h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [hcset]
    exact hrect.2
  have hexact : (ball D V u (a+3)).card=(a+6)*(a+3) := by nlinarith only [he,hSc,hS]
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hy => hn (Finset.mem_of_mem_erase hy)⟩
  have hreach (h) (hh : h ∈ C) (y) (hy : y ∈ U) : h ∈ ball D V y (a+4) := by
    have hlarge := radius_R_growth hf hm (hUV hy)
    have hsmall : ((ball D V u (a+3)).erase u).card+1=(a+6)*(a+3) := by
      have he := Finset.card_erase_of_mem (s:=ball D V u (a+3)) (self_mem_ball hu)
      have hp : 0<(ball D V u (a+3)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
      omega
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hu (by omega : (a+3)+1≤2*a+7) hy (by omega)
    exact ball_step hyz (Finset.mem_sdiff.mp (hCK hh)).1 ((Finset.mem_filter.mp hh).2 z hz)
  have hballs := bank_avoids (k:=a+3) hf hCK (by omega : (a+3)+(a+4)≤2*a+7) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hbound : K.card≤(a+6)*(a+3)+1 := by nlinarith only [hn,hK,hnU,Nat.zero_le f]
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+3)).card≤1 := by
    have hg := radius_R_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+3)).card+(ball D V h (a+3)).card=K.card at he
    omega
  exact near_full_container_false hf (by omega : (a+3)+2≤2*a+7)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss hC
    ((Finset.card_le_card hCT).trans (by omega))

theorem middle_tight_root_false {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V)
    (hn : V.card+1≤(2*a+7)*(a+6))
    (hroot : (ball D V u (a+3)).card=(a+6)*(a+3)) : False := by
  obtain ⟨U,C,hUV,hCK,hC,hCq,hU,hreach⟩ := tight_root_bank hf hm hu hroot
  have hballs := bank_avoids (k:=a+5) hf hCK (by omega : (a+5)+(a+2)≤2*a+7) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hbound : K.card+1≤(a+6)*(a+5) := by nlinarith only [hn,hK,hU]
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+5)).card≤1 := by
    have hg := radius_R2_improved hf hm (Finset.mem_sdiff.mp (hCK hh)).1 hn
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+5)).card+(ball D V h (a+5)).card=K.card at he
    omega
  exact near_full_container_false hf (by omega : (a+5)+2≤2*a+7)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega) hCq

theorem middle_endpoint_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card+1=(2*a+7)*(a+6)) : False := by
  let b := (a+6)*(a+3)
  by_cases htight : ∃ u ∈ V, (ball D V u (a+3)).card=b
  · obtain ⟨u,hu,hroot⟩ := htight
    exact middle_tight_root_false hf hm hu hn.le hroot
  have hi (v) (hv : v ∈ V) : b+1≤(ball D V v (a+3)).card := by
    have hg := radius_R_growth hf hm hv
    change b≤(ball D V v (a+3)).card at hg
    by_contra! hh
    exact htight ⟨v,hv,by omega⟩
  have hj (v) (hv : v ∈ V) : (a+6)*(a+4)-1≤(ball D V v (a+4)).card := by
    have h := radius_R1_growth hf hm hv
    omega
  have hcards := two_balls_boundary_cards hf (by omega : (a+3)+(a+4)≤2*a+7) hi hj (by
    have hb : (a+6)*(a+4)-1+1=(a+6)*(a+4) :=
      Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
    dsimp [b]
    nlinarith only [hn,hb])
  obtain ⟨u,hu⟩ := hne
  let B := ball D V u (a+3)
  let U := B.erase u
  let S := B \ ball D V u (a+2)
  let T := ball D V u (a+4) \ B
  let C := T.filter (fun h => ∀ v ∈ S, D v h=true)
  have hB : B.card=b+1 := (hcards u hu).1
  have hT : T.card=a+4 := by
    have he := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : a+3≤a+4))
    have h1 := (hcards u hu).2.1
    change T.card+B.card=(ball D V u (a+4)).card at he
    have hb : (a+6)*(a+4)-1+1=(a+6)*(a+4) :=
      Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
    dsimp [b] at hB
    nlinarith only [he,h1,hB,hb]
  have hU : U.card=b := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    change U.card=B.card-1 at he
    omega
  have hS : S.card+(ball D V u (a+2)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hprev := inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hc : S.card≤a+6 := by dsimp [b] at hB; nlinarith only [hB,hS,hprev]
  have hbudget : U.card+(a+6)*(T.card-1)+4≤(2*a+7)*(a+5)+1+T.card := by
    rw [hT,hU]
    have hsub : a+4-1=a+3 := by omega
    rw [hsub]
    dsimp [b]
    nlinarith
  have hrect := PrefixTensor.rectangle hf hm hu (by omega : 2≤a+6)
    (fun F W hf' hm' hn' => previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn')
    (by omega : (a+2)+2≤2*a+7) (by change T.card<a+6; omega) hc hbudget (by decide : 2≤4)
  have hSc : S.card=a+6 := hrect.1
  have hC : 4≤C.card := by
    have he : C=(ball D V u ((a+2)+2) \ ball D V u ((a+2)+1)).filter
        (fun h => ∀ v ∈ ball D V u ((a+2)+1) \ ball D V u (a+2), D v h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hexact : (ball D V u (a+2)).card=(a+6)*(a+2)+1 := by
    dsimp [b] at hB
    nlinarith only [hB,hS,hSc]
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hy => hn (Finset.mem_of_mem_erase hy)⟩
  have hreach (h) (hh : h ∈ C) (y) (hy : y ∈ U) : h ∈ ball D V y (a+3) := by
    have hlarge := inner_growth hf hm (hUV hy) (a+2) (by omega) (by omega)
    have hsmall : ((ball D V u (a+2)).erase u).card=(a+6)*(a+2) := by
      have he := Finset.card_erase_of_mem (s:=ball D V u (a+2)) (self_mem_ball hu)
      rw [hexact] at he
      omega
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hu (by omega : (a+2)+1≤2*a+7) hy (by omega)
    exact ball_step hyz (Finset.mem_sdiff.mp (hCK hh)).1 ((Finset.mem_filter.mp hh).2 z hz)
  have hballs := bank_avoids (k:=a+4) hf hCK (by omega : (a+4)+(a+3)≤2*a+7) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+4)).card≤1 := by
    have hg := (hcards h (Finset.mem_sdiff.mp (hCK hh)).1).2.1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+4)).card+(ball D V h (a+4)).card=K.card at he
    have hb : (a+6)*(a+4)-1+1=(a+6)*(a+4) :=
      Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
    dsimp [b] at hU
    nlinarith only [hn,hK,hU,hg,he,hb]
  exact near_full_container_false hf (by omega : (a+4)+2≤2*a+7)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega)
    ((Finset.card_le_card hCT).trans (by omega))

/-- With the lower and middle orders excluded, the order bound improves at the same degree. -/
theorem order_to_top {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hne : V.Nonempty) : (2*a+7)*(a+6)≤V.card := by
  have h := order_bound hf hm hne
  by_contra! hh
  rcases (by omega : V.card+2=(2*a+7)*(a+6) ∨ V.card+1=(2*a+7)*(a+6)) with h|h
  · exact lowest_endpoint_false hf hm hne h
  · exact middle_endpoint_false hf hm hne h

/-- Same-degree feedback available for the last endpoint. -/
theorem current_degree_deficiency {a : ℕ} {D : CH.Digraph} {W : Finset ℕ}
    (hf : QFree D W (2*a+7)) (hm : ∀ v ∈ W, 1≤(outN D W v).card) (hne : W.Nonempty) :
    (2*a+7)*(a+6)≤W.card+∑ v ∈ W, (a+6-(outN D W v).card) :=
  deficiency_bound_of_size (fun F U hf' hm' hn' =>
    order_to_top (a:=a) (D:=F) (V:=U) hf' hm' hn') hf hm hne

#print axioms radius_R2_improved
#print axioms middle_tight_root_false
#print axioms middle_endpoint_false
#print axioms order_to_top
#print axioms current_degree_deficiency
end LeanCH.BR.ShenThirdStrip

namespace LeanCH.BR.ShenThirdStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

/-- Prefix feedback at the current degree, rather than at degree s-1. -/
theorem current_degree_prefix {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V)
    (hk : k+2≤2*a+7) (ht : (ball D V u (k+2) \ ball D V u (k+1)).card<a+6) :
    (2*a+7)*(a+6)≤(ball D V u (k+1)).card-1+
      (ball D V u (k+1) \ ball D V u k).card*
        (ball D V u (k+2) \ ball D V u (k+1)).card := by
  have h := prefix_deficiency_of_size (fun F W hf' hm' hn' =>
    order_to_top (a:=a) (D:=F) (V:=W) hf' hm' hn') hf hu hk hm (by omega : a+6≤a+6) ht
  simpa only [Nat.add_sub_cancel_left] using h

theorem cycle_third_strip_below_top {s q n : ℕ} {D : CH.Digraph}
    (hs : 6≤s) (hq : q=2*s-5) (hn : 0<n) (hnq : n<q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s=a+6 := ⟨s-6,by omega⟩
  subst s
  have hq' : q=2*a+7 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_to_top (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms current_degree_prefix
#print axioms cycle_third_strip_below_top
end LeanCH.BR.ShenThirdStrip

namespace LeanCH.BR.ShenThirdStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

/-- At the last order, a genuine minimum-radius root has excess zero, one, or two. -/
theorem top_minimum_root {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+7)*(a+6)) :
    ∃ u ∈ V, (a+6)*(a+3)≤(ball D V u (a+3)).card ∧
      (ball D V u (a+3)).card≤(a+6)*(a+3)+2 ∧
      ∀ v ∈ V, (ball D V u (a+3)).card≤(ball D V v (a+3)).card := by
  obtain ⟨u,hu,hminimum⟩ := Finset.exists_min_image V (fun v => (ball D V v (a+3)).card) hne
  refine ⟨u,hu,radius_R_growth hf hm hu,?_,hminimum⟩
  by_contra! hbad
  have hi (v) (hv : v ∈ V) : (a+6)*(a+3)+3≤(ball D V v (a+3)).card := by
    have hh := hminimum v hv
    omega
  have hj (v) (hv : v ∈ V) : (a+6)*(a+4)-1≤(ball D V v (a+4)).card := by
    have hh := radius_R1_growth hf hm hv
    omega
  have hh := card_ge_of_two_balls hf (by omega : (a+3)+(a+4)≤2*a+7) hi hj hne
  have hsub : (a+6)*(a+4)-1+1=(a+6)*(a+4) :=
    Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
  nlinarith only [hh,hn,hsub]

#print axioms top_minimum_root
end LeanCH.BR.ShenThirdStrip
