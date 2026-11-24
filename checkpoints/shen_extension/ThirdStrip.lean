import checkpoints.shen_extension.CommonTensorClosure

/-! Prefix bounds at q = 2s-5, with the actual lower-degree input discharged. -/
namespace LeanCH.BR.ShenThirdStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

theorem previous_degree_order {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+5≤(outN D V v).card)
    (hne : V.Nonempty) : (2*a+7)*(a+5)+1≤V.card := by
  have h := order_first_strip hf hm hne
  by_contra! hh
  have he : V.card=(2*a+7)*(a+5) := by omega
  exact odd_endpoint_false hf hm he

private theorem base_budget {a r N c t : ℕ} (hr : r ≤ a+4)
    (hN : N+t+1 ≤ (a+5)*r) (hc : c+t+1 ≤ 2*(a+5)) (ht : t < a+5)
    (hw : r ≤ a+3 ∨ c+t+2 ≤ 2*(a+5)) :
    N+c*(a+4+t-(a+5)) < (2*a+7)*(a+4)+1 := by
  by_cases hz : t=0
  · subst t
    have he : a+4+0-(a+5)=0 := by omega
    rw [he, Nat.mul_zero, Nat.add_zero]
    nlinarith [Nat.mul_le_mul_left (a+5) hr]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have he : a+4+(b+1)-(a+5)=b := by omega
  rw [he]
  zify at *
  rcases hw with h | h
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ a+3-r by linarith) (show (0:ℤ) ≤ a+5 by positivity),
      mul_nonneg (show (0:ℤ) ≤ 2*(a+5)-c-(b+1)-1 by linarith) (Int.natCast_nonneg b),
      sq_nonneg ((a:ℤ)+3-b), (show (b:ℤ) ≤ a+3 by linarith)]
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ a+4-r by linarith) (show (0:ℤ) ≤ a+5 by positivity),
      mul_nonneg (show (0:ℤ) ≤ 2*(a+5)-c-(b+1)-2 by linarith) (Int.natCast_nonneg b),
      sq_nonneg ((a:ℤ)+3-b)]


private theorem inner_step {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V)
    (hr : k+2≤a+3)
    (hi : (a+6)*k+1≤(ball D V u k).card)
    (hp : (a+6)*(k+1)+1≤(ball D V u (k+1)).card) :
    (a+6)*(k+2)≤(ball D V u (k+2)).card ∧
    (k+2≤a+2 → (a+6)*(k+2)+1≤(ball D V u (k+2)).card) := by
  classical
  let c := (ball D V u (k+1) \ ball D V u k).card
  let t := (ball D V u (k+2) \ ball D V u (k+1)).card
  have hc : c+(ball D V u k).card=(ball D V u (k+1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t+(ball D V u (k+1)).card=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have aux (hbad : (ball D V u (k+2)).card≤(a+6)*(k+2))
      (hmore : k+2≤a+2 ∨ (ball D V u (k+2)).card<(a+6)*(k+2)) : False := by
    have hpos : 0<(ball D V u (k+1)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    have htlt : t<a+6 := by simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *; omega
    have hN : (ball D V u (k+1)).card-1+t+1≤(a+6)*(k+2) := by omega
    have hct : c+t+1≤2*(a+6) := by simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *; omega
    have hw : k+4≤(a+1)+3 ∨ c+t+2≤2*((a+1)+5) := by
      rcases hmore with h|h
      · exact Or.inl (by omega)
      · right; simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *; omega
    have hb := prefix_deficiency_of_size (fun F W hf' hm' hn' =>
      previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn')
      hf hu (by omega : k+2≤2*a+7) hm (by omega : a+5≤a+6) htlt
    change (2*a+7)*(a+5)+1≤(ball D V u (k+1)).card-1+c*(a+5+t-(a+6)) at hb
    let N := (ball D V u (k+1)).card-1
    have hshift : (N+2*(a+5))+t+1≤((a+1)+5)*(k+4) := by
      change N+t+1≤(a+6)*(k+2) at hN
      nlinarith
    have hcap := base_budget (a:=a+1) (by omega : k+4≤(a+1)+4) hshift (by omega) (by omega) hw
    change (2*a+7)*(a+5)+1≤N+c*(a+5+t-(a+6)) at hb
    have hloss : (a+1)+4+t-((a+1)+5)=a+5+t-(a+6) := by omega
    rw [hloss] at hcap
    nlinarith only [hcap,hb]
  constructor
  · by_contra! hh
    exact aux hh.le (Or.inr hh)
  · intro hh
    by_contra! hn
    exact aux (by omega) (Or.inl hh)

theorem inner_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V) :
    ∀ k, 1≤k → k≤a+2 → (a+6)*k+1≤(ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hr
    by_cases h : k=1
    · subst k; rw [card_B1 (hf.mono_bound (by omega)) hu,Nat.mul_one]
      exact Nat.add_le_add_right (hm u hu) 1
    by_cases h : k=2
    · subst k
      have hh := card_ball_two_ge_twice (by omega : 2≤a+6) (hf.mono_bound (by omega)) hm hu
      simpa only [Nat.mul_comm (a+6) 2] using hh
    obtain ⟨l,rfl⟩ : ∃ l, k=l+2 := ⟨k-2,by omega⟩
    exact (inner_step hf hm hu (by omega)
      (ih l (by omega) (by omega) (by omega)) (ih (l+1) (by omega) (by omega) (by omega))).2 hr

theorem radius_R_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V) :
    (a+6)*(a+3)≤(ball D V u (a+3)).card := by
  exact (inner_step (k:=a+1) hf hm hu (by omega)
    (inner_growth hf hm hu (a+1) (by omega) (by omega))
    (inner_growth hf hm hu ((a+1)+1) (by omega) (by omega))).1

theorem radius_R1_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V) :
    (a+6)*(a+4)≤(ball D V u (a+4)).card+1 := by
  classical
  let b := (a+6)*(a+3)
  let c := (ball D V u (a+3) \ ball D V u (a+2)).card
  let t := (ball D V u (a+4) \ ball D V u (a+3)).card
  have hc : c+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hprev := inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hhalf := radius_R_growth hf hm hu
  change b≤(ball D V u (a+3)).card at hhalf
  let e := (ball D V u (a+3)).card-b
  have he : (ball D V u (a+3)).card=b+e := by omega
  have hcm : c≤a+5+e := by dsimp [b] at he; nlinarith
  by_contra! hbad
  have hbad' : (ball D V u (a+4)).card+2≤b+(a+6) := by dsimp [b]; nlinarith only [hbad]
  have htlt : t<a+6 := by omega
  have hd := prefix_deficiency_of_size (fun F W hf' hm' hn' =>
    previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn') hf hu
      (by omega : (a+2)+2≤2*a+7) hm (by omega : a+5≤a+6) htlt
  change (2*a+7)*(a+5)+1≤(ball D V u (a+3)).card-1+c*(a+5+t-(a+6)) at hd
  have hpos : 0<(ball D V u (a+3)).card := by dsimp [b] at hhalf; nlinarith
  by_cases ht0 : t=0
  · rw [ht0] at hd
    have hloss : a+5+0-(a+6)=0 := by omega
    rw [hloss,Nat.mul_zero,Nat.add_zero] at hd
    have hd' : (2*a+7)*(a+5)+2≤(ball D V u (a+3)).card := by omega
    have hb' : (ball D V u (a+3)).card≤b+(a+4) := by omega
    dsimp [b] at hb'
    nlinarith only [hd',hb']
  obtain ⟨l,hl⟩ : ∃ l, t=l+1 := ⟨t-1,by omega⟩
  have hloss : a+5+t-(a+6)=l := by omega
  rw [hloss] at hd
  have het : e+l≤a+3 := by omega
  have hprod := Nat.mul_le_mul_right l hcm
  have hprod2 := Nat.mul_le_mul_left (a+5+e) het
  have hd' : (2*a+7)*(a+5)+2≤b+e+c*l := by omega
  dsimp [b] at hd'
  nlinarith only [hd',hprod,hprod2,Int.natCast_nonneg e,sq_nonneg (e:ℤ)]

theorem radius_R2_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hu : u ∈ V) :
    (a+6)*(a+5)≤(ball D V u (a+5)).card+3 := by
  classical
  let b := (a+6)*(a+4)-1
  let c := (ball D V u (a+4) \ ball D V u (a+3)).card
  let t := (ball D V u (a+5) \ ball D V u (a+4)).card
  have hc : c+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t+(ball D V u (a+4)).card=(ball D V u (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hprev := radius_R_growth hf hm hu
  have hhalf := radius_R1_growth hf hm hu
  have hb : b+1=(a+6)*(a+4) := by
    exact Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
  have hhalf' : b≤(ball D V u (a+4)).card := by omega
  let e := (ball D V u (a+4)).card-b
  have he : (ball D V u (a+4)).card=b+e := by omega
  have hcm : c≤a+5+e := by nlinarith
  by_contra! hbad
  have hbad' : (ball D V u (a+5)).card+3≤b+(a+6) := by nlinarith only [hbad,hb]
  have htlt : t<a+6 := by omega
  have hd := prefix_deficiency_of_size (fun F W hf' hm' hn' =>
    previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn') hf hu
      (by omega : (a+3)+2≤2*a+7) hm (by omega : a+5≤a+6) htlt
  change (2*a+7)*(a+5)+1≤(ball D V u (a+4)).card-1+c*(a+5+t-(a+6)) at hd
  have hpos : 0<(ball D V u (a+4)).card := by nlinarith only [hhalf',hb]
  by_cases ht0 : t=0
  · rw [ht0] at hd
    have hloss : a+5+0-(a+6)=0 := by omega
    rw [hloss,Nat.mul_zero,Nat.add_zero] at hd
    have hd' : (2*a+7)*(a+5)+2≤(ball D V u (a+4)).card := by omega
    have hb' : (ball D V u (a+4)).card≤b+(a+3) := by omega
    nlinarith only [hd',hb',hb]
  obtain ⟨l,hl⟩ : ∃ l, t=l+1 := ⟨t-1,by omega⟩
  have hloss : a+5+t-(a+6)=l := by omega
  rw [hloss] at hd
  have het : e+l≤a+2 := by omega
  have hprod := Nat.mul_le_mul_right l hcm
  have hprod2 := Nat.mul_le_mul_left (a+5+e) het
  have hd' : (2*a+7)*(a+5)+2≤b+e+c*l := by omega
  nlinarith only [hd',hprod,hprod2,hb,Int.natCast_nonneg e,sq_nonneg (e:ℤ)]

theorem order_bound {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card) (hne : V.Nonempty) :
    (2*a+7)*(a+6)≤V.card+2 := by
  have hi := fun u hu => radius_R_growth hf hm (u:=u) hu
  have hj (u) (hu : u ∈ V) : (a+6)*(a+4)-1≤(ball D V u (a+4)).card := by
    have h := radius_R1_growth hf hm hu
    omega
  have h := card_ge_of_two_balls hf (by omega : (a+3)+(a+4)≤2*a+7) hi hj hne
  have hb : (a+6)*(a+4)-1+1=(a+6)*(a+4) := by
    exact Nat.sub_add_cancel (by nlinarith : 1≤(a+6)*(a+4))
  nlinarith

#print axioms previous_degree_order
#print axioms inner_growth
#print axioms radius_R_growth
#print axioms radius_R1_growth
#print axioms radius_R2_growth
#print axioms order_bound
end LeanCH.BR.ShenThirdStrip
