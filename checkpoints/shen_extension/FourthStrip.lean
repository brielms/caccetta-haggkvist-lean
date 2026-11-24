import checkpoints.shen_extension.ThirdStripEndpoints
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The cutoff q = 2s-6

Write s = a+7, R = a+4 and q = 2R = 2a+8.  The lower-degree input is the closed
strip q = 2(s-1)-4 at degree s-1.  One arithmetic lemma drives every radius:
`growth_arith` turns the prefix deficiency bound into the next ball bound from
the two preceding ones.  The resulting profile is

  |B_k| ≥ sk+1 (k ≤ R-2),  sR-s,  sR-1,  s(R+1)-3,  s(R+2)-5,

so the two-ball bound at radii (R,R) gives order at least qs-3, and the
order qs-3 is excluded by a full-column bank at a tight root.
-/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- The closed strip q = 2(s-1)-4 at degree s-1 = a+6. -/
theorem previous_degree_order {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hne : V.Nonempty) : (2*a+8)*(a+6)+1≤V.card :=
  even_strip_order (a:=a+1) hf hm hne

/-- The scalar step.  `g0 g1 g2` are the allowed losses below the ideal size
`s*k+1` at three consecutive radii.  The step is valid whenever the product
`(s-(g1-g0))*(s-2-(g2-g1))` is below the order still owed by the prefix. -/
private theorem growth_arith {a k P0 P1 P2 c t g0 g1 g2 : ℕ}
    (hc : c+P0=P1) (ht : t+P1=P2) (hpos : 1≤P1)
    (h0 : (a+7)*k+1≤P0+g0) (h1 : (a+7)*(k+1)+1≤P1+g1)
    (hg : g1≤g2) (hde : 2*g1≤g2+g0+1)
    (hd : t<a+7 → (2*a+8)*(a+6)+1≤P1-1+c*(a+6+t-(a+7)))
    (hkey : ((a:ℤ)+7-(g1-g0))*((a:ℤ)+5-(g2-g1)) <
      (2*(a:ℤ)+8)*(a+6)+1-(a+7)*(k+1)+g1)
    (hzero : (a+7)*(k+2)≤(2*a+8)*(a+6)+1+g2) :
    (a+7)*(k+2)+1≤P2+g2 := by
  by_contra! hbad
  have hexp : (a+7)*(k+2)=(a+7)*(k+1)+(a+7) := by ring
  have htlt : t<a+7 := by omega
  have hdef := hd htlt
  rcases Nat.eq_zero_or_pos t with h|h
  · subst h
    have hz : a+6+0-(a+7)=0 := by omega
    rw [hz,Nat.mul_zero] at hdef
    omega
  obtain ⟨l,rfl⟩ : ∃ l, t=l+1 := ⟨t-1,by omega⟩
  have hl : a+6+(l+1)-(a+7)=l := by omega
  rw [hl] at hdef
  have hdef' : (2*a+8)*(a+6)+2≤P1+c*l := by omega
  have hbad' : P2+g2≤(a+7)*(k+2) := by omega
  zify at hc ht h0 h1 hg hde hdef' hbad'
  have hy0 : (0:ℤ)≤P1+g1-((a+7)*(k+1)+1) := by linarith
  have hcb : (c:ℤ)≤(a+7)-(g1-g0)+(P1+g1-((a+7)*(k+1)+1)) := by linarith
  have hlb : (l:ℤ)≤(a+5)-(g2-g1)-(P1+g1-((a+7)*(k+1)+1)) := by linarith
  have m1 := mul_le_mul_of_nonneg_right hcb (Int.natCast_nonneg l)
  have m2 := mul_le_mul_of_nonneg_left hlb
    (by linarith [Int.natCast_nonneg c] :
      (0:ℤ)≤(a+7)-(g1-g0)+(P1+g1-((a+7)*(k+1)+1)))
  have m3 := mul_nonneg hy0 (by linarith : (0:ℤ)≤1+(g2-g1)-(g1-g0))
  nlinarith [m1,m2,m3,sq_nonneg ((P1:ℤ)+g1-((a+7)*(k+1)+1))]

/-- The step on actual balls. -/
theorem growth_step {a k u g0 g1 g2 : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V)
    (hk : k+2≤2*a+8)
    (h0 : (a+7)*k+1≤(ball D V u k).card+g0)
    (h1 : (a+7)*(k+1)+1≤(ball D V u (k+1)).card+g1)
    (hg : g1≤g2) (hde : 2*g1≤g2+g0+1)
    (hkey : ((a:ℤ)+7-(g1-g0))*((a:ℤ)+5-(g2-g1)) <
      (2*(a:ℤ)+8)*(a+6)+1-(a+7)*(k+1)+g1)
    (hzero : (a+7)*(k+2)≤(2*a+8)*(a+6)+1+g2) :
    (a+7)*(k+2)+1≤(ball D V u (k+2)).card+g2 := by
  have hc : (ball D V u (k+1) \ ball D V u k).card+(ball D V u k).card=
      (ball D V u (k+1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : (ball D V u (k+2) \ ball D V u (k+1)).card+(ball D V u (k+1)).card=
      (ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hpos : 1≤(ball D V u (k+1)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
  refine growth_arith hc ht hpos h0 h1 hg hde (fun htlt => ?_) hkey hzero
  exact prefix_deficiency_of_size (fun F W hf' hm' hn' =>
    previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn') hf hu hk hm
      (by omega : a+6≤a+7) htlt

theorem inner_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V) :
    ∀ k, 1≤k → k≤a+2 → (a+7)*k+1≤(ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hr
    by_cases h : k=1
    · subst k; rw [card_B1 (hf.mono_bound (by omega)) hu,Nat.mul_one]
      exact Nat.add_le_add_right (hm u hu) 1
    by_cases h : k=2
    · subst k
      have hh := card_ball_two_ge_twice (by omega : 2≤a+7) (hf.mono_bound (by omega)) hm hu
      simpa only [Nat.mul_comm (a+7) 2] using hh
    obtain ⟨l,rfl⟩ : ∃ l, k=l+2 := ⟨k-2,by omega⟩
    have hl : (l:ℤ)+1≤a+1 := by exact_mod_cast (by omega : l+1≤a+1)
    have hstep := growth_step (g0:=0) (g1:=0) (g2:=0) hf hm hu (by omega)
      (ih l (by omega) (by omega) (by omega)) (ih (l+1) (by omega) (by omega) (by omega))
      le_rfl (by omega)
      (by push_cast; nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : (0:ℤ)≤a+7)])
      (by nlinarith [Nat.mul_le_mul_left (a+7) (by omega : l+2≤a+6)])
    exact hstep

/-- |B_(R-1)| ≥ s(R-1). -/
theorem radius_Rm1_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V) :
    (a+7)*(a+3)≤(ball D V u (a+3)).card := by
  have h : (a+7)*(a+3)+1≤(ball D V u (a+3)).card+1 :=
    growth_step (k:=a+1) (g0:=0) (g1:=0) (g2:=1) hf hm hu (by omega)
      (inner_growth hf hm hu (a+1) (by omega) (by omega))
      (inner_growth hf hm hu (a+2) (by omega) (by omega))
      (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  omega

/-- |B_R| ≥ sR-1. -/
theorem radius_R_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V) :
    (a+7)*(a+4)≤(ball D V u (a+4)).card+1 := by
  have h1 : (a+7)*(a+3)+1≤(ball D V u (a+3)).card+1 :=
    Nat.add_le_add_right (radius_Rm1_growth hf hm hu) 1
  have h : (a+7)*(a+4)+1≤(ball D V u (a+4)).card+2 :=
    growth_step (k:=a+2) (g0:=0) (g1:=1) (g2:=2) hf hm hu (by omega)
      (inner_growth hf hm hu (a+2) (by omega) (by omega))
      h1 (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  omega

/-- |B_(R+1)| ≥ s(R+1)-3. -/
theorem radius_R1_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V) :
    (a+7)*(a+5)≤(ball D V u (a+5)).card+3 := by
  have h0 : (a+7)*(a+3)+1≤(ball D V u (a+3)).card+1 :=
    Nat.add_le_add_right (radius_Rm1_growth hf hm hu) 1
  have h1 : (a+7)*(a+4)+1≤(ball D V u (a+4)).card+2 :=
    Nat.add_le_add_right (radius_R_growth hf hm hu) 1
  have h : (a+7)*(a+5)+1≤(ball D V u (a+5)).card+4 :=
    growth_step (k:=a+3) (g0:=1) (g1:=2) (g2:=4) hf hm hu (by omega)
      h0 h1 (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  omega

/-- |B_(R+2)| ≥ s(R+2)-5. -/
theorem radius_R2_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V) :
    (a+7)*(a+6)≤(ball D V u (a+6)).card+5 := by
  have h0 : (a+7)*(a+4)+1≤(ball D V u (a+4)).card+2 :=
    Nat.add_le_add_right (radius_R_growth hf hm hu) 1
  have h1 : (a+7)*(a+5)+1≤(ball D V u (a+5)).card+4 :=
    Nat.add_le_add_right (radius_R1_growth hf hm hu) 1
  have h : (a+7)*(a+6)+1≤(ball D V u (a+6)).card+6 :=
    growth_step (k:=a+4) (g0:=2) (g1:=4) (g2:=6) hf hm hu (by omega)
      h0 h1 (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  omega

/-- Order at least qs-3. -/
theorem order_bound {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hne : V.Nonempty) :
    (2*a+8)*(a+7)≤V.card+3 := by
  have hi (u) (hu : u ∈ V) : (a+7)*(a+4)-1≤(ball D V u (a+4)).card := by
    have h := radius_R_growth hf hm hu
    omega
  have h := card_ge_of_two_balls hf (by omega : (a+4)+(a+4)≤2*a+8) hi hi hne
  have hb : (a+7)*(a+4)-1+1=(a+7)*(a+4) :=
    Nat.sub_add_cancel (by nlinarith : 1≤(a+7)*(a+4))
  nlinarith

#print axioms previous_degree_order
#print axioms growth_step
#print axioms inner_growth
#print axioms radius_Rm1_growth
#print axioms radius_R_growth
#print axioms radius_R1_growth
#print axioms radius_R2_growth
#print axioms order_bound
end LeanCH.BR.ShenFourthStrip

/-! ## The order qs-3 -/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

private theorem root_budget {a j t N : ℕ}
    (hn : N+t+2=(a+7)*(a+4)) (htj : t+j=a+6) :
    N+(a+6+j)*(t-1)+5≤(2*a+8)*(a+6)+1+t := by
  by_cases ht0 : t=0
  · rw [ht0] at hn ⊢
    simp only [Nat.zero_sub,Nat.mul_zero,Nat.add_zero]
    nlinarith only [hn]
  have hloss : t-1+1=t := by omega
  have hprod := congrArg (fun z : ℕ => z*(a+6+j)) htj
  have hprod2 := congrArg (fun z : ℕ => (a+6+j)*z) hloss
  nlinarith only [hn,htj,hprod,hprod2,Nat.zero_le (j*j),Nat.le_mul_self j]

/-- A root whose radius-R ball has the minimum size sR-1 has at least five full
columns in its last arc table, and every vertex of the punctured (R-1)-ball
reaches each of them within R-1 steps. -/
theorem tight_root_bank {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u ∈ V)
    (hroot : (ball D V u (a+4)).card+1=(a+7)*(a+4)) :
    ∃ (U C : Finset ℕ), U ⊆ V ∧ C ⊆ V \ U ∧ 5≤C.card ∧ C.card≤2*a+8 ∧
      (a+7)*(a+3)≤U.card+1 ∧
      ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y (a+3) := by
  let B := ball D V u (a+3)
  let U := B.erase u
  let S := B \ ball D V u (a+2)
  let T := ball D V u (a+4) \ B
  let j := a+6-T.card
  let C := T.filter (fun h => ∀ v ∈ S, D v h=true)
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card+1=(a+7)*(a+4) := by
    have h := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : a+3≤a+4))
    change T.card+B.card=(ball D V u (a+4)).card at h
    omega
  have hS : S.card+(ball D V u (a+2)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hprev := radius_Rm1_growth hf hm hu
  change (a+7)*(a+3)≤B.card at hprev
  have hinner := inner_growth hf hm hu (a+2) (by omega) (by omega)
  have ht : T.card≤a+6 := by nlinarith only [hT,hprev]
  have htj : T.card+j=a+6 := by dsimp [j]; omega
  have hc : S.card≤a+6+j := by nlinarith only [hT,hS,hinner,htj]
  have hn : U.card+T.card+2=(a+7)*(a+4) := by omega
  have budget := root_budget hn htj
  have hrect := PrefixTensor.rectangle hf hm hu (by omega : 2≤a+7)
    (fun F W hf' hm' hn' => previous_degree_order (a:=a) (D:=F) (V:=W) hf' hm' hn')
    (by omega : (a+2)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by decide : 2≤5)
  have hSc : S.card=a+6+j := hrect.1
  have hC : 5≤C.card := by
    have he : C = (ball D V u ((a+2)+2) \ ball D V u ((a+2)+1)).filter
        (fun h => ∀ v ∈ ball D V u ((a+2)+1) \ ball D V u (a+2), D v h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hexact : (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
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
  have hlarge := inner_growth hf hm hyV (a+2) (by omega) (by omega)
  have hsmall : ((ball D V u (a+2)).erase u).card=(a+7)*(a+2) := by
    have he := Finset.card_erase_of_mem (s:=ball D V u (a+2)) (self_mem_ball hu)
    rw [hexact] at he
    omega
  obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hu (by omega : (a+2)+1≤2*a+8) hy (by omega)
  have hhV := (Finset.mem_sdiff.mp (hCK hh)).1
  exact ball_step hyz hhV ((Finset.mem_filter.mp hh).2 z hz)

/-- The order qs-3 is impossible. -/
theorem lowest_endpoint_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card+3=(2*a+8)*(a+7)) : False := by
  have hsub : (a+7)*(a+4)-1+1=(a+7)*(a+4) :=
    Nat.sub_add_cancel (by nlinarith : 1≤(a+7)*(a+4))
  have hi (v) (hv : v ∈ V) : (a+7)*(a+4)-1≤(ball D V v (a+4)).card := by
    have h := radius_R_growth hf hm hv
    omega
  have hcards := two_balls_boundary_cards hf (by omega : (a+4)+(a+4)≤2*a+8) hi hi (by
    nlinarith only [hn,hsub])
  obtain ⟨u,hu⟩ := hne
  obtain ⟨U,C,hUV,hCK,hC,hCq,hU,hreach⟩ :=
    tight_root_bank hf hm hu (by have := (hcards u hu).1; omega)
  have hballs := ShenThirdStrip.bank_avoids (k:=a+5) hf hCK
    (by omega : (a+5)+(a+3)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+(U.card)=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hbound : K.card+2≤(a+7)*(a+5) := by
    nlinarith only [hn,hK,hU]
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+5)).card≤1 := by
    have hg := radius_R1_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+5)).card+(ball D V h (a+5)).card=K.card at he
    omega
  exact near_full_container_false hf (by omega : (a+5)+2≤2*a+8)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega) hCq

/-- Order at least qs-2. -/
theorem order_above_lowest {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hne : V.Nonempty) :
    (2*a+8)*(a+7)≤V.card+2 := by
  have h := order_bound hf hm hne
  by_contra! hh
  exact lowest_endpoint_false hf hm hne (by omega)

/-- CH at the cutoff q = 2s-6 for every order n ≤ qs-3. -/
theorem cycle_fourth_strip_low {s q n : ℕ} {D : CH.Digraph}
    (hs : 7≤s) (hq : q=2*s-6) (hn : 0<n) (hnq : n+3≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  subst s
  have hq' : q=2*a+8 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_above_lowest (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms tight_root_bank
#print axioms lowest_endpoint_false
#print axioms order_above_lowest
#print axioms cycle_fourth_strip_low
end LeanCH.BR.ShenFourthStrip

/-! ## Containers with two omissions, and the order qs-2 -/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- If every bank ball lies in one container and omits at most two of its
labels, a bank vertex reached within k is reached within two steps. -/
theorem two_omission_reach_short {D : CH.Digraph} {V K C : Finset ℕ} {q k x y : ℕ}
    (hf : QFree D V q) (hk : k+3≤q) (hCV : C ⊆ V)
    (hballs : ∀ h ∈ C, ball D V h k ⊆ K)
    (hmiss : ∀ h ∈ C, (K \ ball D V h k).card≤2)
    (hx : x ∈ C) (hy : y ∈ C) (hyball : y ∈ ball D V x k) :
    y ∈ ball D V x 2 := by
  obtain ⟨hyV,m,hm,w⟩ := mem_ball.mp hyball
  by_cases hsmall : m≤2
  · exact mem_ball.mpr ⟨hyV,m,hsmall,w⟩
  obtain ⟨l,rfl⟩ : ∃ l, m=l+3 := ⟨m-3,by omega⟩
  obtain ⟨v,wv,_,hvy⟩ := w.unsnoc
  obtain ⟨z,wz,hvV,hzv⟩ := wv.unsnoc
  obtain ⟨p,wp,hzV,hpz⟩ := wz.unsnoc
  have hpV : p ∈ V := by
    rcases wp.end_mem_or with h|h
    · exact h ▸ hCV hx
    · exact h
  have hpK : p ∈ K := hballs x hx (mem_ball.mpr ⟨hpV,l,by omega,wp⟩)
  have hzK : z ∈ K := hballs x hx (mem_ball.mpr ⟨hzV,l+1,by omega,wz⟩)
  have hvK : v ∈ K := hballs x hx (mem_ball.mpr ⟨hvV,l+2,by omega,wv⟩)
  have hpnot : p ∉ ball D V y k := by
    intro hp
    obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hp
    exact hf y (i+3) (by omega) (by omega)
      (wi.append (.step hzV hpz (.step hvV hzv (.step hyV hvy (.refl y)))))
  have hznot : z ∉ ball D V y k := by
    intro hz
    obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hz
    exact hf y (i+2) (by omega) (by omega)
      (wi.append (.step hvV hzv (.step hyV hvy (.refl y))))
  have hvnot : v ∉ ball D V y k := by
    intro hv
    obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hv
    exact hf y (i+1) (by omega) (by omega) (wi.snoc hyV hvy)
  have hpz' : p ≠ z := by
    intro he; subst he
    exact hf p 1 (by omega) (by omega) (.step hzV hpz (.refl p))
  have hzv' : z ≠ v := by
    intro he; subst he
    exact hf z 1 (by omega) (by omega) (.step hvV hzv (.refl z))
  have hpv' : p ≠ v := by
    intro he; subst he
    exact hf p 2 (by omega) (by omega) (.step hzV hpz (.step hvV hzv (.refl p)))
  have sub : ({p,z,v} : Finset ℕ) ⊆ K \ ball D V y k := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    · exact Finset.mem_sdiff.mpr ⟨hpK,hpnot⟩
    · exact Finset.mem_sdiff.mpr ⟨hzK,hznot⟩
    · exact Finset.mem_sdiff.mpr ⟨hvK,hvnot⟩
  have hc := Finset.card_le_card sub
  have h3 : ({p,z,v} : Finset ℕ).card=3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact fun h => h.elim hpz' hpv'),Finset.card_pair hzv']
  have hh := hmiss y hy
  omega

/-- Walks in the two-step reach relation lift to walks of at most twice the length. -/
private theorem reach_lift {D : CH.Digraph} {V C : Finset ℕ} {x y m : ℕ}
    (w : Walk (fun a b => decide (a ≠ b ∧ b ∈ ball D V a 2)) C x y m) :
    ∃ l, m≤l ∧ l≤2*m ∧ Walk D V x y l := by
  induction w with
  | refl a => exact ⟨0,le_rfl,le_rfl,.refl a⟩
  | step hb hab _ ih =>
    obtain ⟨l,h1,h2,wl⟩ := ih
    have hd := of_decide_eq_true hab
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hd.2
    have hjp : 1≤j := by
      cases j with
      | zero => cases wj; exact (hd.1 rfl).elim
      | succ => omega
    exact ⟨j+l,by omega,by omega,wj.append wl⟩

/-- Four bank vertices whose balls share a container with at most two omissions each
cannot exist. -/
theorem two_omission_container_false {D : CH.Digraph} {V K C : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hk : k+3≤q) (hq : 8≤q) (hCV : C ⊆ V) (hCK : C ⊆ K)
    (hballs : ∀ h ∈ C, ball D V h k ⊆ K)
    (hmiss : ∀ h ∈ C, (K \ ball D V h k).card≤2)
    (hcard : 4≤C.card) : False := by
  obtain ⟨C',hsub,hC'⟩ := Finset.exists_subset_card_eq hcard
  let E : CH.Digraph := fun a b => decide (a ≠ b ∧ b ∈ ball D V a 2)
  have hE : QFree E C' 4 := by
    intro a m h1 h4 w
    obtain ⟨l,hl1,hl2,wl⟩ := reach_lift w
    exact hf a l (by omega) (by omega) wl
  obtain ⟨t,ht,hsink⟩ := exists_sink hE (Finset.card_pos.mp (by omega)) (by omega)
  have hsubK : C'.erase t ⊆ K \ ball D V t k := by
    intro y hy
    obtain ⟨hne,hyC⟩ := Finset.mem_erase.mp hy
    refine Finset.mem_sdiff.mpr ⟨hCK (hsub hyC),fun hb => ?_⟩
    have h2 := two_omission_reach_short hf hk hCV hballs hmiss (hsub ht) (hsub hyC) hb
    exact hsink y hyC (decide_eq_true ⟨Ne.symm hne,h2⟩)
  have hc := Finset.card_le_card hsubK
  rw [Finset.card_erase_of_mem ht] at hc
  have hh := hmiss t (hsub ht)
  omega

/-- The order qs-2 is impossible. -/
theorem second_endpoint_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card+2=(2*a+8)*(a+7)) : False := by
  obtain ⟨u,hu,hroot⟩ : ∃ u ∈ V, (ball D V u (a+4)).card+1=(a+7)*(a+4) := by
    by_contra hh
    push Not at hh
    have hall (v) (hv : v ∈ V) : (a+7)*(a+4)≤(ball D V v (a+4)).card := by
      have h := radius_R_growth hf hm hv
      have h' := hh v hv
      omega
    have h := card_ge_of_two_balls hf (by omega : (a+4)+(a+4)≤2*a+8) hall hall hne
    nlinarith only [h,hn]
  obtain ⟨U,C,hUV,hCK,hC,_,hU,hreach⟩ := tight_root_bank hf hm hu hroot
  have hballs := ShenThirdStrip.bank_avoids (k:=a+5) hf hCK
    (by omega : (a+5)+(a+3)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+(U.card)=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hbound : K.card+1≤(a+7)*(a+5) := by
    nlinarith only [hn,hK,hU]
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+5)).card≤2 := by
    have hg := radius_R1_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+5)).card+(ball D V h (a+5)).card=K.card at he
    omega
  exact two_omission_container_false hf (by omega : (a+5)+3≤2*a+8) (by omega)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega)

/-- Order at least qs-1: the same-degree host bound for the next orders. -/
theorem order_above_second {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hne : V.Nonempty) :
    (2*a+8)*(a+7)≤V.card+1 := by
  have h := order_above_lowest hf hm hne
  by_contra! hh
  exact second_endpoint_false hf hm hne (by omega)

/-- CH at the cutoff q = 2s-6 for every order n ≤ qs-2. -/
theorem cycle_fourth_strip_below_two {s q n : ℕ} {D : CH.Digraph}
    (hs : 7≤s) (hq : q=2*s-6) (hn : 0<n) (hnq : n+2≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  subst s
  have hq' : q=2*a+8 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_above_second (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms two_omission_reach_short
#print axioms two_omission_container_false
#print axioms second_endpoint_false
#print axioms order_above_second
#print axioms cycle_fourth_strip_below_two
end LeanCH.BR.ShenFourthStrip

/-! ## Same-degree feedback and the rigid order qs-1 -/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- Same-degree rectangle: if the unclipped budget leaves less than one row of
slack, the last layer has its maximal size and `m` columns are full. -/
theorem same_rectangle {q s L k u cmax m : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (hu : u ∈ V) (hs : 1≤s)
    (hlower : ∀ (F : CH.Digraph) (W : Finset ℕ), QFree F W q →
      (∀ v ∈ W, s≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hk : k+2≤q) (ht : (ball D V u (k+2) \ ball D V u (k+1)).card<s)
    (hc : (ball D V u (k+1) \ ball D V u k).card≤cmax)
    (hbudget : ((ball D V u (k+1)).erase u).card+
      cmax*(ball D V u (k+2) \ ball D V u (k+1)).card+m≤
      L+(ball D V u (k+2) \ ball D V u (k+1)).card)
    (hm1 : 1≤m) :
    (ball D V u (k+1) \ ball D V u k).card=cmax ∧
    m≤((ball D V u (k+2) \ ball D V u (k+1)).filter
      (fun h => ∀ v ∈ ball D V u (k+1) \ ball D V u k, D v h=true)).card := by
  have hret := minOut_prefix_erase (d:=1) hf hu (by omega : (k+1)+1≤q) hm
    (by change 1+(ball D V u (k+2) \ ball D V u (k+1)).card≤s; omega)
  have cap := PrefixTensor.same_degree_missing_capacity hf hm hu hs hlower hk hret
  let U := (ball D V u (k+1)).erase u
  let S := ball D V u (k+1) \ ball D V u k
  let T := ball D V u (k+2) \ ball D V u (k+1)
  let miss := fun v => T \ outN D T v
  change L+(∑ v ∈ S,(miss v).card)≤U.card+S.card*T.card at cap
  change T.card<s at ht
  change S.card≤cmax at hc
  change U.card+cmax*T.card+m≤L+T.card at hbudget
  suffices result : S.card=cmax ∧ m≤(T.filter (fun h => ∀ v ∈ S, D v h=true)).card by
    refine ⟨result.1,?_⟩
    have he : T.filter (fun h => ∀ v ∈ S, D v h=true) =
        (ball D V u (k+2) \ ball D V u (k+1)).filter
          (fun h => ∀ v ∈ ball D V u (k+1) \ ball D V u k, D v h=true) := by
      ext h
      simp only [Finset.mem_filter]
      rfl
    rw [← he]
    exact result.2
  have hSc : S.card=cmax := by
    by_contra hne
    have hstep : S.card+1≤cmax := by omega
    have hmul := Nat.mul_le_mul_right T.card hstep
    have hexp : (S.card+1)*T.card=S.card*T.card+T.card := by ring
    omega
  refine ⟨hSc,?_⟩
  rw [hSc] at cap
  have hmSum : (∑ v ∈ S,(miss v).card)+m≤T.card := by omega
  have sub : T \ S.biUnion miss ⊆ T.filter (fun h => ∀ v ∈ S, D v h=true) := by
    intro h hh
    obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp hh
    refine Finset.mem_filter.mpr ⟨ht,fun v hv => ?_⟩
    by_contra hb
    exact hn (Finset.mem_biUnion.mpr
      ⟨v,hv,Finset.mem_sdiff.mpr ⟨ht,fun he => hb (mem_outN.mp he).2⟩⟩)
  have hbi : S.biUnion miss ⊆ T := by
    intro h hh
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hh
    exact (Finset.mem_sdiff.mp hv).1
  have h1 := Finset.card_biUnion_le (s:=S) (t:=miss)
  have h2 := Finset.card_sdiff_add_card_eq_card hbi
  have h3 := Finset.card_le_card sub
  omega

private theorem capped_budget {a e t N : ℕ}
    (hN : N+2=(a+7)*(a+4)+e) (ht : t+e=a+5) :
    N+(a+6+e)*t+(a+4)≤(2*a+8)*(a+7)-1+t := by
  have hpos : 1≤(2*a+8)*(a+7) := by nlinarith
  have hprod := congrArg (fun z : ℕ => (a+6+e)*z) ht
  have hsq : e≤e*e := Nat.le_mul_self e
  have key : N+(a+6+e)*t+(a+4)+1≤(2*a+8)*(a+7)+t := by
    nlinarith only [hN,ht,hprod,hsq]
  omega

/-- Under the order cap n ≤ qs-1, every (R+1)-ball has at least s(R+1)-2 vertices. -/
theorem capped_R1_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (hcap : V.card+1≤(2*a+8)*(a+7)) :
    (a+7)*(a+5)≤(ball D V v (a+5)).card+2 := by
  by_contra! hbad
  have hlow := radius_R1_growth hf hm hv
  have hR := radius_R_growth hf hm hv
  have hRm := radius_Rm1_growth hf hm hv
  let B := ball D V v (a+4)
  let U := B.erase v
  let S := B \ ball D V v (a+3)
  let T := ball D V v (a+5) \ B
  let e := B.card+1-(a+7)*(a+4)
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hv)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    change U.card=B.card-1 at he
    omega
  have hBe : B.card+1=(a+7)*(a+4)+e := by
    change (a+7)*(a+4)≤B.card+1 at hR
    dsimp only [e]; omega
  have hT : T.card+B.card=(ball D V v (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V v (a+3)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hte : T.card+e=a+5 := by omega
  have hc : S.card≤a+6+e := by omega
  have hN : U.card+2=(a+7)*(a+4)+e := by omega
  have budget := capped_budget hN hte
  have hrect := same_rectangle (L:=(2*a+8)*(a+7)-1) hf hm hv (by omega : 1≤a+7)
    (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
    (by omega : (a+3)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+4)
  have hSc : S.card=a+6+e := hrect.1
  let C := T.filter (fun h => ∀ w ∈ S, D w h=true)
  have hC : a+4≤C.card := by
    have he : C = (ball D V v ((a+3)+2) \ ball D V v ((a+3)+1)).filter
        (fun h => ∀ w ∈ ball D V v ((a+3)+1) \ ball D V v (a+3), D w h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hexact : (ball D V v (a+3)).card=(a+7)*(a+3) := by omega
  have hUV : U ⊆ V := (Finset.erase_subset v B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hn (Finset.mem_of_mem_erase hU)⟩
  have hreach : ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y (a+4) := by
    intro h hh y hy
    have hlarge := radius_Rm1_growth hf hm (hUV hy)
    have hsmall : ((ball D V v (a+3)).erase v).card+1=(a+7)*(a+3) := by
      have he := Finset.card_erase_of_mem (s:=ball D V v (a+3)) (self_mem_ball hv)
      have hp : 0<(ball D V v (a+3)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
      omega
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hv (by omega : (a+3)+1≤2*a+8) hy (by omega)
    exact ball_step hyz (Finset.mem_sdiff.mp (hCK hh)).1 ((Finset.mem_filter.mp hh).2 z hz)
  have hballs := ShenThirdStrip.bank_avoids (k:=a+4) hf hCK
    (by omega : (a+4)+(a+4)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+4)).card≤2 := by
    have hg := radius_R_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+4)).card+(ball D V h (a+4)).card=K.card at he
    omega
  exact two_omission_container_false hf (by omega : (a+4)+3≤2*a+8) (by omega)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega)

/-- At the order qs-1 every forward and backward R-ball has exactly sR vertices. -/
theorem third_order_rigid {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card+1=(2*a+8)*(a+7)) :
    ∀ v ∈ V, (ball D V v (a+4)).card=(a+7)*(a+4) ∧
      (reverseBall D V v (a+4)).card=(a+7)*(a+4) := by
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hall (u) (hu : u ∈ V) : (a+7)*(a+4)≤(ball D V u (a+4)).card := by
    by_contra! hlt
    have hroot : (ball D V u (a+4)).card+1=(a+7)*(a+4) := by
      have h := radius_R_growth hf hm hu
      omega
    obtain ⟨U,C,hUV,hCK,hC,_,hU,hreach⟩ := tight_root_bank hf hm hu hroot
    have hballs := ShenThirdStrip.bank_avoids (k:=a+5) hf hCK
      (by omega : (a+5)+(a+3)≤2*a+8) hreach
    let K := V \ U
    have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
    have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+5)).card≤2 := by
      have hg := capped_R1_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1 (by omega)
      have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
      change (K \ ball D V h (a+5)).card+(ball D V h (a+5)).card=K.card at he
      omega
    exact two_omission_container_false hf (by omega : (a+5)+3≤2*a+8) (by omega)
      (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega)
  have hcards := two_balls_boundary_cards hf (by omega : (a+4)+(a+4)≤2*a+8) hall hall
    (by omega)
  intro v hv
  exact ⟨(hcards v hv).1,(hcards v hv).2.2⟩

#print axioms same_rectangle
#print axioms capped_R1_growth
#print axioms third_order_rigid
end LeanCH.BR.ShenFourthStrip

/-! ## The order qs-1 is flat when s ≥ 8

Throughout this section the order is qs-1 and a ≥ 1.  Three container arguments raise the
ball bounds at radii R+2, R-1 and R+1 by one unit each.  The two-ball bound at radii
(R-1, R+1) is then saturated at every vertex. -/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

private theorem two_le_sq_add_one (f : ℕ) : 2*f≤f*f+1 := by
  rcases Nat.eq_zero_or_pos f with h|h
  · subst h; omega
  obtain ⟨k,rfl⟩ : ∃ k, f=k+1 := ⟨f-1,by omega⟩
  have hk : (k+1)*(k+1)=k*k+2*k+1 := by ring
  omega

private theorem outer_budget {a f g t N m : ℕ}
    (hN : N+3=(a+7)*(a+5)+f) (ht : t+f+g=a+5)
    (hm : m≤a+2 ∨ (f=0 ∧ m≤a+3)) :
    N+(a+5+f)*t+m≤(2*a+8)*(a+7)-1+t := by
  have hpos : 1≤(2*a+8)*(a+7) := by nlinarith
  have hprod := congrArg (fun z : ℕ => (a+5+f)*z) ht
  have hsq := two_le_sq_add_one f
  have key : N+(a+5+f)*t+m+1≤(2*a+8)*(a+7)+t := by
    rcases hm with hm|⟨hf0,hm⟩
    · nlinarith only [hN,ht,hprod,hsq,hm,Nat.zero_le (g*a),Nat.zero_le (g*f),Nat.zero_le g]
    · subst hf0
      nlinarith only [hN,ht,hprod,hm,Nat.zero_le (g*a),Nat.zero_le g]
  omega

/-- At the order qs-1 every (R+2)-ball has at least s(R+2)-3 vertices. -/
theorem capped_R2_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    (a+7)*(a+6)≤(ball D V v (a+6)).card+3 := by
  by_contra! hbad
  have hrig := third_order_rigid hf hm hn
  have hcap := capped_R1_growth hf hm hv hn.le
  let B := ball D V v (a+5)
  let U := B.erase v
  let S := B \ ball D V v (a+4)
  let T := ball D V v (a+6) \ B
  let f := B.card+2-(a+7)*(a+5)
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hv)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    change U.card=B.card-1 at he
    omega
  have hBf : B.card+2=(a+7)*(a+5)+f := by
    change (a+7)*(a+5)≤B.card+2 at hcap
    dsimp only [f]; omega
  have hT : T.card+B.card=(ball D V v (a+6)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V v (a+4)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hR := (hrig v hv).1
  have hexp : (a+7)*(a+6)=(a+7)*(a+5)+(a+7) := by ring
  have hexq : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexr : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  let g := a+5-f-T.card
  have htg : T.card+f+g=a+5 := by dsimp only [g]; omega
  have hc : S.card≤a+5+f := by omega
  have hN : U.card+3=(a+7)*(a+5)+f := by omega
  have hUV : U ⊆ V := (Finset.erase_subset v B).trans ball_subset
  let C := T.filter (fun h => ∀ w ∈ S, D w h=true)
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hn (Finset.mem_of_mem_erase hU)⟩
  have hCe : C = (ball D V v ((a+4)+2) \ ball D V v ((a+4)+1)).filter
      (fun h => ∀ w ∈ ball D V v ((a+4)+1) \ ball D V v (a+4), D w h=true) := by
    ext h
    simp only [C,Finset.mem_filter]
    rfl
  have hreach : ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y (a+5) := by
    intro h hh y hy
    have hlarge := (hrig y (hUV hy)).1
    have hsmall : ((ball D V v (a+4)).erase v).card+1=(a+7)*(a+4) := by
      have he := Finset.card_erase_of_mem (s:=ball D V v (a+4)) (self_mem_ball hv)
      have hp : 0<(ball D V v (a+4)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
      omega
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hv (by omega : (a+4)+1≤2*a+8) hy (by omega)
    exact ball_step hyz (Finset.mem_sdiff.mp (hCK hh)).1 ((Finset.mem_filter.mp hh).2 z hz)
  have hballs := ShenThirdStrip.bank_avoids (k:=a+3) hf hCK
    (by omega : (a+3)+(a+5)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+3)).card+f≤2 := by
    have hg := radius_Rm1_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+3)).card+(ball D V h (a+3)).card=K.card at he
    omega
  have hCV : C ⊆ V := fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1
  have hmiss2 (h) (hh : h ∈ C) : (K \ ball D V h (a+3)).card≤2 := by
    have := hmiss h hh; omega
  have hmiss1 (hpos : 1≤f) (h) (hh : h ∈ C) : (K \ ball D V h (a+3)).card≤1 := by
    have := hmiss h hh; omega
  by_cases hf0 : f=0
  · have budget := outer_budget (m:=a+3) hN htg (Or.inr ⟨hf0,le_rfl⟩)
    have hrect := same_rectangle (L:=(2*a+8)*(a+7)-1) hf hm hv (by omega : 1≤a+7)
      (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
      (by omega : (a+4)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+3)
    have hC : a+3≤C.card := by rw [hCe]; exact hrect.2
    exact two_omission_container_false hf (by omega : (a+3)+3≤2*a+8) (by omega)
      hCV hCK hballs hmiss2 (by omega)
  · have budget := outer_budget (m:=a+2) hN htg (Or.inl le_rfl)
    have hrect := same_rectangle (L:=(2*a+8)*(a+7)-1) hf hm hv (by omega : 1≤a+7)
      (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
      (by omega : (a+4)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+2)
    have hC : a+2≤C.card := by rw [hCe]; exact hrect.2
    exact near_full_container_false hf (by omega : (a+3)+2≤2*a+8)
      hCV hCK hballs (hmiss1 (by omega)) (by omega)
      ((Finset.card_le_card hCT).trans (by omega))

private theorem inner_budget {a x t N : ℕ}
    (hN : N=(a+7)*(a+2)+x) (ht : t+x=a+6) :
    N+(a+7+x)*t+(a+5)≤(2*a+8)*(a+7)-1+t := by
  have hpos : 1≤(2*a+8)*(a+7) := by nlinarith
  have hprod := congrArg (fun z : ℕ => (a+7+x)*z) ht
  have hsq : x≤x*x := Nat.le_mul_self x
  have key : N+(a+7+x)*t+(a+5)+1≤(2*a+8)*(a+7)+t := by
    nlinarith only [hN,ht,hprod,hsq]
  omega

/-- At the order qs-1 every (R-1)-ball has at least s(R-1)+1 vertices. -/
theorem third_inner_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    (a+7)*(a+3)+1≤(ball D V v (a+3)).card := by
  by_contra! hbad
  have hlow := radius_Rm1_growth hf hm hv
  have hroot : (ball D V v (a+3)).card=(a+7)*(a+3) := by omega
  let B := ball D V v (a+2)
  let U := B.erase v
  let S := B \ ball D V v (a+1)
  let T := ball D V v (a+3) \ B
  have hprev := inner_growth hf hm hv (a+2) (by omega) (by omega)
  have hinner := inner_growth hf hm hv (a+1) (by omega) (by omega)
  change (a+7)*(a+2)+1≤B.card at hprev
  let x := B.card-((a+7)*(a+2)+1)
  have hBx : B.card=(a+7)*(a+2)+1+x := by dsimp only [x]; omega
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hv)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card=(ball D V v (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V v (a+1)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexp : (a+7)*(a+3)=(a+7)*(a+2)+(a+7) := by ring
  have hexq : (a+7)*(a+2)=(a+7)*(a+1)+(a+7) := by ring
  have hexr : (a+7)*(a+6)=(a+7)*(a+2)+4*(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+2))+4*(a+7) := by ring
  have htx : T.card+x=a+6 := by omega
  have hc : S.card≤a+7+x := by omega
  have hN : U.card=(a+7)*(a+2)+x := by omega
  have budget := inner_budget hN htx
  have hrect := same_rectangle (L:=(2*a+8)*(a+7)-1) hf hm hv (by omega : 1≤a+7)
    (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
    (by omega : (a+1)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+5)
  have hSc : S.card=a+7+x := hrect.1
  let C := T.filter (fun h => ∀ w ∈ S, D w h=true)
  have hC : a+5≤C.card := by
    have he : C = (ball D V v ((a+1)+2) \ ball D V v ((a+1)+1)).filter
        (fun h => ∀ w ∈ ball D V v ((a+1)+1) \ ball D V v (a+1), D w h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hexact : (ball D V v (a+1)).card=(a+7)*(a+1)+1 := by omega
  have hUV : U ⊆ V := (Finset.erase_subset v B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hn (Finset.mem_of_mem_erase hU)⟩
  have hreach : ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y (a+2) := by
    intro h hh y hy
    have hlarge := inner_growth hf hm (hUV hy) (a+1) (by omega) (by omega)
    have hsmall : ((ball D V v (a+1)).erase v).card=(a+7)*(a+1) := by
      have he := Finset.card_erase_of_mem (s:=ball D V v (a+1)) (self_mem_ball hv)
      rw [hexact] at he
      omega
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hv (by omega : (a+1)+1≤2*a+8) hy (by omega)
    exact ball_step hyz (Finset.mem_sdiff.mp (hCK hh)).1 ((Finset.mem_filter.mp hh).2 z hz)
  have hballs := ShenThirdStrip.bank_avoids (k:=a+6) hf hCK
    (by omega : (a+6)+(a+2)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+6)).card≤2 := by
    have hg := capped_R2_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1 hn ha
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+6)).card+(ball D V h (a+6)).card=K.card at he
    omega
  exact two_omission_container_false hf (by omega : (a+6)+3≤2*a+8) (by omega)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega)

/-- At the order qs-1 every (R+1)-ball has at least s(R+1)-1 vertices. -/
theorem third_outer_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    (a+7)*(a+5)≤(ball D V v (a+5)).card+1 := by
  by_contra! hbad
  have hrig := third_order_rigid hf hm hn
  have hcap := capped_R1_growth hf hm hv hn.le
  have hin := third_inner_growth hf hm hv hn ha
  let B := ball D V v (a+4)
  let U := B.erase v
  let S := B \ ball D V v (a+3)
  let T := ball D V v (a+5) \ B
  have hR : B.card=(a+7)*(a+4) := (hrig v hv).1
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hv)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card=(ball D V v (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V v (a+3)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hTc : T.card=a+5 := by omega
  have hc : S.card≤a+6 := by omega
  have hprod : (a+6)*(a+5)=(a+7)*(a+4)+2 := by ring
  have budget : U.card+(a+6)*T.card+(a+3)≤(2*a+8)*(a+7)-1+T.card := by
    rw [hTc]; omega
  have hrect := same_rectangle (L:=(2*a+8)*(a+7)-1) hf hm hv (by omega : 1≤a+7)
    (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
    (by omega : (a+3)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+3)
  have hSc : S.card=a+6 := hrect.1
  let C := T.filter (fun h => ∀ w ∈ S, D w h=true)
  have hC : a+3≤C.card := by
    have he : C = (ball D V v ((a+3)+2) \ ball D V v ((a+3)+1)).filter
        (fun h => ∀ w ∈ ball D V v ((a+3)+1) \ ball D V v (a+3), D w h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hUV : U ⊆ V := (Finset.erase_subset v B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hn (Finset.mem_of_mem_erase hU)⟩
  have hreach : ∀ h ∈ C, ∀ y ∈ U, h ∈ ball D V y (a+4) := by
    intro h hh y hy
    have hlarge := third_inner_growth hf hm (hUV hy) hn ha
    have hsmall : ((ball D V v (a+3)).erase v).card+1=(ball D V v (a+3)).card := by
      have he := Finset.card_erase_of_mem (s:=ball D V v (a+3)) (self_mem_ball hv)
      have hp : 0<(ball D V v (a+3)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
      omega
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hv (by omega : (a+3)+1≤2*a+8) hy (by omega)
    exact ball_step hyz (Finset.mem_sdiff.mp (hCK hh)).1 ((Finset.mem_filter.mp hh).2 z hz)
  have hballs := ShenThirdStrip.bank_avoids (k:=a+4) hf hCK
    (by omega : (a+4)+(a+4)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+4)).card≤1 := by
    have hg := (hrig h (Finset.mem_sdiff.mp (hCK hh)).1).1
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+4)).card+(ball D V h (a+4)).card=K.card at he
    omega
  exact near_full_container_false hf (by omega : (a+4)+2≤2*a+8)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss (by omega)
    ((Finset.card_le_card hCT).trans (by omega))

/-- At the order qs-1 with s ≥ 8 the three middle balls have forced sizes at every vertex,
and the backward (R+1)-ball has the forward size. -/
theorem third_order_flat {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    ∀ v ∈ V, (ball D V v (a+3)).card=(a+7)*(a+3)+1 ∧
      (ball D V v (a+4)).card=(a+7)*(a+4) ∧
      (ball D V v (a+5)).card+1=(a+7)*(a+5) ∧
      (reverseBall D V v (a+5)).card+1=(a+7)*(a+5) := by
  have hpos : 1≤(a+7)*(a+5) := by nlinarith
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hi := fun v hv => third_inner_growth hf hm (v:=v) hv hn ha
  have hj (v) (hv : v ∈ V) : (a+7)*(a+5)-1≤(ball D V v (a+5)).card := by
    have h := third_outer_growth hf hm hv hn ha
    omega
  have hcards := two_balls_boundary_cards hf (by omega : (a+3)+(a+5)≤2*a+8) hi hj (by omega)
  intro v hv
  obtain ⟨h1,h2,h3⟩ := hcards v hv
  exact ⟨h1,(third_order_rigid hf hm hn v hv).1,by omega,by omega⟩

#print axioms capped_R2_growth
#print axioms third_inner_growth
#print axioms third_outer_growth
#print axioms third_order_flat
end LeanCH.BR.ShenFourthStrip
