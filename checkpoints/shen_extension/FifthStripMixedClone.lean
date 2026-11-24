import checkpoints.shen_extension.MixedCloneTensor
import checkpoints.shen_extension.FifthStripCommonSuccessors
import checkpoints.shen_extension.DotFourthStripClosure_20261118

namespace LeanCH.BR.ShenFifthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open DotTwoPassShellTransport
open Classical

local macro "strip_arith" : tactic =>
  `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at * <;> omega))

private theorem price_arith {a : ℕ} (ha : 52≤a) :
    let s := a+7
    let q := 2*a+7
    let B := s*(a+3)-1
    let C := s*(a+4)-3
    (2*s)*(q*s+8)*((q*s+8)-(B+C)) < (B+C-1-s*s)^2 := by
  obtain ⟨x,rfl⟩ : ∃ x,a=x+52 := ⟨a-52,by omega⟩
  dsimp only
  let s := x+52+7
  let q := 2*(x+52)+7
  let B := s*(x+52+3)-1
  let C := s*(x+52+4)-3
  change (2*s)*(q*s+8)*((q*s+8)-(B+C)) < (B+C-1-s*s)^2
  have hs : B+C+4=q*s := by dsimp [B,C,s,q]; strip_arith
  have h1 : q*s+8-(B+C)=12 := by omega
  have h2 : B+C-1-s*s=x^2+111*x+3063 := by
    have he : q*s=s*s+5+(x^2+111*x+3063) := by dsimp [q,s]; ring
    omega
  rw [h1,h2]
  dsimp [q,s]
  ring_nf
  omega

private theorem fifth_payment {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 52≤a) (hf : QFree D V (2*a+7)) (hm : ∀ v∈V,a+7≤(outN D V v).card)
    (hu : u∈V) (hk : k+2≤a+7) (ht : (shell D V (k+1) u).card<a+7)
    (small : (ball D V u (k+2)).card≤(a+7)*(k+2))
    (prev : (a+7)*k+1≤(ball D V u k).card) :
    (2*a+7)*(a+7)+8+holes D V (k+1) u≤((ball D V u (k+1)).erase u).card+
      (layer D V (k+1) u).card*(shell D V (k+1) u).card := by
  apply ShenMixedClone.prefix_price (s:=a+7) (i:=a+3) (j:=a+4)
    (B:=(a+7)*(a+3)-1) (C:=(a+7)*(a+4)-3) (M:=2*(a+7)) (J:=(a+7)*(a+7))
    (by omega) _ hf hm hu (by omega) (by omega) ht _ _ (price_arith ha)
  · intro F W h m _ v hv
    obtain ⟨_,h1,h2⟩ := middle_growth h m hv
    constructor <;> omega
  · have h1 := Finset.card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+1≤k+2 by omega))
    have h2 := Finset.card_le_card (Finset.erase_subset u (ball D V u (k+1)))
    have h3 := Nat.mul_le_mul_left (a+7) hk
    omega
  · have h := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
      (show k≤k+1 by omega))
    have h1 := Finset.card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+1≤k+2 by omega))
    simp only [layer,Nat.add_sub_cancel]
    rw [Nat.mul_add] at small
    omega

/-- Two applications of the paid-prefix transfer on the same capped
source. The universal floors charged to copies remain the weaker floors. -/
theorem mixed_profile {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 52≤a) (hf : QFree D V (2*a+7)) (hm : ∀ v∈V,a+7≤(outN D V v).card)
    (hn : V.card≤(2*a+7)*(a+7)) :
    ∀ u∈V, (a+7)*(a+2)+1≤(ball D V u (a+2)).card ∧
      (a+7)*(a+3)+1≤(ball D V u (a+3)).card ∧
      (a+7)*(a+4)≤(ball D V u (a+4)).card := by
  let s := a+7
  let L := (2*a+7)*s+8
  have prof := iterated_profile (e:=8) hf hm (by omega) (by omega) (by omega)
  have near (u) (hu : u∈V) := (prof u hu).1
  have mid (u) (hu : u∈V) : s*(a+3)+1≤(ball D V u (a+3)).card := by
    have h := ShenMixedClone.paid_growth (k:=a+1) (r:=a+5) (c:=s) (t:=a+6)
      (L:=L) (H:=s*(a+5)-5) (e:=5) hf hu (fun v hv => inner_growth hf hm hv (a+1) le_rfl)
      (near u hu) (fun v hv => by have := (outer_growth hf hm hv).1; dsimp [s]; omega)
      (by dsimp [s]; ring) (by dsimp [s]; omega) (by dsimp [s,L]; strip_arith)
      (by dsimp [s]; strip_arith) (by omega) (by omega) (by omega) (by
        intro bad
        have hp := near u hu
        have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
          (show (a+1)+1≤(a+1)+2 by omega))
        apply fifth_payment ha hf hm hu (by omega) _ _ (inner_growth hf hm hu (a+1) le_rfl)
        · unfold shell
          simp only [Nat.add_assoc,Nat.reduceAdd] at ht bad ⊢
          strip_arith
        · strip_arith)
    rw [show a+1+2=a+3 by omega] at h
    dsimp [s] at *
    strip_arith
  intro u hu
  refine ⟨near u hu,mid u hu,?_⟩
  have h := ShenMixedClone.paid_growth (k:=a+2) (r:=a+4) (c:=s) (t:=a+5)
    (L:=L) (H:=s*(a+4)-3) (e:=3) hf hu near (mid u hu)
    (fun v hv => by have := (middle_growth hf hm hv).2.2; dsimp [s]; omega)
    (by dsimp [s]; ring) (by dsimp [s]; omega) (by dsimp [s,L]; strip_arith)
    (by dsimp [s]; strip_arith) (by omega) (by omega) (by omega) (by
      intro bad
      have hp := mid u hu
      have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
        (show (a+2)+1≤(a+2)+2 by omega))
      apply fifth_payment ha hf hm hu (by omega) _ _ (near u hu)
      · unfold shell
        simp only [Nat.add_assoc,Nat.reduceAdd] at ht bad ⊢
        dsimp [s] at *
        strip_arith
      · dsimp [s] at *; strip_arith)
  rw [show a+2+2=a+4 by omega] at h
  dsimp [s] at *
  strip_arith

#print axioms mixed_profile

theorem mixed_order_floor {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 52≤a) (hf : QFree D V (2*a+7)) (hm : ∀ v∈V,a+7≤(outN D V v).card)
    (ne : V.Nonempty) : (2*a+7)*(a+7)≤V.card := by
  by_contra! small
  have pr := mixed_profile ha hf hm small.le
  have := card_ge_of_two_balls hf (by omega : (a+3)+(a+4)≤2*a+7)
    (fun v hv => (pr v hv).2.1) (fun v hv => (pr v hv).2.2) ne
  strip_arith

/-- The two improved floors saturate the mixed-radius budget at the top
order. A boundary table there violates the common-successor tensor bound. -/
theorem mixed_top_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 52≤a) (hf : QFree D V (2*a+7)) (hm : ∀ v∈V,a+7≤(outN D V v).card)
    (ne : V.Nonempty) (hn : V.card=(2*a+7)*(a+7)) : False := by
  have pr := mixed_profile ha hf hm hn.le
  have pair : (a+3)+(a+4)≤2*a+7 := by omega
  have rigid := two_balls_boundary_cards hf pair (fun v hv => (pr v hv).2.1)
    (fun v hv => (pr v hv).2.2) (by strip_arith)
  have total (x) (hx : x∈V) (y) (hy : y∈V) :
      y∈ball D V x (a+4) ∨ x∈ball D V y (a+4) := by
    by_cases h : y∈ball D V x (a+3)
    · exact Or.inl (ball_mono_radius (by omega) h)
    · have comp := two_balls_boundary_complement hf pair (fun v hv => (pr v hv).2.1)
        (fun v hv => (pr v hv).2.2) (by strip_arith) hx
      have back : y∈reverseBall D V x (a+4) := by
        rw [comp]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy,h⟩)
      exact Or.inr (Finset.mem_filter.mp back).2
  obtain ⟨u,hu⟩ := ne
  let S := ball D V u (a+3) \ ball D V u (a+2)
  let T := ball D V u (a+4) \ ball D V u (a+3)
  let U := (ball D V u (a+3)).erase u
  let H := ∑ x∈S,(T \ outN D T x).card
  have hS : S.card+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hT : T.card+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hU : U.card+1=(ball D V u (a+3)).card := Finset.card_erase_add_one (self_mem_ball hu)
  have hR := (rigid u hu).1
  have hN := (rigid u hu).2.1
  have hTc : T.card=a+6 := by strip_arith
  have hSc : S.card≤a+7 := by have := (pr u hu).1; strip_arith
  have retained := minOut_prefix_erase (d:=1) hf hu (by omega : (a+3)+1≤2*a+7) hm
    (show 1+T.card≤a+7 by omega)
  have budget := PrefixTensor.same_degree_missing_capacity (k:=a+2) hf hm hu (by omega)
    (fun _ _ h m n => mixed_order_floor ha h m n) (by omega) retained
  change (2*a+7)*(a+7)+H≤U.card+S.card*T.card at budget
  rw [hTc] at budget
  have hH : H≤2*(a+7) := by
    nlinarith only [budget,hU,hR,Nat.mul_le_mul_right (a+6) hSc]
  have low : a+5≤S.card := by
    by_contra! bad
    nlinarith only [budget,hU,hR,Nat.mul_le_mul_right (a+6) (show S.card≤a+4 by omega),
      Nat.zero_le H,ha]
  have hSV : S⊆V := Finset.sdiff_subset.trans ball_subset
  have hTV : T⊆V := Finset.sdiff_subset.trans ball_subset
  let e := (a+19)/2
  have obs := ShenCommonSuccessor.dense_table_bound (r:=a+3) (g:=6) (e:=e)
    hf hSV hTV (by omega) (fun z hz => (rigid z (hTV hz)).1.ge)
    (fun x hx => (rigid x (hSV hx)).2.1.le) (fun x hx y hy => total x (hSV hx) y (hSV hy))
    (by omega) (by dsimp [e]; strip_arith) (by dsimp [e]; omega) (by dsimp [e]; omega)
  change 7*S.card≤7*(e+1)+H at obs
  dsimp [e] at obs
  omega

theorem cycle_fifth_strip_closed {s q n : ℕ} {D : CH.Digraph}
    (hs : 59≤s) (hq : q=2*s-7) (hn : 0<n) (hc : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a,s=a+7 := ⟨s-7,by omega⟩
  have he : q=2*a+7 := by omega
  rw [he] at hc ⊢
  by_contra no
  have hf := qfree_of_noShort hl no
  have md := fun v (hv : v∈Finset.range n) => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)
  have ne := Finset.card_pos.mp (by rwa [Finset.card_range] : 0<(Finset.range n).card)
  have h := mixed_order_floor (by omega : 52≤a) hf md ne
  rw [Finset.card_range] at h
  exact mixed_top_false (by omega) hf md ne (by rw [Finset.card_range]; omega)

#print axioms mixed_order_floor
#print axioms mixed_top_false
#print axioms cycle_fifth_strip_closed

/-- Combine the strip with the preceding checked regions using the
literal ceiling in CH. -/
theorem ch_above_fifth_threshold {s n : ℕ} {D : CH.Digraph} (hs : 59≤s)
    (hn : 0<n) (horder : (2*s-8)*s<n)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  let q := CH.ceilDiv n s
  have hcover : n≤q*s := by
    have hr := Nat.mod_lt (n+s-1) (by omega : 0<s)
    have hd := Nat.mod_add_div (n+s-1) s
    rw [Nat.mul_comm s] at hd
    dsimp [q,CH.ceilDiv]
    omega
  have window : 2*s-7≤q := by
    by_contra! bad
    exact (Nat.not_le_of_lt horder) (hcover.trans (Nat.mul_le_mul_right s (by omega)))
  change CH.HasDirectedCycleAtMost D n q
  by_cases h2 : 2*s-4≤q
  · exact cycle_in_two_strip_window (by omega) (by omega) h2 hn hcover hl hm
  by_cases h3 : q=2*s-5
  · exact DotTwoPassShellTransport.cycle_third_strip_closed (by omega) h3 hn hcover hl hm
  by_cases h4 : q=2*s-6
  · exact DotFourthStripClosure.cycle_fourth_strip_closed (by omega) h4 hn hcover hl hm
  exact cycle_fifth_strip_closed hs (by omega) hn hcover hl hm

#print axioms ch_above_fifth_threshold
end LeanCH.BR.ShenFifthStrip
