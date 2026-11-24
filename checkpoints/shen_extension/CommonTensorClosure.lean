import LeanCH.BR.BRHalfBallWindow
import LeanCH.BR.BRTwoBallEquality
import LeanCH.BR.BRq3BallAll
import LeanCH.BR.BRq4All
/-!
# The first cutoff below the native Shen window

For s ≥ 5 and q = 2*s - 3 the two-ball bound gives at least q*s vertices.
At equality distinct full columns of a distance-layer arc table would have
identical forward balls. This excludes equality and closes the entire strip.
For q = 2*s - 4 the current lower order bound is q*s - 1.
-/
namespace LeanCH.BR.ShenFirstStrip
open LeanCH.BR LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 LeanCH.BR.BRsGen
private theorem budget {a r N c t : ℕ} (hr : r ≤ a+4)
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

private theorem step {a p q k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hpq : q+p = 2*a+7) (hle : p ≤ 1)
    (hf : QFree D V q) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card) (hu : u ∈ V)
    (hr : k+2+p ≤ a+4)
    (hi : (a+5)*k+1 ≤ (ball D V u k).card)
    (hp : (a+5)*(k+1)+1 ≤ (ball D V u (k+1)).card) :
    (a+5)*(k+2) ≤ (ball D V u (k+2)).card ∧
    (k+2+p ≤ a+3 → (a+5)*(k+2)+1 ≤ (ball D V u (k+2)).card) := by
  classical
  let c := (ball D V u (k+1) \ ball D V u k).card
  let t := (ball D V u (k+2) \ ball D V u (k+1)).card
  have hc : c + (ball D V u k).card = (ball D V u (k+1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t + (ball D V u (k+1)).card = (ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have aux (hbad : (ball D V u (k+2)).card ≤ (a+5)*(k+2))
      (hmore : k+2+p ≤ a+3 ∨ (ball D V u (k+2)).card < (a+5)*(k+2)) : False := by
    have hpos : 0 < (ball D V u (k+1)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    have htlt : t < a+5 := by simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *; omega
    have hN : (ball D V u (k+1)).card-1+t+1 ≤ (a+5)*(k+2) := by omega
    have hct : c+t+1 ≤ 2*(a+5) := by simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *; omega
    have hw : k+2+p ≤ a+3 ∨ c+t+2 ≤ 2*(a+5) := by
      rcases hmore with h|h
      · exact Or.inl h
      · right; simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *; omega
    have hb := prefix_deficiency_of_size (fun F U hf' hm' hn =>
      order_in_window (a+4) (by omega) q (by omega) (D:=F) (V:=U) hf' hm' hn)
      hf hu (by omega : k+2 ≤ q) hm (by omega : a+4 ≤ a+5) htlt
    change q*(a+4)+1 ≤ (ball D V u (k+1)).card-1+c*(a+4+t-(a+5)) at hb
    let N := (ball D V u (k+1)).card-1
    have hshift : (N+p*(a+4))+t+1 ≤ (a+5)*((k+2)+p) := by
      change N+t+1 ≤ (a+5)*(k+2) at hN
      nlinarith
    have hcap := budget hr hshift hct htlt hw
    change q*(a+4)+1 ≤ N+c*(a+4+t-(a+5)) at hb
    nlinarith [congrArg (fun z : ℕ => z*(a+4)) hpq]
  constructor
  · by_contra! h
    exact aux h.le (Or.inr h)
  · intro hh
    by_contra! h
    exact aux (by omega) (Or.inl hh)

private theorem inner_ball {a p q u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hpq : q+p = 2*a+7) (hle : p ≤ 1)
    (hf : QFree D V q) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card) (hu : u ∈ V) :
    ∀ k, 1 ≤ k → k+p ≤ a+3 → (a+5)*k+1 ≤ (ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hr
    by_cases h : k=1
    · subst k; rw [card_B1 (hf.mono_bound (by omega)) hu, Nat.mul_one]
      exact Nat.add_le_add_right (hm u hu) 1
    by_cases h : k=2
    · subst k
      have hh := card_ball_two_ge_twice (by omega : 2 ≤ a+5) (hf.mono_bound (by omega)) hm hu
      simpa only [Nat.mul_comm (a+5) 2] using hh
    obtain ⟨l,hl⟩ : ∃ l, k=l+2 := ⟨k-2,by omega⟩
    subst k
    exact (step hpq hle hf hm hu (by omega : l+2+p ≤ a+4)
      (ih l (by omega) (by omega) (by omega)) (ih (l+1) (by omega) (by omega) (by omega))).2 hr

theorem inner_ball_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card) (hu : u ∈ V) :
    ∀ k, 1 ≤ k → k ≤ a+3 → (a+5)*k+1 ≤ (ball D V u k).card :=
  inner_ball (p:=0) (by omega) (by omega) hf hm hu

theorem outer_ball_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ w ∈ V, a+5 ≤ (outN D V w).card) (hv : v ∈ V) :
    (a+5)*(a+4) ≤ (ball D V v (a+4)).card :=
  (step (p:=0) (by omega) (by omega) hf hm hv (k:=a+2) (by omega) (inner_ball_growth hf hm hv (a+2) (by omega) (by omega))
       (inner_ball_growth hf hm hv ((a+2)+1) (by omega) (by omega))).1

theorem order_first_strip {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (hne : V.Nonempty) : (2*a+7)*(a+5) ≤ V.card := by
  have hi := fun v hv => inner_ball_growth hf hm (u:=v) hv (a+3) (by omega) (by omega)
  have hj := fun v hv => outer_ball_growth hf hm (v:=v) hv
  have h := card_ge_of_two_balls hf (by omega : (a+3)+(a+4) ≤ 2*a+7) hi hj hne
  nlinarith
theorem cycle_first_strip {a n : ℕ} {D : CH.Digraph} (hn : 0 < n)
    (hnq : n < (2*a+7)*(a+5)) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n (a+5)) :
    CH.HasDirectedCycleAtMost D n (2*a+7) := by
  by_contra hh
  have ho := order_first_strip (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) ⟨0,Finset.mem_range.mpr hn⟩
  exact (Nat.not_le_of_lt hnq) (by simpa using ho)
/-- The vertices first reached at distance s-1 from v. -/
noncomputable def outerLayer (D : CH.Digraph) (V : Finset ℕ) (a v : ℕ) : Finset ℕ :=
  ball D V v (a+4) \ ball D V v (a+3)

theorem endpoint_layer_card {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ w ∈ V, a+5 ≤ (outN D V w).card)
    (he : V.card = (2*a+7)*(a+5)) (hv : v ∈ V) :
    (outerLayer D V a v).card = a+4 := by
  have hi := fun w hw => inner_ball_growth hf hm (u:=w) hw (a+3) (by omega) (by omega)
  have hj := fun w hw => outer_ball_growth hf hm (v:=w) hw
  have hh := two_balls_boundary_cards hf (by omega : (a+3)+(a+4) ≤ 2*a+7) hi hj (by nlinarith) v hv
  have hc : (outerLayer D V a v).card + (ball D V v (a+3)).card = (ball D V v (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  obtain ⟨h1,h2,_⟩ := hh
  nlinarith

theorem endpoint_layer_symmetric {a u v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ w ∈ V, a+5 ≤ (outN D V w).card)
    (he : V.card = (2*a+7)*(a+5)) (hu : u ∈ V) (hv : v ∈ V) :
    v ∈ outerLayer D V a u ↔ u ∈ outerLayer D V a v := by
  classical
  by_cases h : v=u
  · subst v; rfl
  have hi := fun w hw => inner_ball_growth hf hm (u:=w) hw (a+3) (by omega) (by omega)
  have hj := fun w hw => outer_ball_growth hf hm (v:=w) hw
  have h1 := two_balls_boundary_complement hf (by omega : (a+3)+(a+4) ≤ 2*a+7) hi hj (by nlinarith) hu
  have h2 := two_balls_boundary_complement hf (by omega : (a+4)+(a+3) ≤ 2*a+7) hj hi (by nlinarith) hu
  have e1 := Finset.ext_iff.mp h1 v
  have e2 := Finset.ext_iff.mp h2 v
  simp only [reverseBall, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
    hv, true_and, h, or_false] at e1 e2
  simp only [outerLayer, Finset.mem_sdiff]
  tauto

/-- At the next (even) cutoff the two complementary radii coincide. -/
theorem order_second_strip {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card) (hne : V.Nonempty) :
    (2*a+6)*(a+5) ≤ V.card+1 := by
  have hball (v) (hv : v ∈ V) : (a+5)*((a+1)+2) ≤ (ball D V v ((a+1)+2)).card := by
    apply (step (a:=a) (p:=1) (by omega) (by omega) hf hm hv (by omega) ?_ ?_).1
    · exact inner_ball (p:=1) (by omega) (by omega) hf hm hv (a+1) (by omega) (by omega)
    · exact inner_ball (p:=1) (by omega) (by omega) hf hm hv ((a+1)+1) (by omega) (by omega)
  have h := card_ge_of_two_balls hf (by omega : ((a+1)+2)+((a+1)+2) ≤ 2*a+6) hball hball hne
  nlinarith

theorem cycle_second_strip {a n : ℕ} {D : CH.Digraph} (hn : 0 < n)
    (hnq : n+1 < (2*a+6)*(a+5)) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n (a+5)) :
    CH.HasDirectedCycleAtMost D n (2*a+6) := by
  by_contra hh
  have ho := order_second_strip (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) ⟨0,Finset.mem_range.mpr hn⟩
  exact (Nat.not_le_of_lt hnq) (by simpa using ho)

/-- At the remaining odd-cutoff endpoint, at least three outer vertices receive
an arc from every vertex in the preceding distance layer, at each root. -/
theorem endpoint_rectangle {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ w ∈ V, a+5 ≤ (outN D V w).card)
    (he : V.card = (2*a+7)*(a+5)) (hu : u ∈ V) :
    let S := ball D V u (a+3) \ ball D V u (a+2)
    let T := outerLayer D V a u
    S.card = a+5 ∧ (∑ v ∈ S, (T \ outN D T v).card) ≤ a+1 ∧
    3 ≤ (T.filter (fun h => ∀ v ∈ S, D v h = true)).card := by
  classical
  let B := ball D V u (a+3)
  let U := B.erase u
  let S := B \ ball D V u (a+2)
  let T := outerLayer D V a u
  let gap := fun v => (a+4) - (outN D U v).card
  let miss := fun v => T \ outN D T v
  let clipped := fun v => min (a+3) (miss v).card
  change S.card = a+5 ∧ (∑ v ∈ S, (miss v).card) ≤ a+1 ∧
    3 ≤ (T.filter (fun h => ∀ v ∈ S, D v h = true)).card
  have hi := fun w hw => inner_ball_growth hf hm (u:=w) hw (a+3) (by omega) (by omega)
  have hj := fun w hw => outer_ball_growth hf hm (v:=w) hw
  have hB : B.card = (a+5)*(a+3)+1 :=
    (two_balls_boundary_cards hf (by omega : (a+3)+(a+4) ≤ 2*a+7) hi hj (by nlinarith) u hu).1
  have hT : T.card = a+4 := endpoint_layer_card hf hm he hu
  have hU : U.card = (a+5)*(a+3) := by
    have h := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    change (B.erase u).card = _
    omega
  have hSc : S.card ≤ a+5 := by
    have h : S.card + (ball D V u (a+2)).card = B.card :=
      Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
    have hh := inner_ball_growth hf hm hu (a+2) (by omega) (by omega)
    nlinarith
  have hSU : S ⊆ U := by
    intro v hv
    have h := Finset.mem_sdiff.mp hv
    exact Finset.mem_erase.mpr ⟨by intro hh; subst v; exact h.2 (self_mem_ball hu), h.1⟩
  have hmin : ∀ v ∈ U, 1 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : (a+3)+1 ≤ 2*a+7) hm (by
      change 1 + T.card ≤ a+5
      omega)
  have hn : U.Nonempty := Finset.card_pos.mp (by nlinarith)
  have lower := deficiency_bound_of_size (fun F W hf' hm' hn' =>
    order_in_window (a+4) (by omega) (2*a+7) (by omega) (D:=F) (V:=W) hf' hm' hn')
    (hf.mono_set ((Finset.erase_subset u B).trans ball_subset)) hmin hn
  change (2*a+7)*(a+4)+1 ≤ U.card + ∑ v ∈ U, gap v at lower
  have hzero (v) (hv : v ∈ U \ S) : gap v = 0 := by
    obtain ⟨huv,hsv⟩ := Finset.mem_sdiff.mp hv
    have hb : v ∈ ball D V u (a+2) := by
      by_contra hn
      exact hsv (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase huv,hn⟩)
    have hh := (hm v (ball_subset hb)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : (a+2)+1 ≤ 2*a+7) hb))
    change (a+4) - (outN D U v).card = 0
    change a+5 ≤ (outN D U v).card at hh
    omega
  have hsum0 := Finset.sum_eq_zero hzero
  have hsumeq := Finset.sum_sdiff hSU (f:=gap)
  have cap (v) (hv : v ∈ S) : gap v + clipped v ≤ a+3 := by
    have hsub := outN_prefix_loss hf hu (by omega : (a+3)+1 ≤ 2*a+7) (hSU hv)
    have hsub' : outN D V v ⊆ outN D U v ∪ outN D T v := by
      intro w hw
      obtain hh | hh := Finset.mem_union.mp (hsub hw)
      · exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (mem_outN.mpr ⟨hh,(mem_outN.mp hw).2⟩)
    have hcount := (hm v (ball_subset (Finset.mem_of_mem_erase (hSU hv)))).trans
      ((Finset.card_le_card hsub').trans (Finset.card_union_le _ _))
    have hmiss : (miss v).card + (outN D T v).card = T.card :=
      Finset.card_sdiff_add_card_eq_card (fun _ hw => (mem_outN.mp hw).1)
    dsimp only [gap,clipped]
    omega
  have hc := Finset.sum_le_sum cap
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at hc
  have hbudget : (∑ v ∈ S, clipped v) ≤ a+1 := by
    nlinarith [Nat.mul_le_mul_right (a+3) hSc]
  have hmcard (v) (hv : v ∈ S) : (miss v).card = clipped v := by
    have hl := (Finset.single_le_sum (f:=clipped) (fun w _ => Nat.zero_le _) hv).trans hbudget
    change min (a+3) (miss v).card ≤ a+1 at hl
    dsimp only [clipped]
    omega
  have totalMiss := (le_of_eq (Finset.sum_congr rfl hmcard)).trans hbudget
  have exactS : S.card = a+5 := by
    by_contra h
    have hs : S.card ≤ a+4 := by omega
    have hgap : (∑ v ∈ U, gap v) ≤ S.card*(a+3) := by omega
    have hbound := hgap.trans (Nat.mul_le_mul_right (a+3) hs)
    nlinarith only [lower, hU, hbound]
  refine ⟨exactS,totalMiss,?_⟩
  have hunion : (S.biUnion miss).card ≤ a+1 := by
    apply Finset.card_biUnion_le.trans
    exact (le_of_eq (Finset.sum_congr rfl hmcard)).trans hbudget
  have good : T \ S.biUnion miss ⊆ T.filter (fun h => ∀ v ∈ S, D v h = true) := by
    intro h hh
    obtain ⟨ht,hbad⟩ := Finset.mem_sdiff.mp hh
    refine Finset.mem_filter.mpr ⟨ht,fun v hv => ?_⟩
    by_contra hx
    apply hbad
    exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_sdiff.mpr ⟨ht,fun h => hx (mem_outN.mp h).2⟩⟩
  have hc' := Finset.card_le_card good
  have hsub : S.biUnion miss ⊆ T := by
    intro h hh
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hh
    exact (Finset.mem_sdiff.mp hv).1
  have hbound := Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- Literal CH on the two subranges in the usual degree and cutoff parameters. -/
theorem cycle_below_shen {s q n : ℕ} {D : CH.Digraph} (hs : 5 ≤ s)
    (hn : 0 < n) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s)
    (hrange : (q = 2*s-3 ∧ n < q*s) ∨ (q = 2*s-4 ∧ n+1 < q*s)) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a, ha⟩ : ∃ a, s = a+5 := ⟨s-5, by omega⟩
  subst s
  rcases hrange with ⟨hq,hb⟩ | ⟨hq,hb⟩
  · have h : q = 2*a+7 := by omega
    subst q
    exact cycle_first_strip hn hb hl hm
  · have h : q = 2*a+6 := by omega
    subst q
    exact cycle_second_strip hn hb hl hm

#print axioms cycle_below_shen
#print axioms endpoint_rectangle
#print axioms order_second_strip
#print axioms cycle_second_strip
#print axioms endpoint_layer_card
#print axioms endpoint_layer_symmetric
#print axioms order_first_strip
#print axioms cycle_first_strip
/-- Equal radius-k balls determine their root when k ≥ 2 and closed walks
through length 2k-1 are excluded. -/
private theorem ball_root_injective {D : CH.Digraph} {V : Finset ℕ} {x y k q : ℕ}
    (hf : QFree D V q) (hk : 2 ≤ k) (hq : 2*k-1 ≤ q)
    (hx : x ∈ V) (hy : y ∈ V) (heq : ball D V x k = ball D V y k) : x = y := by
  by_contra hxy
  have hforward : y ∈ ball D V x k := heq ▸ self_mem_ball hy
  have hback : x ∈ ball D V y k := heq ▸ self_mem_ball hx
  have hno : ¬ D x y = true := no_back_arc hf hy hback (by omega)
  obtain ⟨_,m,hm,w⟩ := mem_ball.mp hforward
  cases w with
  | refl => exact hxy rfl
  | @step _ z _ l hz hxz rest =>
    have hl : 0 < l := by
      by_contra! hh
      have hl0 : l = 0 := by omega
      subst l
      cases rest
      exact hno hxz
    have hz1 : z ∈ ball D V x k :=
      mem_ball.mpr ⟨hz,1,by omega,.step hz hxz (.refl z)⟩
    rw [heq] at hz1
    obtain ⟨_,j,hj,wback⟩ := mem_ball.mp hz1
    exact hf z (l+j) (by omega) (by omega) (rest.append wback)

/-- A ball larger than the punctured interior has to meet the last layer
when its root lies in the punctured prefix. -/
private theorem prefix_hits_layer {D : CH.Digraph} {V : Finset ℕ} {u y k q : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k+1 ≤ q)
    (hy : y ∈ (ball D V u (k+1)).erase u)
    (hsize : ((ball D V u k).erase u).card < (ball D V y k).card) :
    ∃ z ∈ ball D V u (k+1) \ ball D V u k, z ∈ ball D V y k := by
  classical
  by_contra h
  have hyV := ball_subset (Finset.mem_of_mem_erase hy)
  have stay {z} (hz : z ∈ (ball D V u (k+1)).erase u) (hreach : z ∈ ball D V y k) :
      z ∈ (ball D V u k).erase u := by
    refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,?_⟩
    by_contra hout
    exact h ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hz,hout⟩,hreach⟩
  have walks (m) (hm : m ≤ k) (z) (w : Walk D V y z m) : z ∈ (ball D V u k).erase u := by
    induction m generalizing z with
    | zero =>
      cases w
      exact stay hy (self_mem_ball hyV)
    | succ m ih =>
      obtain ⟨v,wv,hz,hvz⟩ := w.unsnoc
      have hv := Finset.mem_of_mem_erase (ih (by omega) v wv)
      have hret := outN_prefix_erase_root hf hu hk hv (mem_outN.mpr ⟨hz,hvz⟩)
      exact stay (mem_outN.mp hret).1 (mem_ball.mpr ⟨hz,m+1,hm,w⟩)
  have hsub : ball D V y k ⊆ (ball D V u k).erase u := by
    intro z hz
    obtain ⟨_,m,hm,w⟩ := mem_ball.mp hz
    exact walks m hm z w
  exact (Nat.not_le_of_lt hsize) (Finset.card_le_card hsub)

/-- Every full column gives the same outer ball, so there is at most one
full column at each root. -/
theorem endpoint_full_column_cap {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (he : V.card = (2*a+7)*(a+5)) (hu : u ∈ V) :
    let S := ball D V u (a+3) \ ball D V u (a+2)
    ((outerLayer D V a u).filter (fun h => ∀ v ∈ S, D v h = true)).card ≤ 1 := by
  classical
  let B := ball D V u (a+3)
  let U := B.erase u
  let S := B \ ball D V u (a+2)
  let T := outerLayer D V a u
  let C := T.filter (fun h => ∀ v ∈ S, D v h = true)
  have hSc := (endpoint_rectangle hf hm he hu).1
  change S.card = a+5 at hSc
  have hi := fun v hv => inner_ball_growth hf hm (u:=v) hv (a+3) (by omega) (by omega)
  have hj := fun v hv => outer_ball_growth hf hm (v:=v) hv
  have hcards := two_balls_boundary_cards hf (by omega : (a+3)+(a+4) ≤ 2*a+7) hi hj (by nlinarith)
  have hB : B.card = (a+5)*(a+3)+1 := (hcards u hu).1
  have hU : U.card = (a+5)*(a+3) := by
    have hh := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    change (B.erase u).card = _
    omega
  have hsmall : ((ball D V u (a+2)).erase u).card = (a+5)*(a+2) := by
    have hh : S.card + (ball D V u (a+2)).card = B.card :=
      Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
    have hh' := Finset.card_erase_of_mem (s:=ball D V u (a+2)) (self_mem_ball hu)
    have hh'' : (ball D V u (a+2)).card = (a+5)*(a+2)+1 := by nlinarith
    omega
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have same (h) (hc : h ∈ C) : ball D V h (a+4) = V \ U := by
    obtain ⟨hT,hfull⟩ := Finset.mem_filter.mp hc
    have hV := ball_subset (Finset.mem_sdiff.mp hT).1
    have hsub : ball D V h (a+4) ⊆ V \ U := by
      intro y hy
      refine Finset.mem_sdiff.mpr ⟨ball_subset hy,?_⟩
      intro hyU
      have hyV := hUV hyU
      have hlarge := inner_ball_growth hf hm hyV (a+2) (by omega) (by omega)
      obtain ⟨z,hz,hyz⟩ := prefix_hits_layer (k:=a+2) hf hu (by omega) hyU (by omega)
      have hyh : h ∈ ball D V y (a+3) := ball_step hyz hV (hfull z hz)
      have hrev : y ∈ reverseBall D V h (a+3) := Finset.mem_filter.mpr ⟨hyV,hyh⟩
      have ha := reverseBall_subset_complement hf (by omega : (a+4)+(a+3) ≤ 2*a+7) hrev
      rcases Finset.mem_union.mp ha with hout | heq
      · exact (Finset.mem_sdiff.mp hout).2 hy
      · have hyh' := Finset.mem_singleton.mp heq
        subst y
        exact (Finset.mem_sdiff.mp hT).2 (Finset.mem_of_mem_erase hyU)
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_sdiff_of_subset hUV,(hcards h hV).2.1]
    have heq : U.card + (a+5)*(a+4) = V.card := by nlinarith only [hU,he]
    omega
  change C.card ≤ 1
  by_contra! hCc
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
  have memV {h} (hh : h ∈ C) : h ∈ V := ball_subset (Finset.mem_sdiff.mp (Finset.mem_filter.mp hh).1).1
  exact hxy (ball_root_injective hf (by omega : 2 ≤ a+4) (by omega) (memV hx) (memV hy)
    ((same x hx).trans (same y hy).symm))

/-- Each non-full column needs its own missing cell. -/
theorem endpoint_missing_arc_lower {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (he : V.card = (2*a+7)*(a+5)) (hu : u ∈ V) :
    let S := ball D V u (a+3) \ ball D V u (a+2)
    let T := outerLayer D V a u
    a+3 ≤ ∑ v ∈ S, (T \ outN D T v).card := by
  classical
  let S := ball D V u (a+3) \ ball D V u (a+2)
  let T := outerLayer D V a u
  let C := T.filter (fun h => ∀ v ∈ S, D v h = true)
  let miss := fun v => T \ outN D T v
  change a+3 ≤ ∑ v ∈ S, (miss v).card
  have hcap : C.card ≤ 1 := endpoint_full_column_cap hf hm he hu
  have hT : T.card = a+4 := endpoint_layer_card hf hm he hu
  have hct : C ⊆ T := Finset.filter_subset _ _
  have hh := Finset.card_sdiff_add_card_eq_card hct
  have sub : T \ C ⊆ S.biUnion miss := by
    intro h hh
    obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp hh
    have fail : ¬ ∀ v ∈ S, D v h = true := fun hfull => hn (Finset.mem_filter.mpr ⟨ht,hfull⟩)
    push Not at fail
    obtain ⟨v,hv,hnv⟩ := fail
    exact Finset.mem_biUnion.mpr ⟨v,hv, Finset.mem_sdiff.mpr ⟨ht,fun hed => by
      have := (mem_outN.mp hed).2
      simp_all⟩⟩
  have hsum := (Finset.card_le_card sub).trans Finset.card_biUnion_le
  omega

theorem odd_endpoint_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (he : V.card = (2*a+7)*(a+5)) : False := by
  have hne : V.Nonempty := Finset.card_pos.mp (by nlinarith)
  obtain ⟨u,hu⟩ := hne
  have lower := endpoint_missing_arc_lower hf hm he hu
  have upper := (endpoint_rectangle hf hm he hu).2.1
  dsimp only at lower upper
  omega

theorem cycle_first_strip_closed {s q n : ℕ} {D : CH.Digraph}
    (hs : 5 ≤ s) (hq : q = 2*s-3) (hn : 0 < n) (hnq : n ≤ q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s = a+5 := ⟨s-5, by omega⟩
  subst s
  have hq' : q = 2*a+7 := by omega
  rw [hq'] at hnq ⊢
  rcases lt_or_eq_of_le hnq with h | h
  · exact cycle_first_strip hn h hl hm
  · by_contra hh
    exact odd_endpoint_false (qfree_of_noShort hl hh)
      (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) (by simpa using h)

/-- The first strip, the existing Shen window, and the small-degree cases. -/
theorem cycle_in_extended_window {s q n : ℕ} {D : CH.Digraph} (hs : 0 < s)
    (hq : 0 < q) (hwin : 2*s-3 ≤ q) (hn : 0 < n) (hnq : n ≤ q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_cases hlarge : 5 ≤ s
  · by_cases hold : 2*s-2 ≤ q
    · exact BRsGen.ch_in_window (by omega) hold hn hnq hl hm
    · exact cycle_first_strip_closed hlarge (by omega) hn hnq hl hm
  rcases (by omega : s=1 ∨ s=2 ∨ s=3 ∨ s=4) with rfl|rfl|rfl|rfl
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BR45.br_q_one q hq) hn hnq hl hm
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq2.br_q_two q hq) hn hnq hl hm
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq3.br_q_three q hq) hn hnq hl hm
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq4.br_q_four q (by omega)) hn hnq hl hm

/-- Literal CH in terms of graph order and minimum out-degree. -/
theorem ch_above_first_strip_threshold {s n : ℕ} {D : CH.Digraph} (hs : 0 < s)
    (hn : 0 < n) (horder : (2*s-4)*s < n)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  have hcover : n ≤ CH.ceilDiv n s * s := by
    have hmod := Nat.mod_lt (n+s-1) hs
    have hdiv := Nat.mod_add_div (n+s-1) s
    rw [Nat.mul_comm s] at hdiv
    unfold CH.ceilDiv
    omega
  have hq : 0 < CH.ceilDiv n s := by
    by_contra! hz
    have hzero : CH.ceilDiv n s = 0 := by omega
    rw [hzero, Nat.zero_mul] at hcover
    omega
  apply cycle_in_extended_window hs hq ?_ hn hcover hl hm
  by_contra! hsmall
  have hle : CH.ceilDiv n s ≤ 2*s-4 := by omega
  exact (Nat.not_le_of_lt horder) (hcover.trans (Nat.mul_le_mul_right s hle))

#print axioms endpoint_full_column_cap
#print axioms endpoint_missing_arc_lower
#print axioms odd_endpoint_false
#print axioms cycle_first_strip_closed
#print axioms cycle_in_extended_window
#print axioms ch_above_first_strip_threshold
/-- On the even strip the complementary radii both equal s-2. -/
theorem even_half_ball {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card) (hu : u ∈ V) :
    (a+5)*(a+3) ≤ (ball D V u (a+3)).card := by
  exact (step (a:=a) (k:=a+1) (p:=1) (by omega) (by omega) hf hm hu (by omega)
    (inner_ball (p:=1) (by omega) (by omega) hf hm hu (a+1) (by omega) (by omega))
    (inner_ball (p:=1) (by omega) (by omega) hf hm hu ((a+1)+1) (by omega) (by omega))).1

/-- At order qs-1 every radius-(s-2) ball has exactly half the order
rounded up. Among distinct vertices, reaching in this radius orients each pair. -/
theorem even_lower_endpoint_tournament {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (he : V.card+1 = (2*a+6)*(a+5)) :
    (∀ u ∈ V, (ball D V u (a+3)).card = (a+5)*(a+3)) ∧
    (∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (u ∈ ball D V v (a+3) ↔ v ∉ ball D V u (a+3))) := by
  have low := fun u hu => even_half_ball hf hm (u:=u) hu
  have hsum : (a+5)*(a+3) + (a+5)*(a+3) = V.card+1 := by nlinarith
  have hrad : (a+3)+(a+3) ≤ 2*a+6 := by omega
  constructor
  · intro u hu
    exact (two_balls_boundary_cards hf hrad low low hsum u hu).1
  · intro u hu v hv hne
    have h := Finset.ext_iff.mp (two_balls_boundary_complement hf hrad low low hsum hu) v
    simpa only [reverseBall, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_singleton, hv, true_and, Ne.symm hne, or_false] using h

/-- At the upper endpoint the total excess of the forward balls above their
lower bound is at most half the order. -/
theorem even_upper_endpoint_excess {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (he : V.card = (2*a+6)*(a+5)) :
    2*(∑ u ∈ V, ((ball D V u (a+3)).card - (a+5)*(a+3))) ≤ V.card := by
  let b := (a+5)*(a+3)
  have hlow (u) (hu : u ∈ V) : b ≤ (ball D V u (a+3)).card := even_half_ball hf hm hu
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ V) =>
    reverseBall_add_ball_le (v:=u) hf (by omega : (a+3)+(a+3) ≤ 2*a+6))
  rw [Finset.sum_add_distrib, sum_reverseBall_eq_sum_ball D V (a+3),
    Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have hsplit : (∑ u ∈ V, ((ball D V u (a+3)).card-b)) + V.card*b =
      ∑ u ∈ V, (ball D V u (a+3)).card := by
    calc
      _ = (∑ u ∈ V, ((ball D V u (a+3)).card-b)) + ∑ _ ∈ V, b := by
        rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun u hu => Nat.sub_add_cancel (hlow u hu))
  have hcard : V.card = 2*b := by dsimp [b]; nlinarith
  change 2*(∑ u ∈ V, ((ball D V u (a+3)).card-b)) ≤ V.card
  nlinarith only [hsum,hsplit,congrArg (fun n : ℕ => V.card*n) hcard]

#print axioms even_half_ball
#print axioms even_lower_endpoint_tournament
#print axioms even_upper_endpoint_excess
/-- At order qs, missing comparabilities and extra reachable vertices share
one total budget. The first sum counts each incomparable pair twice. -/
theorem even_upper_endpoint_missing_pairs {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (he : V.card = (2*a+6)*(a+5)) :
    (∑ u ∈ V, (V \ (ball D V u (a+3) ∪ reverseBall D V u (a+3))).card) +
      2*(∑ u ∈ V, ((ball D V u (a+3)).card - (a+5)*(a+3))) = V.card := by
  classical
  let b := (a+5)*(a+3)
  let missing := fun u => (V \ (ball D V u (a+3) ∪ reverseBall D V u (a+3))).card
  have hcard : V.card = 2*b := by dsimp [b]; nlinarith
  have part (u) (hu : u ∈ V) : missing u +
      ((ball D V u (a+3)).card + (reverseBall D V u (a+3)).card) = V.card+1 := by
    let F := ball D V u (a+3)
    let I := reverseBall D V u (a+3)
    have hI : I ⊆ (V \ F) ∪ {u} :=
      reverseBall_subset_complement hf (by omega : (a+3)+(a+3) ≤ 2*a+6)
    have hmeet : F ∩ I = {u} := by
      ext v
      constructor
      · intro hv
        obtain ⟨hF,hi⟩ := Finset.mem_inter.mp hv
        rcases Finset.mem_union.mp (hI hi) with hx | hx
        · exact ((Finset.mem_sdiff.mp hx).2 hF).elim
        · exact hx
      · intro hv
        obtain rfl := Finset.mem_singleton.mp hv
        exact Finset.mem_inter.mpr ⟨self_mem_ball hu, Finset.mem_filter.mpr ⟨hu,self_mem_ball hu⟩⟩
    have hsub : F ∪ I ⊆ V := Finset.union_subset ball_subset (Finset.filter_subset _ _)
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    have h2 := Finset.card_union_add_card_inter F I
    rw [hmeet, Finset.card_singleton] at h2
    change (V \ (F ∪ I)).card + (F.card + I.card) = V.card+1
    omega
  have hs := Finset.sum_congr (s₁:=V) rfl part
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_reverseBall_eq_sum_ball D V (a+3), Finset.sum_const_nat (fun _ _ => rfl)] at hs
  have hsplit : (∑ u ∈ V, ((ball D V u (a+3)).card-b)) + V.card*b =
      ∑ u ∈ V, (ball D V u (a+3)).card := by
    calc
      _ = (∑ u ∈ V, ((ball D V u (a+3)).card-b)) + ∑ _ ∈ V, b := by
        rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun u hu => Nat.sub_add_cancel (even_half_ball hf hm hu))
  change (∑ u ∈ V, missing u) + 2*(∑ u ∈ V, ((ball D V u (a+3)).card-b)) = V.card
  nlinarith only [hsplit,hs,congrArg (fun n : ℕ => V.card*n) hcard]

#print axioms even_upper_endpoint_missing_pairs
end LeanCH.BR.ShenFirstStrip

namespace LeanCH.BR.ShenFirstStrip

open LeanCH.BR LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 LeanCH.BR.BRsGen
/-- A container with at most one omission per ball compresses all walks
between distinct bank vertices to actual arcs. -/
private theorem near_full_walk_is_arc {D : CH.Digraph} {V K C : Finset ℕ} {q k x y : ℕ}
    (hf : QFree D V q) (hk : k+2 ≤ q) (hCV : C ⊆ V)
    (hballs : ∀ h ∈ C, ball D V h k ⊆ K)
    (hmiss : ∀ h ∈ C, (K \ ball D V h k).card ≤ 1)
    (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) (hyball : y ∈ ball D V x k) :
    D x y = true := by
  classical
  obtain ⟨_,m,hm,w⟩ := mem_ball.mp hyball
  cases m with
  | zero => cases w; exact (hne rfl).elim
  | succ m =>
    cases m with
    | zero =>
      obtain ⟨v,wv,_,hvy⟩ := w.unsnoc
      cases wv
      exact hvy
    | succ m =>
      obtain ⟨v,wv,hym,hvy⟩ := w.unsnoc
      obtain ⟨z,wz,hvm,hzv⟩ := wv.unsnoc
      have hzV : z ∈ V := by
        rcases wz.end_mem_or with h|h
        · exact h ▸ hCV hx
        · exact h
      have hzK : z ∈ K := hballs x hx (mem_ball.mpr ⟨hzV,m,by omega,wz⟩)
      have hvK : v ∈ K := hballs x hx (mem_ball.mpr ⟨hvm,m+1,by omega,wv⟩)
      have hznot : z ∉ ball D V y k := by
        intro hz
        obtain ⟨_,l,hl,wl⟩ := mem_ball.mp hz
        exact hf y (l+2) (by omega) (by omega)
          (wl.append (.step hvm hzv (.step hym hvy (.refl y))))
      have hvnot : v ∉ ball D V y k := by
        intro hv
        obtain ⟨_,l,hl,wl⟩ := mem_ball.mp hv
        exact hf y (l+1) (by omega) (by omega) (wl.snoc hym hvy)
      have hne' : z ≠ v := by
        intro he
        subst z
        exact loopfree hf (by omega) hvm hzv
      have sub : {z,v} ⊆ K \ ball D V y k := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        · exact Finset.mem_sdiff.mpr ⟨hzK,hznot⟩
        · exact Finset.mem_sdiff.mpr ⟨hvK,hvnot⟩
      have hc := Finset.card_le_card sub
      rw [Finset.card_pair hne'] at hc
      have hh := hmiss y hy
      omega

/-- This uniform capacity statement has no degree or prescribed core size. -/
theorem near_full_container_false {D : CH.Digraph} {V K C : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hk : k+2 ≤ q) (hCV : C ⊆ V) (hCK : C ⊆ K)
    (hballs : ∀ h ∈ C, ball D V h k ⊆ K)
    (hmiss : ∀ h ∈ C, (K \ ball D V h k).card ≤ 1)
    (hcard : 3 ≤ C.card) (hsize : C.card ≤ q) : False := by
  classical
  obtain ⟨x,hx,hsink⟩ := exists_sink (hf.mono_set hCV) (Finset.card_pos.mp (by omega)) hsize
  have subset : C ⊆ insert x (K \ ball D V x k) := by
    intro y hy
    by_cases he : y=x
    · exact Finset.mem_insert.mpr (Or.inl he)
    · apply Finset.mem_insert.mpr
      right
      refine Finset.mem_sdiff.mpr ⟨hCK hy,?_⟩
      intro hb
      exact hsink y hy (near_full_walk_is_arc hf hk hCV hballs hmiss hx hy (Ne.symm he) hb)
  have hb := (Finset.card_le_card subset).trans (Finset.card_insert_le _ _)
  have hh := hmiss x hx
  omega

/-- The next-radius bound is independent of the individual half-ball excess. -/
theorem even_next_ball_growth {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card) (hu : u ∈ V) :
    (a+5)*(a+3)+(a+4) ≤ (ball D V u (a+4)).card := by
  classical
  let b := (a+5)*(a+3)
  let c := (ball D V u (a+3) \ ball D V u (a+2)).card
  let t := (ball D V u (a+4) \ ball D V u (a+3)).card
  have hc : c + (ball D V u (a+2)).card = (ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t + (ball D V u (a+3)).card = (ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hprev := inner_ball (p:=1) (by omega) (by omega) hf hm hu (a+2) (by omega) (by omega)
  have hhalf := even_half_ball hf hm hu
  change b ≤ (ball D V u (a+3)).card at hhalf
  let e := (ball D V u (a+3)).card-b
  have he : (ball D V u (a+3)).card = b+e := by omega
  by_contra! hbad
  change b+(a+4) > (ball D V u (a+4)).card at hbad
  have htlt : t < a+5 := by omega
  have hdef := prefix_deficiency_of_size (fun F W hf' hm' hn' =>
    order_in_window (a+4) (by omega) (2*a+6) (by omega) (D:=F) (V:=W) hf' hm' hn')
    hf hu (by omega : (a+2)+2 ≤ 2*a+6) hm (by omega : a+4 ≤ a+5) htlt
  change (2*a+6)*(a+4)+1 ≤ (ball D V u (a+3)).card-1+c*(a+4+t-(a+5)) at hdef
  have hpos : 0 < (ball D V u (a+3)).card := by dsimp [b] at hhalf; nlinarith
  have hcm : c ≤ a+4+e := by dsimp [b] at he; nlinarith
  by_cases ht0 : t=0
  · rw [ht0] at hdef
    have hl : a+4+0-(a+5)=0 := by omega
    rw [hl,Nat.mul_zero,Nat.add_zero] at hdef
    have hlast : (ball D V u (a+3)).card ≤ b+(a+3) := by omega
    have hd : (2*a+6)*(a+4)+2 ≤ (ball D V u (a+3)).card := by omega
    dsimp [b] at hlast
    nlinarith only [hd,hlast]
  obtain ⟨l,hl⟩ : ∃ l, t=l+1 := ⟨t-1,by omega⟩
  have hloss : a+4+t-(a+5)=l := by omega
  rw [hloss] at hdef
  have het : e+l ≤ a+2 := by omega
  have hprod := Nat.mul_le_mul_right l hcm
  have hprod2 := Nat.mul_le_mul_left (a+4+e) het
  have hd : (2*a+6)*(a+4)+2≤b+e+c*l := by omega
  dsimp [b] at hd
  nlinarith only [hd,hprod,hprod2,Int.natCast_nonneg e,sq_nonneg (e:ℤ)]

#print axioms near_full_container_false
#print axioms even_next_ball_growth
end LeanCH.BR.ShenFirstStrip

namespace LeanCH.BR.ShenFirstStrip

open LeanCH.BR LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 LeanCH.BR.BRsGen
private theorem even_rectangle_budget {a c t N M : ℕ} (ht : 1 ≤ t)
    (hN : N+t+1=(a+5)*(a+3)) (hc : c+t≤2*a+9)
    (hb : (2*a+6)*(a+4)+1+M ≤ N+c*(t-1)) :
    c+t=2*a+9 ∧ M+4≤t := by
  obtain ⟨l,rfl⟩ : ∃ l, t=l+1 := ⟨t-1,by omega⟩
  simp only [Nat.add_sub_cancel] at hb
  zify at *
  have heq : (c:ℤ)+(l+1)=2*a+9 := by
    by_contra h
    have hh : (c:ℤ)+(l+1)≤2*a+8 := by omega
    have hmul := mul_nonneg (show (0:ℤ)≤2*a+8-c-(l+1) by omega) (Int.natCast_nonneg l)
    nlinarith [sq_nonneg ((a:ℤ)+3-l)]
  constructor
  · exact heq
  · nlinarith [sq_nonneg ((a:ℤ)+3-l)]

/-- Every root of minimum half-ball size supplies four common heads. -/
theorem even_minimum_root_rectangle {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (hu : u ∈ V) (hroot : (ball D V u (a+3)).card=(a+5)*(a+3)) :
    let S := ball D V u (a+2) \ ball D V u (a+1)
    let T := ball D V u (a+3) \ ball D V u (a+2)
    (ball D V u (a+1)).card=(a+5)*(a+1)+1 ∧
      4 ≤ (T.filter (fun h => ∀ v ∈ S, D v h=true)).card := by
  classical
  let B := ball D V u (a+2)
  let U := B.erase u
  let S := B \ ball D V u (a+1)
  let T := ball D V u (a+3) \ B
  let gap := fun v => (a+4)-(outN D U v).card
  let miss := fun v => T \ outN D T v
  let clip := fun v => min (T.card-1) (miss v).card
  change (ball D V u (a+1)).card=(a+5)*(a+1)+1 ∧
    4 ≤ (T.filter (fun h => ∀ v ∈ S, D v h=true)).card
  have hN : U.card+T.card+1=(a+5)*(a+3) := by
    have h1 := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : a+2≤a+3))
    have h2 := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    change T.card+B.card=_ at h1
    change U.card=B.card-1 at h2
    have hpos : 0<B.card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    omega
  have hlower := inner_ball (p:=1) (by omega) (by omega) hf hm hu (a+1) (by omega) (by omega)
  have hS : S.card+(ball D V u (a+1)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hU : U.card+1=B.card := by
    have h := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    have hpos : 0<B.card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    change U.card=B.card-1 at h
    omega
  have hc : S.card+T.card≤2*a+9 := by nlinarith
  have htlt : T.card<a+5 := by
    have hb := inner_ball (p:=1) (by omega) (by omega) hf hm hu (a+2) (by omega) (by omega)
    change (a+5)*(a+2)+1≤B.card at hb
    nlinarith
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_erase.mpr ⟨?_,hb⟩
    intro h; subst v
    exact hn (self_mem_ball hu)
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hmin : ∀ v ∈ U, 1≤(outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : (a+2)+1≤2*a+6) hm (by
      change 1+T.card≤a+5
      omega)
  have hne : U.Nonempty := by
    apply Finset.card_pos.mp
    have hh := inner_ball (p:=1) (by omega) (by omega) hf hm hu (a+2) (by omega) (by omega)
    change (a+5)*(a+2)+1≤B.card at hh
    nlinarith
  have low := deficiency_bound_of_size (fun F W hf' hm' hn' =>
    order_in_window (a+4) (by omega) (2*a+6) (by omega) (D:=F) (V:=W) hf' hm' hn')
    (hf.mono_set hUV) hmin hne
  change (2*a+6)*(a+4)+1≤U.card+∑ v ∈ U, gap v at low
  have hz (v) (hv : v ∈ U \ S) : gap v=0 := by
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hv
    have hi : v ∈ ball D V u (a+1) := by
      by_contra hh
      exact hn (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv,hh⟩)
    have h := (hm v (ball_subset hi)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : (a+1)+1≤2*a+6) hi))
    change a+5≤(outN D U v).card at h
    dsimp [gap]; omega
  have hzero := Finset.sum_eq_zero hz
  have hsum := Finset.sum_sdiff hSU (f:=gap)
  have cap (v) (hv : v ∈ S) : gap v+clip v≤T.card-1 := by
    have hsub := outN_prefix_loss hf hu (by omega : (a+2)+1≤2*a+6) (hSU hv)
    have hsub' : outN D V v ⊆ outN D U v ∪ outN D T v := by
      intro w hw
      obtain hh|hh := Finset.mem_union.mp (hsub hw)
      · exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (mem_outN.mpr ⟨hh,(mem_outN.mp hw).2⟩)
    have hcount := (hm v (hUV (hSU hv))).trans
      ((Finset.card_le_card hsub').trans (Finset.card_union_le _ _))
    have hmiss : (miss v).card+(outN D T v).card=T.card :=
      Finset.card_sdiff_add_card_eq_card (fun _ hw => (mem_outN.mp hw).1)
    dsimp only [gap,clip]
    omega
  have hcap := Finset.sum_le_sum cap
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at hcap
  have htpos : 1≤T.card := by
    by_contra! hh
    have ht0 : T.card=0 := by omega
    rw [ht0] at hcap hN
    simp only [Nat.zero_sub,Nat.mul_zero] at hcap
    have hd : (2*a+6)*(a+4)+1≤U.card := by omega
    nlinarith only [hd,hN]
  have budget := even_rectangle_budget htpos hN hc (by omega :
    (2*a+6)*(a+4)+1+(∑ v ∈ S,clip v)≤U.card+S.card*(T.card-1))
  have hmc (v) (hv : v ∈ S) : (miss v).card=clip v := by
    have hle := Finset.single_le_sum (f:=clip) (fun _ _ => Nat.zero_le _) hv
    have hm := budget.2
    dsimp only [clip] at *
    omega
  have hmSum : (∑ v ∈ S,(miss v).card)+4≤T.card := by
    rw [Finset.sum_congr rfl hmc]
    exact budget.2
  constructor
  · have hcExact := budget.1
    nlinarith
  · have sub : T \ S.biUnion miss ⊆ T.filter (fun h => ∀ v ∈ S, D v h=true) := by
      intro h hh
      obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp hh
      refine Finset.mem_filter.mpr ⟨ht,fun v hv => ?_⟩
      by_contra hb
      exact hn (Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_sdiff.mpr ⟨ht,fun he => hb (mem_outN.mp he).2⟩⟩)
    have hbi : S.biUnion miss ⊆ T := by
      intro h hh
      obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hh
      exact (Finset.mem_sdiff.mp hv).1
    have h1 := Finset.card_biUnion_le (s:=S) (t:=miss)
    have h2 := Finset.card_sdiff_add_card_eq_card hbi
    have h3 := Finset.card_le_card sub
    omega
#print axioms even_minimum_root_rectangle
end LeanCH.BR.ShenFirstStrip

namespace LeanCH.BR.ShenFirstStrip
open LeanCH.BR LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 LeanCH.BR.BRsGen

/-- The common-container argument closes both even endpoint orders together. -/
theorem even_strip_order {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+6)) (hm : ∀ v ∈ V, a+5 ≤ (outN D V v).card)
    (hne : V.Nonempty) : (2*a+6)*(a+5)+1≤V.card := by
  classical
  let b := (a+5)*(a+3)
  by_contra! hbad
  have hn : V.card≤2*b := by dsimp [b]; nlinarith
  obtain ⟨u,hu,hroot⟩ : ∃ u ∈ V, (ball D V u (a+3)).card=b := by
    by_contra hh
    have hall (v) (hv : v ∈ V) : b+1≤(ball D V v (a+3)).card := by
      have hmin := even_half_ball hf hm hv
      change b≤(ball D V v (a+3)).card at hmin
      by_contra! hb
      exact hh ⟨v,hv,by omega⟩
    have htwo := card_ge_of_two_balls hf (by omega : (a+3)+(a+3)≤2*a+6) hall hall hne
    omega
  let B := ball D V u (a+2)
  let U := B.erase u
  let S := B \ ball D V u (a+1)
  let T := ball D V u (a+3) \ B
  let C := T.filter (fun h => ∀ v ∈ S, D v h=true)
  let K := V \ U
  obtain ⟨hinner,hC⟩ := even_minimum_root_rectangle hf hm hu hroot
  change 4≤C.card at hC
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_erase.mpr ⟨?_,hb⟩
    intro h; subst v
    exact hn (self_mem_ball hu)
  have hT : T.card+B.card=b := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega)) |>.trans hroot
  have hU : U.card+1=B.card := by
    have h := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    have hpos : 0<B.card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    change U.card=B.card-1 at h
    omega
  have ht : T.card≤a+4 := by
    have hprev := inner_ball (p:=1) (by omega) (by omega) hf hm hu (a+2) (by omega) (by omega)
    change (a+5)*(a+2)+1≤B.card at hprev
    dsimp [b] at hT
    nlinarith
  have hCsub : C ⊆ T := Finset.filter_subset _ _
  have hCV : C ⊆ V := by
    intro h hh
    exact ball_subset (Finset.mem_sdiff.mp (hCsub hh)).1
  have hCK : C ⊆ K := by
    intro h hh
    have hb := Finset.mem_sdiff.mp (hCsub hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb.1,fun hU => hb.2 (Finset.mem_of_mem_erase hU)⟩
  have hsmall : ((ball D V u (a+1)).erase u).card=(a+5)*(a+1) := by
    have hh := Finset.card_erase_of_mem (s:=ball D V u (a+1)) (self_mem_ball hu)
    rw [hinner] at hh
    omega
  have hreach (h) (hh : h ∈ C) (y) (hy : y ∈ U) :
      h ∈ ball D V y (a+2) := by
    have hlarge := inner_ball (p:=1) (by omega) (by omega) hf hm (hUV hy) (a+1) (by omega) (by omega)
    obtain ⟨z,hz,hyz⟩ := prefix_hits_layer (k:=a+1) hf hu (by omega) hy (by omega)
    exact ball_step hyz (hCV hh) ((Finset.mem_filter.mp hh).2 z hz)
  have hballs (h) (hh : h ∈ C) : ball D V h (a+4) ⊆ K := by
    intro y hy
    refine Finset.mem_sdiff.mpr ⟨ball_subset hy,?_⟩
    intro hyU
    have hyh := hreach h hh y hyU
    obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hy
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hyh
    have hne : h ≠ y := by
      intro he
      subst y
      exact (Finset.mem_sdiff.mp (hCK hh)).2 hyU
    have hipos : 0<i := by
      cases i with
      | zero => cases wi; exact (hne rfl).elim
      | succ => omega
    exact hf h (i+j) (by omega) (by omega) (wi.append wj)
  have hK : K.card≤b+(a+5) := by
    have hc := Finset.card_sdiff_add_card_eq_card hUV
    change K.card+U.card=V.card at hc
    omega
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h (a+4)).card≤1 := by
    have hg := even_next_ball_growth hf hm (hCV hh)
    change b+(a+4)≤(ball D V h (a+4)).card at hg
    have hs := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    omega
  apply near_full_container_false hf (by omega : (a+4)+2≤2*a+6) hCV hCK hballs hmiss (by omega)
  exact (Finset.card_le_card hCsub).trans (by omega)

theorem cycle_even_strip_closed {s q n : ℕ} {D : CH.Digraph}
    (hs : 5≤s) (hq : q=2*s-4) (hn : 0<n) (hnq : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s=a+5 := ⟨s-5,by omega⟩
  subst s
  have hq' : q=2*a+6 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := even_strip_order (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms even_strip_order
#print axioms cycle_even_strip_closed
end LeanCH.BR.ShenFirstStrip

namespace LeanCH.BR.ShenFirstStrip
open LeanCH.BR LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 LeanCH.BR.BRsGen

/-- The old window and both newly closed strips. -/
theorem cycle_in_two_strip_window {s q n : ℕ} {D : CH.Digraph}
    (hs : 0<s) (hq : 0<q) (hwin : 2*s-4≤q) (hn : 0<n) (hnq : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_cases hlarge : 5≤s
  · by_cases hold : 2*s-3≤q
    · exact cycle_in_extended_window hs hq hold hn hnq hl hm
    · exact cycle_even_strip_closed hlarge (by omega) hn hnq hl hm
  rcases (by omega : s=1 ∨ s=2 ∨ s=3 ∨ s=4) with rfl|rfl|rfl|rfl
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BR45.br_q_one q hq) hn hnq hl hm
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq2.br_q_two q hq) hn hnq hl hm
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq3.br_q_three q hq) hn hnq hl hm
  · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq4.br_q_four q (by omega)) hn hnq hl hm

/-- Literal CH above the quadratic threshold obtained from the two strips. -/
theorem ch_above_two_strip_threshold {s n : ℕ} {D : CH.Digraph}
    (hs : 0<s) (hn : 0<n) (horder : (2*s-5)*s<n)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  have hcover : n≤CH.ceilDiv n s*s := by
    have hmod := Nat.mod_lt (n+s-1) hs
    have hdiv := Nat.mod_add_div (n+s-1) s
    rw [Nat.mul_comm s] at hdiv
    unfold CH.ceilDiv
    omega
  have hq : 0<CH.ceilDiv n s := by
    by_contra! hz
    have hzero : CH.ceilDiv n s=0 := by omega
    rw [hzero,Nat.zero_mul] at hcover
    omega
  apply cycle_in_two_strip_window hs hq ?_ hn hcover hl hm
  by_contra! hsmall
  have hle : CH.ceilDiv n s≤2*s-5 := by omega
  exact (Nat.not_le_of_lt horder) (hcover.trans (Nat.mul_le_mul_right s hle))

/-- Boolean reachability, indexed by radius, starting vertex, and end vertex. -/
noncomputable def reachTensor (D : CH.Digraph) (V : Finset ℕ) (k u v : ℕ) : ℕ :=
  if v ∈ ball D V u k then 1 else 0

theorem reach_tensor_composition {D : CH.Digraph} {V : Finset ℕ} {i j u v w : ℕ}
    (huv : reachTensor D V i u v=1) (hvw : reachTensor D V j v w=1) :
    reachTensor D V (i+j) u w=1 := by
  classical
  have h1 : v ∈ ball D V u i := by simpa [reachTensor] using huv
  have h2 : w ∈ ball D V v j := by simpa [reachTensor] using hvw
  obtain ⟨_,l,hl,wl⟩ := mem_ball.mp h1
  obtain ⟨hw,m,hm,wm⟩ := mem_ball.mp h2
  simp only [reachTensor,ite_eq_left_iff,Nat.zero_ne_one,imp_false,not_not]
  exact mem_ball.mpr ⟨hw,l+m,by omega,wl.append wm⟩

theorem reach_tensor_return_capacity {D : CH.Digraph} {V : Finset ℕ} {q i j u v : ℕ}
    (hf : QFree D V q) (hij : i+j≤q) (hu : u ∈ V) (hv : v ∈ V) :
    reachTensor D V i u v + reachTensor D V j v u ≤ 1+(if u=v then 1 else 0) := by
  classical
  by_cases he : u=v
  · subst v
    simp [reachTensor,self_mem_ball hu]
  have hnot : ¬ (v ∈ ball D V u i ∧ u ∈ ball D V v j) := by
    rintro ⟨h1,h2⟩
    have hrev : v ∈ reverseBall D V u j := Finset.mem_filter.mpr ⟨hv,h2⟩
    have hcap := reverseBall_subset_complement hf hij hrev
    rcases Finset.mem_union.mp hcap with h|h
    · exact (Finset.mem_sdiff.mp h).2 h1
    · exact he (Finset.mem_singleton.mp h).symm
  by_cases h1 : v ∈ ball D V u i <;> by_cases h2 : u ∈ ball D V v j <;>
    simp_all [reachTensor]

/-- Contracting the two-root tensor counts omissions exactly. -/
theorem tensor_capacity_identity {D : CH.Digraph} {V : Finset ℕ} {q i j : ℕ}
    (hf : QFree D V q) (hij : i+j≤q) :
    (∑ u ∈ V, (V \ (ball D V u i ∪ reverseBall D V u j)).card) +
    (∑ u ∈ V, (ball D V u i).card) + (∑ u ∈ V, (ball D V u j).card) =
    V.card*(V.card+1) := by
  classical
  have part (u) (hu : u ∈ V) :
      (V \ (ball D V u i ∪ reverseBall D V u j)).card +
        ((ball D V u i).card+(reverseBall D V u j).card)=V.card+1 := by
    let F := ball D V u i
    let I := reverseBall D V u j
    have hI : I ⊆ (V \ F) ∪ {u} := reverseBall_subset_complement hf hij
    have hmeet : F ∩ I={u} := by
      ext v
      constructor
      · intro hv
        obtain ⟨hF,hrev⟩ := Finset.mem_inter.mp hv
        rcases Finset.mem_union.mp (hI hrev) with h|h
        · exact ((Finset.mem_sdiff.mp h).2 hF).elim
        · exact h
      · intro hv
        obtain rfl := Finset.mem_singleton.mp hv
        exact Finset.mem_inter.mpr ⟨self_mem_ball hu,Finset.mem_filter.mpr ⟨hu,self_mem_ball hu⟩⟩
    have hsub : F ∪ I ⊆ V := Finset.union_subset ball_subset (Finset.filter_subset _ _)
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    have h2 := Finset.card_union_add_card_inter F I
    rw [hmeet,Finset.card_singleton] at h2
    change (V \ (F ∪ I)).card+(F.card+I.card)=V.card+1
    omega
  have h := Finset.sum_congr (s₁:=V) rfl part
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_reverseBall_eq_sum_ball D V j,
    Finset.sum_const_nat (fun _ _ => rfl)] at h
  omega

/-- The familiar two-ball proof also works from a total tensor lower bound,
without demanding identical growth at every root. -/
theorem order_of_tensor_growth {D : CH.Digraph} {V : Finset ℕ} {q s i j : ℕ}
    (hf : QFree D V q) (hij : i+j≤q) (hne : V.Nonempty)
    (hgrowth : V.card*(q*s+2) ≤
      (∑ u ∈ V, (ball D V u i).card)+(∑ u ∈ V, (ball D V u j).card)) :
    q*s+1≤V.card := by
  have h := tensor_capacity_identity hf hij
  have hcap : V.card*(q*s+2)≤V.card*(V.card+1) := by omega
  have hp := Finset.card_pos.mpr hne
  by_contra! hsmall
  have hm := Nat.mul_lt_mul_of_pos_left (by omega : V.card+1<q*s+2) hp
  exact (Nat.not_le_of_lt hm) hcap

#print axioms cycle_in_two_strip_window
#print axioms ch_above_two_strip_threshold
#print axioms reach_tensor_composition
#print axioms reach_tensor_return_capacity
#print axioms tensor_capacity_identity
#print axioms order_of_tensor_growth
end LeanCH.BR.ShenFirstStrip
