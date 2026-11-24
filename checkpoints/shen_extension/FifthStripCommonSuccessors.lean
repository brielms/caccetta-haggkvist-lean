import checkpoints.shen_extension.FifthStripIteration
import checkpoints.shen_extension.CommonSuccessorTensor

namespace LeanCH.BR.ShenFifthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

local macro "strip_arith" : tactic =>
  `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at * <;> omega))

/-- At qs-2 the enlarged reach relation is semicomplete. The actual
adjacent-layer table has too few holes to obey its two-root overlap bound. -/
theorem second_from_top_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 25≤a)
    (hf : QFree D V (2*a+7)) (hm : ∀ v∈V, a+7≤(outN D V v).card)
    (ne : V.Nonempty) (hn : V.card+2=(2*a+7)*(a+7)) : False := by
  have rig := second_from_top_rigid (by omega) hf hm hn
  have hp := iterated_profile (e:=6) hf hm (by omega) (by omega) (by omega)
  obtain ⟨u,hu⟩ := ne
  let S := ball D V u (a+3) \ ball D V u (a+2)
  let T := ball D V u (a+4) \ ball D V u (a+3)
  let U := (ball D V u (a+3)).erase u
  let holes := ∑ x∈S, (T \ outN D T x).card
  let e := (a+13)/2
  have hSV : S⊆V := Finset.sdiff_subset.trans ball_subset
  have hTV : T⊆V := Finset.sdiff_subset.trans ball_subset
  have hR := (rig u hu).1
  have hR1 := (rig u hu).2.1
  have hS : S.card+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hT : T.card+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hU : U.card+1=(ball D V u (a+3)).card := Finset.card_erase_add_one (self_mem_ball hu)
  have hTc : T.card=a+6 := by strip_arith
  have hSc : S.card≤a+6 := by have := (hp u hu).1; strip_arith
  have bound (F : CH.Digraph) (W : Finset ℕ) (h : QFree F W (2*a+7))
      (m : ∀ v∈W, a+7≤(outN F W v).card) (n : W.Nonempty) : V.card≤W.card := by
    have := order_to_two (by omega) h m n; omega
  have retained := minOut_prefix_erase (d:=1) hf hu (by omega : (a+3)+1≤2*a+7) hm
    (show 1+T.card≤a+7 by omega)
  have budget := PrefixTensor.same_degree_missing_capacity (k:=a+2) hf hm hu (by omega)
    bound (by omega) retained
  change V.card+holes≤U.card+S.card*T.card at budget
  rw [hTc] at budget
  have H : holes≤a+9 := by
    nlinarith only [budget,hn,hU,hR,Nat.mul_le_mul_right (a+6) hSc]
  have hSlow : a+5≤S.card := by
    by_contra! bad
    have := Nat.mul_le_mul_right (a+6) (show S.card≤a+4 by omega)
    nlinarith only [budget,hn,hU,hR,this,Nat.zero_le holes]
  have total (x) (hx : x∈V) (y) (hy : y∈V) :
      y∈ball D V x (a+4) ∨ x∈ball D V y (a+4) := by
    by_cases hb : y∈ball D V x (a+3)
    · exact Or.inl (ball_mono_radius (by omega) hb)
    · have comp := two_balls_boundary_complement hf (by omega : (a+3)+(a+4)≤2*a+7)
        (fun v hv => (rig v hv).1.ge) (fun v hv => (rig v hv).2.1.ge) (by strip_arith) hx
      have back : y∈reverseBall D V x (a+4) := by
        rw [comp]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy,hb⟩)
      exact Or.inr (Finset.mem_filter.mp back).2
  have obs := ShenCommonSuccessor.dense_table_bound (r:=a+3) (g:=3) (e:=e)
    hf hSV hTV (by omega)
    (fun z hz => (rig z (hTV hz)).1.ge)
    (fun x hx => (rig x (hSV hx)).2.1.le)
    (fun x hx y hy => total x (hSV hx) y (hSV hy))
    (by omega) (by dsimp [e]; strip_arith) (by dsimp [e]; omega) (by dsimp [e]; omega)
  change 4*S.card≤4*(e+1)+holes at obs
  dsimp [e] at obs
  omega

theorem order_to_one {a : ℕ} {D : CH.Digraph} {V : Finset ℕ} (ha : 25≤a)
    (hf : QFree D V (2*a+7)) (hm : ∀ v∈V, a+7≤(outN D V v).card)
    (ne : V.Nonempty) : (2*a+7)*(a+7)≤V.card+1 := by
  have h := order_to_two (by omega) hf hm ne
  by_contra! bad
  exact second_from_top_false ha hf hm ne (by omega)

theorem cycle_below_one {s q n : ℕ} {D : CH.Digraph}
    (hs : 32≤s) (hq : q=2*s-7) (hn : 0<n) (hc : n+2≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  have he : q=2*a+7 := by omega
  rw [he] at hc ⊢
  by_contra hno
  have h := order_to_one (a:=a) (by omega) (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h
  omega

#print axioms second_from_top_false
#print axioms order_to_one
#print axioms cycle_below_one
end LeanCH.BR.ShenFifthStrip
