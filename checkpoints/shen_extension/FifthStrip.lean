import checkpoints.shen_extension.StripTransfer

/-! At q=2s-7 the previous degree is in the third strip.
Take s=a+7 and the complementary radii R=a+3 and R+1. -/
namespace LeanCH.BR.ShenFifthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

private theorem step {D : CH.Digraph} {V : Finset ℕ} {a k u i j l : ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u∈V)
    (hk : k+2≤2*a+7)
    (h0 : (a+7)*k+1≤(ball D V u k).card+i)
    (h1 : (a+7)*(k+1)+1≤(ball D V u (k+1)).card+j)
    (hg : j≤l) (hslope : 2*j≤1+l+i)
    (hkey : ((a:ℤ)+7-j+i)*(a+5-l+j) < (2*a+7)*(a+6)-(a+7)*(k+1)+j)
    (hzero : (a+7)*(k+2)≤(2*a+7)*(a+6)+l) :
    (a+7)*(k+2)+1≤(ball D V u (k+2)).card+l := by
  apply ShenStripTransfer.growth_step (j:=1) (d:=a+6) (L:=(2*a+7)*(a+6))
    (fun _ _ h m n => ShenThirdStrip.order_to_top h m n) hf hm hu rfl hk h0 h1 hg hslope
  · push_cast; linarith
  · exact hzero

theorem inner_growth {D : CH.Digraph} {V : Finset ℕ} {a u : ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u∈V) :
    ∀ k, k≤a+1 → (a+7)*k+1≤(ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases k with _|k
    · simpa using (Finset.card_pos.mpr ⟨u,self_mem_ball (k:=0) hu⟩ :
        0<(ball D V u 0).card)
    rcases k with _|k
    · rw [card_B1 (hf.mono_bound (by omega)) hu,Nat.mul_one]
      exact Nat.add_le_add_right (hm u hu) 1
    have hbound : (k:ℤ)+1≤a := by exact_mod_cast (by omega : k+1≤a)
    apply step (i:=0) (j:=0) (l:=0) hf hm hu (by omega)
      (ih k (by omega) (by omega)) (ih (k+1) (by omega) (by omega)) (by omega) (by omega)
    · push_cast; nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℤ)≤a+7)]
    · nlinarith [Nat.mul_le_mul_left (a+7) hk]

theorem middle_growth {D : CH.Digraph} {V : Finset ℕ} {a u : ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u∈V) :
    (a+7)*(a+2)+1≤(ball D V u (a+2)).card+1 ∧
    (a+7)*(a+3)+1≤(ball D V u (a+3)).card+2 ∧
    (a+7)*(a+4)+1≤(ball D V u (a+4)).card+4 := by
  have h0 := inner_growth hf hm hu a (by omega)
  have h1 := inner_growth hf hm hu (a+1) le_rfl
  have h2 := step (k:=a) (i:=0) (j:=0) (l:=1) hf hm hu (by omega) h0 h1
    (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  have h3 := step (k:=a+1) (i:=0) (j:=1) (l:=2) hf hm hu (by omega) h1 h2
    (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  have h4 := step (k:=a+2) (i:=1) (j:=2) (l:=4) hf hm hu (by omega) h2 h3
    (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  exact ⟨h2,h3,h4⟩

/-- The two enlarged balls used on the complementary sides of a shared rectangle. -/
theorem outer_growth {D : CH.Digraph} {V : Finset ℕ} {a u : ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hu : u∈V) :
    (a+7)*(a+5)+1≤(ball D V u (a+5)).card+6 ∧
    (a+7)*(a+6)+1≤(ball D V u (a+6)).card+9 := by
  obtain ⟨_,h3,h4⟩ := middle_growth hf hm hu
  have h5 := step (k:=a+3) (i:=2) (j:=4) (l:=6) hf hm hu (by omega) h3 h4
    (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  have h6 := step (k:=a+4) (i:=4) (j:=6) (l:=9) hf hm hu (by omega) h4 h5
    (by omega) (by omega) (by push_cast; nlinarith) (by nlinarith)
  exact ⟨h5,h6⟩

theorem order_bound {D : CH.Digraph} {V : Finset ℕ} {a : ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) : (2*a+7)*(a+7)≤V.card+5 := by
  have h := card_ge_of_two_balls hf (by omega : (a+3)+(a+4)≤2*a+7)
    (a:=(a+7)*(a+3)-1) (b:=(a+7)*(a+4)-3)
    (fun v hv => by have := (middle_growth hf hm (u:=v) hv).2.1; omega)
    (fun v hv => by have := (middle_growth hf hm (u:=v) hv).2.2; omega) hne
  have h3 : 3≤(a+7)*(a+4) := by nlinarith
  have h1 : 1≤(a+7)*(a+3) := by nlinarith
  have he : (2*a+7)*(a+7)=(a+7)*(a+3)+(a+7)*(a+4) := by ring
  omega

theorem cycle_below_five {s q n : ℕ} {D : CH.Digraph}
    (hs : 7≤s) (hq : q=2*s-7) (hn : 0<n) (hc : n+6≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,rfl⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  have he : q=2*a+7 := by omega
  rw [he] at hc ⊢
  by_contra hno
  have h := order_bound (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h
  omega

#print axioms middle_growth
#print axioms order_bound
#print axioms cycle_below_five
end LeanCH.BR.ShenFifthStrip
