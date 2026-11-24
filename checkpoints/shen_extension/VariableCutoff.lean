import checkpoints.shen_extension.StripTransfer

/-! A single order estimate across unboundedly many cutoff gaps.
Write s=b+2h, q=2b+3h, so h=2s-q. Compare to degree d=b+h.
Every radius through b+2 has ideal growth. Beyond b the deficit grows
by at most h per step in the lower bound, through radius s. -/
namespace LeanCH.BR.ShenVariableCutoff
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

private theorem comparison {b h : ℕ} (hh : 1≤h) (hb : h≤b)
    (F : CH.Digraph) (W : Finset ℕ) (hf : QFree F W (2*b+3*h))
    (hm : ∀ v∈W, b+h≤(outN F W v).card) (ne : W.Nonempty) :
    (2*b+3*h)*(b+h)+1≤W.card :=
  order_in_window (b+h) (by omega) _ (by omega) hf hm ne

private theorem prefix_room {b h k : ℕ} (hb : h≤b) (hk : k≤b+2*h) :
    (b+2*h)*k≤(2*b+3*h)*(b+h)+1 := by
  nlinarith only [Nat.mul_le_mul_left (b+2*h) hk,Nat.mul_le_mul_right h hb,
    Nat.zero_le (b*b)]

theorem ideal_growth {b h u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hh : 1≤h) (hb : h≤b) (hf : QFree D V (2*b+3*h))
    (hm : ∀ v∈V, b+2*h≤(outN D V v).card) (hu : u∈V) :
    ∀ k, k≤b+2 → (b+2*h)*k+1≤(ball D V u k).card := by
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
    apply ShenStripTransfer.growth_step (g0:=0) (g1:=0) (g2:=0)
      (comparison hh hb) hf hm hu (by omega : (b+h)+h=b+2*h) (by omega)
      (ih k (by omega) (by omega)) (ih (k+1) (by omega) (by omega))
      (by decide) (by omega)
    · have hk' : (k:ℤ)≤b := by exact_mod_cast (by omega : k≤b)
      push_cast
      nlinarith only [mul_nonneg (show 0≤(b:ℤ)+2*h by positivity)
        (show 0≤(b:ℤ)-k by omega),sq_nonneg (h:ℤ)]
    · exact prefix_room hb (by omega)

/-- The comparison-degree deficit bound at every radius b+l, for 0≤l≤2h. -/
theorem outer_growth {b h u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hh : 1≤h) (hb : h≤b) (hf : QFree D V (2*b+3*h))
    (hm : ∀ v∈V, b+2*h≤(outN D V v).card) (hu : u∈V) :
    ∀ l, l≤2*h → (b+2*h)*(b+l)+1≤(ball D V u (b+l)).card+h*l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro hl
    rcases l with _|l
    · simpa using ideal_growth hh hb hf hm hu b (by omega)
    rcases l with _|l
    · have := ideal_growth hh hb hf hm hu (b+1) (by omega)
      change (b+2*h)*(b+1)+1≤(ball D V u (b+1)).card+h*1
      omega
    have h0 := ih l (by omega) (by omega)
    have h1 := ih (l+1) (by omega) (by omega)
    rw [← Nat.add_assoc] at h1
    have hstep := ShenStripTransfer.growth_step (k:=b+l) (g0:=h*l) (g1:=h*(l+1))
      (g2:=h*(l+2)) (comparison hh hb) hf hm hu
      (by omega : (b+h)+h=b+2*h) (by omega) h0 h1
      (by nlinarith) (by nlinarith)
      (by
        push_cast
        have hl' : (l:ℤ)≤2*h := by exact_mod_cast (by omega : l≤2*h)
        nlinarith only [mul_nonneg (show 0≤(b:ℤ)+h by positivity)
          (show 0≤2*(h:ℤ)-l by omega),sq_nonneg (h:ℤ)])
      (by have := prefix_room hb (k:=b+l+2) (by omega); omega)
    simpa only [Nat.add_assoc] using hstep

/-- For all gaps at once, a q-free graph of minimum outdegree s has order
at least qs+1-3h² whenever h=2s-q and 1≤h≤s/3. -/
theorem order_bound {q s h : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+h=2*s) (hh : 1≤h) (hs : 3*h≤s)
    (hf : QFree D V q) (hm : ∀ v∈V, s≤(outN D V v).card) (ne : V.Nonempty) :
    q*s+1≤V.card+3*h*h := by
  obtain ⟨b,rfl⟩ : ∃ b, s=b+2*h := ⟨s-2*h,by omega⟩
  have he : q=2*b+3*h := by omega
  subst q
  have hb : h≤b := by omega
  have hp := fun u hu => outer_growth hh hb hf hm (u:=u) hu
  have capacity := card_ge_of_two_balls hf (by omega : (b+h)+(b+2*h)≤2*b+3*h)
    (a:=(b+2*h)*(b+h)+1-h*h) (b:=(b+2*h)*(b+2*h)+1-h*(2*h))
    (fun u hu => by have := hp u hu h (by omega); omega)
    (fun u hu => by have := hp u hu (2*h) le_rfl; omega) ne
  have h1 : h*h≤(b+2*h)*(b+h)+1 := by nlinarith
  have h2 : h*(2*h)≤(b+2*h)*(b+2*h)+1 := by nlinarith
  have he : (2*b+3*h)*(b+2*h)=(b+2*h)*(b+h)+(b+2*h)*(b+2*h) := by ring
  have hw : 3*h*h=h*h+h*(2*h) := by ring
  omega

theorem cycle_in_variable_window {q s h n : ℕ} {D : CH.Digraph}
    (hg : q+h=2*s) (hh : 1≤h) (hs : 3*h≤s) (hn : 0<n)
    (hc : n+3*h*h≤q*s) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra hno
  have bound := order_bound hg hh hs (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at bound
  omega

#print axioms outer_growth
#print axioms order_bound
#print axioms cycle_in_variable_window
end LeanCH.BR.ShenVariableCutoff
