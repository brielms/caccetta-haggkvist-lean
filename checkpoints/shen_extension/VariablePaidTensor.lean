import checkpoints.shen_extension.MixedCloneTensor
import checkpoints.shen_extension.VariableCutoff

namespace LeanCH.BR.ShenVariablePaid
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport

private theorem price_arith {q s h B C : ℕ} (gap : q+h=2*s) (hp : 1≤h)
    (scale : 64*(h*h)≤s) (floors : B+C+3*(h*h)=q*s+2) :
    (2*s)*(q*s+1)*((q*s+1)-(B+C)) < (B+C-1-s*s)^2 := by
  have hh := Nat.le_mul_self h
  have hs : 0<s := by omega
  have mass : q*s+h*s=2*(s*s) := by nlinarith only [congrArg (fun n : ℕ => n*s) gap]
  have room : q*s+1≤2*(s*s) := by
    have := Nat.mul_le_mul_right s hp
    omega
  have smaller := Nat.mul_le_mul_right s (show 4*h≤s by omega)
  have cross := Nat.mul_le_mul_right h (show 3*h≤s by omega)
  have twice : s*s≤2*(B+C-1-s*s) := by
    have h1 : 2*(h*s)+6*(h*h)≤s*s := by nlinarith only [smaller,cross]
    omega
  have loss : q*s+1-(B+C)≤3*(h*h) := by omega
  have upper := Nat.mul_le_mul (Nat.mul_le_mul_left (2*s) room) loss
  have strict := Nat.mul_lt_mul_of_pos_right (show 48*(h*h)<s by omega)
    (show 0<s*s*s by positivity)
  have lower := Nat.pow_le_pow_left twice 2
  nlinarith only [upper,strict,lower]

/-- Across variable cutoff gaps, the older universal floors already pay
for a stronger order bound on every small prefix with concentrated gaps. -/
theorem payment {q s h k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 1≤h) (scale : 64*(h*h)≤s)
    (hf : QFree D V q) (hm : ∀ v∈V,s≤(outN D V v).card) (hu : u∈V)
    (hk : k+2≤q) (ht : (shell D V (k+1) u).card<s)
    (small : ((ball D V u (k+1)).erase u).card≤s*s)
    (support : (layer D V (k+1) u).card≤2*s) :
    q*s+1+holes D V (k+1) u≤((ball D V u (k+1)).erase u).card+
      (layer D V (k+1) u).card*(shell D V (k+1) u).card := by
  have hh := Nat.le_mul_self h
  obtain ⟨b,rfl⟩ : ∃ b,s=b+2*h := ⟨s-2*h,by omega⟩
  have eq : q=2*b+3*h := by omega
  subst q
  let s := b+2*h
  let B := s*(b+h)+1-h*h
  let C := s*(b+2*h)+1-h*(2*h)
  have eqBC : B+C+3*(h*h)=(2*b+3*h)*s+2 := by
    have b1 : h*h≤s*(b+h)+1 := by dsimp [s]; nlinarith
    have b2 : h*(2*h)≤s*(b+2*h)+1 := by dsimp [s]; nlinarith
    have hsum : s*(b+h)+s*(b+2*h)=(2*b+3*h)*s := by ring
    have hmul : h*(2*h)=2*(h*h) := by ring
    dsimp only [B,C]; omega
  apply ShenMixedClone.prefix_price (i:=b+h) (j:=b+2*h) (B:=B) (C:=C)
    (by omega) _ hf hm hu (by omega) hk ht small support (price_arith gap hp scale eqBC)
  intro F W hF m _ v hv
  have grow := ShenVariableCutoff.outer_growth hp (by omega : h≤b) hF m (u:=v) hv
  have g1 := grow h (by omega)
  have g2 := grow (2*h) le_rfl
  dsimp only [B,C,s]; constructor <;> omega

private theorem step {q s h k u g0 g1 g2 : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 1≤h) (scale : 64*(h*h)≤s)
    (hf : QFree D V q) (hm : ∀ v∈V,s≤(outN D V v).card) (hu : u∈V)
    (hk : k+2≤s) (h0 : s*k+1≤(ball D V u k).card+g0)
    (h1 : s*(k+1)+1≤(ball D V u (k+1)).card+g1)
    (g01 : g0≤g2) (g12 : g1≤g2) (slope : 2*g1≤g2+g0)
    (key : ((s:ℤ)-g1+g0)*((s:ℤ)-1-g2+g1) < (q:ℤ)*s+1-s*(k+1)+g1) :
    s*(k+2)+1≤(ball D V u (k+2)).card+g2 := by
  have hh := Nat.le_mul_self h
  have hs : s≤q := by omega
  apply ShenStripTransfer.growth_from_prefix (d:=s) (j:=0) (L:=q*s+1) hu (by omega)
    h0 h1 (by omega) (by push_cast; simpa using key) _ _
  · have := Nat.mul_le_mul_right s (hk.trans hs)
    rw [Nat.mul_comm s (k+2)]; omega
  intro bad
  have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
    (show k+1≤k+2 by omega))
  have hc := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
    (show k≤k+1 by omega))
  have hk1 : s*(k+2)=s*(k+1)+s := by ring
  have hk2 : s*(k+2)=s*k+2*s := by ring
  have pp := payment gap hp scale hf hm hu (by omega : k+2≤q)
    (by unfold shell; rw [show k+1+1=k+2 by omega]; omega)
    (by have := Finset.card_le_card (Finset.erase_subset u (ball D V u (k+1)))
        have := Nat.mul_le_mul_left s hk
        omega)
    (by simp only [layer,Nat.add_sub_cancel]; omega)
  have er := Finset.card_erase_add_one (self_mem_ball hu : u∈ball D V u (k+1))
  simp only [layer,Nat.add_sub_cancel,shell] at pp
  rw [show k+1+1=k+2 by omega] at pp
  rw [show s+(ball D V u (k+2) \ ball D V u (k+1)).card-s =
    (ball D V u (k+2) \ ball D V u (k+1)).card by omega]
  omega

/-- Ideal growth through q-s+2, on every host at the indicated scale.
The available comparison-degree argument stopped at s-2h+2. -/
theorem ideal {b h u : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hp : 2≤h)
    (scale : 64*(h*h)≤b+h) (hf : QFree D V (2*b+h))
    (hm : ∀ v∈V,b+h≤(outN D V v).card) (hu : u∈V) :
    ∀ k,k≤b+2 → (b+h)*k+1≤(ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases k with _|k
    · simpa using (Finset.card_pos.mpr ⟨u,self_mem_ball (k:=0) hu⟩ :
        0<(ball D V u 0).card)
    rcases k with _|k
    · have hh := Nat.le_mul_self h
      rw [card_B1 (hf.mono_bound (by omega)) hu,Nat.mul_one]
      exact Nat.add_le_add_right (hm u hu) 1
    apply step (g0:=0) (g1:=0) (g2:=0) (by omega : 2*b+h+h=2*(b+h)) (by omega) scale hf hm hu
      (by omega) (ih k (by omega) (by omega)) (ih (k+1) (by omega) (by omega))
      (by decide) (by decide) (by decide)
    have hi : (k:ℤ)≤b := by exact_mod_cast (by omega : k≤b)
    push_cast
    nlinarith only [mul_nonneg (show 0≤(b:ℤ)+h by positivity) (show (0:ℤ)≤b-k by omega)]

/-- Above the ideal phase, a single linear loss schedule suffices through
both middle radii. Its slope depends on the gap and is shared by all hosts. -/
theorem outer {b h u : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hp : 2≤h)
    (scale : 64*(h*h)≤b+h) (hf : QFree D V (2*b+h))
    (hm : ∀ v∈V,b+h≤(outN D V v).card) (hu : u∈V) :
    ∀ j,j≤(h+1)/2 → (b+h)*(b+j)+1≤(ball D V u (b+j)).card+((h+3)/4)*j := by
  let m := (h+3)/4
  have msize : m*(m+1)≤b+h := by
    have ml : m≤h := by dsimp [m]; omega
    have p := Nat.mul_le_mul ml (show m+1≤h+1 by omega)
    have hh := Nat.le_mul_self h
    nlinarith only [p,scale,hh]
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    rcases j with _|j
    · simpa using ideal (by omega) scale hf hm hu b (by omega)
    rcases j with _|j
    · have hh := ideal (by omega) scale hf hm hu (b+1) (by omega)
      change (b+h)*(b+1)+1≤(ball D V u (b+1)).card+m*1
      omega
    have h0 := ih j (by omega) (by omega)
    have h1 := ih (j+1) (by omega) (by omega)
    rw [← Nat.add_assoc] at h1
    have inc (k : ℕ) : m*(k+1)=m*k+m := by ring
    have g2 : m*(j+2)=m*j+2*m := by ring
    have grow := step (k:=b+j) (g0:=m*j) (g1:=m*(j+1)) (g2:=m*(j+2))
      (by omega : 2*b+h+h=2*(b+h)) (by omega) scale hf hm hu (by omega) h0 h1
      (by rw [g2]; omega) (by rw [inc,g2]; omega) (by rw [inc,g2]; omega) (by
        have hs : (m:ℤ)*((m:ℤ)+1)≤(b:ℤ)+h := by exact_mod_cast msize
        have hj' : (j:ℤ)+1≤2*m := by exact_mod_cast (show j+1≤2*m by dsimp [m]; omega)
        push_cast
        nlinarith only [mul_nonneg (show 0≤(b:ℤ)+h by positivity)
          (show (0:ℤ)≤2*m-j-1 by omega),hs,
          mul_nonneg (Int.natCast_nonneg m) (show (0:ℤ)≤j+1 by positivity)])
    simpa only [Nat.add_assoc,m] using grow

theorem order_bound {q s h : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (gap : q+h=2*s) (hp : 2≤h) (scale : 64*(h*h)≤s)
    (hf : QFree D V q) (hm : ∀ v∈V,s≤(outN D V v).card) (ne : V.Nonempty) :
    q*s+1≤V.card+((h+3)/4)*h := by
  have hh := Nat.le_mul_self h
  obtain ⟨b,rfl⟩ : ∃ b,s=b+h := ⟨s-h,by omega⟩
  have hq : q=2*b+h := by omega
  subst q
  let j := h/2
  let t := h-j
  let m := (h+3)/4
  have jt : j+t=h := by dsimp [j,t]; omega
  have f1 (u) (hu : u∈V) := outer hp scale hf hm hu j (by dsimp [j]; omega)
  have f2 (u) (hu : u∈V) := outer hp scale hf hm hu t (by dsimp [t,j]; omega)
  have lower := card_ge_of_two_balls hf (by omega : (b+j)+(b+t)≤2*b+h)
    (a:=(b+h)*(b+j)+1-m*j) (b:=(b+h)*(b+t)+1-m*t)
    (fun u hu => by have := f1 u hu; dsimp [m]; omega)
    (fun u hu => by have := f2 u hu; dsimp [m]; omega) ne
  have e1 : (b+h)*(b+j)+(b+h)*(b+t)=(2*b+h)*(b+h) := by
    nlinarith only [congrArg (fun n : ℕ => (b+h)*n) jt]
  have e2 : m*j+m*t=m*h := by rw [← Nat.mul_add,jt]
  change (2*b+h)*(b+h)+1≤V.card+m*h
  omega

theorem cycle_in_window {q s h n : ℕ} {D : CH.Digraph} (gap : q+h=2*s)
    (hp : 2≤h) (scale : 64*(h*h)≤s) (hn : 0<n) (width : n+((h+3)/4)*h≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  have := order_bound gap hp scale (qfree_of_noShort hl no)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at this
  omega

#print axioms payment
#print axioms ideal
#print axioms outer
#print axioms order_bound
#print axioms cycle_in_window
end LeanCH.BR.ShenVariablePaid
