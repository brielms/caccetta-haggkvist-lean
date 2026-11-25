import checkpoints.shen_extension.WindowSchedule
import checkpoints.shen_extension.TightPair

/-!
# Strip windows with the tight pair

`WindowSchedule` closes the strip `q = 2s - h` by the two-ball count on the
half-slope deficit schedule. Here the final comparison is `tight_pair_false`
(`TightPair.lean`) instead, which closes one more order.

* Half-slope window (`strip_window`): for odd `h = 2p+3` the pair at radii
  `R+1+2p`, `R+2+2p` is used with the out-degree floor at radius `1`; for even
  `h = 2p+4` the pair is shifted to `R+1+2p`, `R+3+2p` (one more schedule step)
  with the ideal floor at radius `2`. Every order with
  `2n + h(h-3) ≤ 2qs`, and for even `h ≥ 4` every order with
  `2n + (h-2)² ≤ 2qs + 2`, is closed. (The two-ball count gave exactly one order
  fewer at each `h ≥ 3`.)
* Recursive window (`strip_window_eighth`): every order with
  `8n + h(h+4) ≤ 8qs + 7`. For `h ≢ 0 (mod 4)` this is one more order than the
  exact two-ball count; for `h ≡ 0 (mod 4)` the balanced radii have equal
  deficits and the tight pair gains nothing, and the bound is the exact
  two-ball count.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TightWindow
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip Window TightPair

/-! ## Half-slope window -/

/-- Odd gap `h = 2p+3`: one order beyond `Window.order_odd`. -/
theorem order_odd_tight {q s p : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+(2*p+3)=2*s) (hs : 3*p+4≤s)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (ne : V.Nonempty) :
    q*s+2≤V.card+((p*p+p)+(p+1)*(p+1)) := by
  obtain ⟨R,rfl⟩ : ∃ R, s=R+3*p+3 := ⟨s-(3*p+3),by omega⟩
  have hq : q=2*R+4*p+3 := by omega
  subst hq
  have order := fun F W (hF : QFree F W (2*R+4*p+3))
      (hmF : ∀ v ∈ W, R+2*p+2≤(outN F W v).card) (hn : W.Nonempty) =>
    order_in_window (R+2*p+2) (by omega) (2*R+4*p+3) (by omega) hF hmF hn
  have hb := fun u (hu : u ∈ V) =>
    (Window.schedule (R:=R) (j:=p+1) order hf hm hu (by omega) (by omega) p
      (by nlinarith) (by nlinarith) (by omega))
  have hsq1 : p*p+p≤(R+3*p+3)*(R+1+2*p)+1 := by nlinarith
  have hsq2 : (p+1)*(p+1)≤(R+3*p+3)*(R+2+2*p)+1 := by nlinarith
  have one : ∀ u ∈ V, (R+3*p+3)+1 ≤ (ball D V u 1).card := fun u hu => by
    rw [card_B1 (hf.mono_bound (by omega)) hu]
    exact Nat.add_le_add_right (hm u hu) 1
  have he : (2*R+4*p+3)*(R+3*p+3)=(R+3*p+3)*(R+1+2*p)+(R+3*p+3)*(R+2+2*p) := by ring
  have he2 : (2*R+4*p+3)*(R+3*p+3)=2*((R+3*p+3)*(R+1+2*p))+(R+3*p+3) := by ring
  have esq : (p+1)*(p+1)=p*p+2*p+1 := by ring
  by_contra! big
  exact tight_pair_false (k:=R+1+2*p)
    (a:=(R+3*p+3)*(R+1+2*p)+1-(p*p+p)) (b:=(R+3*p+3)*(R+2+2*p)+1-(p+1)*(p+1))
    (c:=(R+3*p+3)+1) hf (by omega) ne
    (fun u hu => by have := (hb u hu).1; omega)
    (fun u hu => by
      rw [show 2*R+4*p+3-(R+1+2*p) = R+2+2*p by omega]
      have := (hb u hu).2; omega)
    (fun u hu => by
      rw [show 2*R+4*p+3-2*(R+1+2*p) = 1 by omega]
      exact one u hu)
    (by omega) (by omega)

/-- Even gap `h = 2p+4` (with `3h ≤ 2s`): one order beyond `Window.order_even`. -/
theorem order_even_tight {q s p : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+(2*p+4)=2*s) (hs : 3*p+6≤s)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (ne : V.Nonempty) :
    q*s+2≤V.card+2*((p+1)*(p+1)) := by
  obtain ⟨R,rfl⟩ : ∃ R, s=R+3*p+4 := ⟨s-(3*p+4),by omega⟩
  have hq : q=2*R+4*p+4 := by omega
  subst hq
  have hR : 2≤R := by omega
  have order := fun F W (hF : QFree F W (2*R+4*p+4))
      (hmF : ∀ v ∈ W, R+2*p+3≤(outN F W v).card) (hn : W.Nonempty) =>
    order_in_window (R+2*p+3) (by omega) (2*R+4*p+4) (by omega) hF hmF hn
  have hA := fun u (hu : u ∈ V) =>
    (Window.schedule (R:=R) (j:=p+1) order hf hm hu (by omega) (by omega) p
      (by nlinarith) (by nlinarith) (by omega)).1
  have hB := fun u (hu : u ∈ V) =>
    (Window.schedule (R:=R) (j:=p+1) order hf hm hu (by omega) (by omega) (p+1)
      (by nlinarith) (by nlinarith) (by omega)).1
  have two := fun u (hu : u ∈ V) =>
    Window.ideal (R:=R) (j:=p+1) order hf hm hu (by omega) (by omega) (by omega)
      (by nlinarith) (by nlinarith) 2 (by omega)
  have hsq1 : p*p+p≤(R+3*p+4)*(R+1+2*p)+1 := by nlinarith
  have hsq2 : (p+1)*(p+1)+(p+1)≤(R+3*p+4)*(R+3+2*p)+1 := by nlinarith
  have he : (2*R+4*p+4)*(R+3*p+4)=(R+3*p+4)*(R+1+2*p)+(R+3*p+4)*(R+3+2*p) := by ring
  have he2 : (2*R+4*p+4)*(R+3*p+4)=2*((R+3*p+4)*(R+1+2*p))+(R+3*p+4)*2 := by ring
  have esq : (p+1)*(p+1)=p*p+2*p+1 := by ring
  by_contra! big
  exact tight_pair_false (k:=R+1+2*p)
    (a:=(R+3*p+4)*(R+1+2*p)+1-(p*p+p)) (b:=(R+3*p+4)*(R+3+2*p)+1-((p+1)*(p+1)+(p+1)))
    (c:=(R+3*p+4)*2+1) hf (by omega) ne
    (fun u hu => by have := hA u hu; omega)
    (fun u hu => by
      rw [show 2*R+4*p+4-(R+1+2*p) = R+1+2*(p+1) by omega]
      have := hB u hu; rw [show R+1+2*(p+1) = R+3+2*p by omega] at this ⊢; omega)
    (fun u hu => by
      rw [show 2*R+4*p+4-2*(R+1+2*p) = 2 by omega]
      exact two u hu)
    (by omega) (by omega)

/-- The half-slope window with the tight pair. -/
theorem variable_window_tight {q s h n : ℕ} {D : CH.Digraph}
    (hg : q+h=2*s) (hh : 1≤h) (hs : 3*h≤2*s) (hn : 0<n)
    (hc : 2*n+h*(h-3)≤2*(q*s) ∨ (h%2=0 ∧ 4≤h ∧ 2*n+(h-2)*(h-2)≤2*(q*s)+2))
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra hno
  have hf := qfree_of_noShort hl hno
  have hm' : ∀ v ∈ Finset.range n, s≤(outN D (Finset.range n) v).card :=
    fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)
  have ne : (Finset.range n).Nonempty := ⟨0,Finset.mem_range.mpr hn⟩
  rcases Nat.lt_or_ge h 3 with h3|h3
  · have := order_in_window s (by omega) q (by omega) hf hm' ne
    rw [Finset.card_range] at this
    have z : h-3 = 0 := by omega
    rw [z, Nat.mul_zero] at hc
    rcases hc with hc|⟨_,h4,_⟩ <;> omega
  obtain ⟨p,hp|hp⟩ : ∃ p, h=2*p+4 ∨ h=2*p+3 := ⟨(h-3)/2, by omega⟩
  · subst hp
    have := order_even_tight (p:=p) (by omega) (by omega) hf hm' ne
    rw [Finset.card_range] at this
    have e1 : (2*p+4)*(2*p+4-3) = 4*(p*p)+10*p+4 := by
      rw [show 2*p+4-3 = 2*p+1 by omega]; ring
    have e2 : (2*p+4-2)*(2*p+4-2) = 4*(p*p)+8*p+4 := by
      rw [show 2*p+4-2 = 2*p+2 by omega]; ring
    have e3 : (p+1)*(p+1) = p*p+2*p+1 := by ring
    rw [e1, e2] at hc
    rcases hc with hc|⟨_,_,hc⟩ <;> omega
  · subst hp
    have := order_odd_tight (p:=p) (by omega) (by omega) hf hm' ne
    rw [Finset.card_range] at this
    have e1 : (2*p+3)*(2*p+3-3) = 4*(p*p)+6*p := by
      rw [show 2*p+3-3 = 2*p by omega]; ring
    have e3 : (p+1)*(p+1) = p*p+2*p+1 := by ring
    rw [e1] at hc
    rcases hc with hc|⟨hpar,_,_⟩
    · omega
    · omega

/-! ## Recursive window -/

set_option maxHeartbeats 1000000 in
/-- The recursive window `Window.order_rec` with the tight pair: in the contradiction form,
`8n + h(h+4) ≤ 8qs + 7` is impossible. -/
theorem order_rec_tight {h s q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+h=2*s) (hs : 2*h+2≤s) (hsq : h*h≤8*s) (hf : QFree D V q)
    (hm : ∀ v ∈ V, s≤(outN D V v).card) (ne : V.Nonempty) :
    8*(q*s)+8≤8*V.card+h*(h+4) := by
  by_cases h3 : h≤2
  · have := order_in_window s (by omega) q (by omega) hf hm ne
    omega
  obtain ⟨c,rfl⟩ : ∃ c, h=c+3 := ⟨h-3,by omega⟩
  obtain ⟨R,rfl⟩ : ∃ R, s=R+c+4 := ⟨s-(c+4),by omega⟩
  have hq : q=2*R+c+5 := by omega
  subst hq
  have hR : c+4≤R := by omega
  set E := ((c+3)*(c+3)+8)/8 with hE
  have hE1 : (c+3)*(c+3)+1≤8*E := by
    have := Nat.div_add_mod ((c+3)*(c+3)+8) 8
    have := Nat.mod_lt ((c+3)*(c+3)+8) (by norm_num : 0<8); omega
  have hE2 : 8*E≤(c+3)*(c+3)+8 := by
    have := Nat.div_add_mod ((c+3)*(c+3)+8) 8; omega
  have hEle : E≤(2*R+c+5)*(R+c+3) := by nlinarith
  obtain ⟨L,hL⟩ : ∃ L, L+E=(2*R+c+5)*(R+c+3)+1 := ⟨(2*R+c+5)*(R+c+3)+1-E,by omega⟩
  have order : ∀ F W, QFree F W (2*R+c+5) → (∀ v ∈ W, R+c+3≤(outN F W v).card) →
      W.Nonempty → L≤W.card := by
    intro F W hF hmF hn
    have := order_rec (c+1) (R+c+3) (2*R+c+5) (by omega) (by omega) (by nlinarith)
      hF hmF hn
    have e : (c+1+2)*(c+1+2)=(c+3)*(c+3) := by ring
    rw [e] at this
    omega
  set P := (c+3-(c+3)/2)/2 with hP
  have hP4 : 4*P≤c+4 := by omega
  have hid : (2*R+c+5)*(R+c+3)+3*(R+c+4) =
      (R+c+4)*(R+1)+(R+c+4)*(R+c+4)+(R+c+4)+(c+3) := by ring
  have hp : P*(1+1)+(R+c+4)*(R+1)+(R+c+4)*(R+c+4) < L+(R+c+4)*(2+1) := by
    have : (R+c+4)*(2+1) = 3*(R+c+4) := by ring
    rw [this]; omega
  have hz : (R+c+4)*(R+2*P+2)≤L := by
    have h1 : (R+c+4)*(4*P)≤(R+c+4)*(c+4) := Nat.mul_le_mul_left _ hP4
    nlinarith
  have hdef := fun u (hu : u ∈ V) => deficit_at (R:=R) (P:=P) (j:=1) order hf hm hu
    (by omega) (by omega) hp hz (by omega)
  obtain ⟨m1,hm1⟩ : ∃ m1, m1=(c+3)/2 := ⟨_,rfl⟩
  obtain ⟨m2,hm2⟩ : ∃ m2, m2=c+3-m1 := ⟨_,rfl⟩
  have hP' : P=m2/2 := by omega
  have hb1 : Gd m1≤(R+c+4)*(R+1+m1)+1 := Gd_le (by omega) (by omega)
  have hb2 : Gd m2≤(R+c+4)*(R+1+m2)+1 := Gd_le (by omega) (by omega)
  by_contra! big
  rcases (by omega : m2=m1+1 ∨ m2=m1) with h12|h12
  · -- odd gap: radii `R+1+m1`, `R+1+m2` and the out-degree floor at radius 1
    have one : ∀ u ∈ V, (R+c+4)+1 ≤ (ball D V u 1).card := fun u hu => by
      rw [card_B1 (hf.mono_bound (by omega)) hu]
      exact Nat.add_le_add_right (hm u hu) 1
    have he : (2*R+c+5)*(R+c+4)=(R+c+4)*(R+1+m1)+(R+c+4)*(R+1+m2) := by
      rw [← Nat.mul_add, Nat.mul_comm]; congr 1; omega
    have he2 : (2*R+c+5)*(R+c+4)=2*((R+c+4)*(R+1+m1))+(R+c+4) := by
      have : 2*R+c+5 = 2*(R+1+m1)+1 := by omega
      rw [this]; ring
    have gd : 8*(Gd m1+Gd m2) = (c+3)*(c+3+4)+3 ∧ Gd m1+1≤Gd m2 := by
      obtain ⟨t,ht|ht⟩ : ∃ t, m1=2*t ∨ m1=2*t+1 := ⟨m1/2,by omega⟩
      · have ec : c+3 = 4*t+1 := by omega
        rw [h12, ht, Gd_even, Gd_odd, ec]
        constructor
        · ring
        · nlinarith
      · have ec : c+3 = 4*t+3 := by omega
        rw [h12, ht, show 2*t+1+1 = 2*(t+1) by ring, Gd_even, Gd_odd, ec]
        constructor
        · ring
        · nlinarith
    exact tight_pair_false (k:=R+1+m1)
      (a:=(R+c+4)*(R+1+m1)+1-Gd m1) (b:=(R+c+4)*(R+1+m2)+1-Gd m2) (c:=(R+c+4)+1)
      hf (by omega) ne
      (fun u hu => by have := hdef u hu m1 (by omega); omega)
      (fun u hu => by
        rw [show 2*R+c+5-(R+1+m1) = R+1+m2 by omega]
        have := hdef u hu m2 (by omega); omega)
      (fun u hu => by
        rw [show 2*R+c+5-2*(R+1+m1) = 1 by omega]
        exact one u hu)
      (by omega) (by omega)
  · obtain ⟨t,ht|ht⟩ : ∃ t, m1=2*t ∨ m1=2*t+1 := ⟨m1/2,by omega⟩
    · -- `h ≡ 0 (mod 4)`: equal deficits, the exact two-ball count
      have hc := card_ge_of_two_balls hf (by omega : (R+1+m1)+(R+1+m2)≤2*R+c+5)
        (a:=(R+c+4)*(R+1+m1)+1-Gd m1) (b:=(R+c+4)*(R+1+m2)+1-Gd m2)
        (fun u hu => by have := hdef u hu m1 (by omega); omega)
        (fun u hu => by have := hdef u hu m2 (by omega); omega) ne
      have he : (2*R+c+5)*(R+c+4)=(R+c+4)*(R+1+m1)+(R+c+4)*(R+1+m2) := by
        rw [← Nat.mul_add, Nat.mul_comm]; congr 1; omega
      have gd : 16*Gd m1 = (c+3)*(c+3+4) := by
        have ec : c+3 = 4*t := by omega
        rw [ht, Gd_even, ec]; ring
      have g12 : Gd m2 = Gd m1 := by rw [h12]
      omega
    · -- `h ≡ 2 (mod 4)`: shift to radii `R+m1`, `R+2+m1` with the ideal floor at radius 2
      have ec : c+3 = 4*t+2 := by omega
      have c3 : 3≤c := by omega
      have hp1 : (P+1)*(1+1)+(R+c+4)*(R+1)+(R+c+4)*(R+c+4) < L+(R+c+4)*(2+1) := by
        have : (R+c+4)*(2+1) = 3*(R+c+4) := by ring
        rw [this]; omega
      have hz1 : (R+c+4)*(R+2*(P+1)+2)≤L := by
        have h1 : (R+c+4)*(4*P)≤(R+c+4)*(c+4) := Nat.mul_le_mul_left _ hP4
        have h2 : E≤R+c+5 := by omega
        have h7 : 7≤R := by omega
        nlinarith [h1, h2, hL, Nat.mul_le_mul h7 h7, Nat.mul_le_mul c3 c3, Nat.zero_le (R*c)]
      have hdef1 := fun u (hu : u ∈ V) => deficit_at (R:=R) (P:=P+1) (j:=1) order hf hm hu
        (by omega) (by omega) hp1 hz1 (by omega)
      have two := fun u (hu : u ∈ V) =>
        Window.ideal (R:=R) (j:=1) order hf hm hu (by omega) (by omega) (by omega)
          (by omega) (le_trans (Nat.mul_le_mul_left _ (by omega)) hz) 2 (by omega)
      have hb0 : Gd (2*t)≤(R+c+4)*(R+1+2*t)+1 := Gd_le (by omega) (by omega)
      have hb3 : Gd (2*t+2)≤(R+c+4)*(R+1+(2*t+2))+1 := Gd_le (by omega) (by omega)
      have he : (2*R+c+5)*(R+c+4)=(R+c+4)*(R+1+2*t)+(R+c+4)*(R+1+(2*t+2)) := by
        rw [← Nat.mul_add, Nat.mul_comm]; congr 1; omega
      have he2 : (2*R+c+5)*(R+c+4)=2*((R+c+4)*(R+1+2*t))+(R+c+4)*2 := by
        have : 2*R+c+5 = 2*(R+1+2*t)+2 := by omega
        rw [this]; ring
      have gd : 8*(Gd (2*t)+Gd (2*t+2)) = (c+3)*(c+3+4)+4 ∧ 2*Gd (2*t)+1≤Gd (2*t)+Gd (2*t+2) := by
        rw [show 2*t+2 = 2*(t+1) by ring, Gd_even, Gd_even, ec]
        constructor
        · ring
        · nlinarith
      exact tight_pair_false (k:=R+1+2*t)
        (a:=(R+c+4)*(R+1+2*t)+1-Gd (2*t)) (b:=(R+c+4)*(R+1+(2*t+2))+1-Gd (2*t+2))
        (c:=(R+c+4)*2+1) hf (by omega) ne
        (fun u hu => by have := hdef u hu (2*t) (by omega); omega)
        (fun u hu => by
          rw [show 2*R+c+5-(R+1+2*t) = R+1+(2*t+2) by omega]
          have := hdef1 u hu (2*t+2) (by omega); omega)
        (fun u hu => by
          rw [show 2*R+c+5-2*(R+1+2*t) = 2 by omega]
          exact two u hu)
        (by omega) (by omega)

theorem variable_window_rec_tight {q s h n : ℕ} {D : CH.Digraph}
    (hg : q+h=2*s) (hs : 2*h+2≤s) (hsq : h*h≤8*s) (hn : 0<n)
    (hc : 8*n+h*(h+4)≤8*(q*s)+7) (hl : CH.Loopless D n)
    (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra hno
  have bound := order_rec_tight hg hs hsq (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at bound
  omega

#print axioms order_odd_tight
#print axioms order_even_tight
#print axioms variable_window_tight
#print axioms order_rec_tight
#print axioms variable_window_rec_tight
end LeanCH.BR.TightWindow
