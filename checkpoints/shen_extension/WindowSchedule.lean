import checkpoints.shen_extension.VariableCutoff

/-! Variable window with the half-slope deficit schedule.
Comparison degree d = s-j with order bound L.  Ideal growth to radius R+1,
then the deficit at radius R+1+m is ⌊(m+1)²/4⌋ (p*p+p at m=2p, (p+1)² at m=2p+1). -/
namespace LeanCH.BR.Window
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

theorem ideal {q s d j L R u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (order : ∀ F W, QFree F W q → (∀ v ∈ W, d ≤ (outN F W v).card) →
      W.Nonempty → L ≤ W.card)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hd : d+j=s) (hq : R+2≤q) (h4 : 4≤q)
    (hkey : s*(R+1)+s*s < L+s*(2+j)) (hz : s*(R+1)≤L) :
    ∀ k, k≤R+1 → s*k+1≤(ball D V u k).card := by
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
    have hk' : s*(k+1)≤s*R := Nat.mul_le_mul_left s (by omega)
    have hk2 : s*(k+2)≤s*(R+1) := Nat.mul_le_mul_left s (by omega)
    have hs := ShenStripTransfer.growth_step (k:=k) (g0:=0) (g1:=0) (g2:=0) order hf hm hu hd
      (by omega) (by rw [Nat.add_zero]; exact ih k (by omega) (by omega))
      (by rw [Nat.add_zero]; exact ih (k+1) (by omega) (by omega)) le_rfl (by omega)
      (by push_cast; zify at hkey hk'; nlinarith) (by omega)
    rw [Nat.add_zero] at hs
    exact hs

theorem schedule {q s d j L R u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (order : ∀ F W, QFree F W q → (∀ v ∈ W, d ≤ (outN F W v).card) →
      W.Nonempty → L ≤ W.card)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hd : d+j=s) (h4 : 4≤q) :
    ∀ p, p*(j+1)+s*(R+1)+s*s < L+s*(2+j) → s*(R+2*p+2)≤L → R+2*p+2≤q →
      s*(R+1+2*p)+1≤(ball D V u (R+1+2*p)).card+(p*p+p) ∧
      s*(R+2+2*p)+1≤(ball D V u (R+2+2*p)).card+(p+1)*(p+1) := by
  intro p
  induction p with
  | zero =>
    intro hp hz hq
    simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at hp hz hq ⊢
    have hz' : s*(R+1)≤L := le_trans (Nat.mul_le_mul_left s (by omega)) hz
    have hI := ideal order hf hm hu hd (by omega) h4 hp hz'
    refine ⟨hI (R+1) le_rfl, ?_⟩
    have hs := ShenStripTransfer.growth_step (k:=R) (g0:=0) (g1:=0) (g2:=1) order hf hm hu hd
      (by omega) (by rw [Nat.add_zero]; exact hI R (by omega))
      (by rw [Nat.add_zero]; exact hI (R+1) le_rfl) (by omega) (by omega)
      (by push_cast; zify at hp; nlinarith) (by omega)
    simpa using hs
  | succ p ih =>
    intro hp hz hq
    have hp0 : p*(j+1)+s*(R+1)+s*s < L+s*(2+j) := by
      have : p*(j+1)≤(p+1)*(j+1) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hz0 : s*(R+2*p+2)≤L := le_trans (Nat.mul_le_mul_left s (by omega)) hz
    obtain ⟨i0,i1⟩ := ih hp0 hz0 (by omega)
    have hzA : s*(R+1+2*p+2)≤L := le_trans (Nat.mul_le_mul_left s (by omega)) hz
    have hzB : s*(R+2+2*p+2)≤L := le_trans (Nat.mul_le_mul_left s (by omega)) hz
    have eA : R+1+2*p+1 = R+2+2*p := by omega
    have hA := ShenStripTransfer.growth_step (k:=R+1+2*p) (g0:=p*p+p) (g1:=(p+1)*(p+1))
      (g2:=(p+1)*(p+1)+(p+1)) order hf hm hu hd (by omega) i0 (by rw [eA]; exact i1)
      (Nat.le_add_right _ _) (by nlinarith)
      (by push_cast; zify at hp; nlinarith) (by omega)
    have eB : R+2+2*p+1 = R+1+2*p+2 := by omega
    have hB := ShenStripTransfer.growth_step (k:=R+2+2*p) (g0:=(p+1)*(p+1))
      (g1:=(p+1)*(p+1)+(p+1)) (g2:=(p+1+1)*(p+1+1)) order hf hm hu hd (by omega) i1
      (by rw [eB]; exact hA) (by nlinarith) (by nlinarith)
      (by push_cast; zify at hp; nlinarith) (by nlinarith)
    have e1 : R+1+2*(p+1) = R+1+2*p+2 := by omega
    have e2 : R+2+2*(p+1) = R+2+2*p+2 := by omega
    rw [e1,e2]
    exact ⟨hA,hB⟩

/-- Even gap h = 2p+4: comparison degree s-p-1 (closed by `order_in_window`). -/
theorem order_even {q s p : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+(2*p+4)=2*s) (hs : 3*p+4≤s)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (ne : V.Nonempty) :
    q*s+1≤V.card+2*((p+1)*(p+1)) := by
  obtain ⟨R,rfl⟩ : ∃ R, s=R+3*p+4 := ⟨s-(3*p+4),by omega⟩
  have hq : q=2*R+4*p+4 := by omega
  subst hq
  have order := fun F W (hF : QFree F W (2*R+4*p+4))
      (hmF : ∀ v ∈ W, R+2*p+3≤(outN F W v).card) (hn : W.Nonempty) =>
    order_in_window (R+2*p+3) (by omega) (2*R+4*p+4) (by omega) hF hmF hn
  have hb := fun u (hu : u ∈ V) =>
    (schedule (R:=R) (j:=p+1) order hf hm hu (by omega) (by omega) p
      (by nlinarith) (by nlinarith) (by omega)).2
  have hsq : (p+1)*(p+1)≤(R+3*p+4)*(R+2+2*p)+1 := by nlinarith
  have hc := card_ge_of_two_balls hf (by omega : (R+2+2*p)+(R+2+2*p)≤2*R+4*p+4)
    (a:=(R+3*p+4)*(R+2+2*p)+1-(p+1)*(p+1)) (b:=(R+3*p+4)*(R+2+2*p)+1-(p+1)*(p+1))
    (fun u hu => by have := hb u hu; omega) (fun u hu => by have := hb u hu; omega) ne
  have he : (2*R+4*p+4)*(R+3*p+4)=(R+3*p+4)*(R+2+2*p)+(R+3*p+4)*(R+2+2*p) := by ring
  omega

/-- Odd gap h = 2p+3: comparison degree s-p-1. -/
theorem order_odd {q s p : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+(2*p+3)=2*s) (hs : 3*p+4≤s)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (ne : V.Nonempty) :
    q*s+1≤V.card+((p*p+p)+(p+1)*(p+1)) := by
  obtain ⟨R,rfl⟩ : ∃ R, s=R+3*p+3 := ⟨s-(3*p+3),by omega⟩
  have hq : q=2*R+4*p+3 := by omega
  subst hq
  have order := fun F W (hF : QFree F W (2*R+4*p+3))
      (hmF : ∀ v ∈ W, R+2*p+2≤(outN F W v).card) (hn : W.Nonempty) =>
    order_in_window (R+2*p+2) (by omega) (2*R+4*p+3) (by omega) hF hmF hn
  have hb := fun u (hu : u ∈ V) =>
    (schedule (R:=R) (j:=p+1) order hf hm hu (by omega) (by omega) p
      (by nlinarith) (by nlinarith) (by omega))
  have hsq1 : p*p+p≤(R+3*p+3)*(R+1+2*p)+1 := by nlinarith
  have hsq2 : (p+1)*(p+1)≤(R+3*p+3)*(R+2+2*p)+1 := by nlinarith
  have hc := card_ge_of_two_balls hf (by omega : (R+1+2*p)+(R+2+2*p)≤2*R+4*p+3)
    (a:=(R+3*p+3)*(R+1+2*p)+1-(p*p+p)) (b:=(R+3*p+3)*(R+2+2*p)+1-(p+1)*(p+1))
    (fun u hu => by have := (hb u hu).1; omega) (fun u hu => by have := (hb u hu).2; omega) ne
  have he : (2*R+4*p+3)*(R+3*p+3)=(R+3*p+3)*(R+1+2*p)+(R+3*p+3)*(R+2+2*p) := by ring
  omega

/-- Unified order bound: 2|V| + (h-1)² ≥ 2qs + 2 when 1 ≤ h and 3h ≤ 2s. -/
theorem order_bound' {q s h : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hg : q+h=2*s) (hh : 1≤h) (hs : 3*h≤2*s)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (ne : V.Nonempty) :
    2*(q*s+1)≤2*V.card+(h-1)*(h-1) := by
  rcases Nat.lt_or_ge h 3 with h3|h3
  · have := order_in_window s (by omega) q (by omega) hf hm ne
    omega
  obtain ⟨p,hp|hp⟩ : ∃ p, h=2*p+4 ∨ h=2*p+3 := ⟨(h-3)/2, by omega⟩
  · have := order_even (p:=p) (by omega) (by omega) hf hm ne
    have hx : h-1=2*p+3 := by omega
    rw [hx]; nlinarith
  · have := order_odd (p:=p) (by omega) (by omega) hf hm ne
    have hx : h-1=2*p+2 := by omega
    rw [hx]; nlinarith

theorem variable_window' {q s h n : ℕ} {D : CH.Digraph}
    (hg : q+h=2*s) (hh : 1≤h) (hs : 3*h≤2*s) (hn : 0<n)
    (hc : 2*n+(h-1)*(h-1)≤2*(q*s)) (hl : CH.Loopless D n)
    (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra hno
  have bound := order_bound' hg hh hs (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at bound
  omega

/-! ## Recursive comparison degree s-1: slack ⌊(h+2)²/8⌋-ish once h² ≤ 8s -/

def Gd (m : ℕ) : ℕ := (m+1)*(m+1)/4

theorem Gd_even (p : ℕ) : Gd (2*p) = p*p+p := by
  unfold Gd; rw [show (2*p+1)*(2*p+1) = 4*(p*p+p)+1 by ring]; omega

theorem Gd_odd (p : ℕ) : Gd (2*p+1) = (p+1)*(p+1) := by
  unfold Gd; rw [show (2*p+1+1)*(2*p+1+1) = 4*((p+1)*(p+1)) by ring]; omega

theorem Gd_upper (x : ℕ) : 4*Gd x ≤ (x+1)*(x+1) := by
  unfold Gd; have := Nat.div_add_mod ((x+1)*(x+1)) 4; omega

theorem Gd_le {m s r : ℕ} (h1 : m+1≤s) (h2 : m+1≤r) : Gd m≤s*r+1 := by
  have := Gd_upper m; have := Nat.mul_le_mul h1 h2; omega

theorem deficit_at {q s d j L R u P : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (order : ∀ F W, QFree F W q → (∀ v ∈ W, d ≤ (outN F W v).card) →
      W.Nonempty → L ≤ W.card)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hd : d+j=s) (h4 : 4≤q)
    (hp : P*(j+1)+s*(R+1)+s*s < L+s*(2+j)) (hz : s*(R+2*P+2)≤L) (hq : R+2*P+2≤q) :
    ∀ m, m≤2*P+1 → s*(R+1+m)+1≤(ball D V u (R+1+m)).card+Gd m := by
  intro m hmP
  obtain ⟨p,rfl|rfl⟩ : ∃ p, m=2*p ∨ m=2*p+1 := ⟨m/2,by omega⟩
  · have hpP : p≤P := by omega
    have := (schedule (R:=R) order hf hm hu hd h4 p
      (by have : p*(j+1)≤P*(j+1) := Nat.mul_le_mul_right _ hpP
          omega)
      (le_trans (Nat.mul_le_mul_left s (by omega)) hz) (by omega)).1
    rw [Gd_even]; exact this
  · have hpP : p≤P := by omega
    have := (schedule (R:=R) order hf hm hu hd h4 p
      (by have : p*(j+1)≤P*(j+1) := Nat.mul_le_mul_right _ hpP
          omega)
      (le_trans (Nat.mul_le_mul_left s (by omega)) hz) (by omega)).2
    rw [Gd_odd, show R+1+(2*p+1) = R+2+2*p by ring]; exact this

theorem sq_even (m : ℕ) : 2*((m+1)*(m+1))+2*((m+1)*(m+1)) ≤ (2*m+2)*(2*m+2)+1 := by
  nlinarith

theorem sq_odd (m : ℕ) : 2*((m+1)*(m+1))+2*((m+1+1)*(m+1+1)) ≤ (2*m+1+2)*(2*m+1+2)+1 := by
  nlinarith

set_option maxHeartbeats 1000000 in
/-- Recursive window: comparison degree s-1, whose order bound is this theorem at gap h-2. -/
theorem order_rec : ∀ h s q : ℕ, ∀ {D : CH.Digraph} {V : Finset ℕ},
    q+h=2*s → 2*h+2≤s → h*h≤8*s → QFree D V q → (∀ v ∈ V, s≤(outN D V v).card) →
    V.Nonempty → 8*(q*s+1)≤8*V.card+((h+2)*(h+2)+1) := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
  intro s q D V hg hs hsq hf hm ne
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
    have := ih (c+1) (by omega) (R+c+3) (2*R+c+5) (by omega) (by omega) (by nlinarith)
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
  have hc := card_ge_of_two_balls hf (by omega : (R+1+m1)+(R+1+m2)≤2*R+c+5)
    (a:=(R+c+4)*(R+1+m1)+1-Gd m1) (b:=(R+c+4)*(R+1+m2)+1-Gd m2)
    (fun u hu => by have := hdef u hu m1 (by omega); omega)
    (fun u hu => by have := hdef u hu m2 (by omega); omega) ne
  have he : (2*R+c+5)*(R+c+4)=(R+c+4)*(R+1+m1)+(R+c+4)*(R+1+m2) := by
    rw [← Nat.mul_add, Nat.mul_comm]; congr 1; omega
  have g1 := Gd_upper m1
  have g2 := Gd_upper m2
  have hsq2 : 2*((m1+1)*(m1+1))+2*((m2+1)*(m2+1))≤(c+3+2)*(c+3+2)+1 := by
    rcases (by omega : m2=m1 ∨ m2=m1+1) with h12|h12
    · rw [h12]; have : c+3=2*m1 := by omega
      rw [this]; exact sq_even m1
    · rw [h12]; have : c+3=2*m1+1 := by omega
      rw [this]; exact sq_odd m1
  clear hdef order ih hp hz hid hEle
  omega

theorem variable_window_rec {q s h n : ℕ} {D : CH.Digraph}
    (hg : q+h=2*s) (hs : 2*h+2≤s) (hsq : h*h≤8*s) (hn : 0<n)
    (hc : 8*n+((h+2)*(h+2)+1)≤8*(q*s)) (hl : CH.Loopless D n)
    (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra hno
  have bound := order_rec h s q hg hs hsq (qfree_of_noShort hl hno)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at bound
  omega

#print axioms deficit_at
#print axioms order_rec
#print axioms variable_window_rec
#print axioms schedule
#print axioms order_even
#print axioms order_odd
#print axioms order_bound'
#print axioms variable_window'
end LeanCH.BR.Window
