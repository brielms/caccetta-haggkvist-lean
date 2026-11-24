import Mathlib

/-! Breakpoint of the ball-growth method.
The only inequality the window proofs use between consecutive balls is the
prefix-deficiency bound (`prefix_deficiency_of_size`): if the layer t=|B_{k+2}|-|B_{k+1}|
is below s, then for every comparison degree d < s with order bound L_d,
  L_d ≤ |B_{k+1}| - 1 + c·(d+t-s),   c = |B_{k+1}|-|B_k|.
The profile `prof` below satisfies this with the strongest possible oracle
L_d = q·d+1 (CH itself at every degree d < s) at every radius, yet its two-ball
count stays ⌈(h²-4)/8⌉ below q·s+1.  -/
namespace LeanCH.BR.WindowBreakpoint

/-- Deficit after m shrinking radii: ⌊(m+1)²/4⌋ = 0,1,2,4,6,9,12,… -/
def G (m : ℕ) : ℕ := (m+1)*(m+1)/4

/-- Ideal growth to radius s+1-h, then layers s-⌈m/2⌉. -/
def prof (s h r : ℕ) : ℕ := s*r+1 - G (r-(s+1-h))

theorem G_even (p : ℕ) : G (2*p) = p*p+p := by
  unfold G; rw [show (2*p+1)*(2*p+1) = 4*(p*p+p)+1 by ring]; omega

theorem G_odd (p : ℕ) : G (2*p+1) = (p+1)*(p+1) := by
  unfold G; rw [show (2*p+1+1)*(2*p+1+1) = 4*((p+1)*(p+1)) by ring]; omega

theorem G_lower (x : ℕ) : (x+1)*(x+1) ≤ 4*G x + 1 := by
  obtain ⟨p,rfl|rfl⟩ : ∃ p, x=2*p ∨ x=2*p+1 := ⟨x/2,by omega⟩
  · rw [G_even]; nlinarith
  · rw [G_odd]; nlinarith

theorem G_upper (x : ℕ) : 4*G x ≤ (x+1)*(x+1) := by
  unfold G; have := Nat.div_add_mod ((x+1)*(x+1)) 4; omega

/-- Integer core, case d ≥ b. -/
theorem core_hi (R a b e j G1 : ℤ) (hR : 0≤ R) (ha : 0≤ a) (hj : 0≤ j)
    (hG : G1 ≤ a*(b+1)) :
    ((b+e+1+j)+R+1)*(b+e)+2+G1 ≤ (b+e+1+j)*(R+2+(a+b-1))+1+((b+e+1+j)-a)*e := by
  nlinarith [mul_nonneg hR hj, mul_nonneg ha hj]

/-- Integer core, case d < b. -/
theorem core_lo (s R h d b m G1 : ℤ) (hs : s=R+h+1) (hR : 0≤ R) (hh : 0≤ h) (hd0 : 0≤ d)
    (hd : d+1≤ b) (hbm : 2*b≤ m+2) (hm : m+2≤ s) (hG : G1 ≤ b*(b+1)) :
    (s+R+1)*d+2+G1 ≤ s*(R+2+m)+1 := by
  subst hs
  have h1 : (2*(R+h+1)-h)*d ≤ (2*(R+h+1)-h)*(b-1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (R+h+1)*(2*b-2) ≤ (R+h+1)*m :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rcases le_or_gt (b+1) h with hb|hb
  · nlinarith [mul_le_mul_of_nonneg_right hb (by linarith : (0:ℤ)≤ b-1)]
  · nlinarith [mul_le_mul_of_nonneg_left (by linarith : b+1≤ R+2) (by linarith : (0:ℤ)≤ R+h+1)]

/-- The natural-number step check at one radius. -/
theorem core {s h R d a b G0 G1 G2 m P0 P1 P2 X : ℕ} (hs : s=R+h+1)
    (hab : a+b=m+1) (hab' : a≤ b) (hb : b≤ a+1) (hG : G1≤ a*(b+1)) (hm : m+2≤ s)
    (hd : d+1≤ s) (hX : X=s*(R+2+m)) (hG01 : G1=G0+a) (hG12 : G2=G1+b)
    (e0 : P0+s+G0=X+1) (e1 : P1+G1=X+1) (e2 : P2+G2=X+s+1) :
    (2*s-h)*d+1 ≤ P1-1+(P1-P0)*(d+(P2-P1)-s) := by
  have hc : P1-P0 = s-a := by omega
  have ht : P2-P1 = s-b := by omega
  have hq : 2*s-h = s+R+1 := by omega
  rw [hc,ht,hq]
  rcases Nat.lt_or_ge d b with hdb|hdb
  · have hz : d+(s-b)-s = 0 := by omega
    rw [hz,Nat.mul_zero,Nat.add_zero]
    have key := core_lo (s:ℤ) R h d b m G1 (by exact_mod_cast hs) (by positivity)
      (by positivity) (by positivity) (by exact_mod_cast hdb) (by omega) (by exact_mod_cast hm)
      (by have : a*(b+1)≤ b*(b+1) := Nat.mul_le_mul_right _ hab'
          exact_mod_cast hG.trans this)
    have key' : (s+R+1)*d+2+G1 ≤ s*(R+2+m)+1 := by exact_mod_cast key
    omega
  · obtain ⟨e,rfl⟩ : ∃ e, d=b+e := ⟨d-b,by omega⟩
    have hz : b+e+(s-b)-s = e := by omega
    rw [hz]
    obtain ⟨j,hj⟩ : ∃ j, s=b+e+1+j := ⟨s-(b+e+1),by omega⟩
    obtain ⟨a',ha'⟩ : ∃ a', s=a+a' := ⟨s-a,by omega⟩
    have hsa : s-a = a' := by omega
    rw [hsa]
    have key := core_hi R a b e j G1 (by positivity) (by positivity) (by positivity)
      (by exact_mod_cast hG)
    have hm' : (m:ℤ) = a+b-1 := by omega
    have hs' : (s:ℤ) = b+e+1+j := by exact_mod_cast hj
    have ha'' : (a':ℤ) = s-a := by omega
    rw [← hm', ← hs', ← ha''] at key
    have key' : (s+R+1)*(b+e)+2+G1 ≤ s*(R+2+m)+1+a'*e := by exact_mod_cast key
    omega

theorem step_case {R h k d m a b G0 G1 G2 : ℕ} (hm : k+1=R+2+m) (hmS : m+2≤ R+h+1)
    (hd : d+1≤ R+h+1) (hab : a+b=m+1) (hab' : a≤ b) (hb : b≤ a+1) (hG : G1≤ a*(b+1))
    (hG01 : G1=G0+a) (hG12 : G2=G1+b) :
    (2*(R+h+1)-h)*d+1 ≤ ((R+h+1)*(k+1)+1-G1) - 1 +
      (((R+h+1)*(k+1)+1-G1) - ((R+h+1)*k+1-G0))*
        (d+(((R+h+1)*(k+2)+1-G2) - ((R+h+1)*(k+1)+1-G1))-(R+h+1)) := by
  have m1 : (R+h+1)*(k+1) = (R+h+1)*k+(R+h+1) := by ring
  have m2 : (R+h+1)*(k+2) = (R+h+1)*(k+1)+(R+h+1) := by ring
  have hX : (R+h+1)*(k+1) = (R+h+1)*(R+2+m) := by rw [hm]
  have hY : (m+1)*(m+2)+(R+h+1) ≤ (R+h+1)*(R+2+m) := by nlinarith
  have hG1 : G1 ≤ (m+1)*(m+2) := hG.trans (Nat.mul_le_mul (by omega) (by omega))
  exact core (s:=R+h+1) (R:=R) (a:=a) (b:=b) (G0:=G0) (G1:=G1) (G2:=G2) (m:=m)
    (X:=(R+h+1)*(k+1)) rfl hab hab' hb hG hmS hd hX hG01 hG12
    (by omega) (by omega) (by omega)

/-- The profile satisfies the prefix-deficiency inequality at every radius and every
comparison degree d < s, with the CH oracle L_d = q·d+1, whenever h+1 ≤ s. -/
theorem prof_prefix {s h k d : ℕ} (hs : h+1≤ s) (hk : k+2≤ 2*s-h) (hd : d+1≤ s)
    (ht : prof s h (k+2) - prof s h (k+1) < s) :
    (2*s-h)*d+1 ≤ prof s h (k+1) - 1 +
      (prof s h (k+1) - prof s h k)*(d+(prof s h (k+2) - prof s h (k+1))-s) := by
  obtain ⟨R,rfl⟩ : ∃ R, s=R+h+1 := ⟨s-(h+1),by omega⟩
  have hR0 : R+h+1+1-h = R+2 := by omega
  simp only [prof, hR0] at ht ⊢
  have m2 : (R+h+1)*(k+2) = (R+h+1)*(k+1)+(R+h+1) := by ring
  by_cases hlow : k+2≤ R+2
  · have i1 : k+1-(R+2)=0 := by omega
    have i2 : k+2-(R+2)=0 := by omega
    have g0 : G 0 = 0 := by decide
    rw [i1,i2,g0] at ht
    omega
  obtain ⟨m,hm⟩ : ∃ m, k+1=R+2+m := ⟨k+1-(R+2),by omega⟩
  have i0 : k-(R+2)=m-1 := by omega
  have i1 : k+1-(R+2)=m := by omega
  have i2 : k+2-(R+2)=m+1 := by omega
  rw [i0,i1,i2]
  have hmS : m+2 ≤ R+h+1 := by omega
  obtain ⟨p,hp|hp|hp⟩ : ∃ p, m=0 ∨ m=2*p+2 ∨ m=2*p+1 :=
    ⟨(m-1)/2, by omega⟩
  · subst hp
    have g0 : G (0-1) = 0 := by decide
    have g1 : G 0 = 0 := by decide
    have g2 : G (0+1) = 1 := by decide
    simp only [g0,g2]
    exact step_case (a:=0) (b:=1) hm hmS hd (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · rw [hp] at hm hmS ⊢
    have g0 : G (2*p+2-1) = (p+1)*(p+1) := by rw [show 2*p+2-1 = 2*p+1 by omega, G_odd]
    have g1 : G (2*p+2) = (p+1)*(p+1)+(p+1) := by rw [show 2*p+2 = 2*(p+1) by ring, G_even]
    have g2 : G (2*p+2+1) = (p+2)*(p+2) := by rw [show 2*p+2+1 = 2*(p+1)+1 by ring, G_odd]
    rw [g0,g1,g2]
    exact step_case (a:=p+1) (b:=p+2) hm hmS hd (by omega) (by omega) (by omega)
      (by nlinarith) (by ring) (by ring)
  · rw [hp] at hm hmS ⊢
    have g0 : G (2*p+1-1) = p*p+p := by rw [show 2*p+1-1 = 2*p by omega, G_even]
    have g1 : G (2*p+1) = (p+1)*(p+1) := G_odd p
    have g2 : G (2*p+1+1) = (p+1)*(p+1)+(p+1) := by rw [show 2*p+1+1 = 2*(p+1) by ring, G_even]
    rw [g0,g1,g2]
    exact step_case (a:=p+1) (b:=p+1) hm hmS hd (by omega) (by omega) (by omega)
      (by nlinarith) (by ring) (by ring)

/-- Exactness: the subtraction in `prof` never truncates below radius q. -/
theorem prof_exact {s h r : ℕ} (hs : h+1≤ s) (hr : r≤ 2*s-h) :
    prof s h r + G (r-(s+1-h)) = s*r+1 := by
  unfold prof
  have hu := G_upper (r-(s+1-h))
  have hx : r-(s+1-h) ≤ r := Nat.sub_le _ _
  have hx2 : r-(s+1-h)+1 ≤ s := by omega
  have : 4*G (r-(s+1-h)) ≤ 4*(s*r+1) := by
    rcases Nat.eq_zero_or_pos r with h0|h0
    · subst h0; simp at hu ⊢; omega
    · nlinarith [Nat.mul_le_mul hx2 (by omega : r-(s+1-h)+1≤ r+1)]
  omega

/-- The two-ball count on the profile: every complementary pair of radii falls
short of q·s+2 by at least (h²-4)/8.  So the window method, fed by any order oracle
for lower degrees, can at best close the orders with slack ≥ ⌈(h²-4)/8⌉ = ⌊h²/8⌋. -/
theorem prof_two_balls {s h i : ℕ} (hs : h+1≤ s) (hi : i≤ 2*s-h) :
    8*(prof s h i + prof s h (2*s-h-i)) + h*h ≤ 8*((2*s-h)*s+2) + 4 := by
  have e1 := prof_exact (r:=i) hs hi
  have e2 := prof_exact (r:=2*s-h-i) hs (by omega)
  set x := i-(s+1-h) with hx
  set y := 2*s-h-i-(s+1-h) with hy
  have hxy : h ≤ x+y+2 := by omega
  have gx := G_lower x
  have gy := G_lower y
  have hsum : s*i + s*(2*s-h-i) = (2*s-h)*s := by
    rw [← Nat.mul_add, show i+(2*s-h-i) = 2*s-h by omega, Nat.mul_comm]
  have hsq : h*h ≤ (x+y+2)*(x+y+2) := Nat.mul_le_mul hxy hxy
  have hconv : (x+y+2)*(x+y+2) ≤ 2*((x+1)*(x+1)) + 2*((y+1)*(y+1)) := by
    nlinarith [sq_nonneg ((x:ℤ)-y)]
  omega

#print axioms prof_prefix
#print axioms prof_exact
#print axioms prof_two_balls
end LeanCH.BR.WindowBreakpoint
