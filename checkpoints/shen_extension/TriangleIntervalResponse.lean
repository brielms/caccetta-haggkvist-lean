import checkpoints.shen_extension.IntervalArcRecurrence

namespace LeanCH.BR.Closure.TriangleIntervalResponse
open Finset Matrix

open IntervalArcRecurrence
private noncomputable def s : ℝ := -1/2
private noncomputable def z (n i : ℕ) : ℝ :=
  (if i%n=0 then 1 else s^(n-i%n)) / (2*(1-s^n))

private theorem power_bound {k j : ℕ} (h : k≤j) : |s^j| ≤ (1/2:ℝ)^k := by
  rw [abs_pow,show |s|=(1/2:ℝ) by norm_num [s]]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

private theorem z_step {n : ℕ} (hn : 4 ≤ n) (i : ℕ) :
    2*z n i + z n (i+1) = pulse n i := by
  have bd := abs_le.mp (power_bound hn)
  have den : 1-s^n ≠ 0 := by norm_num at bd; linarith [bd.2]
  let u := i%n
  have hu : u<n := Nat.mod_lt _ (by omega)
  have step : (i+1)%n = if u+1=n then 0 else u+1 := by
    rw [Nat.add_mod]; simp only [Nat.mod_eq_of_lt (by omega : 1<n)]
    change (u+1)%n = _
    split_ifs with eq
    · simp [eq]
    · exact Nat.mod_eq_of_lt (by omega)
  unfold z pulse
  rw [step]
  change 2*((if u=0 then 1 else s^(n-u)) / _) + _ = if u=0 then 1 else 0
  by_cases zero : u=0
  · simp only [zero,ite_true,Nat.zero_add,show ¬1=n by omega,ite_false,one_ne_zero]
    have rel : s^n=s^(n-1)*s := by conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
    field_simp [den]; rw [rel]; unfold s; ring
  · by_cases wrap : u+1=n
    · simp only [zero,wrap,ite_true,ite_false,show n-u=1 by omega,pow_one]
      field_simp [den]; unfold s; ring
    · simp [zero,wrap]
      rw [show n-u=(n-(u+1))+1 by omega,pow_succ]
      unfold s; ring

private theorem universal_difference {n : ℕ} (hn : 4≤n) (g : ℕ→ℝ)
    (per : ∀ i, g (i+n)=g i)
    (eqn : ∀ i, g (i+3)-3*g (i+1)+2*g i=3*(pulse n (i+4)-pulse n (i+1)))
    {t : ℕ} (ht : 1≤t) (tn : t<n) :
    g t-g 0 = 3*(pulse n (t+1)-pulse n 1) + 6*(z n t-z n 0) + 3-3*(t:ℝ)/n := by
  let h := fun i => g i - 3*pulse n (i+1)-6*z n i
  let e := fun i => h (i+1)-h i-3*pulse n i
  have hp (i) : h (i+n)=h i := by
    dsimp [h]; rw [per,show i+n+1=i+1+n by omega]; simp [pulse,z]
  have ep (i) : e (i+n)=e i := by
    dsimp [e]; rw [show i+n+1=i+1+n by omega,hp,hp]; simp [pulse]
  have recur (i) : e (i+2)+e (i+1)-2*e i=0 := by
    dsimp only [e,h]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    have h0 := z_step hn i
    have h1 := z_step hn (i+1)
    have h2 := z_step hn (i+2)
    simp only [Nat.add_assoc,Nat.reduceAdd] at h1 h2
    linarith only [eqn i,h0,h1,h2]
  have delta (i : ℕ) : e (i+1)-e i=(-2:ℝ)^i*(e 1-e 0) := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ]; linarith only [recur i,ih]
  have endpt := delta n
  rw [show n+1=1+n by omega,ep,show n=0+n by omega,ep 0] at endpt
  simp only [Nat.zero_add] at endpt
  have powne : (-2:ℝ)^n ≠ 1 := by
    intro bad
    have b := congrArg abs bad
    simp only [abs_pow,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),abs_one] at b
    exact (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : n≠0)).ne' b
  have d0 : e 1-e 0=0 := by
    have hmul : ((-2:ℝ)^n-1)*(e 1-e 0)=0 := by linarith only [endpt]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr powne)
  have constant (i : ℕ) : e i=e 0 := by
    induction i with
    | zero => rfl
    | succ i ih => have hi := delta i; rw [d0,mul_zero] at hi; linarith
  have line (i : ℕ) (hi : i+1≤n) : h (i+1)=h 0+3+(i+1:ℕ)*(e 0) := by
    induction i with
    | zero => dsimp [e]; simp [pulse]
    | succ i ih =>
      have step := constant (i+1)
      change h (i+1+1)-h (i+1)-3*pulse n (i+1)=e 0 at step
      rw [show pulse n (i+1)=0 by simp [pulse,Nat.mod_eq_of_lt (by omega : i+1<n)]] at step
      push_cast at ih ⊢; linarith [ih (by omega)]
  have cycle := line (n-1) (by omega)
  rw [show n-1+1=n by omega] at cycle
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hnval : h n=h 0 := by simpa using hp 0
  have slope : e 0= -3/(n:ℝ) := (eq_div_iff hn0).mpr (by linarith only [cycle,hnval,mul_comm (e 0) (n:ℝ)])
  have val := line (t-1) (by omega)
  rw [show t-1+1=t by omega,slope] at val
  dsimp only [h] at val
  simp only [Nat.zero_add] at val
  linear_combination val

/-- Two columns centered at the endpoints can have different additive
constants. Their local differences nevertheless have a strictly negative sum. -/
theorem local_contrast {n : ℕ} (hn : 4≤n) (g h : ℕ→ℝ)
    (pg : ∀ i, g (i+n)=g i) (ph : ∀ i, h (i+n)=h i)
    (eg : ∀ i, g (i+3)-3*g (i+1)+2*g i=3*(pulse n (i+4)-pulse n (i+1)))
    (eh : ∀ i, h (i+3)-3*h (i+1)+2*h i=3*(pulse n (i+4)-pulse n (i+1)))
    (t : ℕ) (ht : 1≤t) (tn : t<n) :
    1 + (g t-g 0) + (h (n-t)-h 0) < 0 := by
  rw [universal_difference hn g pg eg ht tn,universal_difference hn h ph eh (by omega) (by omega)]
  have sub : ((n-t:ℕ):ℝ)=(n:ℝ)-t := by rw [Nat.cast_sub (by omega)]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have den := abs_le.mp (power_bound hn)
  norm_num at den
  have pos : 0<1-s^n := by linarith [den.2]
  have pp (j : ℕ) (hj : 0<j) (jl : j<n) :
      pulse n (j+1)=(if j+1=n then 1 else 0) := by
    by_cases e : j+1=n
    · simp [pulse,e]
    · simp [pulse,e,Nat.mod_eq_of_lt (by omega : j+1<n)]
  rw [sub,pp t (by omega) tn,pp (n-t) (by omega) (by omega)]
  simp only [pulse,Nat.mod_eq_of_lt (by omega : 1<n),one_ne_zero,ite_false]
  unfold z
  simp only [Nat.mod_eq_of_lt tn,Nat.mod_eq_of_lt (by omega : n-t<n),Nat.zero_mod,ite_true,
    show t≠0 by omega,show n-t≠0 by omega,ite_false,show n-(n-t)=t by omega]
  have reduction : (3:ℝ)*t/n+3*((n:ℝ)-t)/n=3 := by field_simp; ring
  suffices bound : (4+3*(if t+1=n then 1 else 0)+3*(if n-t+1=n then 1 else 0) : ℝ)*
      (1-s^n) < 3*(2-s^t-s^(n-t)) by
    have align : 6*(s^(n-t)/(2*(1-s^n))-1/(2*(1-s^n))) +
        6*(s^t/(2*(1-s^n))-1/(2*(1-s^n))) = -(3*(2-s^t-s^(n-t))/(1-s^n)) := by
      field_simp [pos.ne']; ring
    linarith only [reduction,align,(lt_div_iff₀ pos).mpr bound]
  by_cases small : n=4
  · subst n; interval_cases t <;> norm_num [s]
  have proj (k : ℕ) (hk : 4≤k) : s^k ≤ 1/16 := by
    have := (abs_le.mp (power_bound hk)).2; norm_num at this; exact this
  have tail := abs_le.mp (power_bound (show 5≤n by omega))
  norm_num at tail
  have mid (k : ℕ) (hk : 2≤k) : s^k≤1/4 := by
    have := (abs_le.mp (power_bound hk)).2; norm_num at this; exact this
  by_cases lo : t=1
  · subst t
    simp only [show ¬1+1=n by omega,ite_false,show n-1+1=n by omega,ite_true,pow_one]
    have step := proj (n-1) (by omega)
    linarith only [step,tail.1,show s= -1/2 by rfl]
  · by_cases hi : t+1=n
    · have nt : n-t=1 := by omega
      simp only [hi,ite_true,nt,show ¬1+1=n by omega,ite_false,pow_one]
      have step := proj t (by omega)
      linarith only [step,tail.1,show s= -1/2 by rfl]
    · simp only [hi,show ¬n-t+1=n by omega,ite_false]
      have u := mid t (by omega)
      have v := mid (n-t) (by omega)
      linarith only [u,v,tail.1]

/-- At cutoff three the scalar condition holds at every nonzero displacement. -/
theorem sign {r : ℕ} (hr : 0<r) (g : ℕ→ℝ) (per : Function.Periodic g (3*r+1))
    (eqn : Equation 3 (3*r+1) g) (t : ℕ) (pos : 0<t) (bound : t<3*r+1) :
    1+(g t-g 0)+(g (3*r+1-t)-g 0)<0 := by
  have step (i : ℕ) : g (i+3)-3*g (i+1)+2*g i =
      3*(pulse (3*r+1) (i+4)-pulse (3*r+1) (i+1)) := by
    convert eqn i using 1; norm_num
  exact local_contrast (by omega) g g per per step step t pos bound

end LeanCH.BR.Closure.TriangleIntervalResponse
#print axioms LeanCH.BR.Closure.TriangleIntervalResponse.local_contrast
#print axioms LeanCH.BR.Closure.TriangleIntervalResponse.sign
