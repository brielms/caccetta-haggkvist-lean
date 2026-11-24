import LeanCH.BR.BRWeightedPuncturedBall

/-! Actual first exits from light regions, retaining the original graph and law. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- All vertices before the final crossing are in W. No girth is needed. -/
theorem first_exit_of_walk {D : CH.Digraph} {V W : Finset ℕ} {z y m : ℕ}
    (w : Walk D V z y m) (hz : z∈W) (hy : y∉W) :
    ∃j x b,j+1≤m ∧ x∈W ∧ b∈V\W ∧ Walk D W z x j ∧ D x b=true := by
  induction w with
  | refl z => exact False.elim (hy hz)
  | @step z v y k hv ezv w ih =>
    by_cases hvW : v∈W
    · obtain ⟨j,x,b,hj,hx,hb,wp,exb⟩ := ih hvW hy
      exact ⟨j+1,x,b,by omega,hx,hb,.step hvW ezv wp,exb⟩
    · exact ⟨0,z,v,by omega,hz,mem_sdiff.mpr ⟨hv,hvW⟩,.refl z,ezv⟩

theorem root_retaining_ball_exit {q k : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V W : Finset ℕ} (hf : QFree D V q)
    (hproper : ∀U⊆V,U≠V→SmallRow q D U) (hWV : W⊆V)
    {z : ℕ} (hz : z∈W) (hne : (outN D V z).Nonempty)
    (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ}
    (hr : ∀x∈V,c≤row q D V a x) (hk : 1≤k) (hkq : k≤q)
    (hlight : (q:ℚ)^k*mass W a<
      ((q:ℚ)^k-((q:ℚ)-1)^k)*c+((q:ℚ)^k-((q:ℚ)-1)^(k-1))*a z) :
    ∃j x b,j+1≤k ∧ x∈W ∧ b∈V\W ∧ Walk D W z x j ∧ D x b=true := by
  have hbound := root_retaining_ball_lower hq hf hproper (hWV hz) hne a ha hr hk hkq
  have hnot : ¬ball D V z k⊆W := by
    intro hs
    have hm := mul_le_mul_of_nonneg_left (mass_mono hs (fun x hx=>ha x (hWV hx)))
      (show (0:ℚ)≤(q:ℚ)^k by positivity)
    exact (not_lt_of_ge (hbound.trans hm)) hlight
  obtain ⟨y,hy,hyW⟩ := not_subset.mp hnot
  obtain ⟨_,m,hm,w⟩ := mem_ball.mp hy
  obtain ⟨j,x,b,hj,hx,hb,wp,exb⟩ := first_exit_of_walk w hz hyW
  exact ⟨j,x,b,hj.trans hm,hx,hb,wp,exb⟩

theorem root_ball_coefficient_nonneg {q k : ℕ} (hq : 1≤q) (hk : 1≤k) :
    (0:ℚ)≤(q:ℚ)^k-((q:ℚ)-1)^(k-1) := by
  have hq1 : (1:ℚ)≤q := by exact_mod_cast hq
  have hq0 : (0:ℚ)≤(q:ℚ)-1 := by linarith
  have he := pow_le_pow_left₀ hq0 (by linarith : (q:ℚ)-1≤q) (k-1)
  have hp : (0:ℚ)≤(q:ℚ)^(k-1) := by positivity
  have hs : (q:ℚ)^(k-1)≤(q:ℚ)^k := by
    conv_rhs => rw [←Nat.sub_add_cancel hk,pow_succ]
    nlinarith
  exact sub_nonneg.mpr (he.trans hs)

theorem uniform_ball_exit {q k : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V W : Finset ℕ} (hf : QFree D V q)
    (hproper : ∀U⊆V,U≠V→SmallRow q D U) (hWV : W⊆V)
    {z : ℕ} (hz : z∈W) (hne : (outN D V z).Nonempty)
    (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ}
    (hr : ∀x∈V,c≤row q D V a x) (hk : 1≤k) (hkq : k≤q)
    (hlight : mass W a<(1-(1-1/(q:ℚ))^k)*c) :
    ∃j x b,j+1≤k ∧ x∈W ∧ b∈V\W ∧ Walk D W z x j ∧ D x b=true := by
  have hqpos : (0:ℚ)<q := by exact_mod_cast (by omega : 0<q)
  have he : (q:ℚ)^k*(1-(1-1/(q:ℚ))^k)=(q:ℚ)^k-((q:ℚ)-1)^k := by
    have hbase : 1-1/(q:ℚ)=((q:ℚ)-1)/(q:ℚ) := by field_simp
    rw [hbase,div_pow]
    field_simp
  have hm := mul_lt_mul_of_pos_left hlight (pow_pos hqpos k)
  have hm' : (q:ℚ)^k*mass W a<((q:ℚ)^k-((q:ℚ)-1)^k)*c := by
    simpa only [←mul_assoc,he] using hm
  have hz0 := mul_nonneg (root_ball_coefficient_nonneg hq hk) (ha z (hWV hz))
  exact root_retaining_ball_exit hq hf hproper hWV hz hne a ha hr hk hkq (by linarith)

theorem SmallerSmallRow.strict_root_retaining_ball_exit {q k : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V W : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) (hWV : W⊆V) {z : ℕ} (hz : z∈W)
    (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ} (hc : mass V a<c)
    (hr : ∀x∈V,c≤row q D V a x) (hk : 1≤k) (hkq : k≤q)
    (hlight : (q:ℚ)^k*mass W a<
      ((q:ℚ)^k-((q:ℚ)-1)^k)*c+((q:ℚ)^k-((q:ℚ)-1)^(k-1))*a z) :
    ∃j x b,j+1≤k ∧ x∈W ∧ b∈V\W ∧ Walk D W z x j ∧ D x b=true :=
  root_retaining_ball_exit hq hf (hsmall.induced hf) hWV hz
    (outN_nonempty_of_strict_row a ha (hWV hz) (hc.trans_le (hr z (hWV hz)))) a ha hr hk hkq hlight

theorem SmallerSmallRow.strict_uniform_ball_exit {q k : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V W : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) (hWV : W⊆V) {z : ℕ} (hz : z∈W)
    (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ} (hc : mass V a<c)
    (hr : ∀x∈V,c≤row q D V a x) (hk : 1≤k) (hkq : k≤q)
    (hlight : mass W a<(1-(1-1/(q:ℚ))^k)*c) :
    ∃j x b,j+1≤k ∧ x∈W ∧ b∈V\W ∧ Walk D W z x j ∧ D x b=true :=
  uniform_ball_exit hq hf (hsmall.induced hf) hWV hz
    (outN_nonempty_of_strict_row a ha (hWV hz) (hc.trans_le (hr z (hWV hz)))) a ha hr hk hkq hlight

end LeanCH.BR.WeightedSD
