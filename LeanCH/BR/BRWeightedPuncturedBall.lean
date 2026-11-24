import LeanCH.BR.BRNonParentBanks
import LeanCH.BR.BRWeightedSingleContactCut

/-! Root-retaining ball growth from actual SmallRow on punctured balls.
All subtraction in the coefficients is rational. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem punctured_ball_base {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    {z : ℕ} (hz : z∈V) (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ}
    (hr : c≤row q D V a z) :
    c-a z≤(q:ℚ)*mass ((ball D V z 1).erase z) a := by
  have hm := mass_mono (heads_in_punctured_ball hf hz hq (by decide : 1≤1))
    (fun x hx=>ha x (ball_subset (mem_of_mem_erase hx)))
  have hh := mul_le_mul_of_nonneg_left hm (show (0:ℚ)≤q by positivity)
  rw [row,outW_eq_mass] at hr
  linarith

/-- Only this punctured child's SmallRow is used. No acyclicity is assumed. -/
theorem punctured_ball_smallRow_step {q k : ℕ}
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    {z : ℕ} (hz : z∈V) (hk : k+1≤q)
    (hne : ((ball D V z k).erase z).Nonempty)
    (hs : SmallRow q D ((ball D V z k).erase z))
    (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ}
    (hr : ∀x∈(ball D V z k).erase z,c≤row q D V a x) :
    c+((q:ℚ)-1)*mass ((ball D V z k).erase z) a≤
      (q:ℚ)*mass ((ball D V z (k+1)).erase z) a := by
  have hAV : (ball D V z k).erase z⊆V := (erase_subset _ _).trans ball_subset
  obtain ⟨x,hx,he⟩ := cut_contact_mass hAV hne hs a (fun x hx=>ha x (hAV hx)) c hr
  have hheads : outN D (V\(ball D V z k).erase z) x⊆
      (ball D V z (k+1)).erase z\(ball D V z k).erase z := by
    intro y hy
    obtain ⟨hyV,hyA⟩ := mem_sdiff.mp (mem_outN.mp hy).1
    have exy := (mem_outN.mp hy).2
    have hyz : y≠z := by
      intro eq
      subst y
      exact no_back_arc hf hz (mem_of_mem_erase hx) hk exy
    exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨hyz,ball_step (mem_of_mem_erase hx) hyV exy⟩,hyA⟩
  have hm := mass_mono hheads (fun y hy=>ha y
    (ball_subset (mem_of_mem_erase (mem_sdiff.mp hy).1)))
  rw [outW_eq_mass] at he
  have hh := mul_le_mul_of_nonneg_left hm (show (0:ℚ)≤q by positivity)
  have hnest : (ball D V z k).erase z⊆(ball D V z (k+1)).erase z :=
    erase_subset_erase z (ball_mono_radius (by omega))
  have hsum : mass ((ball D V z (k+1)).erase z\(ball D V z k).erase z) a+
      mass ((ball D V z k).erase z) a=mass ((ball D V z (k+1)).erase z) a := sum_sdiff hnest
  nlinarith

theorem punctured_ball_power_lower {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hproper : ∀U⊆V,U≠V→SmallRow q D U) {z : ℕ} (hz : z∈V)
    (hne : (outN D V z).Nonempty) (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x)
    {c : ℚ} (hr : ∀x∈V,c≤row q D V a x) (j : ℕ) (hj : j+1≤q) :
    ((q:ℚ)^(j+1)-((q:ℚ)-1)^(j+1))*c-((q:ℚ)-1)^j*a z≤
      (q:ℚ)^(j+1)*mass ((ball D V z (j+1)).erase z) a := by
  induction j with
  | zero => simpa using punctured_ball_base hq hf hz a ha (hr z hz)
  | succ j ih =>
    have ih := ih (by omega)
    have hAV : (ball D V z (j+1)).erase z⊆V := (erase_subset _ _).trans ball_subset
    have hneV : (ball D V z (j+1)).erase z≠V := by
      intro he
      have hzA := he.symm ▸ hz
      exact (mem_erase.mp hzA).1 rfl
    have hs := punctured_ball_smallRow_step hf hz hj
      (hne.mono (heads_in_punctured_ball hf hz hq (by omega)))
      (hproper _ hAV hneV) a ha (fun x hx=>hr x (hAV hx))
    have hq1 : (1:ℚ)≤q := by exact_mod_cast hq
    have hq0 : (0:ℚ)≤(q:ℚ)-1 := by linarith
    have hi := mul_le_mul_of_nonneg_left ih hq0
    have ht := mul_le_mul_of_nonneg_left hs (show (0:ℚ)≤(q:ℚ)^(j+1) by positivity)
    simp only [pow_succ] at hi ht ⊢
    nlinarith

theorem root_retaining_ball_lower {q k : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hproper : ∀U⊆V,U≠V→SmallRow q D U) {z : ℕ} (hz : z∈V)
    (hne : (outN D V z).Nonempty) (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x)
    {c : ℚ} (hr : ∀x∈V,c≤row q D V a x) (hk : 1≤k) (hkq : k≤q) :
    ((q:ℚ)^k-((q:ℚ)-1)^k)*c+((q:ℚ)^k-((q:ℚ)-1)^(k-1))*a z≤
      (q:ℚ)^k*mass (ball D V z k) a := by
  have he : k-1+1=k := Nat.sub_add_cancel hk
  have h := punctured_ball_power_lower hq hf hproper hz hne a ha hr (k-1) (by omega)
  rw [he] at h
  have hs : mass ((ball D V z k).erase z) a+a z=mass (ball D V z k) a :=
    sum_erase_add _ a (self_mem_ball hz)
  rw [←hs]
  nlinarith only [h]

/-- Strict nonnegative rows force a genuine head, independently of girth. -/
theorem outN_nonempty_of_strict_row {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {z : ℕ} (hz : z∈V)
    (hr : mass V a<row q D V a z) : (outN D V z).Nonempty := by
  by_contra hn
  have he := not_nonempty_iff_eq_empty.mp hn
  have ho : outW D V a z=0 := by rw [outW_eq_mass,he]; simp [mass]
  have hm : a z≤mass V a := single_le_sum ha hz
  rw [row,ho,mul_zero,add_zero] at hr
  exact (not_lt_of_ge hm) hr

theorem SmallerSmallRow.strict_root_retaining_ball_lower {q k : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) (a : ℕ→ℚ) (ha : ∀x∈V,0≤a x) {c : ℚ}
    (hc : mass V a<c) (hr : ∀x∈V,c≤row q D V a x)
    {z : ℕ} (hz : z∈V) (hk : 1≤k) (hkq : k≤q) :
    ((q:ℚ)^k-((q:ℚ)-1)^k)*c+((q:ℚ)^k-((q:ℚ)-1)^(k-1))*a z≤
      (q:ℚ)^k*mass (ball D V z k) a :=
  root_retaining_ball_lower hq hf (hsmall.induced hf) hz
    (outN_nonempty_of_strict_row a ha hz (hc.trans_le (hr z hz))) a ha hr hk hkq

end LeanCH.BR.WeightedSD
