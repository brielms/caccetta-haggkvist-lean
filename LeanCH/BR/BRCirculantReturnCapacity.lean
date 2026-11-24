import LeanCH.BR.BRClosedNeighborhoodRepair
import LeanCH.BR.BRFiniteWalk

/-! Parametric displacement and maximum-step counts on C_(qd+1)(1,...,d).
No smaller-instance hypothesis or capacity supplier is assumed. -/
namespace LeanCH.BR.CirculantReturnCapacity
open Finset BRq2 BRq3 BR45 BRsub ClosedNeighborhoodRepair

/-- Every nonmaximum term spends at least one unit of total deficit. -/
theorem maximum_count_deficit {ι : Type*} (S : Finset ι) (f : ι → ℕ) (d : ℕ)
    (hb : ∀ i ∈ S, f i ≤ d) :
    S.card ≤ (S.filter (fun i => f i=d)).card + (S.card*d-∑ i ∈ S, f i) := by
  classical
  calc
    S.card = ∑ _i ∈ S, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ S, ((if f i=d then 1 else 0)+(d-f i)) := by
      apply sum_le_sum
      intro i hi
      have h := hb i hi
      split_ifs <;> omega
    _ = _ := by
      rw [sum_add_distrib,Finset.sum_tsub_distrib S hb]
      simp

theorem bounded_sum_rigidity {ι : Type*} (S : Finset ι) (f : ι → ℕ) (d : ℕ)
    (hb : ∀ i ∈ S, f i ≤ d) (hs : ∑ i ∈ S, f i=S.card*d) :
    ∀ i ∈ S, f i=d := by
  classical
  have h := maximum_count_deficit S f d hb
  rw [hs,Nat.sub_self,add_zero] at h
  exact Finset.card_filter_eq_iff.mp (le_antisymm (Finset.card_filter_le _ _) h)

theorem one_deficit_maximum_count {ι : Type*} (S : Finset ι) (f : ι → ℕ) (d : ℕ)
    (hb : ∀ i ∈ S, f i ≤ d) (hs : (∑ i ∈ S, f i)+1=S.card*d) :
    (S.filter (fun i => f i=d)).card+1=S.card := by
  classical
  have h := maximum_count_deficit S f d hb
  have hu := Finset.card_filter_le (s := S) (p := fun i => f i=d)
  have hne : (S.filter (fun i => f i=d)).card ≠ S.card := by
    intro he
    have hall := Finset.card_filter_eq_iff.mp he
    have heq : (∑ i ∈ S, f i)=S.card*d := by
      calc
        _ = ∑ _i ∈ S, d := Finset.sum_congr rfl hall
        _ = _ := by simp
    omega
  omega

theorem modular_trace_sum (N : ℕ) (f s : ℕ → ℕ) (l : ℕ)
    (hstep : ∀ k, k<l → Nat.ModEq N (f k+s k) (f (k+1))) :
    Nat.ModEq N (f 0+∑ k ∈ range l, s k) (f l) := by
  induction l with
  | zero => simp only [range_zero,sum_empty,Nat.add_zero]; rfl
  | succ l ih =>
    have h := (ih (fun k hk => hstep k (by omega))).add_right (s l)
    rw [Finset.sum_range_succ]
    simpa only [Nat.add_assoc] using h.trans (hstep l (by omega))

theorem edge_step {q d x y : ℕ} (h : graph q d x y=true) :
    ∃ k, 1≤k ∧ k≤d ∧ Nat.ModEq (q*d+1) (x+k) y := by
  obtain ⟨_,hh⟩ := of_decide_eq_true h
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hh
  refine ⟨k,(Finset.mem_Icc.mp hk).1,(Finset.mem_Icc.mp hk).2,?_⟩
  change (x+k)%(q*d+1)=y%(q*d+1)
  rw [← he,Nat.mod_mod]

theorem step_equals_maximum {N d x y s : ℕ} (hs : s≤d) (hd : d<N) (hy : y<N)
    (hm : Nat.ModEq N (x+s) y) : y=(x+d)%N ↔ s=d := by
  constructor
  · intro he
    have hr : Nat.ModEq N y (x+d) := by
      change y%N=(x+d)%N
      rw [Nat.mod_eq_of_lt hy,he]
    have hh := (hm.trans hr).add_left_cancel' x
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (lt_of_le_of_lt hs hd),Nat.mod_eq_of_lt hd] using hh
  · intro he
    subst s
    change (x+d)%N=y%N at hm
    rw [Nat.mod_eq_of_lt hy] at hm
    exact hm.symm

theorem offset_edge {q d i r : ℕ} (hi : i<q*d+1) (hr : 1≤r) (hrd : r≤d) :
    graph q d i ((i+r)%(q*d+1))=true := by
  apply decide_eq_true
  exact ⟨hi,Finset.mem_image.mpr ⟨r,Finset.mem_Icc.mpr ⟨hr,hrd⟩,rfl⟩⟩

/-- Any actual return of length at most q has length exactly q. -/
theorem return_length {q d i r l : ℕ} (hi : i<q*d+1) (hr : 1≤r) (hrd : r≤d)
    (hl : l≤q) (w : Walk (graph q d) (range (q*d+1)) ((i+r)%(q*d+1)) i l) : l=q := by
  have hstart : (i+r)%(q*d+1) ∈ range (q*d+1) :=
    Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  by_contra hn
  exact free q d i (l+1) (by omega) (by omega) (.step hstart (offset_edge hi hr hrd) w)

/-- Actual finite return traces carry an offset certificate whose total
deficit from q maximum steps is exactly r-1. -/
theorem return_steps {q d i r l : ℕ} (hq : 1≤q) (hi : i<q*d+1)
    (hr : 1≤r) (hrd : r≤d) (hl : l≤q) (f : ℕ → ℕ)
    (hstart : f 0=(i+r)%(q*d+1)) (hend : f l=i)
    (hpath : ∀ k, k<l → f (k+1) ∈ range (q*d+1) ∧ graph q d (f k) (f (k+1))=true) :
    l=q ∧ ∃ s : ℕ → ℕ,
      (∀ k, k<q → 1≤s k ∧ s k≤d ∧ Nat.ModEq (q*d+1) (f k+s k) (f (k+1))) ∧
      (∑ k ∈ range q, s k)+(r-1)=q*d := by
  classical
  have hw := walk_of_edges hpath
  rw [hstart,hend] at hw
  have he := return_length hi hr hrd hl hw
  subst l
  refine ⟨rfl,?_⟩
  have hx : ∀ k, k<q → ∃ t, 1≤t ∧ t≤d ∧ Nat.ModEq (q*d+1) (f k+t) (f (k+1)) :=
    fun k hk => edge_step (hpath k hk).2
  let s : ℕ → ℕ := fun k => if hk : k<q then Classical.choose (hx k hk) else 0
  have hs : ∀ k, k<q → 1≤s k ∧ s k≤d ∧ Nat.ModEq (q*d+1) (f k+s k) (f (k+1)) := by
    intro k hk
    dsimp only [s]
    rw [dite_eq_left hk]
    exact Classical.choose_spec (hx k hk)
  refine ⟨s,hs,?_⟩
  let t := ∑ k ∈ range q, s k
  have ht : t≤q*d := by
    calc
      t ≤ ∑ _k ∈ range q, d := Finset.sum_le_sum (fun k hk => (hs k (mem_range.mp hk)).2.1)
      _ = q*d := by simp
  have hm := modular_trace_sum (q*d+1) f s q (fun k hk => (hs k hk).2.2)
  rw [hstart,hend] at hm
  have hm' : Nat.ModEq (q*d+1) (i+(r+t)) i := by
    have hmod : Nat.ModEq (q*d+1) (i+r) ((i+r)%(q*d+1)) := by
      change (i+r)%(q*d+1)=((i+r)%(q*d+1))%(q*d+1)
      rw [Nat.mod_mod]
    simpa only [Nat.add_assoc] using (hmod.add_right t).trans hm
  have hdvd : q*d+1 ∣ r+t := by simpa using hm'.symm.dvd'
  have hlow : q*d+1≤r+t := Nat.le_of_dvd (by omega) hdvd
  have hdq : d≤q*d := by nlinarith
  have hupper : r+t<2*(q*d+1) := by omega
  have hz : (r+t-(q*d+1))%(q*d+1)=0 := by
    rw [← Nat.mod_eq_sub_mod hlow]
    exact Nat.mod_eq_zero_of_dvd hdvd
  rw [Nat.mod_eq_of_lt (by omega)] at hz
  change t+(r-1)=q*d
  omega

theorem return_maximum_count {q d i r l : ℕ} (hq : 1≤q) (hi : i<q*d+1)
    (hr : 1≤r) (hrd : r≤d) (hl : l≤q) (f : ℕ → ℕ)
    (hstart : f 0=(i+r)%(q*d+1)) (hend : f l=i)
    (hpath : ∀ k, k<l → f (k+1) ∈ range (q*d+1) ∧ graph q d (f k) (f (k+1))=true) :
    l=q ∧ ∃ s : ℕ → ℕ,
      (∀ k, k<q → 1≤s k ∧ s k≤d ∧ Nat.ModEq (q*d+1) (f k+s k) (f (k+1))) ∧
      (∑ k ∈ range q, s k)+(r-1)=q*d ∧
      q ≤ ((range q).filter (fun k => s k=d)).card+(r-1) := by
  obtain ⟨he,s,hs,ht⟩ := return_steps hq hi hr hrd hl f hstart hend hpath
  refine ⟨he,s,hs,ht,?_⟩
  have h := maximum_count_deficit (range q) s d (fun k hk => (hs k (mem_range.mp hk)).2.1)
  simp only [card_range] at h
  omega

theorem unit_return_maximum_steps {q d i l : ℕ} (hq : 1≤q) (hd : 1≤d)
    (hi : i<q*d+1) (hl : l≤q) (f : ℕ → ℕ)
    (hstart : f 0=(i+1)%(q*d+1)) (hend : f l=i)
    (hpath : ∀ k, k<l → f (k+1) ∈ range (q*d+1) ∧ graph q d (f k) (f (k+1))=true) :
    l=q ∧ ∀ k, k<q → Nat.ModEq (q*d+1) (f k+d) (f (k+1)) := by
  obtain ⟨he,s,hs,ht⟩ := return_steps hq hi (by omega) hd hl f hstart hend hpath
  have hsum : ∑ k ∈ range q, s k=(range q).card*d := by simpa using ht
  have hmax := bounded_sum_rigidity (range q) s d (fun k hk => (hs k (mem_range.mp hk)).2.1) hsum
  exact ⟨he,fun k hk => by simpa only [hmax k (mem_range.mpr hk)] using (hs k hk).2.2⟩

theorem offset_two_maximum_count {q d i l : ℕ} (hq : 1≤q) (hd : 2≤d)
    (hi : i<q*d+1) (hl : l≤q) (f : ℕ → ℕ)
    (hstart : f 0=(i+2)%(q*d+1)) (hend : f l=i)
    (hpath : ∀ k, k<l → f (k+1) ∈ range (q*d+1) ∧ graph q d (f k) (f (k+1))=true) :
    l=q ∧ ∃ s : ℕ → ℕ,
      (∀ k, k<q → 1≤s k ∧ s k≤d ∧ Nat.ModEq (q*d+1) (f k+s k) (f (k+1))) ∧
      ((range q).filter (fun k => s k=d)).card+1=q := by
  obtain ⟨he,s,hs,ht⟩ := return_steps hq hi (by omega) hd hl f hstart hend hpath
  refine ⟨he,s,hs,?_⟩
  simpa only [card_range] using one_deficit_maximum_count (range q) s d
    (fun k hk => (hs k (mem_range.mp hk)).2.1) (by simpa using ht)

theorem unit_return_trace {q d i l : ℕ} (hq : 1≤q) (hd : 1≤d)
    (hi : i<q*d+1) (hl : l≤q) (f : ℕ → ℕ)
    (hstart : f 0=(i+1)%(q*d+1)) (hend : f l=i)
    (hpath : ∀ k, k<l → f (k+1) ∈ range (q*d+1) ∧ graph q d (f k) (f (k+1))=true) :
    l=q ∧ ∀ k, k≤q → f k=(i+1+k*d)%(q*d+1) := by
  obtain ⟨he,hmax⟩ := unit_return_maximum_steps hq hd hi hl f hstart hend hpath
  subst l
  refine ⟨rfl,?_⟩
  intro k hk
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
    have hkq : k<q := by omega
    have hm := hmax k hkq
    have hbound := Finset.mem_range.mp (hpath k hkq).1
    change (f k+d)%(q*d+1)=f (k+1)%(q*d+1) at hm
    rw [Nat.mod_eq_of_lt hbound] at hm
    calc
      f (k+1) = (f k+d)%(q*d+1) := hm.symm
      _ = (((i+1+k*d)%(q*d+1))+d)%(q*d+1) := by rw [ih (by omega)]
      _ = (i+1+(k+1)*d)%(q*d+1) := by rw [Nat.mod_add_mod]; congr 1; ring

theorem canonical_unit_return {q d i : ℕ} (hd : 1≤d) (hi : i<q*d+1) :
    Walk (graph q d) (range (q*d+1)) ((i+1)%(q*d+1)) i q := by
  let f := fun k => (i+1+k*d)%(q*d+1)
  have hf : ∀ k, k<q → f (k+1) ∈ range (q*d+1) ∧ graph q d (f k) (f (k+1))=true := by
    intro k _
    have he : (f k+d)%(q*d+1)=f (k+1) := by
      dsimp [f]
      rw [Nat.mod_add_mod]
      congr 1
      ring
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)),?_⟩
    rw [← he]
    exact offset_edge (Nat.mod_lt _ (by omega)) hd le_rfl
  have hw := walk_of_edges hf
  have h0 : f 0=(i+1)%(q*d+1) := by simp [f]
  have hq : f q=i := by
    dsimp [f]
    rw [show i+1+q*d=i+(q*d+1) by ring,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
  simpa only [h0,hq] using hw

/-- Origins of the unit-offset demands using max-edge tail t at position k. -/
def origins (q d t : ℕ) : Finset ℕ :=
  (range q).image (fun k => (t+(q-k)*d)%(q*d+1))

theorem origin_tail {q d t k : ℕ} (ht : t<q*d+1) (hk : k<q) :
    (((t+(q-k)*d)%(q*d+1))+1+k*d)%(q*d+1)=t := by
  have hsub : (q-k)*d+k*d=q*d := by
    rw [← Nat.add_mul,Nat.sub_add_cancel (by omega)]
  rw [Nat.add_assoc,Nat.mod_add_mod]
  rw [show t+(q-k)*d+(1+k*d)=t+(q*d+1) by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt ht]

theorem origin_unique {q d t i k : ℕ} (hi : i<q*d+1) (hk : k<q)
    (he : (i+1+k*d)%(q*d+1)=t) : i=(t+(q-k)*d)%(q*d+1) := by
  have hsub : k*d+(q-k)*d=q*d := by
    rw [← Nat.add_mul,Nat.add_sub_of_le (by omega)]
  have hm : Nat.ModEq (q*d+1) (i+1+k*d) t := by
    change (i+1+k*d)%(q*d+1)=t%(q*d+1)
    rw [← he,Nat.mod_mod]
  have hh := hm.add_right ((q-k)*d)
  change (i+1+k*d+(q-k)*d)%(q*d+1)=(t+(q-k)*d)%(q*d+1) at hh
  rw [show i+1+k*d+(q-k)*d=i+(q*d+1) by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt hi] at hh
  exact hh

theorem origins_card {q d t : ℕ} (hd : 1≤d) : (origins q d t).card=q := by
  rw [origins,Finset.card_image_iff.mpr]
  · exact card_range q
  · intro k hk l hl he
    have hkq := mem_range.mp hk
    have hlq := mem_range.mp hl
    have hkb : (q-k)*d<q*d+1 := by nlinarith [Nat.sub_le q k]
    have hlb : (q-l)*d<q*d+1 := by nlinarith [Nat.sub_le q l]
    have hm : Nat.ModEq (q*d+1) (t+(q-k)*d) (t+(q-l)*d) := he
    have hh := hm.add_left_cancel' t
    simp only [Nat.ModEq,Nat.mod_eq_of_lt hkb,Nat.mod_eq_of_lt hlb] at hh
    have hkl : q-k=q-l := Nat.eq_of_mul_eq_mul_right (by omega : 0<d) hh
    omega

/-- Exactly q distinct unit-offset demands traverse each maximum-offset edge. -/
theorem unit_edge_load {q d t : ℕ} (hd : 1≤d) (ht : t<q*d+1) :
    ((range (q*d+1)).filter (fun i => ∃ k<q, (i+1+k*d)%(q*d+1)=t)).card=q := by
  classical
  have he : (range (q*d+1)).filter (fun i => ∃ k<q, (i+1+k*d)%(q*d+1)=t)=origins q d t := by
    ext i
    constructor
    · intro hi
      obtain ⟨hi,k,hk,he⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨k,mem_range.mpr hk,(origin_unique (mem_range.mp hi) hk he).symm⟩
    · intro hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)),k,mem_range.mp hk,
        origin_tail ht (mem_range.mp hk)⟩
  rw [he,origins_card hd]

/-- The aggregate count forces congestion at least 2q-1 somewhere. -/
theorem two_class_congestion {ι : Type*} (E : Finset ι) (hE : E.Nonempty)
    (q : ℚ) (L₁ L₂ : ι → ℚ)
    (h₁ : (q : ℚ)*E.card ≤ ∑ e ∈ E, L₁ e)
    (h₂ : ((q : ℚ)-1)*E.card ≤ ∑ e ∈ E, L₂ e) :
    ∃ e ∈ E, 2*q-1≤L₁ e+L₂ e := by
  by_contra hnot
  have hlt : ∀ e ∈ E, L₁ e+L₂ e<2*q-1 := fun e he =>
    lt_of_not_ge (fun h => hnot ⟨e,he,h⟩)
  have hcap : ∑ e ∈ E, (L₁ e+L₂ e) < (2*q-1)*E.card := by
    calc
      _ < ∑ _e ∈ E, (2*q-1) := by
        apply Finset.sum_lt_sum (fun e he => (hlt e he).le)
        obtain ⟨e,he⟩ := hE
        exact ⟨e,he,hlt e he⟩
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  rw [Finset.sum_add_distrib] at hcap
  nlinarith

/-- Fractional routing with the two forced total-load lower bounds exceeds
q capacity. No positivity of the abstract load functions is needed. -/
theorem two_class_overload {ι : Type*} (E : Finset ι) (hE : E.Nonempty)
    {q : ℕ} (hq : 2≤q) (L₁ L₂ : ι → ℚ)
    (h₁ : (q : ℚ)*E.card ≤ ∑ e ∈ E, L₁ e)
    (h₂ : ((q : ℚ)-1)*E.card ≤ ∑ e ∈ E, L₂ e) :
    ∃ e ∈ E, (q : ℚ)<L₁ e+L₂ e := by
  obtain ⟨e,he,hload⟩ := two_class_congestion E hE (q : ℚ) L₁ L₂ h₁ h₂
  have hq' : (2 : ℚ)≤q := by exact_mod_cast hq
  exact ⟨e,he,by linarith⟩

/-- Pointwise forced counts give the exact two-class aggregate, before any
distribution of that load among physical maximum-offset edges. -/
theorem two_class_step_total {ι : Type*} (U : Finset ι) (q d : ℕ)
    (s₁ s₂ : ι → ℕ → ℕ)
    (hb₁ : ∀ i ∈ U, ∀ k<q, s₁ i k≤d) (hb₂ : ∀ i ∈ U, ∀ k<q, s₂ i k≤d)
    (hs₁ : ∀ i ∈ U, ∑ k ∈ range q, s₁ i k=q*d)
    (hs₂ : ∀ i ∈ U, (∑ k ∈ range q, s₂ i k)+1=q*d) :
    (∑ i ∈ U, ((range q).filter (fun k => s₁ i k=d)).card)+
      (∑ i ∈ U, ((range q).filter (fun k => s₂ i k=d)).card)+U.card=2*q*U.card := by
  have h₁ : ∀ i ∈ U, ((range q).filter (fun k => s₁ i k=d)).card=q := by
    intro i hi
    have hmax := bounded_sum_rigidity (range q) (s₁ i) d
      (fun k hk => hb₁ i hi k (mem_range.mp hk)) (by simpa using hs₁ i hi)
    simpa using Finset.card_filter_eq_iff.mpr hmax
  have h₂ : ∀ i ∈ U, ((range q).filter (fun k => s₂ i k=d)).card+1=q := by
    intro i hi
    simpa using one_deficit_maximum_count (range q) (s₂ i) d
      (fun k hk => hb₂ i hi k (mem_range.mp hk)) (by simpa using hs₂ i hi)
  have hs : (∑ i ∈ U, (((range q).filter (fun k => s₂ i k=d)).card+1))=U.card*q := by
    calc
      _ = ∑ _i ∈ U, q := Finset.sum_congr rfl h₂
      _ = _ := by simp
  simp only [sum_add_distrib,sum_const,smul_eq_mul] at hs
  have ht : (∑ i ∈ U, ((range q).filter (fun k => s₁ i k=d)).card)=U.card*q := by
    calc
      _ = ∑ _i ∈ U, q := Finset.sum_congr rfl h₁
      _ = _ := by simp
  rw [ht]
  nlinarith

end LeanCH.BR.CirculantReturnCapacity
