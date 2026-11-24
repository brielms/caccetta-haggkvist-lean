import LeanCH.BR.BROutUniformContraction
import LeanCH.BR.BRWeightedPositiveParentTransfer

/-! Exact one-sided quotient accounting, SmallRow composition, and native
primeness. Saturation and full-module incoming uniformity are not assumed. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def contractWeight (M : Finset ℕ) (r : ℕ) (a : ℕ → ℚ) : ℕ → ℚ :=
  fun x => if x=r then mass M a else a x

theorem contractWeight_mass {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (a : ℕ → ℚ) :
    mass (representativeSet V M r) (contractWeight M r a)=mass V a := by
  have hrE : r∉V\M := fun h => (mem_sdiff.mp h).2 hr
  unfold mass representativeSet
  rw [sum_insert hrE]
  simp only [contractWeight,ite_true]
  have hs : (∑ x∈V\M, if x=r then mass M a else a x)=∑ x∈V\M,a x := by
    apply sum_congr rfl
    intro x hx
    have hn : x≠r := fun he => (mem_sdiff.mp hx).2 (he ▸ hr)
    simp [hn]
  rw [hs]
  exact (add_comm _ _).trans (sum_sdiff hMV)

theorem contractWeight_nonneg {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) {a : ℕ → ℚ} (ha : ∀ x∈V, 0≤a x) :
    ∀ x∈representativeSet V M r, 0≤contractWeight M r a x := by
  intro x hx
  by_cases he : x=r
  · simp only [contractWeight,he,ite_true]
    exact mass_nonneg (fun x hx => ha x (hMV hx))
  · simp only [contractWeight,he,ite_false]
    exact ha x (representative_subset hMV hr hx)

theorem contractWeight_positive {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) {a : ℕ → ℚ} (ha : ∀ x∈V, 0<a x) :
    ∀ x∈representativeSet V M r, 0<contractWeight M r a x := by
  intro x hx
  by_cases he : x=r
  · simp only [contractWeight,he,ite_true]
    exact sum_pos' (fun x hx => (ha x (hMV hx)).le) ⟨r,hr,ha r (hMV hr)⟩
  · simp only [contractWeight,he,ite_false]
    exact ha x (representative_subset hMV hr hx)

theorem outContract_root_row {q : ℕ} (D : CH.Digraph) {V M : Finset ℕ} {r : ℕ}
    (hr : r∈M) (a : ℕ → ℚ) :
    row q (outContract D M r) (representativeSet V M r) (contractWeight M r a) r=
      mass M a+q*outW D (V\M) a r := by
  have hrE : r∉V\M := fun h => (mem_sdiff.mp h).2 hr
  simp only [row,contractWeight,ite_true,outW,representativeSet,sum_insert hrE]
  simp only [outContract,ite_true,Bool.false_eq_true,ite_false,zero_add]
  congr 2
  apply sum_congr rfl
  intro x hx
  have hn : x≠r := fun he => (mem_sdiff.mp hx).2 (he ▸ hr)
  simp [hn]

/-- Exact exterior gain, including all original partial-head mass. -/
theorem outContract_exterior_row {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r x : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hx : x∈V\M) (a : ℕ → ℚ) :
    row q (outContract D M r) (representativeSet V M r) (contractWeight M r a) x=
      row q D V a x+q*((if ∃ m∈M,D x m=true then mass M a else 0)-outW D M a x) := by
  classical
  have hrE : r∉V\M := fun h => (mem_sdiff.mp h).2 hr
  have hxr : x≠r := fun he => (mem_sdiff.mp hx).2 (he ▸ hr)
  have ho : outW (outContract D M r) (representativeSet V M r) (contractWeight M r a) x=
      (if ∃ m∈M,D x m=true then mass M a else 0)+outW D (V\M) a x := by
    simp only [outW,representativeSet,sum_insert hrE]
    simp only [outContract,hxr,ite_false,ite_true,decide_eq_true_eq,contractWeight]
    congr 1
    apply sum_congr rfl
    intro y hy
    have hyr : y≠r := fun he => (mem_sdiff.mp hy).2 (he ▸ hr)
    simp [hyr]
  rw [row,ho,row,outW_split hMV a x]
  simp only [contractWeight,hxr,ite_false]
  ring

theorem outContract_exterior_row_le {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r x : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hx : x∈V\M) {a : ℕ → ℚ}
    (ha : ∀ m∈M, 0≤a m) :
    row q D V a x ≤ row q (outContract D M r) (representativeSet V M r) (contractWeight M r a) x := by
  rw [outContract_exterior_row hMV hr hx]
  have hlo : outW D M a x ≤ if ∃ m∈M,D x m=true then mass M a else 0 := by
    split_ifs with hh
    · apply sum_le_sum
      intro m hm
      split_ifs <;> linarith [ha m hm]
    · have hz : outW D M a x=0 := by
        apply sum_eq_zero
        intro m hm
        simp [show ¬ D x m=true from fun he => hh ⟨m,hm,he⟩]
      exact hz.le
  have hh := mul_nonneg (Nat.cast_nonneg q : (0 : ℚ)≤q) (sub_nonneg.mpr hlo)
  linarith

theorem outUniform_core_row {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r x : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M) (hx : x∈M) (a : ℕ → ℚ) :
    row q D V a x=row q D M a x+q*outW D (V\M) a r := by
  have ho : outW D (V\M) a x=outW D (V\M) a r := by
    apply sum_congr rfl
    intro y hy
    rw [hout x hx r hr y (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2]
  simp only [row,outW_split hMV a x,ho]
  ring

/-- SmallRow composes through the actual one-sided quotient. Natural q is
arbitrary; no girth or saturation is needed for this analytic implication. -/
theorem smallRow_of_outContract {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M)
    (hinside : SmallRow q D M)
    (hquot : SmallRow q (outContract D M r) (representativeSet V M r)) : SmallRow q D V := by
  intro a ha _
  have hQ : (representativeSet V M r).Nonempty := ⟨r,mem_insert_self _ _⟩
  obtain ⟨x,hx,hsmall⟩ := hquot (contractWeight M r a) (contractWeight_nonneg hMV hr ha) hQ
  rw [contractWeight_mass hMV hr] at hsmall
  by_cases he : x=r
  · subst x
    obtain ⟨m,hm,hs⟩ := hinside a (fun m hm => ha m (hMV hm)) ⟨r,hr⟩
    refine ⟨m,hMV hm,?_⟩
    rw [outUniform_core_row hMV hr hout hm]
    rw [outContract_root_row D hr a] at hsmall
    linarith
  · have hxE := mem_sdiff.mpr (representative_outside hx he)
    exact ⟨x,representative_subset hMV hr hx,
      (outContract_exterior_row_le hMV hr hxE (fun m hm => ha m (hMV hm))).trans hsmall⟩

/-- Feasibility transfers at the same level and total mass. -/
theorem outContract_feasible {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M) (hinside : SmallRow q D M)
    (a : ℕ → ℚ) (ha : ∀ m∈M, 0≤a m) (c : ℚ) (hrows : ∀ x∈V,c≤row q D V a x) :
    ∀ x∈representativeSet V M r,
      c≤row q (outContract D M r) (representativeSet V M r) (contractWeight M r a) x := by
  intro x hx
  by_cases he : x=r
  · subst x
    obtain ⟨m,hm,hs⟩ := hinside a ha ⟨r,hr⟩
    have hh := hrows m (hMV hm)
    rw [outUniform_core_row hMV hr hout hm] at hh
    rw [outContract_root_row D hr a]
    linarith
  · exact (hrows x (representative_subset hMV hr hx)).trans
      (outContract_exterior_row_le hMV hr (mem_sdiff.mpr (representative_outside hx he)) ha)

theorem smaller_outContract_smallRow {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r : ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hMV : M ⊆ V) (hr : r∈M) (hM : 2≤M.card) (hout : OutUniform D V M) :
    SmallRow q (outContract D M r) (representativeSet V M r) := by
  exact hsmall _ _ (card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨representative_subset hMV hr,representative_ne hMV hr hM⟩))
    (outContract_qfree hf hMV hr hout)

theorem smallRow_of_smaller_outUniform {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : 2≤M.card) (hne : M≠V) (hout : OutUniform D V M) :
    SmallRow q D V := by
  obtain ⟨r,hr⟩ := card_pos.mp (by omega : 0<M.card)
  exact smallRow_of_outContract hMV hr hout (hsmall.induced hf M hMV hne)
    (smaller_outContract_smallRow hsmall hf hMV hr hM hout)

theorem not_smallRow_out_prime {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hbad : ¬ SmallRow q D V) :
    ∀ M⊆V, 2≤M.card → M≠V → ¬ OutUniform D V M := by
  intro M hMV hM hne hout
  exact hbad (smallRow_of_smaller_outUniform hsmall hf hMV hM hne hout)

/-- Positivity and actual quotient rigidity forbid partial incoming
contacts. This analytic master does not assume girth, IH, or saturation. -/
theorem positive_feasible_outContract_inUniform {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M)
    (hinside : SmallRow q D M)
    (hquot : SmallRow q (outContract D M r) (representativeSet V M r))
    (a : ℕ → ℚ) (ha : ∀ x∈V,0<a x)
    (hrows : ∀ x∈V,mass V a≤row q D V a x) : InUniform D V M := by
  have hfeas := outContract_feasible hMV hr hout hinside a
    (fun x hx => (ha x (hMV hx)).le) (mass V a) hrows
  have htight := positive_feasible_rows_tight_of_smallRow hq hquot (contractWeight M r a)
    (contractWeight_positive hMV hr ha) (by
      intro x hx
      rw [contractWeight_mass hMV hr]
      exact hfeas x hx)
  have hcover (z : ℕ) (hz : z∈V) (hzM : z∉M) (hex : ∃m∈M,D z m=true) :
      ∀ m∈M,D z m=true := by
    have hzE : z∈V\M := mem_sdiff.mpr ⟨hz,hzM⟩
    have hzQ : z∈representativeSet V M r := mem_insert_of_mem hzE
    have he := htight z hzQ
    rw [contractWeight_mass hMV hr,outContract_exterior_row hMV hr hzE a] at he
    simp only [hex,ite_true] at he
    have hsub : outN D M z ⊆ M := fun x hx => (mem_outN.mp hx).1
    have hlo : outW D M a z≤mass M a := by
      rw [outW_eq_mass]
      exact mass_mono hsub (fun x hx => (ha x (hMV hx)).le)
    have hqpos : (0 : ℚ)<q := by exact_mod_cast (show 0<q by omega)
    have heq : mass (outN D M z) a=mass M a := by
      rw [← outW_eq_mass]
      nlinarith [hrows z hz]
    have hs := positive_mass_eq_subset hsub (fun x hx => ha x (hMV hx)) heq
    intro m hm
    exact (mem_outN.mp (by rw [hs]; exact hm : m∈outN D M z)).2
  intro x hx y hy z hz hzM
  by_cases hzx : D z x=true
  · rw [hzx,hcover z hz hzM ⟨x,hx,hzx⟩ y hy]
  · have hzy : ¬ D z y=true := fun hyz => hzx (hcover z hz hzM ⟨y,hy,hyz⟩ x hx)
    rw [Bool.eq_false_iff.mpr hzx,Bool.eq_false_iff.mpr hzy]

theorem positive_feasible_outUniform_inUniform {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V M : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : 2≤M.card) (hne : M≠V) (hout : OutUniform D V M)
    (a : ℕ → ℚ) (ha : ∀ x∈V,0<a x)
    (hrows : ∀ x∈V,mass V a≤row q D V a x) : InUniform D V M := by
  obtain ⟨r,hr⟩ := card_pos.mp (by omega : 0<M.card)
  exact positive_feasible_outContract_inUniform hq hMV hr hout
    (hsmall.induced hf M hMV hne) (smaller_outContract_smallRow hsmall hf hMV hr hM hout) a ha hrows

end LeanCH.BR.WeightedSD
