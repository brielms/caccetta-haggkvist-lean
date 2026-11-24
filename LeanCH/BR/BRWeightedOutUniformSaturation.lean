import LeanCH.BR.BRWeightedOutUniformContraction
import LeanCH.BR.BRWeightedInverseComparison
import LeanCH.BR.BRWeightedNonnegativePressure

/-! A positive feasible host with a proper one-sided module is saturated
under actual global smaller-SmallRow. Reverse arguments use its own dual. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem positive_feasible_no_added_arc {q : ℕ} (hq : 2≤q)
    {D E : CH.Digraph} {V : Finset ℕ} (hDE : ∀ x∈V,∀ y∈V,D x y=true → E x y=true)
    (hs : SmallRow q E V) (a : ℕ → ℚ) (ha : ∀ x∈V,0<a x)
    (hr : ∀ x∈V,mass V a≤row q D V a x)
    {u v : ℕ} (hu : u∈V) (hv : v∈V) (hD : ¬ D u v=true) (hE : E u v=true) : False := by
  have hfeas : ∀ x∈V,mass V a≤row q E V a x := by
    intro x hx
    exact (hr x hx).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (outW_mono_graph hDE (fun x hx => (ha x hx).le) hx)
        (Nat.cast_nonneg q)))
  have ht := positive_feasible_rows_tight_of_smallRow hq hs a ha hfeas u hu
  have ho : outW D V a u<outW E V a u := by
    apply sum_lt_sum
    · intro x hx
      by_cases hd : D u x=true
      · simp [hd,hDE u hu x hx hd]
      · by_cases he : E u x=true <;> simp [hd,he,(ha x hx).le]
    · exact ⟨v,hv,by simp [hD,hE,ha v hv]⟩
  have hqpos : (0 : ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have hh := mul_lt_mul_of_pos_left ho hqpos
  have hold := hr u hu
  unfold row at ht hold
  linarith

theorem outUniform_insert_not_outgoing {D : CH.Digraph} {V M : Finset ℕ}
    (hout : OutUniform D V M) {u v : ℕ} (hkeep : u∉M ∨ v∈M) :
    OutUniform (insertArc D u v) V M := by
  intro x hx y hy z hz hzM
  rcases hkeep with hu | hv
  · have hxu : x≠u := fun he => hu (he ▸ hx)
    have hyu : y≠u := fun he => hu (he ▸ hy)
    simpa only [insertArc,hxu,hyu,false_and,ite_false] using hout x hx y hy z hz hzM
  · have hzv : z≠v := fun he => hzM (he ▸ hv)
    simpa only [insertArc,hzv,and_false,ite_false] using hout x hx y hy z hz hzM

theorem insertArc_reverse (D : CH.Digraph) (u v : ℕ) :
    (fun x y => insertArc D u v y x)=insertArc (fun x y => D y x) v u := by
  funext x y
  simp only [insertArc,and_comm]

/-- Both original positive feasible laws are retained separately. A newly
added arc is tested in an orientation whose actual module survives. -/
theorem two_law_outUniform_saturated {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V M : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : 2≤M.card) (hne : M≠V) (hout : OutUniform D V M)
    (a p : ℕ → ℚ) (ha : ∀ x∈V,0<a x) (hp : ∀ x∈V,0<p x)
    (hr : ∀ x∈V,mass V a≤row q D V a x)
    (hc : ∀ x∈V,mass V p≤col q D V p x) : Sat q D V := by
  have hin := positive_feasible_outUniform_inUniform hq hsmall hf hMV hM hne hout a ha hr
  intro v hv u hu hmissing
  by_contra hreturn
  have hfE := qfree_insertArc hf ⟨u,hu⟩ ⟨v,hv⟩ hreturn
  by_cases hkeep : u∉M ∨ v∈M
  · have hs := smallRow_of_smaller_outUniform hsmall hfE hMV hM hne
      (outUniform_insert_not_outgoing hout hkeep)
    exact positive_feasible_no_added_arc hq (fun x _ y _ hxy => insertArc_mono D u v x y hxy)
      hs a ha hr hu hv hmissing (by simp [insertArc])
  · have hvM : v∉M := by tauto
    have hrevout : OutUniform (fun x y => D y x) V M := hin
    have hfR : QFree (insertArc (fun x y => D y x) v u) V q := by
      rw [← insertArc_reverse]
      exact hfE.reverse
    have hs := smallRow_of_smaller_outUniform hsmall hfR hMV hM hne
      (outUniform_insert_not_outgoing hrevout (Or.inl hvM))
    exact positive_feasible_no_added_arc hq
      (fun x _ y _ hxy => insertArc_mono (fun x y => D y x) v u x y hxy)
      hs p hp hc hv hu hmissing (by simp [insertArc])

/-- The reverse law is produced from this host's SmallRow and positive
feasibility; no source-wide SelfDual assumption is made. -/
theorem positive_feasible_outUniform_saturated {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V M : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : 2≤M.card) (hne : M≠V) (hout : OutUniform D V M)
    (a : ℕ → ℚ) (ha : ∀ x∈V,0<a x)
    (hr : ∀ x∈V,mass V a≤row q D V a x) : Sat q D V := by
  have hs := smallRow_of_smaller_outUniform hsmall hf hMV hM hne hout
  obtain ⟨r,hrM⟩ := card_pos.mp (by omega : 0<M.card)
  have hmpos : 0<mass V a := sum_pos' (fun x hx => (ha x hx).le) ⟨r,hMV hrM,ha r (hMV hrM)⟩
  let w := fun x => a x/mass V a
  have hw : ∀ x∈V,0<w x := fun x hx => div_pos (ha x hx) hmpos
  have hwm : mass V w=1 := by rw [mass_div]; exact div_self (ne_of_gt hmpos)
  have hwr : ∀ x∈V,1≤row q D V w x := by
    intro x hx
    rw [row_div]
    exact (le_div_iff₀ hmpos).mpr (by simpa using hr x hx)
  obtain ⟨_,p,hp,hpm,hpc⟩ := normalized_pair_of_no_strict hq w hw hwm hwr hs.not_strictPositiveRows
  exact two_law_outUniform_saturated hq hsmall hf hMV hM hne hout a p ha hp hr
    (fun x hx => by rw [hpm,hpc x hx])

/-- Nonsaturation forces out-module primeness in a positive feasible host
with the actual global smaller-order SmallRow hypothesis. -/
theorem positive_feasible_nonsaturated_out_prime {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hn : ¬ Sat q D V)
    (a : ℕ → ℚ) (ha : ∀ x∈V,0<a x)
    (hr : ∀ x∈V,mass V a≤row q D V a x) :
    ∀ M⊆V,2≤M.card → M≠V → ¬ OutUniform D V M := by
  intro M hMV hM hne hout
  exact hn (positive_feasible_outUniform_saturated hq hsmall hf hMV hM hne hout a ha hr)

/-- Every actual exact-threshold deletion is out-module prime under the
original global smaller-order IH. Its nonsaturation is proved separately. -/
theorem exact_threshold_deletion_out_prime {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) {H : Matrix V V ℝ}
    (hH : FiniteCutInverse.CommonInverse (realMatrix q D V) H)
    (u v : V) (huv : D u v=true) (ht : (q : ℝ)*H v u=1) :
    ∀ M⊆V,2≤M.card → M≠V → ¬ OutUniform (eraseArc D u v) V M := by
  obtain ⟨a,p,ha,ham,har,_⟩ := exact_arc_threshold_two_laws hq hH u v huv ht
  exact positive_feasible_nonsaturated_out_prime hq hsmall
    (qfree_sub (eraseArc_sub D u v) hf) (erase_actual_arc_not_sat (by omega) hf u v huv)
    a ha (fun x hx => by rw [ham,har x hx])

theorem exact_threshold_deletion_two_sided_prime {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) {H : Matrix V V ℝ}
    (hH : FiniteCutInverse.CommonInverse (realMatrix q D V) H)
    (u v : V) (huv : D u v=true) (ht : (q : ℝ)*H v u=1) :
    (∀ M⊆V,2≤M.card → M≠V → ¬ OutUniform (eraseArc D u v) V M) ∧
    (∀ M⊆V,2≤M.card → M≠V → ¬ InUniform (eraseArc D u v) V M) := by
  refine ⟨exact_threshold_deletion_out_prime hq hsmall hf hH u v huv ht,?_⟩
  have hh := exact_threshold_deletion_out_prime hq hsmall hf.reverse
    (commonInverse_reverse hH) v u huv ht
  simpa only [eraseArc_reverse,OutUniform,InUniform] using hh

/-- The supplied single-excess boundary descendant is genuinely prime in
both orientations. Nonsaturation remains explicit, so this is not an
application of the saturated-prime equality supplier. -/
theorem arc_core_pressure_or_prime_boundary {q : ℕ} (hq : 3≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hV : V.Nonempty)
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : FiniteCutInverse.CommonInverse (realMatrix q D V) H) :
    (∃ v∈V,1+q*(outN D V v).card<V.card) ∨
    ∃ h v : V,D h v=true ∧ QFree (eraseArc D h v) V q ∧
      SmallRow q (eraseArc D h v) V ∧ ¬ Sat q (eraseArc D h v) V ∧
      (∀ i∈V,row q (eraseArc D h v) V (fun _ => 1/(V.card : ℚ)) i=1) ∧
      mass V (fun _ => 1/(V.card : ℚ))=1 ∧
      (∀ i∈V,0<(1/(V.card : ℚ))) ∧
      (∀ M⊆V,2≤M.card → M≠V → ¬ OutUniform (eraseArc D h v) V M) ∧
      (∀ M⊆V,2≤M.card → M≠V → ¬ InUniform (eraseArc D h v) V M) ∧
      ∃ p : ℕ → ℚ,(∀ i∈V,0<p i) ∧ mass V p=1 ∧
        (∀ i∈V,col q (eraseArc D h v) V p i=1) ∧
        (∀ i : V,(p i : ℝ)=ThresholdUnit.inverseRowLaw H v i) ∧
        ¬ ∀ i∈V,p i=1/(V.card : ℚ) := by
  rcases arc_core_negative_pressure_or_unequal_boundary hq hV hf hcritical hH with hn | hb
  · exact Or.inl hn
  obtain ⟨h,v,hav,hfE,hsE,hnE,hrE,hmE,haE,p,hp,hpm,hpc,hpi,hpn⟩ := hb
  have hOut := positive_feasible_nonsaturated_out_prime (by omega : 2≤q)
    hsmall hfE hnE (fun _ => 1/(V.card : ℚ)) haE (fun i hi => by rw [hmE,hrE i hi])
  have hnR : ¬ Sat q (fun x y => eraseArc D h v y x) V := by
    simpa only [eraseArc_reverse] using erase_actual_arc_not_sat (by omega : 1≤q) hf.reverse v h hav
  have hIn := positive_feasible_nonsaturated_out_prime (by omega : 2≤q)
    hsmall hfE.reverse hnR p hp (fun i hi => by
      change mass V p≤col q (eraseArc D h v) V p i
      rw [hpm,hpc i hi])
  exact Or.inr ⟨h,v,hav,hfE,hsE,hnE,hrE,hmE,haE,hOut,hIn,p,hp,hpm,hpc,hpi,hpn⟩

end LeanCH.BR.WeightedSD
