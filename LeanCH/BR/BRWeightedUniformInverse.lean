import LeanCH.BR.BRFiniteUniformInverse
import LeanCH.BR.BRWeightedInverseTransport

/-! The native arc-critical host has low-degree vertices in both directions
and neither strict equalizer is uniform. No ambient saturation is used. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix BRq2 BRq3 BR45 BRsub FiniteCutInverse
open scoped Matrix

theorem subtype_out_card (D : CH.Digraph) (V : Finset ℕ) (i : V) :
    (univ.filter (fun j : V => D i j = true)).card = (outN D V i).card := by
  simp only [outN,card_filter]
  exact sum_coe_sort V (fun j => if D i j = true then (1 : ℕ) else 0)

theorem arc_core_degree_violation {q : ℕ} (hq : 3 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    (hV : V.Nonempty) (hf : QFree D V q) (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H) :
    ∃ v ∈ V, q*(outN D V v).card < V.card := by
  let : Nonempty V := ⟨⟨hV.choose,hV.choose_spec⟩⟩
  by_contra hn
  push Not at hn
  obtain ⟨hdeg,hcard⟩ := UniformInverse.degree_floor_one hq
    (fun i j : V => D i j) hH (by
      intro i j
      by_cases h : D i j = true <;> simp [realMatrix_entry,h])
    (inverse_arc_charge hcritical hH) (fun i => by
      simpa only [Fintype.card_coe,subtype_out_card] using hn i i.property)
  have hcount : V.card ≤ q := by simpa only [Fintype.card_coe] using hcard
  obtain ⟨v,hv,hs⟩ := exists_sink hf hV hcount
  have ho : outN D V v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact hs j (mem_outN.mp hj).1 (mem_outN.mp hj).2
  have he := hdeg ⟨v,hv⟩
  rw [subtype_out_card,ho,card_empty] at he
  omega

theorem arc_core_two_degree_violations {q : ℕ} (hq : 3 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    (hV : V.Nonempty) (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H) :
    (∃ v ∈ V, q*(outN D V v).card < V.card) ∧
    (∃ v ∈ V, q*(inN D V v).card < V.card) := by
  refine ⟨arc_core_degree_violation hq hV hf hcritical hH, ?_⟩
  exact arc_core_degree_violation hq hV hf.reverse
    (hcritical.reverse hsmall hf) (commonInverse_reverse hH)

theorem arc_core_primal_nonuniform {q : ℕ} (hq : 3 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a : ℕ → ℚ) (hm : mass V a = 1) (c : ℚ) (hc : 1 < c)
    (hr : ∀ i ∈ V, row q D V a i = c) :
    ¬ ∀ i ∈ V, a i = 1/(V.card : ℚ) := by
  intro hunif
  have hV : V.Nonempty := by
    by_contra hn
    have he : V = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [he,mass] at hm
  let : Nonempty V := ⟨⟨hV.choose,hV.choose_spec⟩⟩
  have hu (i : V) : (a i : ℝ) = 1/(Fintype.card V : ℝ) := by
    simp only [Fintype.card_coe]
    rw [hunif i i.property]
    push_cast
    rfl
  have hrow : ∀ i : V, (realMatrix q D V *ᵥ (fun _ => 1/(Fintype.card V : ℝ))) i = c := by
    intro i
    have he := realMatrix_rational_rows a c hr i
    simpa only [hu] using he
  obtain ⟨hdeg,hcard⟩ := UniformInverse.uniform_degree_one hq
    (fun i j : V => D i j) hH (by
      intro i j
      by_cases h : D i j = true <;> simp [realMatrix_entry,h])
    (inverse_arc_charge hcritical hH) (c : ℝ) (by exact_mod_cast hc) hrow
  have hcount : V.card ≤ q := by simpa only [Fintype.card_coe] using hcard
  obtain ⟨v,hv,hs⟩ := exists_sink hf hV hcount
  have ho : outN D V v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact hs j (mem_outN.mp hj).1 (mem_outN.mp hj).2
  have he := hdeg ⟨v,hv⟩
  rw [subtype_out_card,ho,card_empty] at he
  omega

theorem arc_core_nonuniform_equalizers {q : ℕ} (hq : 3 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a p : ℕ → ℚ) (hm : mass V a = 1) (hpm : mass V p = 1) (c : ℚ) (hc : 1 < c)
    (hr : ∀ i ∈ V, row q D V a i = c) (hp : ∀ i ∈ V, col q D V p i = c) :
    (¬ ∀ i ∈ V, a i = 1/(V.card : ℚ)) ∧
    (¬ ∀ i ∈ V, p i = 1/(V.card : ℚ)) := by
  refine ⟨arc_core_primal_nonuniform hq hf hcritical hH a hm c hc hr, ?_⟩
  exact arc_core_primal_nonuniform hq hf.reverse (hcritical.reverse hsmall hf)
    (commonInverse_reverse hH) p hpm c hc hp

end LeanCH.BR.WeightedSD
