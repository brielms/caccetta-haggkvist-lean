import LeanCH.BR.BRCycleReturn
import LeanCH.BR.BRNearBoundaryRows

/-! Variable-cutoff local geometry for rich missed incidences.
No positivity, normalization, saturation, or ambient order bound is used here. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- At a tight reentry of length t, every positive cycle return of length at
most t+1 starts at a parent of z. Both lengths remain arbitrary. -/
theorem tight_reentry_short_predecessors {q t k : ℕ} (ht : t + 1 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hmin : ∀ v ∈ M, 1 ≤ (outN D M v).card)
    {z r a : ℕ} (hz : z ∈ V) (hr : r ∈ M)
    (hreach : r ∈ ball D V z t) (hI : t + 1 ≤ (inN D M z).card)
    (ha : a ∈ M) (hk0 : 1 ≤ k) (hk : k ≤ t + 1) (war : Walk D M a r k) :
    a ∈ inN D M z := by
  let B := ball D M r (q - t - 1)
  have hB : q - t ≤ B.card := by
    have h := ball_one_growth (hf.mono_set hMV) hmin hr (q - t - 1) (by omega)
    change q - t ≤ (ball D M r (q - t - 1)).card
    omega
  have hdis : Disjoint (inN D M z) B := by
    apply disjoint_left.mpr
    intro x hxI hxB
    obtain ⟨_, i, hi, wzi⟩ := mem_ball.mp hreach
    obtain ⟨_, j, hj, wrx⟩ := mem_ball.mp hxB
    exact hf z (i + j + 1) (by omega) (by omega)
      ((wzi.append (wrx.mono hMV)).snoc hz (mem_inN.mp hxI).2)
  have hsub : inN D M z ∪ B ⊆ M :=
    union_subset (fun _ h => (mem_inN.mp h).1) ball_subset
  have hcover : inN D M z ∪ B = M := by
    apply eq_of_subset_of_card_le hsub
    rw [card_union_of_disjoint hdis, hM]
    omega
  by_contra hn
  have haB : a ∈ B := (mem_union.mp (hcover.symm ▸ ha)).resolve_left hn
  obtain ⟨_, j, hj, wra⟩ := mem_ball.mp haB
  exact hf r (j + k) (by omega) (by omega) ((wra.append war).mono hMV)

/-- A two-edge detour from a cycle vertex can reenter only at its first
two cycle successors. The cutoff remains arbitrary q>=2. -/
theorem cycle_two_step_detour_heads {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    {u v w g : ℕ} (hu : u ∈ M) (hv : v ∈ M) (hw : w ∈ M) (hg : g ∈ V)
    (huv : D u v = true) (hvw : D v w = true) (hug : D u g = true) :
    outN D M g ⊆ {v, w} := by
  have hin := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
    (hf.mono_set hMV) (fun x hx => (hout x hx).ge) (by simpa using hM)).2
  let B := ball (fun x y => D y x) M u (q - 2)
  have hB : q - 1 ≤ B.card := by
    have h := ball_one_growth (hf.mono_set hMV).reverse (fun x hx => (hin x hx).ge)
      hu (q - 2) (by omega)
    change q - 1 ≤ (ball (fun x y => D y x) M u (q - 2)).card
    omega
  have hvB : v ∉ B := by
    intro h
    obtain ⟨_, k, hk, wuv⟩ := mem_ball.mp h
    exact hf u (k + 1) (by omega) (by omega)
      (.step (hMV hv) huv ((wuv.reverse_of_mem hu).mono hMV))
  have hwB : w ∉ B := by
    intro h
    obtain ⟨_, k, hk, wuw⟩ := mem_ball.mp h
    exact hf u (k + 2) (by omega) (by omega)
      (.step (hMV hv) huv (.step (hMV hw) hvw ((wuw.reverse_of_mem hu).mono hMV)))
  have hvwne : v ≠ w := by
    intro he
    subst w
    exact loopfree hf (by omega) (hMV hv) hvw
  have hdis : Disjoint ({v, w} : Finset ℕ) B := by
    apply disjoint_left.mpr
    intro a ha hB
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hvB hB
    · exact hwB hB
  have hsub : ({v, w} : Finset ℕ) ∪ B ⊆ M :=
    union_subset (by intro a ha; simp only [mem_insert, mem_singleton] at ha; rcases ha with rfl | rfl <;> assumption) ball_subset
  have hcover : ({v, w} : Finset ℕ) ∪ B = M := by
    apply eq_of_subset_of_card_le hsub
    rw [card_union_of_disjoint hdis, hM]
    have hc : ({v, w} : Finset ℕ).card = 2 := by simp [hvwne]
    omega
  intro a ha
  by_contra hn
  have haB : a ∈ B := (mem_union.mp (hcover.symm ▸ outN_subset ha)).resolve_left hn
  obtain ⟨_, k, hk, wua⟩ := mem_ball.mp haB
  exact hf u (k + 2) (by omega) (by omega)
    (.step hg hug (.step (hMV (outN_subset ha)) (mem_outN.mp ha).2
      ((wua.reverse_of_mem hu).mono hMV)))

/-- A common head of u and z cannot return to M when the two cycle
successors of u both feed z. No ambient-size or weight premise is used. -/
theorem cycle_common_head_no_return {q : ℕ} (hq : 3 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    {u v w z g : ℕ} (hu : u ∈ M) (hv : v ∈ M) (hw : w ∈ M)
    (hz : z ∈ V) (hg : g ∈ V) (huv : D u v = true) (hvw : D v w = true)
    (hvz : D v z = true) (hwz : D w z = true) (hug : D u g = true) (hzg : D z g = true) :
    outN D M g = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h := cycle_two_step_detour_heads (by omega : 2 ≤ q) hf hMV hM hout hu hv hw hg huv hvw hug ha
  simp only [mem_insert, mem_singleton] at h
  rcases h with hv' | hw'
  · subst a
    exact hf v 3 (by omega) (by omega)
      (.step hz hvz (.step hg hzg (.step (hMV hv) (mem_outN.mp ha).2 (.refl v))))
  · subst a
    exact hf w 3 (by omega) (by omega)
      (.step hz hwz (.step hg hzg (.step (hMV hw) (mem_outN.mp ha).2 (.refl w))))

end LeanCH.BR.WeightedSD
