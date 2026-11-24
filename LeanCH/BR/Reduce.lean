import LeanCH.BR.Weighted
import Mathlib.Data.Finset.Prod

/-!
# Minimal counterexamples are saturated and in-Sperner (Lean 4.35.0)

`reduce`: if every *saturated* and *in-Sperner* weighted boundary graph is regular, then every weighted boundary graph
is regular (weighted BR, equivalent to BR by blowing vertices up into independent twins).

* *Saturated*: adding any missing arc creates a cycle of length `≤ q`.
* *In-Sperner*: no two present, non-adjacent vertices have nested in-neighbourhoods among present vertices.

Proof: induction on the support, then on the number of missing arcs. A non-saturated graph gains an arc, and a
regular supergraph forces regularity (`mono`). A non-in-Sperner graph merges a vertex (`merge_regular`).
-/

namespace LeanCH.BR.Reduce

open Finset LeanCH.BR.Weighted

def addArc (G : CH.Digraph) (u v : Nat) : CH.Digraph := fun x y => if x = u ∧ y = v then true else G x y

def Saturated (G : CH.Digraph) (n q : Nat) : Prop :=
  ∀ u v, u < n → v < n → u ≠ v → G u v = false → CH.HasDirectedCycleAtMost (addArc G u v) n q

def InSperner (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) : Prop :=
  ∀ a b, a < n → b < n → 0 < ω a → 0 < ω b → a ≠ b → G a b = false → G b a = false →
    ¬ (∀ x, x < n → 0 < ω x → G x b = true → G x a = true)

def miss (G : CH.Digraph) (n : Nat) : Nat :=
  ((range n ×ˢ range n).filter (fun p => p.1 ≠ p.2 ∧ G p.1 p.2 = false)).card

theorem addArc_ge (G : CH.Digraph) (u v x y : Nat) (h : G x y = true) : addArc G u v x y = true := by
  simp [addArc, h]

theorem miss_lt {G : CH.Digraph} {n u v : Nat} (hu : u < n) (hv : v < n) (huv : u ≠ v) (hG : G u v = false) :
    miss (addArc G u v) n < miss G n := by
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, hp.2.1, ?_⟩
    cases h : G p.1 p.2
    · rfl
    · have := addArc_ge G u v p.1 p.2 h; rw [hp.2.2] at this; exact absurd this (by decide)
  · intro hsub
    have hmem : (u, v) ∈ (range n ×ˢ range n).filter (fun p => p.1 ≠ p.2 ∧ G p.1 p.2 = false) := by
      simp [hu, hv, huv, hG]
    have := (Finset.mem_filter.mp (hsub hmem)).2.2
    simp [addArc] at this

/-- A regular boundary supergraph on the same weights forces regularity. -/
theorem mono {G G' : CH.Digraph} {n q s : Nat} {ω : Nat → Nat} (hW : WB G n q s ω)
    (sub : ∀ x y, G x y = true → G' x y = true) (hR : Regular G' n s ω) : Regular G n s ω := by
  have hin : ∀ v, inW G n ω v ≤ inW G' n ω v := by
    intro v; apply Finset.sum_le_sum; intro u _
    by_cases h : G u v = true
    · simp [h, sub u v h]
    · simp [h]
  have hle : ∀ v ∈ range n, ω v * inW G n ω v ≤ ω v * s := by
    intro v hv
    rcases Nat.eq_zero_or_pos (ω v) with h | h
    · simp [h]
    · rw [← hR v (Finset.mem_range.mp hv) h]; exact Nat.mul_le_mul_left _ (hin v)
  have hge : ∑ v ∈ range n, ω v * s ≤ ∑ v ∈ range n, ω v * inW G n ω v := by
    rw [← double_count]
    apply Finset.sum_le_sum; intro v hv
    rcases Nat.eq_zero_or_pos (ω v) with h | h
    · simp [h]
    · exact Nat.mul_le_mul_left _ (hW.out v (Finset.mem_range.mp hv) h)
  have heq : ∑ v ∈ range n, ω v * inW G n ω v = ∑ v ∈ range n, ω v * s :=
    le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv hpos
  exact Nat.eq_of_mul_eq_mul_left hpos (each v (Finset.mem_range.mpr hv))

theorem addArc_WB {G : CH.Digraph} {n q s : Nat} {ω : Nat → Nat} {u v : Nat} (hW : WB G n q s ω)
    (huv : u ≠ v) (hno : ¬ CH.HasDirectedCycleAtMost (addArc G u v) n q) : WB (addArc G u v) n q s ω where
  total := hW.total
  loopless := by
    intro w hw
    have : ¬ (w = u ∧ w = v) := fun h => huv (h.1.symm.trans h.2)
    simp only [addArc, if_neg this]; exact hW.loopless w hw
  noShort := hno
  out := by
    intro x hx hpos
    refine le_trans (hW.out x hx hpos) ?_
    apply Finset.sum_le_sum; intro y _
    by_cases h : G x y = true
    · simp [h, addArc_ge G u v x y h]
    · simp [h]

/-- **Reduction.** Weighted boundary regularity follows from the saturated in-Sperner case. -/
theorem reduce {q s : Nat}
    (H : ∀ (G : CH.Digraph) (n : Nat) (ω : Nat → Nat), WB G n q s ω → Saturated G n q → InSperner G n ω →
      Regular G n s ω) :
    ∀ (G : CH.Digraph) (n : Nat) (ω : Nat → Nat), WB G n q s ω → Regular G n s ω := by
  intro G n ω hW
  induction hk : (supp n ω).card using Nat.strong_induction_on generalizing G ω with
  | _ k IHk =>
  induction hm : miss G n using Nat.strong_induction_on generalizing G with
  | _ m IHm =>
  by_cases hsat : Saturated G n q
  · by_cases hsp : InSperner G n ω
    · exact H G n ω hW hsat hsp
    · simp only [InSperner, not_forall] at hsp
      obtain ⟨a, b, ha, hb, pa, pb, hab, nab, nba, nest⟩ := hsp
      exact merge_regular hW ha hb hab pa pb nab nba
        (fun x hx hpx hGb => by by_contra h; exact nest ⟨x, hx, hpx, hGb, h⟩)
        (fun ω' hW' hlt => IHk _ (hk ▸ hlt) G ω' hW' rfl)
  · simp only [Saturated, not_forall] at hsat
    obtain ⟨u, v, hu, hv, huv, hG, hno⟩ := hsat
    have hW' := addArc_WB hW huv hno
    have hR' := IHm _ (hm ▸ miss_lt hu hv huv hG) (addArc G u v) hW' rfl
    exact mono hW (addArc_ge G u v) hR'

/-! ## Clean graphs: absent vertices carry no arcs, saturation among present vertices only -/

def Clean (G : CH.Digraph) (ω : Nat → Nat) : Prop := ∀ u v, G u v = true → 0 < ω u ∧ 0 < ω v

def SaturatedP (G : CH.Digraph) (n q : Nat) (ω : Nat → Nat) : Prop :=
  ∀ u v, u < n → v < n → 0 < ω u → 0 < ω v → u ≠ v → G u v = false →
    CH.HasDirectedCycleAtMost (addArc G u v) n q

def cleanG (G : CH.Digraph) (ω : Nat → Nat) : CH.Digraph :=
  fun u v => G u v && decide (0 < ω u) && decide (0 < ω v)

theorem cleanG_le (G : CH.Digraph) (ω : Nat → Nat) (u v : Nat) (h : cleanG G ω u v = true) : G u v = true := by
  simp only [cleanG, Bool.and_eq_true] at h; exact h.1.1

theorem cleanG_clean (G : CH.Digraph) (ω : Nat → Nat) : Clean (cleanG G ω) ω := by
  intro u v h; simp only [cleanG, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1.2, h.2⟩

/-- Cycles of a subgraph are cycles of the graph. -/
theorem edges_mono {G H : CH.Digraph} (sub : ∀ x y, H x y = true → G x y = true) :
    ∀ (p : Nat) (l : List Nat), CH.EdgesFrom H p l → CH.EdgesFrom G p l := by
  intro p l
  induction l generalizing p with
  | nil => intro _; trivial
  | cons x rest ih => intro h; exact ⟨sub _ _ h.1, ih x h.2⟩

theorem short_mono {G H : CH.Digraph} {n q : Nat} (sub : ∀ x y, H x y = true → G x y = true)
    (h : CH.HasDirectedCycleAtMost H n q) : CH.HasDirectedCycleAtMost G n q := by
  obtain ⟨l, hc, hlen⟩ := h
  refine ⟨l, ?_, hlen⟩
  cases l with
  | nil => exact hc
  | cons f rest =>
    exact ⟨hc.1, hc.2.1, hc.2.2.1, edges_mono sub f rest hc.2.2.2.1, sub _ _ hc.2.2.2.2⟩

theorem outW_clean (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) (x : Nat) (hx : 0 < ω x) :
    outW (cleanG G ω) n ω x = outW G n ω x := by
  apply Finset.sum_congr rfl; intro u _
  rcases Nat.eq_zero_or_pos (ω u) with h | h
  · simp [h]
  · simp [cleanG, hx, h]

theorem inW_clean (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) (y : Nat) (hy : 0 < ω y) :
    inW (cleanG G ω) n ω y = inW G n ω y := by
  apply Finset.sum_congr rfl; intro u _
  rcases Nat.eq_zero_or_pos (ω u) with h | h
  · simp [h]
  · simp [cleanG, hy, h]

theorem clean_WB {G : CH.Digraph} {n q s : Nat} {ω : Nat → Nat} (hW : WB G n q s ω) :
    WB (cleanG G ω) n q s ω where
  total := hW.total
  loopless := by intro v hv; simp [cleanG, hW.loopless v hv]
  out := fun x hx hpos => by rw [outW_clean G n ω x hpos]; exact hW.out x hx hpos
  noShort := fun h => hW.noShort (short_mono (cleanG_le G ω) h)

theorem addArc_clean {G : CH.Digraph} {ω : Nat → Nat} {u v : Nat} (hc : Clean G ω) (pu : 0 < ω u)
    (pv : 0 < ω v) : Clean (addArc G u v) ω := by
  intro x y h
  simp only [addArc] at h
  split_ifs at h with hxy
  · exact ⟨hxy.1 ▸ pu, hxy.2 ▸ pv⟩
  · exact hc x y h

/-- **Reduction, clean form.** It suffices to treat clean, saturated (among present vertices), in-Sperner graphs. -/
theorem reduce_clean {q s : Nat}
    (H : ∀ (G : CH.Digraph) (n : Nat) (ω : Nat → Nat), WB G n q s ω → Clean G ω → SaturatedP G n q ω →
      InSperner G n ω → Regular G n s ω) :
    ∀ (G : CH.Digraph) (n : Nat) (ω : Nat → Nat), WB G n q s ω → Regular G n s ω := by
  intro G n ω hW
  induction hk : (supp n ω).card using Nat.strong_induction_on generalizing G ω with
  | _ k IHk =>
  -- regularity of the cleaned graph suffices
  suffices hC : Regular (cleanG G ω) n s ω by
    intro y hy hpy; rw [← inW_clean G n ω y hpy]; exact hC y hy hpy
  have hW0 := clean_WB hW
  have hc0 := cleanG_clean G ω
  generalize cleanG G ω = G0 at hW0 hc0
  induction hm : miss G0 n using Nat.strong_induction_on generalizing G0 with
  | _ m IHm =>
  by_cases hsat : SaturatedP G0 n q ω
  · by_cases hsp : InSperner G0 n ω
    · exact H G0 n ω hW0 hc0 hsat hsp
    · simp only [InSperner, not_forall] at hsp
      obtain ⟨a, b, ha, hb, pa, pb, hab, nab, nba, nest⟩ := hsp
      exact merge_regular hW0 ha hb hab pa pb nab nba
        (fun x hx hpx hGb => by by_contra h; exact nest ⟨x, hx, hpx, hGb, h⟩)
        (fun ω' hW' hlt => IHk _ (hk ▸ hlt) G0 ω' hW' rfl)
  · simp only [SaturatedP, not_forall] at hsat
    obtain ⟨u, v, hu, hv, pu, pv, huv, hG, hno⟩ := hsat
    have hW' := addArc_WB hW0 huv hno
    have hR' := IHm _ (hm ▸ miss_lt hu hv huv hG) (addArc G0 u v) hW' (addArc_clean hc0 pu pv) rfl
    exact mono hW0 (addArc_ge G0 u v) hR'

end LeanCH.BR.Reduce
