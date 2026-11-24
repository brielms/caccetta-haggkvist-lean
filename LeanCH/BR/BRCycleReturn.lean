import LeanCH.BR.BRModuleReach
import LeanCH.BR.BRSmallHighSet

/-! Set expansion on shortest cycles and the total capacity of two-sided contacts. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

/-- Each proper set-ball on a shortest cycle gains a vertex at its next step. -/
theorem cycle_set_ball_step {D : CH.Digraph} {M A : Finset ℕ} {q k : ℕ}
    (hq : 1 ≤ q) (hf : QFree D M q) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hAM : A ⊆ M) (hAn : A.Nonempty) (hne : ballSet D M A k ≠ M) :
    (ballSet D M A k).card + 1 ≤ (ballSet D M A (k + 1)).card := by
  classical
  have hBn : (ballSet D M A k).Nonempty := hAn.mono (subset_ballSet hAM)
  obtain ⟨x, hx, y, hy, hxy⟩ := cycle_cut_crossing hq hf hM hcyc
    ballSet_subset hBn hne
  obtain ⟨hyM, hyB⟩ := Finset.mem_sdiff.mp hy
  have hnext : y ∈ ballSet D M A (k + 1) :=
    outN_subset_ballSet_succ hx (mem_outN.mpr ⟨hyM, hxy⟩)
  have hsub : insert y (ballSet D M A k) ⊆ ballSet D M A (k + 1) :=
    Finset.insert_subset hnext (ballSet_mono (by omega))
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hyB] at hc

/-- A nonempty set expands by at least one vertex per step until the cycle is full. -/
theorem cycle_set_ball_growth {D : CH.Digraph} {M A : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D M q) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hAM : A ⊆ M) (hAn : A.Nonempty) (k : ℕ) :
    min M.card (A.card + k) ≤ (ballSet D M A k).card := by
  induction k with
  | zero =>
    have hc := Finset.card_le_card (subset_ballSet (E := D) (k := 0) hAM)
    omega
  | succ k ih =>
    by_cases hfull : ballSet D M A k = M
    · have hc := Finset.card_le_card
        (ballSet_mono (E := D) (V := M) (Y := A) (by omega : k ≤ k + 1))
      rw [hfull] at hc
      exact (Nat.min_le_left _ _).trans hc
    · have hlt : (ballSet D M A k).card < M.card := by
        by_contra hn
        exact hfull (Finset.eq_of_subset_of_card_le ballSet_subset (by omega))
      have hs := cycle_set_ball_step hq hf hM hcyc hAM hAn hfull
      omega

/-- Cycle predecessors of z and nonempty cycle targets reached from z within t
steps have total size at most t+2. This bounds their union of possible targets. -/
theorem cycle_reentry_window {D : CH.Digraph} {V M A : Finset ℕ} {q z t : ℕ}
    (ht : t + 1 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : (inN D M z).Nonempty)
    (hAM : A ⊆ M) (hAn : A.Nonempty) (hreach : A ⊆ ball D V z t) :
    (inN D M z).card + A.card ≤ t + 2 := by
  classical
  let B := ballSet D M A (q - t - 1)
  have hd : Disjoint (inN D M z) B := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxb
    obtain ⟨y, hy, hxy⟩ := mem_ballSet.mp hxb
    obtain ⟨_, i, hi, wy⟩ := mem_ball.mp (hreach hy)
    obtain ⟨_, j, hj, w⟩ := mem_ball.mp hxy
    exact hf z (i + j + 1) (by omega) (by omega)
      ((wy.append (w.mono hMV)).snoc hz (mem_inN.mp hxi).2)
  have hsub : inN D M z ∪ B ⊆ M :=
    Finset.union_subset (fun _ h => (mem_inN.mp h).1) ballSet_subset
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  have hg := cycle_set_ball_growth (by omega : 1 ≤ q) (hf.mono_set hMV) hM hcyc
    hAM hAn (q - t - 1)
  have hi : 0 < (inN D M z).card := Finset.card_pos.mpr hin
  change min M.card (A.card + (q - t - 1)) ≤ B.card at hg
  omega

/-- Quantitative reentry capacity, valid also when no cycle target is reached. -/
theorem cycle_reachable_card_cap {D : CH.Digraph} {V M : Finset ℕ} {q z t : ℕ}
    (ht : t + 1 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : (inN D M z).Nonempty) :
    (M ∩ ball D V z t).card ≤ t + 2 - (inN D M z).card := by
  by_cases hn : (M ∩ ball D V z t).Nonempty
  · have hc := cycle_reentry_window ht hf hMV hM hcyc hz hin
      Finset.inter_subset_left hn Finset.inter_subset_right
    omega
  · have he : (M ∩ ball D V z t).card = 0 := by
      by_contra h
      exact hn (Finset.card_pos.mp (by omega))
    omega

/-- A vertex which both receives from and returns to a shortest cycle has at
most three contacts in total. Both nonemptiness assumptions are necessary. -/
theorem cycle_two_sided_contact_cap {D : CH.Digraph} {V M : Finset ℕ} {q z : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V)
    (hin : (inN D M z).Nonempty) (hout : (outN D M z).Nonempty) :
    (inN D M z).card + (outN D M z).card ≤ 3 := by
  exact cycle_reentry_window (t := 1) hq hf hMV hM hcyc hz hin outN_subset hout
    (fun y hy => ball_of_adj (hMV (outN_subset hy)) (mem_outN.mp hy).2)

/-- A row receiving at least three cycle arcs cannot return to the cycle. -/
theorem cycle_three_feeds_no_return {D : CH.Digraph} {V M : Finset ℕ} {q z : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : 3 ≤ (inN D M z).card) :
    outN D M z = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra hn
  have hc := cycle_two_sided_contact_cap hq hf hMV hM hcyc hz
    (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
  omega

/-- The exact return capacity, including rows with no return at all. -/
theorem cycle_feed_return_budget {D : CH.Digraph} {V M : Finset ℕ} {q z : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : (inN D M z).Nonempty) :
    (outN D M z).card + min 3 (inN D M z).card ≤ 3 := by
  by_cases hout : (outN D M z).Nonempty
  · have hc := cycle_two_sided_contact_cap hq hf hMV hM hcyc hz hin hout
    omega
  · have he : (outN D M z).card = 0 := by
      by_contra hn
      exact hout (Finset.card_pos.mp (by omega))
    omega

/-- A high row reached from the cycle retains a feed-dependent minimum degree
after the cycle is removed. This uses the actual exterior, not a quotient. -/
theorem cycle_fed_exterior_degree {D : CH.Digraph} {V M : Finset ℕ} {q z d : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : (inN D M z).Nonempty)
    (hdeg : d + 3 ≤ (outN D V z).card) :
    d + min 3 (inN D M z).card ≤ (outN D (V \ M) z).card := by
  have hc := cycle_feed_return_budget hq hf hMV hM hcyc hz hin
  have hs := card_outN_union (D := D)
    (show Disjoint M (V \ M) from Finset.disjoint_sdiff) z
  rw [Finset.union_sdiff_of_subset hMV] at hs
  omega

/-- In a host of size at most q+2, a row and high-degree heads of that row
require disjoint room. This is the existing near-boundary high-set bound after
deleting the root, whose heads cannot return to it. -/
theorem small_host_two_step_fan_bound {D : CH.Digraph} {V : Finset ℕ} {q d u : ℕ}
    (hq : 2 ≤ q) (hd : 2 ≤ d) (hf : QFree D V q) (hV : V.card ≤ q + 2)
    (hu : u ∈ V) (hXn : (outN D V u).Nonempty)
    (hh : ∀ x ∈ outN D V u, d ≤ (outN D V x).card) :
    (outN D V u).card + d + 1 ≤ V.card := by
  classical
  let W := V.erase u
  have hW : W.card = V.card - 1 := Finset.card_erase_of_mem hu
  have hXW : outN D V u ⊆ W := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun heq => loopfree hf (by omega) hu
      (heq ▸ (mem_outN.mp hx).2), outN_subset hx⟩
  have hretain : ∀ x ∈ outN D V u, outN D V x ⊆ outN D W x := by
    intro x hx y hy
    refine mem_outN.mpr ⟨Finset.mem_erase.mpr ⟨?_, outN_subset hy⟩, (mem_outN.mp hy).2⟩
    intro heq
    exact digonfree hf hq hu (outN_subset hx) (mem_outN.mp hx).2
      (heq ▸ (mem_outN.mp hy).2)
  have hc := near_boundary_high_set_card (by omega : 1 ≤ q) hd
    (hf.mono_set (Finset.erase_subset _ _)) (by change W.card ≤ q + 1; omega) hXW
    (fun x hx => (hh x hx).trans (Finset.card_le_card (hretain x hx)))
  have hn : 0 < V.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hXpos : 0 < (outN D V u).card := Finset.card_pos.mpr hXn
  change (outN D V u).card ≤ W.card - d at hc
  omega

/-- A shortest cycle cannot feed a set of at most q+2 vertices whose rows all
retain q+1 heads in the union of that set and the cycle, for q>=5. -/
theorem cycle_no_feed_small_high_set {D : CH.Digraph} {V M T : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hTV : T ⊆ V)
    (hMT : Disjoint T M) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hT : T.card ≤ q + 2) (hm : ∀ x ∈ T, q + 1 ≤ (outN D (T ∪ M) x).card) :
    ∀ m ∈ M, ∀ x ∈ T, ¬ D m x = true := by
  intro m hmM x hx hmx
  have hin : (inN D M x).Nonempty := ⟨m, mem_inN.mpr ⟨hmM, hmx⟩⟩
  have hcap := cycle_feed_return_budget (by omega) hf hMV hM hcyc (hTV hx) hin
  have hpos : 1 ≤ (inN D M x).card := Finset.card_pos.mpr hin
  have hsplit := card_outN_union (D := D) hMT x
  have hmin := hm x hx
  have hroot : q - 1 ≤ (outN D T x).card := by omega
  have hwindow := cycle_reachable_card_cap (t := 2) (by omega) hf hMV hM hcyc (hTV hx) hin
  have hnext : ∀ y ∈ outN D T x, q - 2 ≤ (outN D T y).card := by
    intro y hy
    have hsub : outN D M y ⊆ M ∩ ball D V x 2 := by
      intro z hz
      exact Finset.mem_inter.mpr ⟨outN_subset hz,
        ball_step (ball_of_adj (hTV (outN_subset hy)) (mem_outN.mp hy).2)
          (hMV (outN_subset hz)) (mem_outN.mp hz).2⟩
    have hc := Finset.card_le_card hsub
    have hs := card_outN_union (D := D) hMT y
    have hh := hm y (outN_subset hy)
    omega
  have hfan := small_host_two_step_fan_bound (by omega : 2 ≤ q)
    (by omega : 2 ≤ q - 2) (hf.mono_set hTV) hT hx
    (Finset.card_pos.mp (by omega)) hnext
  omega

end LeanCH.BR.BRsub
