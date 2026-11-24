import checkpoints.shen_extension.FiveParentEndpoint
import checkpoints.shen_extension.TransitionClosure

/-!
# Tight rows at the boundary order, for any count (idea 4 of 18 November)

Lean 4.35.0. Own file. Generalises `FiveProfileWrapper.lean` from five tight rows to any count `k`.
Setting: cutoff 3 where the conjecture is used, `W.card = 3 * d + 1`, `BankLaw s` always a hypothesis.

Part 1, deletion and domination.
* `low_row_off`: if `W \ Z` is nonempty with at most `3d` vertices, some row of `W \ Z` has fewer than `d` heads in `W \ Z` (given `BankLaw d`).
* `low_row_outside`: for `W.card = 3d+1+r`, `1 ≤ d` and any `Z ⊆ W` of size `r+1`, some row outside `Z` has fewer than `d` heads outside `Z`.
* `tight_dominate`: on `3d+1` vertices with every row at least `d`, every vertex has a parent whose row has exactly `d` heads.
* `card_le_mul_tight`: hence `W.card ≤ d * t`, `t` the number of tight rows.
* `four_tight_rows`: hence at least four tight rows.

Part 2, thinning for any count.
* `QProfile q k d` / `Profile k d`: some `q`-free digraph on `3d+1` vertices has exactly the rows of a `k`-set at `d` heads and all others at `d+1`.
* `tight_rows_of_not_profile`: if the `k`-profile does not exist (and `k ≤ 3d+1`), every `q`-free digraph on `3d+1` vertices with all rows at least `d` has at least `k+1` tight rows.
* `not_profile_five`, `six_tight_rows_of_thinning`: the five-row instance recovers `six_tight_rows`.
* `regular_of_not_profile_top`: excluding the single profile `k = 3d` already forces out-regularity (`BoundaryRegular`).
* `regular_of_not_profile`: excluding all profiles `k ≤ 3d` forces out-regularity.
* `not_profile_of_regular`: conversely, out-regularity excludes every profile `k ≤ 3d`.
* `regular_iff_not_profile`: out-regularity is equivalent to excluding all profiles `k ≤ 3d`.

Part 3, the first step for any count.
* `heavy_row_core`: if every row of `W \ H` has at least `s + m` heads, `W \ H` is nonempty with at most `3s` vertices, and `BankLaw s`, then some row of `W \ H` has at least `m + 1` heads in `H`.
* `first_step_heavy`: with `W.card ≤ 3d+1`, `H ⊆ W` of size `k`, `3j+1 ≤ k < W.card`, rows outside `H` at least `d+1`, and `BankLaw (d-j)`, some row outside `H` has at least `j+2` heads in `H`.
* `first_step`: the same under the exact profile hypotheses.
* `best_step`: with `j = (k-1)/3` (needs `1 ≤ k`).
* `five_heavy_three`: the instance `k = 5`: some heavy row has three tight heads.

Part 4, closure states.
* `state_tight_dominate`, `state_low_row_outside`, `state_tight_rows_of_not_profile`, `state_first_step`, `state_best_step`: the same statements for a closure `State`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.TightProfile

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 Finset LeanCH.BR.ShenPuncture LeanCH.BR.Closure

/-! ## Part 1 -/

/-- Deletion core: on a nonempty `W \ Z` with at most `3d` vertices some row has fewer than `d` heads. -/
theorem low_row_off {D : CH.Digraph} {W Z : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (law : BankLaw d)
    (live : (W \ Z).Nonempty) (small : (W \ Z).card ≤ 3 * d) :
    ∃ v ∈ W \ Z, (outN D (W \ Z) v).card < d := by
  by_contra h
  push Not at h
  exact (bankLaw_iff d).mp law D (W \ Z) (free.mono_set sdiff_subset) live small h

/-- For `W.card = 3d+1+r` and `Z ⊆ W` of size `r+1`, some row outside `Z` has fewer than `d` heads outside `Z`. -/
theorem low_row_outside {D : CH.Digraph} {W Z : Finset ℕ} {d r : ℕ}
    (free : QFree D W 3) (hd : 1 ≤ d) (size : W.card = 3 * d + 1 + r) (law : BankLaw d)
    (hZ : Z ⊆ W) (zc : Z.card = r + 1) :
    ∃ v ∈ W \ Z, (outN D (W \ Z) v).card < d := by
  have cs := card_sdiff_add_card_eq_card hZ
  exact low_row_off free law (by rw [← card_pos]; omega) (by omega)

/-- **Domination with no profile.** On `3d+1` vertices with every row at least `d`, every vertex has a tight parent. -/
theorem tight_dominate {D : CH.Digraph} {W : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (hd : 1 ≤ d) (size : W.card = 3 * d + 1) (law : BankLaw d)
    (deg : ∀ z ∈ W, d ≤ (outN D W z).card) :
    ∀ z ∈ W, ∃ p ∈ W, D p z = true ∧ (outN D W p).card = d := by
  classical
  intro z hz
  obtain ⟨v, hv, lowv⟩ := low_row_outside (Z := {z}) (r := 0) free hd (by omega) law
    (singleton_subset_iff.mpr hz) (by simp)
  have vW : v ∈ W := (mem_sdiff.mp hv).1
  have sub : outN D W v ⊆ insert z (outN D (W \ {z}) v) := by
    intro x hx
    rw [mem_insert]
    by_cases e : x = z
    · exact Or.inl e
    · right
      obtain ⟨xW, hx⟩ := mem_outN.mp hx
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨xW, by simpa using e⟩, hx⟩
  have up := (card_le_card sub).trans (card_insert_le _ _)
  have lo := deg v vW
  refine ⟨v, vW, ?_, by omega⟩
  by_contra nz
  have sub' : outN D W v ⊆ outN D (W \ {z}) v := by
    intro x hx
    obtain ⟨xW, hx⟩ := mem_outN.mp hx
    have e : x ≠ z := fun e => nz (e ▸ hx)
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨xW, by simpa using e⟩, hx⟩
  have := card_le_card sub'
  omega

/-- Counting heads of tight rows: `W.card ≤ d * t`. -/
theorem card_le_mul_tight {D : CH.Digraph} {W : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (hd : 1 ≤ d) (size : W.card = 3 * d + 1) (law : BankLaw d)
    (deg : ∀ z ∈ W, d ≤ (outN D W z).card) :
    W.card ≤ d * (W.filter (fun p => (outN D W p).card = d)).card := by
  classical
  have dom := tight_dominate free hd size law deg
  have cover : W ⊆ (W.filter (fun p => (outN D W p).card = d)).biUnion (fun p => outN D W p) := by
    intro z hz
    obtain ⟨p, hp, hpz, hc⟩ := dom z hz
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨hp, hc⟩, mem_outN.mpr ⟨hz, hpz⟩⟩
  calc W.card ≤ _ := card_le_card cover
    _ ≤ ∑ p ∈ W.filter (fun p => (outN D W p).card = d), (outN D W p).card := card_biUnion_le
    _ = ∑ p ∈ W.filter (fun p => (outN D W p).card = d), d :=
        sum_congr rfl (fun p hp => (mem_filter.mp hp).2)
    _ = d * (W.filter (fun p => (outN D W p).card = d)).card := by
        rw [sum_const, smul_eq_mul, mul_comm]

/-- Hence at least four tight rows. -/
theorem four_tight_rows {D : CH.Digraph} {W : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (hd : 1 ≤ d) (size : W.card = 3 * d + 1) (law : BankLaw d)
    (deg : ∀ z ∈ W, d ≤ (outN D W z).card) :
    4 ≤ (W.filter (fun p => (outN D W p).card = d)).card := by
  have h := card_le_mul_tight free hd size law deg
  by_contra few
  have : d * (W.filter (fun p => (outN D W p).card = d)).card ≤ d * 3 :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Part 2 -/

/-- The `k`-row profile at cutoff `q`: a `q`-free digraph on `3d+1` vertices whose rows in a `k`-set `H` have
exactly `d` heads and all other rows exactly `d+1`. -/
def QProfile (q k d : ℕ) : Prop :=
  ∃ (D : CH.Digraph) (W H : Finset ℕ), QFree D W q ∧ W.card = 3 * d + 1 ∧ H ⊆ W ∧ H.card = k ∧
    ∀ z ∈ W, (outN D W z).card = if z ∈ H then d else d + 1

/-- The `k`-row profile at cutoff 3. -/
abbrev Profile (k d : ℕ) : Prop := QProfile 3 k d

/-- Out-regularity at the boundary order: every `q`-free digraph on `3d+1` vertices with all rows at least `d`
has all rows exactly `d`. -/
def QBoundaryRegular (q d : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (W : Finset ℕ), QFree D W q → W.card = 3 * d + 1 →
    (∀ z ∈ W, d ≤ (outN D W z).card) → ∀ z ∈ W, (outN D W z).card = d

/-- Out-regularity at the boundary order, cutoff 3. -/
abbrev BoundaryRegular (d : ℕ) : Prop := QBoundaryRegular 3 d

/-- **Thinning for any count.** If the `k`-profile does not exist, every such digraph has at least `k+1` tight rows. -/
theorem tight_rows_of_not_profile {q k d : ℕ} (none : ¬ QProfile q k d) (hk : k ≤ 3 * d + 1)
    {D : CH.Digraph} {W : Finset ℕ}
    (free : QFree D W q) (size : W.card = 3 * d + 1)
    (deg : ∀ z ∈ W, d ≤ (outN D W z).card) :
    k + 1 ≤ (W.filter (fun z => (outN D W z).card = d)).card := by
  classical
  by_contra few
  push Not at few
  obtain ⟨H, tH, hW, kc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.filter_subset (fun z => (outN D W z).card = d) W) (by omega) (by omega : k ≤ W.card)
  have target : ∀ v, ∃ t ⊆ outN D W v, v ∈ W → t.card = if v ∈ H then d else d + 1 := by
    intro v
    by_cases hv : v ∈ W
    · have lo := deg v hv
      by_cases vh : v ∈ H
      · obtain ⟨t, ht, hc⟩ := Finset.exists_subset_card_eq lo
        exact ⟨t, ht, fun _ => by simp [vh, hc]⟩
      · have ne : (outN D W v).card ≠ d := fun e => vh (tH (Finset.mem_filter.mpr ⟨hv, e⟩))
        obtain ⟨t, ht, hc⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ (outN D W v).card by omega)
        exact ⟨t, ht, fun _ => by simp [vh, hc]⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hv⟩
  choose sel hsel hcard using target
  have sub : ∀ a b, (fun a b => decide (b ∈ sel a)) a b = true → D a b = true :=
    fun a b h => (mem_outN.mp (hsel a (of_decide_eq_true h))).2
  have row : ∀ v, outN (fun a b => decide (b ∈ sel a)) W v = sel v := by
    intro v
    ext z
    rw [mem_outN, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨(mem_outN.mp (hsel v h)).1, h⟩⟩
  exact none ⟨_, W, H, qfree_sub sub free, size, hW, kc, fun z hz => by rw [row z]; exact hcard z hz⟩

/-- The five-row profile is excluded: `FiveParent.five_dominating_false`, with domination supplied by
`tight_dominate` (this is `five_profile_false` of `FiveProfileWrapper.lean`, which has no `.olean`). -/
theorem not_profile_five {d : ℕ} (hd : 2 ≤ d) (law : BankLaw d) (lower : BankLaw (d - 1)) :
    ¬ Profile 5 d := by
  rintro ⟨D, W, H, free, size, hh, five, counts⟩
  have deg : ∀ z ∈ W, d ≤ (outN D W z).card := by
    intro z hz
    rw [counts z hz]
    split_ifs <;> omega
  apply FiveParent.five_dominating_false free hd size law lower hh five counts
  intro z hz
  obtain ⟨p, hp, hpz, hc⟩ := tight_dominate free (by omega) size law deg z hz
  refine ⟨p, ?_, hpz⟩
  by_contra pH
  rw [counts p hp] at hc
  simp [pH] at hc

/-- (a) `six_tight_rows` recovered as the instance `k = 5` of thinning. -/
theorem six_tight_rows_of_thinning {D : CH.Digraph} {W : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (hd : 2 ≤ d) (size : W.card = 3 * d + 1)
    (law : BankLaw d) (lower : BankLaw (d - 1))
    (deg : ∀ z ∈ W, d ≤ (outN D W z).card) :
    6 ≤ (W.filter (fun z => (outN D W z).card = d)).card :=
  tight_rows_of_not_profile (not_profile_five hd law lower) (by omega) free size deg

/-- Excluding the single profile `k = 3d` already forces out-regularity. -/
theorem regular_of_not_profile_top {q d : ℕ} (none : ¬ QProfile q (3 * d) d) : QBoundaryRegular q d := by
  classical
  intro D W free size deg z hz
  have h := tight_rows_of_not_profile none (by omega) free size deg
  have eq : W.filter (fun z => (outN D W z).card = d) = W :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have : z ∈ W.filter (fun z => (outN D W z).card = d) := by rw [eq]; exact hz
  exact (mem_filter.mp this).2

/-- (b) Excluding every profile `k ≤ 3d` forces out-regularity. -/
theorem regular_of_not_profile {q d : ℕ} (none : ∀ k ≤ 3 * d, ¬ QProfile q k d) : QBoundaryRegular q d :=
  regular_of_not_profile_top (none _ le_rfl)

/-- Conversely, out-regularity excludes every profile `k ≤ 3d`. -/
theorem not_profile_of_regular {q d : ℕ} (reg : QBoundaryRegular q d) : ∀ k ≤ 3 * d, ¬ QProfile q k d := by
  classical
  rintro k hk ⟨D, W, H, free, size, hh, kc, counts⟩
  have cs := card_sdiff_add_card_eq_card hh
  obtain ⟨z, hz⟩ : (W \ H).Nonempty := by rw [← card_pos]; omega
  obtain ⟨zW, zH⟩ := mem_sdiff.mp hz
  have deg : ∀ x ∈ W, d ≤ (outN D W x).card := by
    intro x hx
    rw [counts x hx]
    split_ifs <;> omega
  have e := reg D W free size deg z zW
  rw [counts z zW] at e
  simp [zH] at e

/-- Out-regularity at the boundary order is equivalent to excluding every profile `k ≤ 3d`. -/
theorem regular_iff_not_profile {q d : ℕ} : QBoundaryRegular q d ↔ ∀ k ≤ 3 * d, ¬ QProfile q k d :=
  ⟨not_profile_of_regular, regular_of_not_profile⟩

/-! ## Part 3 -/

/-- First-step core: rows of `W \ H` with at least `s + m` heads, `W \ H` nonempty with at most `3s` vertices,
`BankLaw s`; then some row of `W \ H` has at least `m + 1` heads in `H`. -/
theorem heavy_row_core {D : CH.Digraph} {W H : Finset ℕ} {s m : ℕ}
    (free : QFree D W 3) (law : BankLaw s)
    (live : (W \ H).Nonempty) (small : (W \ H).card ≤ 3 * s)
    (heavy : ∀ v ∈ W \ H, s + m ≤ (outN D W v).card) :
    ∃ v ∈ W \ H, m + 1 ≤ (outN D H v).card := by
  classical
  by_contra h
  push Not at h
  apply (bankLaw_iff s).mp law D (W \ H) (free.mono_set sdiff_subset) live small
  intro v hv
  have split : (outN D W v).card ≤ (outN D H v).card + (outN D (W \ H) v).card := by
    calc (outN D W v).card ≤ (outN D H v ∪ outN D (W \ H) v).card := by
          apply card_le_card
          intro z hz
          obtain ⟨zW, hz⟩ := mem_outN.mp hz
          rw [mem_union]
          by_cases zH : z ∈ H
          · exact Or.inl (mem_outN.mpr ⟨zH, hz⟩)
          · exact Or.inr (mem_outN.mpr ⟨mem_sdiff.mpr ⟨zW, zH⟩, hz⟩)
      _ ≤ _ := card_union_le _ _
  have := heavy v hv
  have := h v hv
  omega

/-- **First step, heavy-row form.** -/
theorem first_step_heavy {D : CH.Digraph} {W H : Finset ℕ} {k d j : ℕ}
    (free : QFree D W 3) (size : W.card ≤ 3 * d + 1) (hh : H ⊆ W) (kc : H.card = k)
    (hj : 3 * j + 1 ≤ k) (live : k < W.card)
    (heavy : ∀ z ∈ W, z ∉ H → d + 1 ≤ (outN D W z).card)
    (law : BankLaw (d - j)) :
    ∃ v ∈ W \ H, j + 2 ≤ (outN D H v).card := by
  have cs : (W \ H).card + H.card = W.card := card_sdiff_add_card_eq_card hh
  have pos : 0 < (W \ H).card := by omega
  have small : (W \ H).card ≤ 3 * (d - j) := by omega
  have jd : j < d := by omega
  obtain ⟨v, hv, c⟩ := heavy_row_core (s := d - j) (m := j + 1) free law (card_pos.mp pos) small
    (fun v hv => by have := heavy v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2; omega)
  exact ⟨v, hv, by omega⟩

/-- **First step for any count**, under the exact profile hypotheses. -/
theorem first_step {D : CH.Digraph} {W H : Finset ℕ} {k d j : ℕ}
    (free : QFree D W 3) (size : W.card = 3 * d + 1) (hh : H ⊆ W) (kc : H.card = k)
    (counts : ∀ z ∈ W, (outN D W z).card = if z ∈ H then d else d + 1)
    (hj : 3 * j + 1 ≤ k) (hk : k < 3 * d + 1) (law : BankLaw (d - j)) :
    ∃ v ∈ W \ H, j + 2 ≤ (outN D H v).card :=
  first_step_heavy free size.le hh kc hj (by omega)
    (fun z hz zH => by rw [counts z hz]; simp [zH]) law

/-- The best `j`: `j = (k-1)/3`. -/
theorem best_step {D : CH.Digraph} {W H : Finset ℕ} {k d : ℕ}
    (free : QFree D W 3) (size : W.card = 3 * d + 1) (hh : H ⊆ W) (kc : H.card = k)
    (counts : ∀ z ∈ W, (outN D W z).card = if z ∈ H then d else d + 1)
    (hk1 : 1 ≤ k) (hk : k < 3 * d + 1) (law : BankLaw (d - (k - 1) / 3)) :
    ∃ v ∈ W \ H, (k - 1) / 3 + 2 ≤ (outN D H v).card :=
  first_step free size hh kc counts (by omega) hk law

/-- The instance `k = 5`: some heavy row has three tight heads. -/
theorem five_heavy_three {D : CH.Digraph} {W H : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (hd : 2 ≤ d) (size : W.card = 3 * d + 1) (hh : H ⊆ W) (five : H.card = 5)
    (counts : ∀ z ∈ W, (outN D W z).card = if z ∈ H then d else d + 1)
    (lower : BankLaw (d - 1)) :
    ∃ v ∈ W \ H, 3 ≤ (outN D H v).card :=
  first_step (j := 1) free size hh five counts (by omega) (by omega) lower

/-! ## Part 4: closure states -/

theorem state_tight_dominate {st : State} {d : ℕ}
    (free : QFree st.H st.U 3) (hd : 1 ≤ d) (size : st.U.card = 3 * d + 1) (law : BankLaw d)
    (deg : ∀ z ∈ st.U, d ≤ (outN st.H st.U z).card) :
    ∀ z ∈ st.U, ∃ p ∈ st.U, st.H p z = true ∧ (outN st.H st.U p).card = d :=
  tight_dominate free hd size law deg

theorem state_low_row_outside {st : State} {Z : Finset ℕ} {d r : ℕ}
    (free : QFree st.H st.U 3) (hd : 1 ≤ d) (size : st.U.card = 3 * d + 1 + r) (law : BankLaw d)
    (hZ : Z ⊆ st.U) (zc : Z.card = r + 1) :
    ∃ v ∈ st.U \ Z, (outN st.H (st.U \ Z) v).card < d :=
  low_row_outside free hd size law hZ zc

theorem state_tight_rows_of_not_profile {st : State} {k d : ℕ} (none : ¬ Profile k d) (hk : k ≤ 3 * d + 1)
    (free : QFree st.H st.U 3) (size : st.U.card = 3 * d + 1)
    (deg : ∀ z ∈ st.U, d ≤ (outN st.H st.U z).card) :
    k + 1 ≤ (st.U.filter (fun z => (outN st.H st.U z).card = d)).card :=
  tight_rows_of_not_profile none hk free size deg

theorem state_first_step {st : State} {H : Finset ℕ} {k d j : ℕ}
    (free : QFree st.H st.U 3) (size : st.U.card = 3 * d + 1) (hh : H ⊆ st.U) (kc : H.card = k)
    (counts : ∀ z ∈ st.U, (outN st.H st.U z).card = if z ∈ H then d else d + 1)
    (hj : 3 * j + 1 ≤ k) (hk : k < 3 * d + 1) (law : BankLaw (d - j)) :
    ∃ v ∈ st.U \ H, j + 2 ≤ (outN st.H H v).card :=
  first_step free size hh kc counts hj hk law

theorem state_best_step {st : State} {H : Finset ℕ} {k d : ℕ}
    (free : QFree st.H st.U 3) (size : st.U.card = 3 * d + 1) (hh : H ⊆ st.U) (kc : H.card = k)
    (counts : ∀ z ∈ st.U, (outN st.H st.U z).card = if z ∈ H then d else d + 1)
    (hk1 : 1 ≤ k) (hk : k < 3 * d + 1) (law : BankLaw (d - (k - 1) / 3)) :
    ∃ v ∈ st.U \ H, (k - 1) / 3 + 2 ≤ (outN st.H H v).card :=
  best_step free size hh kc counts hk1 hk law

end LeanCH.BR.TightProfile

open LeanCH.BR.TightProfile in
#print axioms low_row_off
open LeanCH.BR.TightProfile in
#print axioms low_row_outside
open LeanCH.BR.TightProfile in
#print axioms tight_dominate
open LeanCH.BR.TightProfile in
#print axioms card_le_mul_tight
open LeanCH.BR.TightProfile in
#print axioms four_tight_rows
open LeanCH.BR.TightProfile in
#print axioms tight_rows_of_not_profile
open LeanCH.BR.TightProfile in
#print axioms not_profile_five
open LeanCH.BR.TightProfile in
#print axioms six_tight_rows_of_thinning
open LeanCH.BR.TightProfile in
#print axioms regular_of_not_profile_top
open LeanCH.BR.TightProfile in
#print axioms regular_of_not_profile
open LeanCH.BR.TightProfile in
#print axioms not_profile_of_regular
open LeanCH.BR.TightProfile in
#print axioms regular_iff_not_profile
open LeanCH.BR.TightProfile in
#print axioms heavy_row_core
open LeanCH.BR.TightProfile in
#print axioms first_step_heavy
open LeanCH.BR.TightProfile in
#print axioms first_step
open LeanCH.BR.TightProfile in
#print axioms best_step
open LeanCH.BR.TightProfile in
#print axioms five_heavy_three
open LeanCH.BR.TightProfile in
#print axioms state_tight_dominate
open LeanCH.BR.TightProfile in
#print axioms state_low_row_outside
open LeanCH.BR.TightProfile in
#print axioms state_tight_rows_of_not_profile
open LeanCH.BR.TightProfile in
#print axioms state_first_step
open LeanCH.BR.TightProfile in
#print axioms state_best_step
