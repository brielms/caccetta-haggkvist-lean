import LeanCH.BR.BRsGenPad
import LeanCH.BR.BRq3BallAll
import LeanCH.BR.BRq4Rigid

/-!
# Ball(q,4) route: the fold at out-degree four and shared tools (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BallQ4b_attempt_subagent.md` §1, `BallQ4_attempt_subagent.md` §3,
`Route1_GeneralS_subagent.md` §1. No existing file is changed.

* `BallSmall k s`: `Ball(k,s)` restricted to hosts with at most `sk+1` vertices (the paper's `(Diam_k)` input).
  `in_eq_b`, `in_compl_b`, `diam_small_b`, `exit_small`: Lemma 1_s and Lemma 4_{s,r} from `BallSmall` only.
* `rewire_outEq_s`, `closed_outEq_s`: `BRq3Rewire.rewire_outEq` and `BRq3Util.closed_outEq` at out-degree `s`
  (the originals are stated for out-degree three only).
* Level convention: the paper's level `k ≥ 3` is `j + 3`. `KK = N_{k+1}`, `VV = B_{k+1} ∖ {u}`, `FF` = fold,
  `BB z = B^F_k(z)`.
* `fold_walk`, `fold_two`: the last-`K` decomposition (F3) of an `F`-walk from `z ∉ K`.
* `ch3_set`, `ch2_set`: CH(3), CH(2) on a vertex set (`ball_all`, `corB`).
* `unique_succ`: in a `q`-free digraph on `≤ q+1` vertices with min out `≥ 1`, out-neighbours are unique.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

/-- `Ball(k,s)` on hosts with at most `sk+1` vertices. -/
def BallSmall (k s : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (W : Finset ℕ), QFree D W k → OutEq s D W → W.card ≤ s * k + 1 →
    ∀ u ∈ W, s * (k - 1) + 1 ≤ (ball D W u (k - 1)).card

theorem ballSmall_of_ball {k s : ℕ} (h : Ball k s) : BallSmall k s :=
  fun D W hf ho _ u hu => h D W hf ho u hu

variable {D : CH.Digraph} {W : Finset ℕ}

theorem in_eq_b {j s : ℕ} (hj : 1 ≤ j) (hball : BallSmall j s) (hfree : QFree D W j) (hout : OutEq s D W)
    (hcard : W.card ≤ s * j + 1) : ∀ y ∈ W, (W.filter (fun a => D a y = true)).card = s := by
  have hsj : s * (j - 1) + s = s * j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_add_one]
  have hle : ∀ y ∈ W, (W.filter (fun a => D a y = true)).card ≤ s := by
    intro y hy
    have h1 := Finset.card_le_card (in_sub_s hj hfree hy)
    rw [Finset.card_sdiff_of_subset ball_subset] at h1
    have h2 := hball D W hfree hout hcard y hy
    omega
  have hsum : ∑ y ∈ W, (W.filter (fun a => D a y = true)).card = ∑ _y ∈ W, s :=
    calc ∑ y ∈ W, (W.filter (fun a => D a y = true)).card
        = ∑ x ∈ W, (W.filter (fun w => D x w = true)).card := (Compose.ThinRigid.sum_out_eq_sum_in D W).symm
      _ = ∑ _y ∈ W, s := Finset.sum_congr rfl (fun y hy => hout y hy)
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum

/-- In an extremal host, the in-neighbours of `y` are exactly `W ∖ B_{j-1}(y)`. -/
theorem in_compl_b {j s : ℕ} (hj : 1 ≤ j) (hball : BallSmall j s) (hfree : QFree D W j) (hout : OutEq s D W)
    (hcard : W.card ≤ s * j + 1) {y : ℕ} (hy : y ∈ W) :
    W.filter (fun a => D a y = true) = W \ ball D W y (j - 1) := by
  have hsj : s * (j - 1) + s = s * j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_add_one]
  refine Finset.eq_of_subset_of_card_le (in_sub_s hj hfree hy) ?_
  rw [Finset.card_sdiff_of_subset ball_subset, in_eq_b hj hball hfree hout hcard y hy]
  have h2 := hball D W hfree hout hcard y hy
  omega

theorem diam_small_b {j s : ℕ} (hj : 1 ≤ j) (hball : BallSmall j s) (hfree : QFree D W j) (hout : OutEq s D W)
    (hcard : W.card ≤ s * j + 1) : ∀ v ∈ W, ball D W v j = W := by
  have hsj : s * (j - 1) + s = s * j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_add_one]
  intro v hv
  refine Finset.Subset.antisymm ball_subset (fun x hx => ?_)
  by_contra hxb
  have hsub : W.filter (fun a => D a x = true) ⊆ (W \ ball D W v (j - 1)).erase x := by
    intro a ha
    obtain ⟨haW, hax⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨haW, fun hab => hxb ?_⟩⟩
    · rintro rfl; exact loopfree hfree hj hx hax
    · have := ball_step hab hx hax
      rwa [show j - 1 + 1 = j by omega] at this
  have hxin : x ∈ W \ ball D W v (j - 1) :=
    Finset.mem_sdiff.mpr ⟨hx, fun h => hxb (ball_mono_radius (by omega) h)⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hxin, Finset.card_sdiff_of_subset ball_subset] at h1
  have h2 := hball D W hfree hout hcard v hv
  have h3 := in_eq_b hj hball hfree hout hcard x hx
  have h5 : 0 < (W \ ball D W v (j - 1)).card := Finset.card_pos.mpr ⟨x, hxin⟩
  rw [Finset.card_sdiff_of_subset ball_subset] at h5
  have h4 := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := j - 1))
  omega

/-- **Lemma 4_{s,r}** from `BallSmall k s`. -/
theorem exit_small {G : CH.Digraph} {s k z r : ℕ} (hk : 1 ≤ k) (hbk : BallSmall k s) (hfree : QFree G W k)
    (hout : OutEq s G W) (hz : z ∈ W) (hr : 1 ≤ r) (hcard : (ball G W z k).card + r ≤ s * k + 1) :
    ∃ y ∈ ball G W z k, r + 2 ≤ (exitN G W (ball G W z k) z y).card := by
  by_contra hcon
  push Not at hcon
  obtain ⟨X, hX, hXW, H, hHout, hHfree, hHball⟩ :=
    exists_pad_r (r := r) hk hfree hout hz (fun y hy => by have := hcon y hy; omega)
  have hdisj : Disjoint (ball G W z k) X := by
    rw [Finset.disjoint_left]
    intro a ha haX
    exact hXW a haX (ball_subset ha)
  have hU : (ball G W z k ∪ X).card ≤ s * k + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hX]; exact hcard
  have hdiam := diam_small_b hk hbk hHfree hHout hU z (Finset.mem_union_left _ (self_mem_ball hz))
  rw [hHball] at hdiam
  obtain ⟨x, hx⟩ : X.Nonempty := by rw [← Finset.card_pos, hX]; omega
  have : x ∈ ball G W z k := by rw [hdiam]; exact Finset.mem_union_right _ hx
  exact hXW x hx (ball_subset this)

/-! ### The fold at out-degree `s` -/

variable {u : ℕ}

/-- `BRq3Rewire.rewire_outEq` at out-degree `s`. -/
theorem rewire_outEq_s {q k s : ℕ} (hkq : k + 1 ≤ q) (hfree : QFree D W q) (hout : OutEq s D W) (hu : u ∈ W) :
    OutEq s (rewire D u (ball D W u (k + 1) \ ball D W u k)) ((ball D W u (k + 1)).erase u) := by
  classical
  intro a ha
  obtain ⟨hau, ha1⟩ := Finset.mem_erase.mp ha
  have hVW : (ball D W u (k + 1)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  by_cases haK : a ∈ ball D W u (k + 1) \ ball D W u k
  · have e : outN (rewire D u (ball D W u (k + 1) \ ball D W u k)) ((ball D W u (k + 1)).erase u) a =
        outN D W u := by
      ext b
      rw [mem_outN, mem_outN, rewire_of_mem haK]
      constructor
      · rintro ⟨hb, h⟩; exact ⟨hVW hb, h⟩
      · rintro ⟨hbW, h⟩
        refine ⟨Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) (ball_of_adj hbW h)⟩, h⟩
        intro hbu
        rw [hbu] at h
        exact loopfree hfree (by omega) hu h
    rw [e]; exact hout u hu
  · have hak : a ∈ ball D W u k := by
      by_contra h; exact haK (Finset.mem_sdiff.mpr ⟨ha1, h⟩)
    have e : outN (rewire D u (ball D W u (k + 1) \ ball D W u k)) ((ball D W u (k + 1)).erase u) a =
        outN D W a := by
      ext b
      rw [mem_outN, mem_outN, rewire_of_not_mem haK]
      constructor
      · rintro ⟨hb, h⟩; exact ⟨hVW hb, h⟩
      · rintro ⟨hbW, h⟩
        refine ⟨Finset.mem_erase.mpr ⟨?_, ball_step hak hbW h⟩, h⟩
        intro hbu
        rw [hbu] at h
        exact no_back_arc hfree hu hak hkq h
    rw [e]; exact hout a (hVW ha)

/-- `BRq3Util.closed_outEq` at out-degree `s ≥ 1`. -/
theorem closed_outEq_s {q k s : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k) (hkq : k + 1 ≤ q) (hfree : QFree D W q)
    (hout : OutEq s D W) (hu : u ∈ W) (h : (ball D W u (k + 1)).card ≤ (ball D W u k).card) :
    OutEq s D ((ball D W u k).erase u) ∧ ((ball D W u k).erase u).Nonempty := by
  classical
  have hsub : ball D W u k ⊆ ball D W u (k + 1) := ball_mono_radius (by omega)
  have heq : ball D W u k = ball D W u (k + 1) := Finset.eq_of_subset_of_card_le hsub h
  have hUW : (ball D W u k).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hcl : ∀ y ∈ (ball D W u k).erase u, outN D ((ball D W u k).erase u) y = outN D W y := by
    intro y hy
    ext z
    rw [mem_outN, mem_outN]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hUW hz, h⟩
    · rintro ⟨hzW, hyz⟩
      have hyB := Finset.mem_of_mem_erase hy
      have hzk : z ∈ ball D W u k := by rw [heq]; exact ball_step hyB hzW hyz
      refine ⟨Finset.mem_erase.mpr ⟨?_, hzk⟩, hyz⟩
      intro hzu
      rw [hzu] at hyz
      exact no_back_arc hfree hu hyB (by omega) hyz
  refine ⟨fun y hy => by rw [hcl y hy]; exact hout y (hUW hy), ?_⟩
  obtain ⟨z, hz⟩ : (outN D W u).Nonempty := by rw [← Finset.card_pos, hout u hu]; omega
  refine ⟨z, Finset.mem_erase.mpr ⟨?_, ball_mono_radius hk (mem_ball_one_of_out hz)⟩⟩
  intro hzu
  have h' := (mem_outN.mp hz).2
  rw [hzu] at h'
  exact loopfree hfree (by omega) hu h'

/-! ### Level `k = j + 3`: the fold `F` on `V = B_{k+1} ∖ {u}` -/

/-- `K = N_{k+1}`. -/
noncomputable abbrev KK (D : CH.Digraph) (W : Finset ℕ) (u j : ℕ) : Finset ℕ := ball D W u (j + 4) \ ball D W u (j + 3)
/-- `V♮ = B_{k+1} ∖ {u}`. -/
noncomputable abbrev VV (D : CH.Digraph) (W : Finset ℕ) (u j : ℕ) : Finset ℕ := (ball D W u (j + 4)).erase u
/-- The fold `F`. -/
noncomputable abbrev FF (D : CH.Digraph) (W : Finset ℕ) (u j : ℕ) : CH.Digraph := rewire D u (KK D W u j)
/-- `B^F_k(z)`. -/
noncomputable abbrev BB (D : CH.Digraph) (W : Finset ℕ) (u j z : ℕ) : Finset ℕ := ball (FF D W u j) (VV D W u j) z (j + 3)

variable {j : ℕ}

theorem FF_of_not_mem {a b : ℕ} (ha : a ∉ KK D W u j) : FF D W u j a b = D a b := rewire_of_not_mem ha

theorem FF_of_mem {a b : ℕ} (ha : a ∈ KK D W u j) : FF D W u j a b = D u b := rewire_of_mem ha

theorem VV_sub : VV D W u j ⊆ W := (Finset.erase_subset _ _).trans ball_subset

theorem FF_outEq (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W) :
    OutEq 4 (FF D W u j) (VV D W u j) :=
  rewire_outEq_s (q := j + 5) (k := j + 3) (by omega) hfree hout hu

theorem FF_qfree (hfree : QFree D W (j + 5)) : QFree (FF D W u j) (VV D W u j) (j + 3) :=
  rewire_qfree (k := j + 3) (by omega) hfree

/-- **(F3), last-`K` decomposition.** An `F`-walk from `z ∉ K` is a `D`-walk, or reaches some `c ∈ K` after
`m1 ≥ 1` steps and its end is reached from `u` by a `D`-walk of length `m - m1`. -/
theorem fold_walk {z x m : ℕ} (hzK : z ∉ KK D W u j) (w : Walk (FF D W u j) (VV D W u j) z x m) :
    Walk D W z x m ∨ ∃ c ∈ KK D W u j, ∃ m1 m2, m1 + m2 = m ∧ 1 ≤ m1 ∧
      Walk (FF D W u j) (VV D W u j) z c m1 ∧ Walk D W u x m2 := by
  rcases rewire_walk VV_sub w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
  · exact Or.inl h
  · refine Or.inr ⟨c, hc, m1, m2, hsum, ?_, w1, w2⟩
    rcases Nat.eq_zero_or_pos m1 with h0 | h0
    · subst h0
      rw [walk_zero w1] at hzK
      exact absurd hc hzK
    · exact h0

theorem fold_one {z c : ℕ} (hzK : z ∉ KK D W u j) (w : Walk (FF D W u j) (VV D W u j) z c 1) :
    D z c = true := by
  obtain ⟨_, h⟩ := walk_one w
  rwa [FF_of_not_mem hzK] at h

theorem fold_two {z c : ℕ} (hzK : z ∉ KK D W u j) (hc : c ∈ KK D W u j)
    (w : Walk (FF D W u j) (VV D W u j) z c 2) :
    ∃ y ∈ VV D W u j, y ∉ KK D W u j ∧ D z y = true ∧ D y c = true := by
  obtain ⟨y, hy, hzy, w'⟩ := walk_uncons_s (m := 1) w
  obtain ⟨_, hyc⟩ := walk_one w'
  rw [FF_of_not_mem hzK] at hzy
  have hcW : c ∈ W := ball_subset (Finset.mem_sdiff.mp hc).1
  by_cases hyK : y ∈ KK D W u j
  · rw [FF_of_mem hyK] at hyc
    exact absurd (ball_mono_radius (by omega) (ball_of_adj hcW hyc)) (Finset.mem_sdiff.mp hc).2
  · rw [FF_of_not_mem hyK] at hyc
    exact ⟨y, hy, hyK, hzy, hyc⟩

/-- `z ∈ V ∖ K` lies in `B_k`. -/
theorem mem_ball_of_V {z : ℕ} (hzV : z ∈ VV D W u j) (hzK : z ∉ KK D W u j) : z ∈ ball D W u (j + 3) := by
  by_contra h
  exact hzK (Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hzV).2, h⟩)

/-- Out-neighbours of `B_k` lie in `V`. -/
theorem toV (hfree : QFree D W (j + 5)) (hu : u ∈ W) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hpz : D p z = true) (hzW : z ∈ W) : z ∈ VV D W u j := by
  refine Finset.mem_erase.mpr ⟨?_, ball_step hp hzW hpz⟩
  intro hzu
  rw [hzu] at hpz
  exact no_back_arc hfree hu hp (by omega) hpz

/-- A vertex of `B_{k+1}` outside `B_i` lies in `V`. -/
theorem memV_of {x i : ℕ} (hu : u ∈ W) (hx : x ∈ ball D W u (j + 4)) (hxi : x ∉ ball D W u i) :
    x ∈ VV D W u j := by
  refine Finset.mem_erase.mpr ⟨?_, hx⟩
  rintro rfl
  exact hxi (self_mem_ball hu)

/-! ### CH(3) and CH(2) on vertex sets -/

theorem ch3_set {U : Finset ℕ} {q : ℕ} (hq : 1 ≤ q) (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, 3 ≤ (outN D U y).card) (hne : U.Nonempty) : 3 * q + 1 ≤ U.card := by
  obtain ⟨G', hsub', hout'⟩ := exists_outEq hmin
  have hfG' : QFree G' U q := qfree_sub hsub' hfree
  have hc := card_ge_of_ball (q := q) (s := 3) (b := 3 * (q - 1) + 1) hq hfree hmin
    (fun z hz => (ball_all q hq G' U hfG' hout' z hz).trans (Finset.card_le_card (ball_sub hsub'))) hne
  omega

theorem ch2_set {U : Finset ℕ} {q : ℕ} (hq : 1 ≤ q) (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, 2 ≤ (outN D U y).card) (hne : U.Nonempty) : 2 * q + 1 ≤ U.card :=
  corB hq hfree hmin hne

/-- `outN D W v ⊆ outN D U v ∪ outN D S v` when every out-neighbour of `v` lies in `U ∪ S`. -/
theorem out_split {U S : Finset ℕ} {v : ℕ} (h : ∀ b ∈ W, D v b = true → b ∈ U ∨ b ∈ S) :
    (outN D W v).card ≤ (outN D U v).card + (outN D S v).card := by
  have hsub : outN D W v ⊆ outN D U v ∪ outN D S v := by
    intro b hb
    obtain ⟨hbW, hvb⟩ := mem_outN.mp hb
    rcases h b hbW hvb with h' | h'
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨h', hvb⟩)
    · exact Finset.mem_union_right _ (mem_outN.mpr ⟨h', hvb⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-! ### Unique successors in a short-cycle-free digraph on `≤ q+1` vertices -/

theorem unique_succ {E : CH.Digraph} {T : Finset ℕ} {q : ℕ} (hq : 1 ≤ q) (hfree : QFree E T q)
    (hT : T.card ≤ q + 1) (hmin : ∀ t ∈ T, ∃ t' ∈ T, E t t' = true) {t a b : ℕ} (ht : t ∈ T) (ha : a ∈ T)
    (hb : b ∈ T) (hta : E t a = true) (htb : E t b = true) : a = b := by
  classical
  let nx : ℕ → ℕ := fun t => if h : ∃ z ∈ T, E t z = true then h.choose else t
  have hnx : ∀ t ∈ T, nx t ∈ T ∧ E t (nx t) = true := by
    intro t ht
    have h := hmin t ht
    simp only [nx]
    split
    · next h' => exact h'.choose_spec
    · next h' => exact absurd h h'
  let f : ℕ → ℕ := fun i => nx^[i] t
  have hg : ∀ i, f i ∈ T := by
    intro i
    induction i with
    | zero => exact ht
    | succ i ih =>
      change nx^[i + 1] t ∈ T
      rw [Function.iterate_succ_apply']; exact (hnx _ ih).1
  have hw : ∀ i l, Walk E T (f i) (f (i + l)) l := by
    intro i l
    induction l with
    | zero => exact .refl _
    | succ l ih =>
      have e : f (i + (l + 1)) = nx (f (i + l)) := by
        change nx^[i + (l + 1)] t = nx (nx^[i + l] t)
        rw [← Nat.add_assoc, Function.iterate_succ_apply']
      rw [e]
      exact ih.snoc (hnx _ (hg _)).1 (hnx _ (hg _)).2
  -- `f 0, …, f q` are distinct
  have hinj : ∀ i ≤ q, ∀ i' ≤ q, f i = f i' → i = i' := by
    intro i hi i' hi' he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have w := hw i (i' - i)
      rw [Nat.add_sub_cancel' h.le, ← he] at w
      exact hfree _ (i' - i) (by omega) (by omega) w
    · have w := hw i' (i - i')
      rw [Nat.add_sub_cancel' h.le, he] at w
      exact hfree _ (i - i') (by omega) (by omega) w
  have himg : (Finset.range (q + 1)).image f = T := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hg i
    · rw [Finset.card_image_of_injOn (fun i hi i' hi' he => hinj i (by simpa [Nat.lt_succ_iff] using hi) i'
        (by simpa [Nat.lt_succ_iff] using hi') he), Finset.card_range]
      exact hT
  have hidx : ∀ x ∈ T, ∃ i ≤ q, f i = x := by
    intro x hx
    rw [← himg] at hx
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hx
    exact ⟨i, by simpa [Nat.lt_succ_iff] using hi, he⟩
  -- `f (q+1) = t`
  have hper : f (q + 1) = t := by
    obtain ⟨i, hi, he⟩ := hidx _ (hg (q + 1))
    by_contra hne
    have hi0 : i ≠ 0 := by rintro rfl; exact hne he.symm
    have w := hw i (q + 1 - i)
    rw [Nat.add_sub_cancel' (by omega), ← he] at w
    exact hfree _ (q + 1 - i) (by omega) (by omega) w
  -- every out-neighbour of `t` in `T` is `f 1`
  have key : ∀ x ∈ T, E t x = true → x = f 1 := by
    intro x hx htx
    obtain ⟨i, hi, rfl⟩ := hidx x hx
    by_contra hne
    have hi1 : i ≠ 1 := by rintro rfl; exact hne rfl
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hfree t 1 le_rfl hq (.step ht htx (.refl t))
    · have w := hw i (q + 1 - i)
      rw [Nat.add_sub_cancel' (by omega), hper] at w
      exact hfree t (q + 1 - i + 1) (by omega) (by omega) (.step (hg i) htx w)
  rw [key a ha hta, key b hb htb]

/-- Two-step digraph: `a ⇒ b` iff `a → z → b` for some `z ∈ S`. -/
noncomputable def two (D : CH.Digraph) (S : Finset ℕ) : CH.Digraph := by
  classical exact fun a b => decide (∃ z ∈ S, D a z = true ∧ D z b = true)

theorem two_iff {S : Finset ℕ} {a b : ℕ} : two D S a b = true ↔ ∃ z ∈ S, D a z = true ∧ D z b = true := by
  classical
  unfold two
  simp

theorem walk_two {S T : Finset ℕ} (hS : S ⊆ W) {a b m : ℕ} (w : Walk (two D S) T a b m) (hT : T ⊆ W) :
    Walk D W a b (2 * m) := by
  induction w with
  | refl a => exact .refl a
  | @step a b c m hb hab _ ih =>
    obtain ⟨z, hz, haz, hzb⟩ := two_iff.mp hab
    rw [show 2 * (m + 1) = m * 2 + 1 + 1 by omega]
    have : Walk D W a b 2 := .step (hS hz) haz (.step (hT hb) hzb (.refl b))
    have h := this.append ih
    rwa [show 2 + 2 * m = m * 2 + 1 + 1 by omega] at h

theorem two_qfree {S T : Finset ℕ} {q q' : ℕ} (hS : S ⊆ W) (hT : T ⊆ W) (hfree : QFree D W q)
    (hq : 2 * q' ≤ q) : QFree (two D S) T q' :=
  fun a ℓ h1 h2 w => hfree a (2 * ℓ) (by omega) (by omega) (walk_two hS w hT)

end LeanCH.BR.BRq4
