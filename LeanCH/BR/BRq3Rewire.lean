import LeanCH.BR.BRq3Top3
import LeanCH.BR.BRq3Ball4

/-!
# The rewiring step (Proposition 8) and Corollary 9, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq3_attempt_subagent.md`, §5.2.

Indexing: the paper's `k` is `k + 1` here. Let `D` be `q`-free with out-degree three on `W`, `u ∈ W`,
`K = N_{k+1}(u)`, `V = B_{k+1}(u) ∖ {u}`, and `rewire D u K a b = if a ∈ K then D u b else D a b` (every frontier
vertex copies `O(u)`).

* `rewire_walk` ((R2)/(R3) as one walk lemma): a rewired walk inside `V` either is a `D`-walk that does not start in
  `K` (or is empty), or splits as a rewired walk to some `c ∈ K` followed by a `D`-walk from `u` of length `≥ 1`.
* `rewire_outEq` (R1), `rewire_qfree` (R4): the rewired digraph has out-degree three on `V` and is `k`-free.
* `prop8` (Proposition 8): if `2 ≤ k`, `k + 2 ≤ q`, `TOP(k)` and `|B_k(u)| ≥ 3k+1`, then `|B_{k+1}(u)| ≥ 3k+4`.
  Cases `n_{k+1} = 0` (Lemma 1 and `TOP(k)` with the degree sum) and `n_{k+1} ∈ {1,2}` (π-step, a-step 1, a-step 2).
* `ball_of_top` (Corollary 9(a), general form): `∀ q, (∀ m, 3 ≤ m → m ≤ q - 2 → TOP m) → Ball q 3`.
* `ball53_of_top3` (Corollary 9(b)): `Ball(5,3)` from `TOP(3)`, without Lemma R (this file does not import
  `BRq3LemmaR` or `BRq3Ball5`).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

/-- The rewired digraph: every vertex of `K` copies the out-neighbourhood of `u`. -/
def rewire (D : CH.Digraph) (u : ℕ) (K : Finset ℕ) : CH.Digraph :=
  fun a b => if a ∈ K then D u b else D a b

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

theorem rewire_of_mem {K : Finset ℕ} {a b : ℕ} (ha : a ∈ K) : rewire D u K a b = D u b := by
  simp [rewire, ha]

theorem rewire_of_not_mem {K : Finset ℕ} {a b : ℕ} (ha : a ∉ K) : rewire D u K a b = D a b := by
  simp [rewire, ha]

/-- **(R2)/(R3).** A rewired walk inside `V ⊆ W` is either a `D`-walk (not starting in `K` unless empty), or a
rewired walk to some `c ∈ K` followed by a `D`-walk from `u` of length `≥ 1`. -/
theorem rewire_walk {K V : Finset ℕ} (hVW : V ⊆ W) {a v m : ℕ} (w : Walk (rewire D u K) V a v m) :
    (Walk D W a v m ∧ (a ∈ K → m = 0)) ∨
      ∃ c ∈ K, ∃ m1 m2, m1 + m2 = m ∧ 1 ≤ m2 ∧ Walk (rewire D u K) V a c m1 ∧ Walk D W u v m2 := by
  induction w with
  | refl a => exact Or.inl ⟨.refl a, fun _ => rfl⟩
  | @step a b e k hb hab _ ih =>
    rcases ih with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
    · by_cases ha : a ∈ K
      · rw [rewire_of_mem ha] at hab
        exact Or.inr ⟨a, ha, 0, k + 1, by omega, by omega, .refl a, .step (hVW hb) hab h⟩
      · rw [rewire_of_not_mem ha] at hab
        exact Or.inl ⟨.step (hVW hb) hab h, fun h' => absurd h' ha⟩
    · exact Or.inr ⟨c, hc, m1 + 1, m2, by omega, h1, .step hb hab w1, w2⟩

/-- A rewired walk of length `≤ j + 1` from `z ∉ K` to `p` that passes through `K` puts `p` in `B_j(u)`. -/
theorem rewire_far {K V : Finset ℕ} {z p m j c m1 m2 : ℕ} (hz : z ∉ K) (hc : c ∈ K) (hsum : m1 + m2 = m)
    (hm : m ≤ j + 1) (w1 : Walk (rewire D u K) V z c m1) (w2 : Walk D W u p m2) (hp : p ∈ W) :
    p ∈ ball D W u j := by
  have hm1 : m1 ≠ 0 := by
    rintro rfl
    rw [walk_zero w1] at hz
    exact hz hc
  exact mem_ball_of_walk w2 (by omega) hp

/-- **(R1).** The rewired digraph has out-degree exactly three on `V = B_{k+1} ∖ {u}`. -/
theorem rewire_outEq {q k : ℕ} (hkq : k + 1 ≤ q) (hfree : QFree D W q) (hout : OutEq 3 D W) (hu : u ∈ W) :
    OutEq 3 (rewire D u (ball D W u (k + 1) \ ball D W u k)) ((ball D W u (k + 1)).erase u) := by
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

/-- **(R4).** The rewired digraph is `k`-free on `V = B_{k+1} ∖ {u}`. -/
theorem rewire_qfree {q k : ℕ} (hkq : k ≤ q) (hfree : QFree D W q) :
    QFree (rewire D u (ball D W u (k + 1) \ ball D W u k)) ((ball D W u (k + 1)).erase u) k := by
  intro a ℓ h1 hℓ w
  have hVW : (ball D W u (k + 1)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
  · exact hfree a ℓ h1 (by omega) h
  · have hck : c ∉ ball D W u k := (Finset.mem_sdiff.mp hc).2
    have hcW : c ∈ W := ball_subset (Finset.mem_sdiff.mp hc).1
    rcases rewire_walk hVW w1 with ⟨h', _⟩ | ⟨c', _, m1', m2', hsum', _, _, w2'⟩
    · exact hck (mem_ball_of_walk (w2.append h') (by omega) hcW)
    · exact hck (mem_ball_of_walk w2' (by omega) hcW)

/-- **Proposition 8 (rewiring step).** If `2 ≤ k`, `k + 2 ≤ q`, `D` is `q`-free with out-degree three, `TOP(k)`
holds and `|B_k(u)| ≥ 3k+1`, then `|B_{k+1}(u)| ≥ 3(k+1)+1`. -/
theorem prop8 {q k : ℕ} (hk : 2 ≤ k) (hkq : k + 2 ≤ q) (htop : TOP k) (hfree : QFree D W q)
    (hout : OutEq 3 D W) (hu : u ∈ W) (hb : 3 * k + 1 ≤ (ball D W u k).card) :
    3 * (k + 1) + 1 ≤ (ball D W u (k + 1)).card := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 + 1 = j + 3 by omega]
  by_contra hlt
  have hsub : ball D W u (j + 2) ⊆ ball D W u (j + 3) := ball_mono_radius (by omega)
  have eK := Finset.card_sdiff_add_card_eq_card hsub
  -- `n_{k+1} = 0`: Lemma 1 and `TOP(k)` with the degree sum
  by_cases c0 : (ball D W u (j + 3)).card ≤ (ball D W u (j + 2)).card
  · obtain ⟨hout', hne⟩ := closed_outEq (q := q) (k := j + 2) (by omega) (by omega) hfree hout hu c0
    have hUW : (ball D W u (j + 2)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hfE : QFree D ((ball D W u (j + 2)).erase u) (j + 3) := (hfree.mono_bound (by omega)).mono_set hUW
    have hc := card_ge_of_ball (q := j + 3) (s := 3) (b := 3 * (j + 2) + 1) (by omega) hfE
      (fun y hy => (hout' y hy).ge)
      (fun z hz => by
        rw [show j + 3 - 1 = j + 2 by omega]
        exact htop D _ (hfE.mono_bound (by omega)) hout' z hz) hne
    have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := j + 2) hu)
    omega
  -- `n_{k+1} ∈ {1, 2}`: rewire
  have hKcard : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ 2 := by omega
  have hVW : (ball D W u (j + 3)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hVcard : ((ball D W u (j + 3)).erase u).card ≤ 3 * (j + 2) + 2 := by
    rw [Finset.card_erase_of_mem (self_mem_ball hu)]; omega
  have hDout : OutEq 3 (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) :=
    rewire_outEq (q := q) (k := j + 2) (by omega) hfree hout hu
  have hDfree : QFree (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) (j + 2) :=
    rewire_qfree (k := j + 2) (by omega) hfree
  have hTOP := htop _ _ hDfree hDout
  have huj : ∀ i, u ∈ ball D W u i := fun i => self_mem_ball hu
  -- out-neighbours of `B_{k}` stay in `V`
  have toV : ∀ p z, p ∈ ball D W u (j + 2) → D p z = true → z ∈ W → z ∈ (ball D W u (j + 3)).erase u := by
    intro p z hp hpz hzW
    refine Finset.mem_erase.mpr ⟨?_, ball_step hp hzW hpz⟩
    intro hzu
    rw [hzu] at hpz
    exact no_back_arc hfree hu hp (by omega) hpz
  -- π-step: for `p ∈ N_k` and `p → z`, `z ∉ K`, every vertex of `V` other than `p` is within `k` of `z`
  have pi : ∀ p z, p ∈ ball D W u (j + 2) → p ∉ ball D W u (j + 1) → D p z = true → z ∈ W →
      z ∉ ball D W u (j + 3) \ ball D W u (j + 2) →
      ∀ v ∈ (ball D W u (j + 3)).erase u, v ≠ p →
        v ∈ ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2) := by
    intro p z hp hp1 hpz hzW hzK v hv hvp
    have hzV := toV p z hp hpz hzW
    have hpV : p ∈ (ball D W u (j + 3)).erase u := by
      refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) hp⟩
      intro hpu; rw [hpu] at hp1; exact hp1 (huj _)
    have hnot : p ∉ ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2) := by
      intro hpb
      obtain ⟨_, m, hm, w⟩ := mem_ball.mp hpb
      rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
      · exact hfree z (m + 1) (by omega) (by omega) (h.snoc hzW hpz)
      · exact hp1 (rewire_far hzK hc hsum (by omega) w1 w2 (ball_subset hp))
    have hsub' : ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2) ⊆
        ((ball D W u (j + 3)).erase u).erase p := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, ball_subset hx⟩
      intro hxp; rw [hxp] at hx; exact hnot hx
    have heq := Finset.eq_of_subset_of_card_le hsub' (by
      rw [Finset.card_erase_of_mem hpV]
      have := hTOP z hzV
      omega)
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hvp, hv⟩
  -- a frontier vertex `c0 ∈ K` and its parent `p ∈ N_k`
  obtain ⟨c0, hc0⟩ : (ball D W u (j + 3) \ ball D W u (j + 2)).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨hc03, hc02⟩ := Finset.mem_sdiff.mp hc0
  obtain ⟨p, hp, hpc0⟩ := ball_succ_pred hu hc03 hc02
  have hp1 : p ∉ ball D W u (j + 1) := fun h => hc02 (ball_step h (ball_subset hc03) hpc0)
  have hpW : p ∈ W := ball_subset hp
  -- an out-neighbour outside `K` of a vertex of `B_k`
  have exOut : ∀ y ∈ W, ∃ z ∈ W, D y z = true ∧ z ∉ ball D W u (j + 3) \ ball D W u (j + 2) := by
    intro y hy
    have h1 := Finset.le_card_sdiff (ball D W u (j + 3) \ ball D W u (j + 2)) (outN D W y)
    rw [hout y hy] at h1
    obtain ⟨z, hz⟩ : (outN D W y \ (ball D W u (j + 3) \ ball D W u (j + 2))).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
    exact ⟨z, (mem_outN.mp hz1).1, (mem_outN.mp hz1).2, hz2⟩
  obtain ⟨z, hzW, hpz, hzK⟩ := exOut p hpW
  have hzV := toV p z hp hpz hzW
  -- a-step 1: the parent `a ∈ N_{k-1}` of `p` forces `z → c1 ∈ K`
  obtain ⟨a, ha, hap⟩ := ball_succ_pred hu hp hp1
  have haj : a ∉ ball D W u j := fun h => hp1 (ball_step h hpW hap)
  have haW : a ∈ W := ball_subset ha
  have haV : a ∈ (ball D W u (j + 3)).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) ha⟩
    intro hau; rw [hau] at haj; exact haj (huj _)
  have hap' : a ≠ p := by intro h; rw [h] at ha; exact hp1 ha
  obtain ⟨c1, hc1, hzc1⟩ : ∃ c1 ∈ ball D W u (j + 3) \ ball D W u (j + 2), D z c1 = true := by
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp (pi p z hp hp1 hpz hzW hzK a haV hap')
    rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
    · exact absurd ((h.snoc hpW hap).snoc hzW hpz) (hfree z (m + 1 + 1) (by omega) (by omega))
    · have hm2 : j + 1 ≤ m2 := by
        by_contra hlt2
        exact haj (mem_ball_of_walk w2 (by omega) haW)
      have hm1 : m1 = 1 := by
        have : m1 ≠ 0 := by
          rintro rfl
          rw [walk_zero w1] at hzK
          exact hzK hc
        omega
      subst hm1
      obtain ⟨_, hzc⟩ := walk_one w1
      rw [rewire_of_not_mem hzK] at hzc
      exact ⟨c, hc, hzc⟩
  -- `z ∈ N_k`
  have hzk : z ∈ ball D W u (j + 2) := by
    by_contra h
    exact hzK (Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hzV).2, h⟩)
  have hz1 : z ∉ ball D W u (j + 1) :=
    fun h => (Finset.mem_sdiff.mp hc1).2 (ball_step h (ball_subset (Finset.mem_sdiff.mp hc1).1) hzc1)
  -- a-step 2: `z → z'` with `z' ∉ K`; then `p` is within `k` of `z'`
  obtain ⟨z', hz'W, hzz', hz'K⟩ := exOut z hzW
  have hpz' : p ≠ z := by intro h; rw [h] at hpz; exact loopfree hfree (by omega) hzW hpz
  have hpV : p ∈ (ball D W u (j + 3)).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) hp⟩
    intro hpu; rw [hpu] at hp1; exact hp1 (huj _)
  obtain ⟨_, m, hm, w⟩ := mem_ball.mp (pi z z' hzk hz1 hzz' hz'W hz'K p hpV hpz')
  rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
  · exact hfree z' (m + 1 + 1) (by omega) (by omega) ((h.snoc hzW hpz).snoc hz'W hzz')
  · exact hp1 (rewire_far hz'K hc hsum (by omega) w1 w2 hpW)

/-- **Corollary 9(a), general form.** `TOP(3), …, TOP(q-2)` imply `Ball(q,3)`. -/
theorem ball_of_top : ∀ q, (∀ m, 3 ≤ m → m ≤ q - 2 → TOP m) → Ball q 3 := by
  intro q htop D W hfree hout u hu
  rcases Nat.lt_or_ge q 5 with hq | hq
  · -- `q ≤ 4`: no `TOP` needed
    rcases q with _ | _ | _ | _ | _ | q
    · change 1 ≤ (ball D W u 0).card
      exact Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    · change 1 ≤ (ball D W u 0).card
      exact Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    · change 4 ≤ (ball D W u 1).card
      exact (card_ball_one (hfree.mono_bound (by omega)) hout hu).ge
    · change 7 ≤ (ball D W u 2).card
      exact ball_three_three hfree hout hu
    · change 10 ≤ (ball D W u 3).card
      exact ball43 hfree hout hu
    · omega
  · obtain ⟨r, rfl⟩ : ∃ r, q = r + 5 := ⟨q - 5, by omega⟩
    have step : ∀ i, i ≤ r + 1 → 3 * (i + 3) + 1 ≤ (ball D W u (i + 3)).card := by
      intro i
      induction i with
      | zero =>
        intro _
        exact htop 3 le_rfl (by omega) D W (hfree.mono_bound (by omega)) hout u hu
      | succ i ih =>
        intro hi
        have := prop8 (q := r + 5) (k := i + 3) (by omega) (by omega)
          (htop (i + 3) (by omega) (by omega)) hfree hout hu (ih (by omega))
        rw [show i + 1 + 3 = i + 3 + 1 by omega]
        exact this
    have := step (r + 1) le_rfl
    rw [show r + 5 - 1 = r + 1 + 3 by omega]
    omega

/-- **Corollary 9(d).** `TOP(3), …, TOP(m)` imply `Ball(m+2,3)`. -/
theorem ball_of_top_le {m : ℕ} (htop : ∀ i, 3 ≤ i → i ≤ m → TOP i) : Ball (m + 2) 3 :=
  ball_of_top (m + 2) (fun i h1 h2 => htop i h1 (by omega))

/-- **Corollary 9(b).** `Ball(5,3)` from `TOP(3)` alone (a second proof, without Lemma R). -/
theorem ball53_of_top3 : Ball 5 3 :=
  ball_of_top 5 (fun m h1 h2 => by
    obtain rfl : m = 3 := by omega
    exact top3_TOP)

/-- `Ball(5,3)` from `TOP(3)`, stated pointwise. -/
theorem ball53' (hfree : QFree D W 5) (hout : OutEq 3 D W) (hu : u ∈ W) : 13 ≤ (ball D W u 4).card :=
  ball53_of_top3 D W hfree hout u hu

/-- `BR(5,3)` again, through the rewiring route. -/
theorem br_five_three' : Compose.Boundary.BoundaryRegular 5 3 :=
  br_of_ball (by omega) ball53_of_top3

end LeanCH.BR.BRq3
