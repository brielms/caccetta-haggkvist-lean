import LeanCH.BR.BRq2Walk

/-!
# Theorem A (out-ball growth at out-degree two), Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq2_attempt_subagent.md`, §2.

`ball_growth`: if `D` has no closed walk of length `1..q` inside the finite vertex set `V` (`QFree D V q`) and every
vertex of `V` has at least two out-neighbours in `V` (`MinOut2 D V`), then for every `u ∈ V` and `k ≤ q` the out-ball
`ball D V u k` (vertices of `V` reachable from `u` within `k` steps inside `V`) has at least `2k+1` vertices.

Proof as in the paper: strong induction on `q`, inner induction on `k`; the inductive hypothesis is used only at
`q' = k` for the radius-`(k+1)` step (paper's `q' = k-1`), on the induced set `S ∖ {u}` (Case 1, Claim A.1) or on
`D* = fun a b => D a (if b = u then x else b)` over `S` (Case 2).
-/

namespace LeanCH.BR.BRq2

open Classical in
/-- Vertices of `W` reachable from `u` within `k` steps inside `W`. -/
noncomputable def ball (D : CH.Digraph) (W : Finset ℕ) (u k : ℕ) : Finset ℕ :=
  W.filter (fun v => ∃ j, j ≤ k ∧ Walk D W u v j)

/-- Every vertex of `W` has at least two out-neighbours in `W`. -/
def MinOut2 (D : CH.Digraph) (W : Finset ℕ) : Prop :=
  ∀ v ∈ W, 2 ≤ (W.filter (fun w => D v w = true)).card

variable {D : CH.Digraph} {W : Finset ℕ} {u k : ℕ}

theorem mem_ball {v : ℕ} : v ∈ ball D W u k ↔ v ∈ W ∧ ∃ j, j ≤ k ∧ Walk D W u v j := by
  simp only [ball, Finset.mem_filter]

theorem ball_subset : ball D W u k ⊆ W := fun _ hv => (mem_ball.mp hv).1

theorem self_mem_ball (hu : u ∈ W) : u ∈ ball D W u k :=
  mem_ball.mpr ⟨hu, 0, Nat.zero_le _, .refl u⟩

theorem ball_mono_radius {k' : ℕ} (h : k ≤ k') : ball D W u k ⊆ ball D W u k' := by
  intro v hv
  obtain ⟨hvW, j, hj, w⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨hvW, j, hj.trans h, w⟩

/-- Fact 1.2: out-neighbours of `B_k(u)` lie in `B_{k+1}(u)`. -/
theorem ball_step {y w : ℕ} (hy : y ∈ ball D W u k) (hw : w ∈ W) (hyw : D y w = true) :
    w ∈ ball D W u (k + 1) := by
  obtain ⟨_, j, hj, wk⟩ := mem_ball.mp hy
  exact mem_ball.mpr ⟨hw, j + 1, by omega, wk.snoc hw hyw⟩

/-- Fact 1.1(a): no vertex of `B_j(u)`, `j + 1 ≤ q`, is an in-neighbour of `u`. -/
theorem no_back_arc {q j y : ℕ} (hfree : QFree D W q) (hu : u ∈ W) (hy : y ∈ ball D W u j) (hj : j + 1 ≤ q) :
    ¬ D y u = true := by
  intro h
  obtain ⟨_, i, hi, w⟩ := mem_ball.mp hy
  exact hfree u (i + 1) (by omega) (by omega) (w.snoc hu h)

/-- Claim A.1: given the radius-`k` ball bound on `W`, a nonempty `(k+1)`-free `W` with min out `≥ 2` has at least
`2k+2` vertices. -/
theorem claimA1 (ih : ∀ z ∈ W, 2 * k + 1 ≤ (ball D W z k).card) (hfree : QFree D W (k + 1))
    (hmin : MinOut2 D W) (hne : W.Nonempty) : 2 * k + 2 ≤ W.card := by
  by_contra hlt
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz⟩ : (W.filter (fun w => D y w = true)).Nonempty := by
    rw [← Finset.card_pos]; have := hmin y hy; omega
  obtain ⟨hzW, hyz⟩ := Finset.mem_filter.mp hz
  have hball : ball D W z k = W :=
    Finset.eq_of_subset_of_card_le ball_subset (by have := ih z hzW; omega)
  have hyb : y ∈ ball D W z k := by rw [hball]; exact hy
  obtain ⟨_, j, hj, w⟩ := mem_ball.mp hyb
  exact hfree z (j + 1) (by omega) (by omega) (w.snoc hzW hyz)

/-- The inductive step of Theorem A, from radius `k ≥ 1` to radius `k + 1 ≤ q`. `IHq` is Theorem A at `q' = k`,
radius `k`, for every digraph and vertex set. -/
theorem growth_step {q : ℕ} (hk : 1 ≤ k) (hkq : k + 1 ≤ q)
    (IHq : ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U k → MinOut2 E U →
      ∀ z ∈ U, 2 * k + 1 ≤ (ball E U z k).card)
    {G : CH.Digraph} {V : Finset ℕ} (hfree : QFree G V q) (hmin : MinOut2 G V) (hu : u ∈ V)
    (hS : 2 * k + 1 ≤ (ball G V u k).card) : 2 * (k + 1) + 1 ≤ (ball G V u (k + 1)).card := by
  set S := ball G V u k with hSdef
  set B := ball G V u (k + 1) with hBdef
  by_contra hlt
  have hBle : B.card ≤ 2 * k + 2 := by omega
  have hSB : S ⊆ B := ball_mono_radius (by omega)
  have hSV : S ⊆ V := ball_subset
  have huS : u ∈ S := self_mem_ball hu
  -- (ii) no vertex of S heads u
  have back : ∀ y ∈ S, ¬ G y u = true := fun y hy => no_back_arc hfree hu hy (by omega)
  -- (iii) out-neighbours of S lie in B
  have fwd : ∀ y ∈ S, ∀ w ∈ V, G y w = true → w ∈ B := fun y hy w hw h => ball_step hy hw h
  have hEV : S.erase u ⊆ V := (Finset.erase_subset _ _).trans hSV
  by_cases hcase : B ⊆ S
  · -- Case 1: F = ∅; S ∖ {u} is out-closed, contradicting Claim A.1
    have hWcard : (S.erase u).card ≤ 2 * k + 1 := by
      have := Finset.card_erase_of_mem huS
      have := Finset.card_le_card hSB
      omega
    have hWmin : MinOut2 G (S.erase u) := by
      intro y hy
      have hyS : y ∈ S := Finset.mem_of_mem_erase hy
      refine (hmin y (hSV hyS)).trans (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨hwV, hyw⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hcase (fwd y hyS w hwV hyw)⟩, hyw⟩
      rintro rfl; exact back y hyS hyw
    have hWne : (S.erase u).Nonempty := by
      obtain ⟨w, hw⟩ : (V.filter (fun w => G u w = true)).Nonempty := by
        rw [← Finset.card_pos]; have := hmin u hu; omega
      obtain ⟨hwV, huw⟩ := Finset.mem_filter.mp hw
      refine ⟨w, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · rintro rfl; exact hfree w 1 le_rfl (by omega) (Walk.step hwV huw (.refl w))
      · exact ball_mono_radius (by omega : 0 + 1 ≤ k) (ball_step (self_mem_ball hu) hwV huw)
    have hWfree : QFree G (S.erase u) (k + 1) := (hfree.mono_bound hkq).mono_set hEV
    have := claimA1 (fun z hz => IHq G (S.erase u) (hWfree.mono_bound (by omega)) hWmin z hz)
      hWfree hWmin hWne
    omega
  · -- Case 2: F = {x}, |S| = 2k+1
    obtain ⟨x, hxB, hxS⟩ := Finset.not_subset.mp hcase
    have hxV : x ∈ V := ball_subset hxB
    have hBS : ∀ w ∈ B, w ∉ S → w = x := by
      intro w hw hwS
      have h1 : (B \ S).card ≤ 1 := by rw [Finset.card_sdiff_of_subset hSB]; omega
      exact Finset.card_le_one.mp h1 w (Finset.mem_sdiff.mpr ⟨hw, hwS⟩) x (Finset.mem_sdiff.mpr ⟨hxB, hxS⟩)
    have hScard : S.card = 2 * k + 1 := by
      have : S.card < B.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSB, fun h => hxS (h ▸ hxB)⟩)
      omega
    -- P ≠ ∅: a predecessor p ∈ S of x
    obtain ⟨p, hpS, hpx⟩ : ∃ p ∈ S, G p x = true := by
      obtain ⟨_, j, hj, w⟩ := mem_ball.mp hxB
      cases j with
      | zero => cases w; exact absurd huS hxS
      | succ j =>
        obtain ⟨p, wp, _, hpx⟩ := w.unsnoc
        refine ⟨p, mem_ball.mpr ⟨?_, j, by omega, wp⟩, hpx⟩
        rcases wp.end_mem_or with rfl | h
        · exact hu
        · exact h
    -- D*: the column of x moved onto u
    let Ds : CH.Digraph := fun a b => G a (if b = u then x else b)
    have Ds_ne : ∀ a b, b ≠ u → Ds a b = G a b := fun a b h => by simp [Ds, h]
    have Ds_u : ∀ a, Ds a u = G a x := fun a => by simp [Ds]
    -- (b) D*-walks that never enter u are G-walks
    have toG : ∀ {a b m : ℕ}, Walk Ds (S.erase u) a b m → Walk G V a b m := fun w =>
      (w.congr (fun a b hb => Ds_ne a b (Finset.ne_of_mem_erase hb))).mono hEV
    -- (c) at u: a closed D*-walk at u of length 1..k would put x within distance k of u
    have cu : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ¬ Walk Ds S u u ℓ := by
      intro ℓ h1 hℓ w
      obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
      obtain ⟨y, wy, _, hyu⟩ := w.unsnoc
      obtain ⟨m', hm', w'⟩ := wy.fromStart
      have g := (toG w').snoc hxV (by rw [← Ds_u]; exact hyu)
      exact hxS (mem_ball.mpr ⟨hxV, m' + 1, by omega, g⟩)
    -- (c) D* is k-free on S
    have Dfree : QFree Ds S k := by
      intro a ℓ h1 hℓ w
      rcases w.lastVisit u with h | ⟨m1, m2, _, hsum, w1, w2⟩
      · exact hfree a ℓ h1 (by omega) (toG h)
      · exact cu (m2 + m1) (by omega) (by omega) ((w2.mono (Finset.erase_subset _ _)).append w1)
    -- (a) D* has min out ≥ 2 on S
    have Dmin : MinOut2 Ds S := by
      intro y hy
      refine (hmin y (hSV hy)).trans
        (Finset.card_le_card_of_injOn (fun w => if w = x then u else w) ?_ ?_)
      · intro w hw
        obtain ⟨hwV, hyw⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ?_)
        by_cases hwx : w = x
        · subst hwx
          simp only [ite_true]
          exact ⟨huS, by rw [Ds_u]; exact hyw⟩
        · simp only [hwx, ite_false]
          have hwS : w ∈ S := by
            by_contra hwS; exact hwx (hBS w (fwd y hy w hwV hyw) hwS)
          have hwu : w ≠ u := by rintro rfl; exact back y hy hyw
          exact ⟨hwS, by rw [Ds_ne y w hwu]; exact hyw⟩
      · intro w1 hw1 w2 hw2 heq
        obtain ⟨_, hyw1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw1)
        obtain ⟨_, hyw2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw2)
        simp only at heq
        split_ifs at heq with h1 h2 h2
        · rw [h1, h2]
        · rw [← heq] at hyw2; exact absurd hyw2 (back y hy)
        · rw [heq] at hyw1; exact absurd hyw1 (back y hy)
        · exact heq
    -- an out-neighbour z ∈ S of p
    obtain ⟨z, hzS, hpz⟩ : ∃ z ∈ S, G p z = true := by
      have h2 := hmin p (hSV hpS)
      obtain ⟨z, hz⟩ : ((V.filter (fun w => G p w = true)).erase x).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.pred_card_le_card_erase (s := V.filter (fun w => G p w = true)) (a := x)
        omega
      obtain ⟨hzx, hz'⟩ := Finset.mem_erase.mp hz
      obtain ⟨hzV, hpz⟩ := Finset.mem_filter.mp hz'
      refine ⟨z, ?_, hpz⟩
      by_contra hzS; exact hzx (hBS z (fwd p hpS z hzV hpz) hzS)
    -- Theorem A at q' = k for D*: the D*-ball of z is all of S, so p is within k of z in D*
    have hball : ball Ds S z k = S :=
      Finset.eq_of_subset_of_card_le ball_subset (by have := IHq Ds S Dfree Dmin z hzS; omega)
    have hpb : p ∈ ball Ds S z k := by rw [hball]; exact hpS
    obtain ⟨_, j, hj, w⟩ := mem_ball.mp hpb
    rcases w.lastVisit u with h | ⟨m1, m2, h0, hsum, _, w2⟩
    · -- the D*-walk avoids u: a G-walk z ⇝ p, closed by p → z
      exact hfree z (j + 1) (by omega) (by omega) ((toG h).snoc (hSV hzS) hpz)
    · -- it passes through u: its tail u ⇝ p, closed by the new arc p → u, contradicts (c)
      exact cu (m2 + 1) (by omega) (by omega)
        ((w2.mono (Finset.erase_subset _ _)).snoc huS (by rw [Ds_u]; exact hpx))

/-- **Theorem A (out-ball growth, s = 2).** -/
theorem ball_growth : ∀ q, 1 ≤ q → ∀ (G : CH.Digraph) (V : Finset ℕ), QFree G V q → MinOut2 G V →
    ∀ u ∈ V, ∀ k, k ≤ q → 2 * k + 1 ≤ (ball G V u k).card := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q IH =>
  intro hq G V hfree hmin u hu k hk
  induction k with
  | zero => simpa using Finset.card_pos.mpr ⟨u, self_mem_ball (D := G) (k := 0) hu⟩
  | succ k ihk =>
    have ihk := ihk (by omega)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- radius one: u and its out-neighbours
      have hsub : insert u (V.filter (fun w => G u w = true)) ⊆ ball G V u (0 + 1) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact self_mem_ball hu
        · obtain ⟨hwV, huw⟩ := Finset.mem_filter.mp hw
          exact ball_step (self_mem_ball hu) hwV huw
      have hnot : u ∉ V.filter (fun w => G u w = true) := by
        intro h
        obtain ⟨_, huu⟩ := Finset.mem_filter.mp h
        exact hfree u 1 le_rfl hq (Walk.step hu huu (.refl u))
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      have := hmin u hu
      omega
    · exact growth_step hk1 hk
        (fun E U hfr hm z hz => IH k (by omega) hk1 E U hfr hm z hz k le_rfl) hfree hmin hu ihk

end LeanCH.BR.BRq2
