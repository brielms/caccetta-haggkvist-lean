import checkpoints.shen_extension.LastArcHeadDeposit

/-!
# The spread over `L ∪ {v}`, with the cycle deposit eliminated (20 November 2026)

Keep one old dual `p` fixed. Deposit `C-1` on the common head `v` and the same amount `a ≥ 0` on every vertex
of the alternative cycle `L`, then normalize once by `C + (q+1)a`. Column `j` pays exactly when

  `demand j ≤ a * coeff j`,

where `demand j = val j - C + [j=v](C-1) + q[v→j](C-1)` and `coeff j = q+1 - [j∈L] - q·h(j)`. Here `h(j)` is the
number of G-parents of `j` on `L`.

* On `L`, `h = 1`, so `coeff = 0` and `a` cancels.
* Off `L`, `coeff = q+1-q·h`. Columns with `h ≤ 1` give lower bounds on `a`, columns with `h ≥ 2` give upper
  bounds.

`eliminate` removes `a` exactly. `spread_obstruction` says what an empty interval means in labelled old
columns:

* **E1** an expensive G-head of `v` on `L`. With the merged orientation it is the successor of `t`, and
  `insert v (L.erase t)` is a cycle (`LastArcHeadDeposit.blocker_location`).
* **E2** an expensive G-head `k` of `v` off `L` with at least two G-parents on `L`.
* **E3** an expensive G-head `j` of `v` off `L` with at most one G-parent on `L` (it demands deposit), and a
  column `k` off `L` with at least two (it forbids deposit), such that
  `demand k · (q+1-q·h j) > demand j · (q+1-q·h k)`.

Off `L` every value equals the old value in `F`. The forbidding column may be `v` itself. Its demand is
`col_F v - 1`, so whenever `col_F v = 1` it caps `a` at `0`.
-/

namespace LeanCH.BR.Closure.CycleSpread
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier
open ShenCycleSuccessor MarkedCyclePeeling

/-! ### Eliminating one nonnegative variable -/

/-- **Fourier–Motzkin for one variable `a ≥ 0`.** -/
theorem eliminate {J : Finset ℕ} (b c : ℕ → ℝ) :
    (∃ a : ℝ, 0 ≤ a ∧ ∀ j ∈ J, b j ≤ a * c j) ↔
      (∀ j ∈ J, c j ≤ 0 → b j ≤ 0) ∧
        ∀ j ∈ J, ∀ k ∈ J, 0 < c j → c k < 0 → b k * c j ≤ b j * c k := by
  classical
  constructor
  · rintro ⟨a, ha, all⟩
    refine ⟨fun j jm cj => ?_, fun j jm k km cj ck => ?_⟩
    · have h := all j jm
      have := mul_nonneg ha (neg_nonneg.mpr cj)
      nlinarith
    · have h1 := all j jm
      have h2 := all k km
      have e1 := mul_le_mul_of_nonneg_right h2 cj.le
      have e2 := mul_le_mul_of_nonpos_right h1 ck.le
      have e3 : a * c k * c j = a * c j * c k := by ring
      linarith
  · rintro ⟨sign, pair⟩
    by_cases some : (J.filter (fun j => 0 < c j)).Nonempty
    · obtain ⟨m, mm, top⟩ :=
        (J.filter (fun j => 0 < c j)).exists_max_image (fun j => b j / c j) some
      obtain ⟨mJ, cm⟩ := mem_filter.mp mm
      refine ⟨max 0 (b m / c m), le_max_left _ _, fun j jm => ?_⟩
      rcases lt_trichotomy (c j) 0 with neg | zero | posit
      · have hb := sign j jm neg.le
        have hp := pair m mJ j jm cm neg
        have hx : b j ≤ b m / c m * c j := by
          rw [div_mul_eq_mul_div, le_div_iff₀ cm]
          linarith
        rcases le_total 0 (b m / c m) with h | h
        · rw [max_eq_right h]
          exact hx
        · rw [max_eq_left h, zero_mul]
          exact hb
      · rw [zero, mul_zero]
        exact sign j jm zero.le
      · have h1 : b j / c j ≤ b m / c m := top j (mem_filter.mpr ⟨jm, posit⟩)
        have h2 : b j / c j ≤ max 0 (b m / c m) := h1.trans (le_max_right _ _)
        rwa [div_le_iff₀ posit] at h2
    · refine ⟨0, le_rfl, fun j jm => ?_⟩
      have : ¬ 0 < c j := fun h => some ⟨j, mem_filter.mpr ⟨jm, h⟩⟩
      rw [zero_mul]
      exact sign j jm (not_lt.mp this)

/-! ### Deposits are linear -/

/-- Add a deposit vector `δ`, then divide by `s`. -/
noncomputable def deposit (p δ : ℕ → ℝ) (s : ℝ) (i : ℕ) : ℝ := (p i + δ i) / s

theorem col_deposit {D : CH.Digraph} {q : ℕ} {V : Finset ℕ} (p δ : ℕ → ℝ) (s : ℝ) (j : ℕ) :
    realCol q D V (deposit p δ s) j = (realCol q D V p j + realCol q D V δ j) / s := by
  have inw : realInW D V (deposit p δ s) j = (realInW D V p j + realInW D V δ j) / s := by
    unfold realInW deposit
    rw [← sum_add_distrib, sum_div]
    apply sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [realCol, inw, realCol, realCol, deposit]
  ring

/-- The deposit `u` on `v` and `a` on every vertex of `L`. -/
noncomputable def bump (v : ℕ) (u : ℝ) (L : Finset ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  (if i = v then u else 0) + (if i ∈ L then a else 0)

theorem col_bump {D : CH.Digraph} {q : ℕ} {V L : Finset ℕ} {v : ℕ} (vv : v ∈ V) (ls : L ⊆ V)
    (u a : ℝ) (j : ℕ) :
    realCol q D V (bump v u L a) j =
      (if j = v then u else 0) + (if j ∈ L then a else 0) +
        q * ((if D v j = true then u else 0) + (inN D L j).card * a) := by
  classical
  have pts : ∀ i ∈ V, (if D i j = true then bump v u L a i else 0) =
      (if i = v then (if D v j = true then u else 0) else 0) +
        (if i ∈ inN D L j then a else 0) := by
    intro i _
    by_cases e : i = v
    · subst e
      by_cases arc : D i j = true <;> by_cases il : i ∈ L <;> simp [bump, arc, il, mem_inN]
    · by_cases arc : D i j = true <;> by_cases il : i ∈ L <;> simp [bump, arc, il, e, mem_inN]
  have sub : inN D L j ⊆ V := fun x hx => ls (mem_inN.mp hx).1
  have inw : realInW D V (bump v u L a) j =
      (if D v j = true then u else 0) + (inN D L j).card * a := by
    unfold realInW
    rw [sum_congr rfl pts, sum_add_distrib, sum_ite_eq', if_pos vv, sum_ite_mem,
      inter_eq_right.mpr sub, sum_const, nsmul_eq_mul]
  rw [realCol, inw]
  simp only [bump]

theorem mass_bump {V L : Finset ℕ} {v : ℕ} (vv : v ∈ V) (ls : L ⊆ V) (u a : ℝ) :
    realMass V (bump v u L a) = u + L.card * a := by
  classical
  unfold realMass bump
  rw [sum_add_distrib, sum_ite_eq', if_pos vv, sum_ite_mem, inter_eq_right.mpr ls, sum_const,
    nsmul_eq_mul]

/-! ### The spread over `L ∪ {v}` -/

/-- Demand of column `j` once `v` carries `C-1`. -/
noncomputable def demand (q : ℕ) (G : CH.Digraph) (V : Finset ℕ) (p : ℕ → ℝ) (C : ℝ)
    (v j : ℕ) : ℝ :=
  realCol q G V p j - C + (if j = v then C - 1 else 0) + q * (if G v j = true then C - 1 else 0)

/-- Coefficient of the cycle deposit `a` in column `j`. -/
noncomputable def coeff (q : ℕ) (G : CH.Digraph) (L : Finset ℕ) (j : ℕ) : ℝ :=
  q + 1 - (if j ∈ L then 1 else 0) - q * (inN G L j).card

/-- The arcs of `L` belong to the merged graph. -/
theorem cycle_arc {D : CH.Digraph} {F : Family} {L : Finset ℕ} {x y : ℕ} (xl : x ∈ L) (yl : y ∈ L)
    (arc : D x y = true) : graph D (insert L F) x y = true :=
  active.mpr ⟨L, mem_col.mpr ⟨mem_insert_self L F, xl, yl, arc⟩⟩

/-- Every vertex of `L` has exactly one G-parent on `L`, so the cycle deposit cancels there. -/
theorem coeff_on_L {q n F L} (X : Model q n) (cy : Cycle X.D X.V q L) {j : ℕ} (jl : j ∈ L) :
    coeff q (graph X.D (insert L F)) L j = 0 := by
  classical
  have eq : inN (graph X.D (insert L F)) L j = inN X.D L j := by
    ext x
    simp only [mem_inN]
    exact ⟨fun ⟨xl, e⟩ => ⟨xl, CrossValueOmissions.selected_sub e⟩,
      fun ⟨xl, e⟩ => ⟨xl, cycle_arc xl jl e⟩⟩
  have one : (inN X.D L j).card = 1 := cy.incoming j jl
  simp [coeff, jl, eq, one]

/-- **Per-column test.** -/
theorem column_iff {q : ℕ} {G : CH.Digraph} {V L : Finset ℕ} {v : ℕ} (vv : v ∈ V) (ls : L ⊆ V)
    (size : L.card = q + 1) (p : ℕ → ℝ) {C a : ℝ} (high : 1 ≤ C) (ha : 0 ≤ a) (j : ℕ) :
    realCol q G V (deposit p (bump v (C - 1) L a) (C + (q + 1) * a)) j ≤ 1 ↔
      demand q G V p C v j ≤ a * coeff q G L j := by
  have den : 0 < C + ((q : ℝ) + 1) * a := by
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1) ha
    linarith
  rw [col_deposit, col_bump vv ls, div_le_iff₀ den, one_mul]
  have key : (C + ((q : ℝ) + 1) * a) - (realCol q G V p j + ((if j = v then C - 1 else 0) +
      (if j ∈ L then a else 0) + q * ((if G v j = true then C - 1 else 0) +
        (inN G L j).card * a))) = a * coeff q G L j - demand q G V p C v j := by
    unfold coeff demand
    split_ifs <;> ring
  constructor <;> intro h <;> linarith

/-- **The spread over `L ∪ {v}` with `a` eliminated.** -/
theorem cycle_spread_iff {q n F L v} (X : Model q n) (cy : Cycle X.D X.V q L) (vv : v ∈ X.V)
    (p : ℕ → ℝ) (old : RealDual q (graph X.D F) X.V 1 p) {C : ℝ} (high : 1 ≤ C) :
    (∃ a : ℝ, 0 ≤ a ∧
        RealDual q (graph X.D (insert L F)) X.V 1
          (deposit p (bump v (C - 1) L a) (C + (q + 1) * a))) ↔
      (∀ j ∈ X.V, coeff q (graph X.D (insert L F)) L j ≤ 0 →
          demand q (graph X.D (insert L F)) X.V p C v j ≤ 0) ∧
        ∀ j ∈ X.V, ∀ k ∈ X.V, 0 < coeff q (graph X.D (insert L F)) L j →
          coeff q (graph X.D (insert L F)) L k < 0 →
          demand q (graph X.D (insert L F)) X.V p C v k * coeff q (graph X.D (insert L F)) L j ≤
            demand q (graph X.D (insert L F)) X.V p C v j * coeff q (graph X.D (insert L F)) L k := by
  classical
  rw [← eliminate]
  have size := cy.size
  have ls := cy.sub
  constructor
  · rintro ⟨a, ha, dual⟩
    exact ⟨a, ha, fun j jv => (column_iff vv ls size p high ha j).mp (dual.columns j jv)⟩
  · rintro ⟨a, ha, bills⟩
    refine ⟨a, ha, ⟨fun i iv => ?_, ?_, fun j jv => (column_iff vv ls size p high ha j).mpr
      (bills j jv)⟩⟩
    · have den : 0 < C + ((q : ℝ) + 1) * a := by
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1) ha
        linarith
      unfold deposit bump
      apply div_nonneg _ den.le
      have := old.nonneg i iv
      have c1 : 0 ≤ C - 1 := sub_nonneg.mpr high
      split_ifs <;> linarith
    · have den : C + ((q : ℝ) + 1) * a ≠ 0 := by
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1) ha
        linarith
      unfold realMass deposit
      rw [← sum_div, sum_add_distrib, show (∑ i ∈ X.V, p i) = 1 from old.normalized,
        show (∑ i ∈ X.V, bump v (C - 1) L a i) = (C - 1) + L.card * a from mass_bump vv ls _ _,
        size]
      push_cast
      rw [div_eq_one_iff_eq den]
      ring

/-! ### Labelled obstructions -/

/-- Off the cycle, columns keep their values in the old family. -/
theorem exterior_old {q n F L} (X : Model q n) (cy : Cycle X.D X.V q L) (p : ℕ → ℝ) {j : ℕ}
    (jv : j ∈ X.V) (jl : j ∉ L) :
    realCol q (graph X.D (insert L F)) X.V p j = realCol q (graph X.D F) X.V p j :=
  (SharedArcBarrier.column (q := q) (F := F) cy p jv).1 (fun m => jl (mem_filter.mp m).2.1)

/-- **What an empty interval means.** If no cycle deposit `a ≥ 0` pays, one of E1, E2, E3 holds. All three
name G-heads of `v` that are expensive. In E2 and E3 every named column is off `L` and has its old value. -/
theorem spread_obstruction {q n F L v} (X : Model q n) (hq : 2 ≤ q) (cy : Cycle X.D X.V q L)
    (vv : v ∈ X.V) (vL : v ∉ L) (p : ℕ → ℝ) (old : RealDual q (graph X.D F) X.V 1 p)
    {C : ℝ} (high : 1 ≤ C) (cap : ∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C)
    (none : ¬ ∃ a : ℝ, 0 ≤ a ∧ RealDual q (graph X.D (insert L F)) X.V 1
      (deposit p (bump v (C - 1) L a) (C + (q + 1) * a))) :
    let G := graph X.D (insert L F)
    let val := realCol q G X.V p
    -- E1: the interior successor blocks
    (∃ s ∈ L, G v s = true ∧ 1 < val s + ((q : ℝ) - 1) * (C - 1)) ∨
    -- E2: an expensive head of `v` with two parents on `L`
    (∃ k ∈ X.V, k ∉ L ∧ 2 ≤ (inN G L k).card ∧ G v k = true ∧
        1 < val k + ((q : ℝ) - 1) * (C - 1) ∧ val k = realCol q (graph X.D F) X.V p k) ∨
    -- E3: a demanding head `j` of `v` against a forbidding column `k`
    (∃ j ∈ X.V, j ∉ L ∧ (inN G L j).card ≤ 1 ∧ G v j = true ∧
        1 < val j + ((q : ℝ) - 1) * (C - 1) ∧ val j = realCol q (graph X.D F) X.V p j ∧
      ∃ k ∈ X.V, k ∉ L ∧ 2 ≤ (inN G L k).card ∧ val k = realCol q (graph X.D F) X.V p k ∧
        demand q G X.V p C v k ≤ 0 ∧
        demand q G X.V p C v j * (q * (inN G L k).card - q - 1) >
          - demand q G X.V p C v k * (q + 1 - q * (inN G L j).card)) := by
  classical
  intro G val
  have vpaid : val v ≤ 1 := by
    show realCol q (graph X.D (insert L F)) X.V p v ≤ 1
    rw [exterior_old (F := F) X cy p vv vL]
    exact old.columns v vv
  have q2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  -- demand of `v` is never positive
  have dv : demand q G X.V p C v v ≤ 0 := by
    simp only [demand, ↓reduceIte]
    have loop : G v v = false := Bool.eq_false_iff.mpr
      (fun e => loopfree X.free (by omega) vv (CrossValueOmissions.selected_sub e))
    simp only [loop, Bool.false_eq_true, ↓reduceIte]
    linarith
  -- a positive demand names an expensive head of `v`
  have head {j : ℕ} (jv : j ∈ X.V) (pos : 0 < demand q G X.V p C v j) :
      j ≠ v ∧ G v j = true ∧ 1 < val j + ((q : ℝ) - 1) * (C - 1) := by
    have jv' : j ≠ v := fun e => by subst e; linarith
    have cj := cap j jv
    by_cases arc : G v j = true
    · refine ⟨jv', arc, ?_⟩
      simp only [demand, jv', arc, ↓reduceIte] at pos
      linarith
    · simp only [demand, jv', ↓reduceIte, arc, Bool.false_eq_true] at pos
      linarith
  have offL {j : ℕ} (jl : j ∉ L) : coeff q G L j = q + 1 - q * (inN G L j).card := by
    simp [coeff, jl]
  have spread := (cycle_spread_iff X cy vv p old high).not.mp none
  rw [not_and_or] at spread
  rcases spread with first | second
  · push Not at first
    obtain ⟨j, jv, cj, dj⟩ := first
    obtain ⟨_, arc, exp⟩ := head jv dj
    by_cases jl : j ∈ L
    · exact Or.inl ⟨j, jl, arc, exp⟩
    · right; left
      have two : 2 ≤ (inN G L j).card := by
        by_contra! few
        have : ((inN G L j).card : ℝ) ≤ 1 := by exact_mod_cast (show (inN G L j).card ≤ 1 by omega)
        rw [offL jl] at cj
        nlinarith
      exact ⟨j, jv, jl, two, arc, exp, exterior_old X cy p jv jl⟩
  · push Not at second
    obtain ⟨j, jv, k, kv, cj, ck, bad⟩ := second
    have jl : j ∉ L := fun m => by rw [coeff_on_L X cy m] at cj; exact lt_irrefl _ cj
    have kl : k ∉ L := fun m => by rw [coeff_on_L X cy m] at ck; exact lt_irrefl _ ck
    rw [offL jl] at cj bad
    rw [offL kl] at ck bad
    have hj : (inN G L j).card ≤ 1 := by
      by_contra! many
      have : (2 : ℝ) ≤ (inN G L j).card := by exact_mod_cast many
      nlinarith
    have hk : 2 ≤ (inN G L k).card := by
      by_contra! few
      have : ((inN G L k).card : ℝ) ≤ 1 := by exact_mod_cast (show (inN G L k).card ≤ 1 by omega)
      nlinarith
    by_cases dk : 0 < demand q G X.V p C v k
    · obtain ⟨_, arc, exp⟩ := head kv dk
      exact Or.inr (Or.inl ⟨k, kv, kl, hk, arc, exp, exterior_old X cy p kv kl⟩)
    · push Not at dk
      have dj : 0 < demand q G X.V p C v j := by
        by_contra! dj
        have e1 : demand q G X.V p C v k * (q + 1 - q * (inN G L j).card) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg dk cj.le
        have e2 : 0 ≤ demand q G X.V p C v j * (q + 1 - q * (inN G L k).card) :=
          mul_nonneg_of_nonpos_of_nonpos dj ck.le
        linarith
      obtain ⟨_, arc, exp⟩ := head jv dj
      refine Or.inr (Or.inr ⟨j, jv, jl, hj, arc, exp, exterior_old X cy p jv jl,
        k, kv, kl, hk, exterior_old X cy p kv kl, dk, ?_⟩)
      nlinarith

/-- **How tight the forbidding column must be.** In E3 the demanding head `j` is off `L`, so its value is an
old value at most `1` and its demand is at most `(q-1)(C-1)`. The forbidding column's slack `-demand k` is
therefore below `(q-1)(C-1)(q·h k - q - 1)/(q+1-q·h j)`. When `k = v` this slack is `1 - col_F v`, so `v`'s old
column is within that amount of tight. -/
theorem forbidder_slack {q n F L v} (X : Model q n) (hq : 2 ≤ q) (p : ℕ → ℝ)
    (old : RealDual q (graph X.D F) X.V 1 p) {C : ℝ} {j k : ℕ} (jv : j ∈ X.V) (jvne : j ≠ v)
    (arc : graph X.D (insert L F) v j = true)
    (oldj : realCol q (graph X.D (insert L F)) X.V p j = realCol q (graph X.D F) X.V p j)
    (hk : 2 ≤ (inN (graph X.D (insert L F)) L k).card)
    (pair : demand q (graph X.D (insert L F)) X.V p C v j *
        (q * (inN (graph X.D (insert L F)) L k).card - q - 1) >
      - demand q (graph X.D (insert L F)) X.V p C v k *
        (q + 1 - q * (inN (graph X.D (insert L F)) L j).card)) :
    - demand q (graph X.D (insert L F)) X.V p C v k *
        (q + 1 - q * (inN (graph X.D (insert L F)) L j).card) <
      ((q : ℝ) - 1) * (C - 1) * (q * (inN (graph X.D (insert L F)) L k).card - q - 1) := by
  have dj : demand q (graph X.D (insert L F)) X.V p C v j ≤ ((q : ℝ) - 1) * (C - 1) := by
    simp only [demand, jvne, arc, ↓reduceIte]
    have := old.columns j jv
    rw [oldj]
    linarith
  have q2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : (2 : ℝ) ≤ (inN (graph X.D (insert L F)) L k).card := by exact_mod_cast hk
  have pos : 0 ≤ (q : ℝ) * (inN (graph X.D (insert L F)) L k).card - q - 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right dj pos
  linarith

/-- The slack of `v` itself under the deposit `C-1` on `v` is its old slack. -/
theorem demand_v {q n F L v} (X : Model q n) (hq : 1 ≤ q) (cy : Cycle X.D X.V q L) (vv : v ∈ X.V)
    (vL : v ∉ L) (p : ℕ → ℝ) (C : ℝ) :
    - demand q (graph X.D (insert L F)) X.V p C v v = 1 - realCol q (graph X.D F) X.V p v := by
  have loop : graph X.D (insert L F) v v = false := Bool.eq_false_iff.mpr
    (fun e => loopfree X.free hq vv (CrossValueOmissions.selected_sub e))
  simp only [demand, loop, Bool.false_eq_true, ↓reduceIte, exterior_old (F := F) X cy p vv vL]
  ring

#print axioms eliminate
#print axioms cycle_spread_iff
#print axioms spread_obstruction
#print axioms forbidder_slack
#print axioms demand_v

end LeanCH.BR.Closure.CycleSpread
