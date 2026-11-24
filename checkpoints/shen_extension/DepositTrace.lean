import checkpoints.shen_extension.LastArcHeadDeposit

/-!
# Repeated deposit failures on the common-parent repair (20 November 2026)

Fix the old family `F`, the alternative cycle `L`, one normalized old dual `p`, and write
`val j = realCol q (graph X.D (insert L F)) X.V p j` and `C` for its maximum. A column is *expensive* when
`1 < val j + (q-1)(C-1)`. Everything below uses this one `p`.

* `spread`, `col_spread`, `spread_iff`: deposit the same amount `a` on every row of a set `K`. The new price
  pays exactly when `val j + [j∈K]·a + q·a·#(G-parents of j in K) ≤ 1 + |K|·a` for every column `j`.
  `LastArcHeadDeposit.deposit_iff` is the case `|K| = 1`, `a = C-1`.
* `two_hit`: if the attachment fails, any `q+1` rows with `val ≤ 1` contain two rows sharing a G-head `j`
  that defeats the spread deposit `a = C-1`. With exactly two parents in `K` and `j ∉ K` this says `j` is
  expensive.
* `blocker`, `Blocking`, `blocking_walk`: the repeated single-row test. A failed deposit on a paid row
  produces an expensive G-head, and iterating from the common head `v` gives a walk that stops only at a
  column with `val > 1`.
* `walk_returns`, `walk_distinct`, `arc_price`: the walk's vertices are distinct for `q` steps and cannot
  return to a parent of `v` within `q - a - 1` steps. Each step carries `p(next) + q·p(row) ≤ val(next)`.
* `meets_L`: a stop with `val > 1` lies on `L` and is entered by a new arc of `L`, with
  `val = col_F + q·p(L-predecessor)`.
* `trace_dichotomy`: if the attachment fails, either the walk meets `L` within `q` steps or its first `q+1`
  rows are paid and distinct, and two of them share a head that defeats the spread deposit.
-/

namespace LeanCH.BR.Closure.DepositTrace
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier
open ShenCycleSuccessor

/-! ### Spreading a deposit above several rows -/

/-- Deposit `a` on every row of `K`, then normalize. -/
noncomputable def spread (p : ℕ → ℝ) (K : Finset ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  (p i + if i ∈ K then a else 0) / (1 + K.card * a)

theorem col_spread {D : CH.Digraph} {q : ℕ} {V K : Finset ℕ} (ks : K ⊆ V) (p : ℕ → ℝ)
    (a : ℝ) (j : ℕ) :
    realCol q D V (spread p K a) j =
      (realCol q D V p j + (if j ∈ K then a else 0) + q * a * (inN D K j).card) /
        (1 + K.card * a) := by
  classical
  have pts : ∀ i ∈ V, (if D i j = true then spread p K a i else 0) =
      ((if D i j = true then p i else 0) + (if i ∈ inN D K j then a else 0)) /
        (1 + K.card * a) := by
    intro i _
    by_cases arc : D i j = true <;> by_cases ik : i ∈ K <;> simp [spread, arc, ik, mem_inN]
  have sub : inN D K j ⊆ V := fun x hx => ks (mem_inN.mp hx).1
  have incoming : realInW D V (spread p K a) j =
      (realInW D V p j + a * (inN D K j).card) / (1 + K.card * a) := by
    unfold realInW
    rw [sum_congr rfl pts, ← sum_div, sum_add_distrib, sum_ite_mem, inter_eq_right.mpr sub,
      sum_const, nsmul_eq_mul, mul_comm (((inN D K j).card : ℕ) : ℝ) a]
  rw [realCol, incoming, realCol, spread]
  ring

/-- **Exact test for a uniform spread deposit.** -/
theorem spread_iff {D : CH.Digraph} {q : ℕ} {V K : Finset ℕ} (ks : K ⊆ V) {p : ℕ → ℝ}
    (pos : ∀ i ∈ V, 0 ≤ p i) (norm : realMass V p = 1) {a : ℝ} (ha : 0 ≤ a) :
    RealDual q D V 1 (spread p K a) ↔
      ∀ j ∈ V, realCol q D V p j + (if j ∈ K then a else 0) + q * a * (inN D K j).card ≤
        1 + K.card * a := by
  classical
  have den : 0 < 1 + (K.card : ℝ) * a := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) K.card) ha
    linarith
  constructor
  · intro dual j jv
    have h := dual.columns j jv
    rw [col_spread ks, div_le_iff₀ den, one_mul] at h
    exact h
  · intro bills
    refine ⟨fun i iv => div_nonneg (add_nonneg (pos i iv) (by split_ifs <;> linarith)) den.le,
      ?_, ?_⟩
    · unfold realMass spread
      rw [← sum_div, sum_add_distrib, sum_ite_mem, inter_eq_right.mpr ks, sum_const,
        nsmul_eq_mul, show (∑ i ∈ V, p i) = 1 from norm]
      exact div_self den.ne'
    · intro j jv
      rw [col_spread ks, div_le_iff₀ den, one_mul]
      exact bills j jv

/-! ### The model-level laws -/

/-- **Two-hit law.** If the alternative cycle cannot be attached, every set of at least `q+1` rows with
`val ≤ 1` has a column with at least two G-parents in it that defeats the spread deposit `C-1`. -/
theorem two_hit {q n F L} (X : Model q n) (p : ℕ → ℝ) (old : RealDual q (graph X.D F) X.V 1 p)
    (bad : ¬ SmallRow q (graph X.D (insert L F)) X.V) {C : ℝ} (high : 1 ≤ C)
    (cap : ∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C)
    {K : Finset ℕ} (ks : K ⊆ X.V) (big : q + 1 ≤ K.card)
    (paid : ∀ i ∈ K, realCol q (graph X.D (insert L F)) X.V p i ≤ 1) :
    ∃ j ∈ X.V, 2 ≤ (inN (graph X.D (insert L F)) K j).card ∧
      1 + K.card * (C - 1) < realCol q (graph X.D (insert L F)) X.V p j +
        (if j ∈ K then C - 1 else 0) + q * (C - 1) * (inN (graph X.D (insert L F)) K j).card := by
  classical
  by_contra! none
  apply bad
  apply smallRow_of_realDual (p := spread p K (C - 1))
  refine (spread_iff ks old.nonneg old.normalized (sub_nonneg.mpr high)).mpr ?_
  intro j jv
  by_cases two : 2 ≤ (inN (graph X.D (insert L F)) K j).card
  · exact none j jv two
  · have h1 : ((inN (graph X.D (insert L F)) K j).card : ℝ) ≤ 1 := by
      exact_mod_cast (show (inN (graph X.D (insert L F)) K j).card ≤ 1 by omega)
    have kq : (q : ℝ) + 1 ≤ K.card := by exact_mod_cast big
    have c1 : 0 ≤ C - 1 := sub_nonneg.mpr high
    have A : (q : ℝ) * (C - 1) * (inN (graph X.D (insert L F)) K j).card ≤ q * (C - 1) * 1 :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg q) c1)
    have B : ((q : ℝ) + 1) * (C - 1) ≤ K.card * (C - 1) := mul_le_mul_of_nonneg_right kq c1
    by_cases jk : j ∈ K
    · simp only [jk, ↓reduceIte]
      have := paid j jk
      linarith
    · simp only [jk, ↓reduceIte]
      have := cap j jv
      linarith

/-- **Zones are heads in the model.** By saturation every non-head of `x` returns to `x` within `q-1`
steps, and by q-freeness no head does. So "a column that returns to the deposit row cannot block it"
removes exactly the non-heads, which never block anyway. -/
theorem returns_iff_not_head {q n} (X : Model q n) (hq : 1 ≤ q) {x y : ℕ} (xv : x ∈ X.V)
    (yv : y ∈ X.V) : x ∈ ball X.D X.V y (q - 1) ↔ ¬ X.D x y = true := by
  constructor
  · intro back arc
    obtain ⟨_, d, hd, w⟩ := mem_ball.mp back
    exact X.free x (d + 1) (by omega) (by omega) (.step yv arc w)
  · intro miss
    exact X.sat y yv x xv miss

/-- A failed single-row deposit on a paid row has an expensive G-head. -/
theorem blocker {q n F L} (X : Model q n) (hq : 1 ≤ q) (p : ℕ → ℝ)
    (old : RealDual q (graph X.D F) X.V 1 p) (bad : ¬ SmallRow q (graph X.D (insert L F)) X.V)
    {C : ℝ} (high : 1 ≤ C) (cap : ∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C)
    (attain : ∃ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j = C)
    {i : ℕ} (iv : i ∈ X.V) (self : realCol q (graph X.D (insert L F)) X.V p i ≤ 1) :
    ∃ j ∈ X.V, graph X.D (insert L F) i j = true ∧
      1 < realCol q (graph X.D (insert L F)) X.V p j + ((q : ℝ) - 1) * (C - 1) := by
  by_contra! none
  have loop : graph X.D (insert L F) i i = false := Bool.eq_false_iff.mpr
    (fun e => loopfree X.free hq iv (CrossValueOmissions.selected_sub e))
  obtain ⟨u, _, paid⟩ := (LastArcHeadDeposit.deposit_iff hq iv loop p old.nonneg old.normalized
    self high cap attain).mpr none
  exact bad (smallRow_of_realDual paid)

/-- A blocking walk of `m` steps from `v`: each step leaves a paid row along a G-arc to an expensive
column. -/
def Blocking {q n} (X : Model q n) (F : MarkedCyclePeeling.Family) (L : Finset ℕ) (p : ℕ → ℝ)
    (C : ℝ) (v : ℕ) (f : ℕ → ℕ) (m : ℕ) : Prop :=
  f 0 = v ∧ (∀ a ≤ m, f a ∈ X.V) ∧
    ∀ a < m, realCol q (graph X.D (insert L F)) X.V p (f a) ≤ 1 ∧
      graph X.D (insert L F) (f a) (f (a + 1)) = true ∧
      1 < realCol q (graph X.D (insert L F)) X.V p (f (a + 1)) + ((q : ℝ) - 1) * (C - 1)

/-- **The repeated test.** If the attachment fails and `v` is paid, then for every horizon `k` there is a
blocking walk from `v` of length `m ≤ k` that either reaches the horizon or stops at a column with
`val > 1`. -/
theorem blocking_walk {q n F L} (X : Model q n) (hq : 1 ≤ q) (p : ℕ → ℝ)
    (old : RealDual q (graph X.D F) X.V 1 p) (bad : ¬ SmallRow q (graph X.D (insert L F)) X.V)
    {C : ℝ} (high : 1 ≤ C) (cap : ∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C)
    (attain : ∃ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j = C)
    {v : ℕ} (vv : v ∈ X.V) (k : ℕ) :
    ∃ f : ℕ → ℕ, ∃ m ≤ k, Blocking X F L p C v f m ∧
      (m = k ∨ 1 < realCol q (graph X.D (insert L F)) X.V p (f m)) := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ => v, 0, le_rfl, ⟨rfl, fun a _ => vv, fun a ha => absurd ha (Nat.not_lt_zero a)⟩,
      Or.inl rfl⟩
  | succ k ih =>
    obtain ⟨f, m, mk, ⟨f0, mem, steps⟩, stop⟩ := ih
    by_cases above : 1 < realCol q (graph X.D (insert L F)) X.V p (f m)
    · exact ⟨f, m, by omega, ⟨f0, mem, steps⟩, Or.inr above⟩
    · have hm : m = k := stop.resolve_right above
      obtain ⟨j, jv, arc, exp⟩ := blocker X hq p old bad high cap attain (mem m le_rfl)
        (le_of_not_gt above)
      refine ⟨fun a => if a = m + 1 then j else f a, m + 1, by omega, ⟨?_, ?_, ?_⟩, Or.inl (by omega)⟩
      · simp [f0]
      · intro a ha
        by_cases e : a = m + 1
        · simp [e, jv]
        · simp only [e, ↓reduceIte]
          exact mem a (by omega)
      · intro a ha
        by_cases e : a = m
        · subst e
          simp only [show a ≠ a + 1 by omega, ↓reduceIte]
          exact ⟨le_of_not_gt above, arc, exp⟩
        · simp only [show a ≠ m + 1 by omega, show a + 1 ≠ m + 1 by omega, ↓reduceIte]
          exact steps a (by omega)

/-! ### What every blocking walk satisfies -/

/-- The walk is an actual walk of the model between any two of its positions. -/
theorem walk_between {q n F L} {X : Model q n} {p : ℕ → ℝ} {C : ℝ} {v : ℕ} {f : ℕ → ℕ} {m : ℕ}
    (w : Blocking X F L p C v f m) : ∀ a l, a + l ≤ m → Walk X.D X.V (f a) (f (a + l)) l := by
  obtain ⟨_, mem, steps⟩ := w
  intro a l
  induction l with
  | zero => intro _; simpa using (Walk.refl (D := X.D) (W := X.V) (f a))
  | succ l ih =>
    intro h
    have wk := ih (by omega)
    rw [show a + (l + 1) = (a + l) + 1 by omega]
    exact wk.snoc (mem _ (by omega)) (CrossValueOmissions.selected_sub (steps (a + l) (by omega)).2.1)

/-- **No return to the parents.** A vertex reached after `a` steps cannot reach any parent of `v` within
`q - a - 1` steps. In particular it is neither a parent of `v` nor an in-neighbour of one while
`a + 2 ≤ q`. -/
theorem walk_returns {q n F L} {X : Model q n} {p : ℕ → ℝ} {C : ℝ} {v : ℕ} {f : ℕ → ℕ} {m : ℕ}
    (w : Blocking X F L p C v f m) {a : ℕ} (am : a ≤ m) {x : ℕ} (xv : x ∈ X.V)
    (parent : X.D x v = true) {d : ℕ} (room : a + d + 1 ≤ q) : ¬ Walk X.D X.V (f a) x d := by
  intro back
  have path := walk_between w 0 a (by omega)
  rw [Nat.zero_add, w.1] at path
  have vv : v ∈ X.V := w.1 ▸ w.2.1 0 (Nat.zero_le _)
  exact X.free x (a + d + 1) (by omega) room (.step vv parent (path.append back))

/-- The first `q+1` positions of a long enough walk are distinct. -/
theorem walk_distinct {q n F L} {X : Model q n} {p : ℕ → ℝ} {C : ℝ} {v : ℕ} {f : ℕ → ℕ} {m : ℕ}
    (w : Blocking X F L p C v f m) {a b : ℕ} (ab : a < b) (bm : b ≤ m) (short : b - a ≤ q) :
    f a ≠ f b := by
  intro eq
  have wk := walk_between w a (b - a) (by omega)
  rw [Nat.add_sub_cancel' ab.le, ← eq] at wk
  exact X.free _ (b - a) (by omega) short wk

/-- Each G-arc charges the head's column with `q` times the row's old price. -/
theorem arc_price {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {p : ℕ → ℝ} (pos : ∀ i ∈ V, 0 ≤ p i)
    {i j : ℕ} (iv : i ∈ V) (arc : G i j = true) : p j + q * p i ≤ realCol q G V p j := by
  rw [realCol, realInW_eq_mass_inN]
  have one : p i ≤ realMass (inN G V j) p :=
    single_le_sum (f := p) (fun k hk => pos k (mem_inN.mp hk).1) (mem_inN.mpr ⟨iv, arc⟩)
  have := mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α := ℝ) q)
  linarith

/-- **Meeting the alternative cycle.** A column above one lies on `L` and is entered by a new arc of `L`
whose source carries the excess. -/
theorem meets_L {q n F L} (X : Model q n) (cy : Cycle X.D X.V q L) (p : ℕ → ℝ)
    (old : RealDual q (graph X.D F) X.V 1 p) {j : ℕ} (jv : j ∈ X.V)
    (above : 1 < realCol q (graph X.D (insert L F)) X.V p j) :
    j ∈ SharedArcBarrier.targets X.D X.V F L ∧ ∃ u ∈ L, j ∈ L ∧ X.D u j = true ∧
      graph X.D F u j = false ∧
      realCol q (graph X.D (insert L F)) X.V p j = realCol q (graph X.D F) X.V p j + q * p u := by
  have account := SharedArcBarrier.column (q := q) (F := F) cy p jv
  have target : j ∈ SharedArcBarrier.targets X.D X.V F L := by
    by_contra no
    exact above.not_ge ((account.1 no).symm ▸ old.columns j jv)
  exact ⟨target, account.2 target⟩

/-- **The dichotomy for the repeated test.** If `L` cannot be attached and the common head `v` is paid,
there is a blocking walk from `v` such that either

* it meets `L` after `m` steps with `1 ≤ m ≤ q`, at a target entered by a new arc of `L`, and that vertex
  cannot reach any parent of `v` within `q - m - 1` steps; or
* it runs `q` steps through paid rows `f 0, …, f q`, these are distinct, and two of them share a G-head that
  defeats the spread deposit `C-1` on all `q+1` of them. -/
theorem trace_dichotomy {q n F L} (X : Model q n) (hq : 1 ≤ q) (cy : Cycle X.D X.V q L)
    (p : ℕ → ℝ) (old : RealDual q (graph X.D F) X.V 1 p)
    (bad : ¬ SmallRow q (graph X.D (insert L F)) X.V)
    {C : ℝ} (high : 1 ≤ C) (cap : ∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C)
    (attain : ∃ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j = C)
    {v : ℕ} (vv : v ∈ X.V) (vpaid : realCol q (graph X.D (insert L F)) X.V p v ≤ 1) :
    ∃ f : ℕ → ℕ,
      (∃ m, 1 ≤ m ∧ m ≤ q ∧ Blocking X F L p C v f m ∧
        1 < realCol q (graph X.D (insert L F)) X.V p (f m) ∧
        f m ∈ SharedArcBarrier.targets X.D X.V F L ∧
        (∃ u ∈ L, f m ∈ L ∧ X.D u (f m) = true ∧ graph X.D F u (f m) = false ∧
          realCol q (graph X.D (insert L F)) X.V p (f m) =
            realCol q (graph X.D F) X.V p (f m) + q * p u) ∧
        ∀ x ∈ X.V, X.D x v = true → ∀ d, m + d + 1 ≤ q → ¬ Walk X.D X.V (f m) x d) ∨
      (Blocking X F L p C v f (q + 1) ∧ ((range (q + 1)).image f).card = q + 1 ∧
        ∃ j ∈ X.V, 2 ≤ (inN (graph X.D (insert L F)) ((range (q + 1)).image f) j).card ∧
          1 + ((range (q + 1)).image f).card * (C - 1) <
            realCol q (graph X.D (insert L F)) X.V p j +
              (if j ∈ (range (q + 1)).image f then C - 1 else 0) +
              q * (C - 1) * (inN (graph X.D (insert L F)) ((range (q + 1)).image f) j).card) := by
  classical
  obtain ⟨f, m, mk, w, stop⟩ := blocking_walk X hq p old bad high cap attain vv (q + 1)
  refine ⟨f, ?_⟩
  by_cases full : m = q + 1
  · subst full
    right
    have inj : Set.InjOn f (range (q + 1) : Set ℕ) := by
      intro a ha b hb eq
      simp only [coe_range, Set.mem_Iio] at ha hb
      by_contra ne
      rcases Nat.lt_or_gt_of_ne ne with h | h
      · exact walk_distinct w h (by omega) (by omega) eq
      · exact walk_distinct w h (by omega) (by omega) eq.symm
    have card : ((range (q + 1)).image f).card = q + 1 := by
      rw [card_image_of_injOn inj, card_range]
    have ks : (range (q + 1)).image f ⊆ X.V := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      exact w.2.1 a (by have := mem_range.mp ha; omega)
    have paid : ∀ i ∈ (range (q + 1)).image f,
        realCol q (graph X.D (insert L F)) X.V p i ≤ 1 := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      exact (w.2.2 a (mem_range.mp ha)).1
    exact ⟨w, card, two_hit X p old bad high cap ks (by omega) paid⟩
  · left
    have above : 1 < realCol q (graph X.D (insert L F)) X.V p (f m) :=
      stop.resolve_left full
    have pos : 1 ≤ m := by
      by_contra zero
      have : m = 0 := by omega
      subst this
      rw [w.1] at above
      exact above.not_ge vpaid
    obtain ⟨target, data⟩ := meets_L X cy p old (w.2.1 m le_rfl) above
    exact ⟨m, pos, by omega, w, above, target, data,
      fun x xv parent d room => walk_returns w le_rfl xv parent room⟩

#print axioms returns_iff_not_head
#print axioms spread_iff
#print axioms two_hit
#print axioms blocking_walk
#print axioms walk_returns
#print axioms meets_L
#print axioms trace_dichotomy

end LeanCH.BR.Closure.DepositTrace
