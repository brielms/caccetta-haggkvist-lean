import checkpoints.shen_extension.BankAverage
import checkpoints.shen_extension.ReachLedger

/-!
# The shortfall floor: instances that hold, and the next step of its induction

`BankAverage.ShortfallFloor q t t` says that a graph with no directed cycle
of length at most `q`, on a nonempty set of at most `q t` labels, has total
shortfall at least `t` at quota `t`.

Instances proved here, with no hypothesis:

* quota one, every cutoff (`floor_one`): some row has no head;
* cutoff two, every quota (`floor_cutoff_two`): an oriented graph on `N`
  labels has at most `C(N,2)` arcs.

They show that the floor is a statement that can hold. The second half
continues the induction from quota `t - 1` to quota `t` on `q (t-1) + 2`
labels: a single short row there must have no head at all
(`one_short_row`).
-/

namespace LeanCH.BR.FloorInduction
open Finset BRq2 BRq3 Closure.DeficitLevels BankAverage

/-- **Quota one, every cutoff.** -/
theorem floor_one (q : ℕ) : ShortfallFloor q 1 1 :=
  fun _ _ live small free => ShortfallBridge.total_pos ReachLedger.noHost_one free live small

/-- With no loops and no two-cycles, the arcs inject into the unordered pairs. -/
theorem arcs_le_pairs {E : CH.Digraph} {U : Finset ℕ} (free : QFree E U 2) :
    ∑ u ∈ U, (outN E U u).card ≤ U.card.choose 2 := by
  classical
  have count : ∑ u ∈ U, (outN E U u).card =
      ((U ×ˢ U).filter (fun p : ℕ × ℕ => E p.1 p.2 = true)).card := by
    rw [card_filter, sum_product]
    refine sum_congr rfl fun u _ => ?_
    unfold outN
    rw [card_filter]
  rw [count, ← card_powersetCard]
  have arcOf : ∀ p ∈ (U ×ˢ U).filter (fun p : ℕ × ℕ => E p.1 p.2 = true),
      p.1 ∈ U ∧ p.2 ∈ U ∧ E p.1 p.2 = true ∧ p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨inside, arc⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_product.mp inside
    refine ⟨h1, h2, arc, fun e => loopfree free (by decide) h1 ?_⟩
    rw [← e] at arc
    exact arc
  refine card_le_card_of_injOn (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ)) ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, _, ne⟩ := arcOf p hp
    refine mem_powersetCard.mpr ⟨?_, card_pair ne⟩
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact h1
    · rw [mem_singleton.mp hz]; exact h2
  · intro p hp p' hp' same
    obtain ⟨h1, h2, arc, ne⟩ := arcOf p (mem_coe.mp hp)
    obtain ⟨_, _, arc', ne'⟩ := arcOf p' (mem_coe.mp hp')
    have same' : ({p.1, p.2} : Finset ℕ) = {p'.1, p'.2} := same
    have m1 : p.1 ∈ ({p'.1, p'.2} : Finset ℕ) := same' ▸ mem_insert_self _ _
    have m2 : p.2 ∈ ({p'.1, p'.2} : Finset ℕ) :=
      same' ▸ mem_insert_of_mem (mem_singleton_self _)
    rcases mem_insert.mp m1 with a | a <;> rcases mem_insert.mp m2 with b | b
    · exact absurd (a.trans b.symm) ne
    · exact Prod.ext a (mem_singleton.mp b)
    · have a' := mem_singleton.mp a
      rw [a', b] at arc
      exact (digonfree free (by decide) (b ▸ h2) (a' ▸ h1) arc' arc).elim
    · exact absurd ((mem_singleton.mp a).trans (mem_singleton.mp b).symm) ne

/-- **Cutoff two, every quota.** -/
theorem floor_cutoff_two (t : ℕ) : ShortfallFloor 2 t t := by
  intro E U live small free
  have arcs := arcs_le_pairs free
  have lower : U.card * t ≤ total t E U + ∑ u ∈ U, (outN E U u).card := by
    unfold total
    rw [← sum_add_distrib, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun u _ => by
      unfold cost
      omega
  obtain ⟨m, hm⟩ : ∃ m, U.card = m + 1 := ⟨U.card - 1, by have := card_pos.mpr live; omega⟩
  rw [hm] at arcs lower small
  have pairs := two_choose m
  have wide := Nat.mul_le_mul_left m small
  nlinarith

/-- A row with at least `t` heads that keeps all but two of them is short at
quota `t - 1` only when it has exactly `t` heads and loses both. -/
theorem cost_two_erased {E : CH.Digraph} {U : Finset ℕ} {t x b u : ℕ}
    (full : t ≤ (outN E U u).card) :
    cost (t-1) E ((U.erase x).erase b) u ≤
      if E u x = true ∧ E u b = true ∧ (outN E U u).card ≤ t then 1 else 0 := by
  classical
  have cover : outN E U u ⊆ insert x (insert b (outN E ((U.erase x).erase b) u)) := by
    intro z zm
    obtain ⟨zu, uz⟩ := mem_outN.mp zm
    by_cases ex : z = x
    · exact ex ▸ mem_insert_self _ _
    by_cases eb : z = b
    · exact mem_insert_of_mem (eb ▸ mem_insert_self _ _)
    · exact mem_insert_of_mem (mem_insert_of_mem
        (mem_outN.mpr ⟨mem_erase.mpr ⟨eb, mem_erase.mpr ⟨ex, zu⟩⟩, uz⟩))
  have two := (card_le_card cover).trans ((card_insert_le _ _).trans
    (Nat.succ_le_succ (card_insert_le _ _)))
  unfold cost
  split
  · omega
  · rename_i miss
    -- one of the two labels is not a head, or the row has a spare head
    by_cases ux : E u x = true
    · by_cases ub : E u b = true
      · have spare : t < (outN E U u).card := by
          by_contra le
          exact miss ⟨ux, ub, by omega⟩
        omega
      · have cover' : outN E U u ⊆ insert x (outN E ((U.erase x).erase b) u) := by
          intro z zm
          obtain ⟨zu, uz⟩ := mem_outN.mp zm
          by_cases ex : z = x
          · exact ex ▸ mem_insert_self _ _
          · exact mem_insert_of_mem (mem_outN.mpr
              ⟨mem_erase.mpr ⟨fun eb => ub (eb ▸ uz), mem_erase.mpr ⟨ex, zu⟩⟩, uz⟩)
        have := (card_le_card cover').trans (card_insert_le _ _)
        omega
    · have cover' : outN E U u ⊆ insert b (outN E ((U.erase x).erase b) u) := by
        intro z zm
        obtain ⟨zu, uz⟩ := mem_outN.mp zm
        by_cases eb : z = b
        · exact eb ▸ mem_insert_self _ _
        · exact mem_insert_of_mem (mem_outN.mpr
            ⟨mem_erase.mpr ⟨eb, mem_erase.mpr ⟨fun ex => ux (ex ▸ uz), zu⟩⟩, uz⟩)
      have := (card_le_card cover').trans (card_insert_le _ _)
      omega

/-- **One short row on `q (t-1) + 2` labels has no head.** Under the natural
floor at quota `t - 1`, if every row other than `x` has at least `t` heads,
then every other label is a parent of `x`, so `x` has no head and the
shortfall is `t`. -/
theorem one_short_row {q t : ℕ} (hq : 2 ≤ q) (ht : 2 ≤ t) (law : ShortfallFloor q (t-1) (t-1))
    {E : CH.Digraph} {U : Finset ℕ} (free : QFree E U q) (size : U.card = q * (t-1) + 2)
    {x : ℕ} (xu : x ∈ U) (others : ∀ u ∈ U, u ≠ x → t ≤ (outN E U u).card) :
    (outN E U x).card = 0 := by
  classical
  have room : 2 ≤ q * (t-1) := by nlinarith [Nat.mul_le_mul hq (show 1 ≤ t - 1 by omega)]
  -- tight parents of `x`
  let T := (U.erase x).filter (fun u => E u x = true ∧ (outN E U u).card ≤ t)
  -- every other label shares at least `t - 1` tight parents with `x`
  have shared : ∀ b ∈ U.erase x, t - 1 ≤ (T.filter (fun u => E u b = true)).card := by
    intro b bm
    obtain ⟨bx, bu⟩ := mem_erase.mp bm
    have left : ((U.erase x).erase b).card = q * (t-1) := by
      rw [card_erase_of_mem bm, card_erase_of_mem xu, size]; omega
    have base := law E ((U.erase x).erase b) (card_pos.mp (by omega)) (by omega)
      (free.mono_set ((erase_subset _ _).trans (erase_subset _ _)))
    refine base.trans ?_
    unfold total
    calc ∑ u ∈ (U.erase x).erase b, cost (t-1) E ((U.erase x).erase b) u
        ≤ ∑ u ∈ (U.erase x).erase b,
            (if E u x = true ∧ E u b = true ∧ (outN E U u).card ≤ t then 1 else 0) :=
          sum_le_sum fun u um => by
            have ux := mem_erase.mp (mem_erase.mp um).2
            exact cost_two_erased (others u ux.2 ux.1)
      _ = (((U.erase x).erase b).filter
            (fun u => E u x = true ∧ E u b = true ∧ (outN E U u).card ≤ t)).card := by
          rw [card_filter]
      _ ≤ (T.filter (fun u => E u b = true)).card := by
          apply card_le_card
          intro u um
          obtain ⟨uin, ux, ub, tight⟩ := mem_filter.mp um
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_erase.mp uin).2, ux, tight⟩, ub⟩
  -- count the pairs (tight parent, other head) both ways
  have rows : ∀ u ∈ T, ((U.erase x).filter (fun b => E u b = true)).card ≤ t - 1 := by
    intro u um
    obtain ⟨uin, ux, tight⟩ := mem_filter.mp um
    have eq : (U.erase x).filter (fun b => E u b = true) = (outN E U u).erase x := by
      ext b
      simp only [mem_filter, mem_erase, mem_outN]
      tauto
    rw [eq, card_erase_of_mem (mem_outN.mpr ⟨xu, ux⟩)]
    omega
  have swap : ∑ b ∈ U.erase x, (T.filter (fun u => E u b = true)).card =
      ∑ u ∈ T, ((U.erase x).filter (fun b => E u b = true)).card := by
    simp_rw [card_filter]
    exact sum_comm
  have low : (U.erase x).card * (t - 1) ≤ ∑ b ∈ U.erase x, (T.filter (fun u => E u b = true)).card := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum shared
  have high : ∑ u ∈ T, ((U.erase x).filter (fun b => E u b = true)).card ≤ T.card * (t - 1) := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum rows
  have all : (U.erase x).card ≤ T.card :=
    Nat.le_of_mul_le_mul_right ((low.trans (swap ▸ high))) (by omega)
  have whole : T = U.erase x :=
    eq_of_subset_of_card_le (filter_subset _ _) all
  -- every other label points to `x`, so a head of `x` would close a two-cycle
  by_contra some
  obtain ⟨h, hm⟩ := card_pos.mp (Nat.pos_of_ne_zero some)
  obtain ⟨hu, xh⟩ := mem_outN.mp hm
  have hx : h ≠ x := fun e => loopfree free (by omega) xu (e ▸ xh)
  have back : h ∈ T := whole ▸ mem_erase.mpr ⟨hx, hu⟩
  exact digonfree free hq xu hu xh (mem_filter.mp back).2.1

/-! ### Averaging over single deletions

Erase one label `b` and keep the quota. A row with at most `t` heads that
pointed to `b` is short by one more; no other row changes. Summing over `b`:

    Σ_b shortfall(U - b) + 2 · shortfall(U) ≤ |U| · (shortfall(U) + t).

So a floor `L` on `N` labels gives `(N+1) L + 2 σ ≤ (N+1) (σ + t)` on `N + 1`
labels. When the floor drops from `2 t - 1` on `q (t-1) + 1` labels this
forces `σ ≥ t` on `q (t-1) + 2` labels, with any number of short rows. -/

/-- At the same quota, erasing `b` costs a row at most one unit, and only a
row with at most `t` heads that pointed to `b`. -/
theorem cost_erase_same {E : CH.Digraph} {U : Finset ℕ} {t b u : ℕ} :
    cost t E (U.erase b) u ≤ cost t E U u +
      (if E u b = true ∧ (outN E U u).card ≤ t then 1 else 0) := by
  classical
  have cover : outN E U u ⊆ insert b (outN E (U.erase b) u) := by
    intro x xm
    obtain ⟨xu, ux⟩ := mem_outN.mp xm
    by_cases e : x = b
    · exact e ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, xu⟩, ux⟩)
  have le := (card_le_card cover).trans (card_insert_le _ _)
  unfold cost
  split
  · omega
  · rename_i miss
    by_cases ub : E u b = true
    · have spare : t < (outN E U u).card := by
        by_contra small
        exact miss ⟨ub, by omega⟩
      omega
    · have same : outN E U u ⊆ outN E (U.erase b) u := by
        intro x xm
        obtain ⟨xu, ux⟩ := mem_outN.mp xm
        exact mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => ub (e ▸ ux), xu⟩, ux⟩
      have := card_le_card same
      omega

/-- **Averaging over single deletions.** -/
theorem delete_average {q t N L : ℕ}
    (hyp : ∀ (E : CH.Digraph) (W : Finset ℕ), W.card = N → QFree E W q → L ≤ total t E W)
    {E : CH.Digraph} {U : Finset ℕ} (size : U.card = N + 1) (free : QFree E U q) :
    (N + 1) * L + 2 * total t E U ≤ (N + 1) * (total t E U + t) := by
  classical
  let ind : ℕ → ℕ → ℕ := fun u b => if E u b = true ∧ (outN E U u).card ≤ t then 1 else 0
  have each : ∀ b ∈ U, L ≤ ∑ u ∈ U.erase b, (cost t E U u + ind u b) := by
    intro b bu
    refine (hyp E (U.erase b) (by rw [card_erase_of_mem bu, size]; rfl)
      (free.mono_set (erase_subset _ _))).trans ?_
    unfold total
    exact sum_le_sum fun u _ => cost_erase_same
  have sumL : (N + 1) * L ≤ ∑ b ∈ U, ∑ u ∈ U.erase b, (cost t E U u + ind u b) := by
    rw [← size, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum each
  have split : ∑ b ∈ U, ∑ u ∈ U.erase b, (cost t E U u + ind u b) =
      ∑ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + ∑ b ∈ U, ∑ u ∈ U.erase b, ind u b := by
    simp_rw [sum_add_distrib]
  have first : ∑ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + total t E U =
      (N + 1) * total t E U := by
    have row : ∀ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + cost t E U b = total t E U :=
      fun b bu => by
        unfold total
        rw [Nat.add_comm]
        exact add_sum_erase U _ bu
    calc ∑ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + total t E U
        = ∑ b ∈ U, (∑ u ∈ U.erase b, cost t E U u + cost t E U b) := by
          rw [sum_add_distrib]; rfl
      _ = ∑ _b ∈ U, total t E U := sum_congr rfl row
      _ = (N + 1) * total t E U := by rw [sum_const, smul_eq_mul, size]
  have second : ∑ b ∈ U, ∑ u ∈ U.erase b, ind u b + total t E U ≤ (N + 1) * t := by
    have swap : ∑ b ∈ U, ∑ u ∈ U.erase b, ind u b = ∑ u ∈ U, ∑ b ∈ U.erase u, ind u b := by
      apply sum_comm'
      intro b u
      simp only [mem_erase]
      constructor
      · rintro ⟨bu, ne, uu⟩
        exact ⟨⟨fun e => ne e.symm, bu⟩, uu⟩
      · rintro ⟨⟨ne, bu⟩, uu⟩
        exact ⟨bu, fun e => ne e.symm, uu⟩
    rw [swap]
    unfold total
    rw [← sum_add_distrib, ← size, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun u _ => ?_
    by_cases low : (outN E U u).card ≤ t
    · have count : ∑ b ∈ U.erase u, ind u b ≤ (outN E U u).card := by
        calc ∑ b ∈ U.erase u, ind u b
            = ((U.erase u).filter (fun b => E u b = true)).card := by
              rw [card_filter]
              refine sum_congr rfl fun b _ => ?_
              simp [ind, low]
          _ ≤ (outN E U u).card := card_le_card fun b hb =>
              mem_outN.mpr ⟨(mem_erase.mp (mem_filter.mp hb).1).2, (mem_filter.mp hb).2⟩
      unfold cost
      omega
    · have none : ∑ b ∈ U.erase u, ind u b = 0 :=
        sum_eq_zero fun b _ => by simp [ind, low]
      unfold cost
      omega
  rw [Nat.mul_add]
  omega

/-- **The first carrier of the plateau.** If every graph on `q (t-1) + 1` labels
has shortfall at least `2 t - 1` at quota `t`, then every graph on
`q (t-1) + 2` labels has shortfall at least `t`. No count of short rows enters. -/
theorem plateau_first {q t : ℕ} (ht : 2 ≤ t)
    (below : ∀ (E : CH.Digraph) (W : Finset ℕ), W.card = q * (t-1) + 1 → QFree E W q →
      2 * t - 1 ≤ total t E W)
    {E : CH.Digraph} {U : Finset ℕ} (size : U.card = q * (t-1) + 2) (free : QFree E U q) :
    t ≤ total t E U := by
  have avg := delete_average below (N := q * (t-1) + 1) size free
  by_contra few
  have cap : (q * (t-1) + 1 + 1) * (total t E U + t) ≤ (q * (t-1) + 1 + 1) * (2 * t - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have zero : total t E U = 0 := by omega
  rw [zero] at avg
  have := Nat.le_of_mul_le_mul_left (by simpa using avg) (by omega : 0 < q * (t-1) + 1 + 1)
  omega

/-! ### The top size: two units from the sink case one label below

On `q t` labels, erase one label. If every row had at least two heads, no
row of the smaller graph is left without a head. Suppose that on `q t - 1`
labels a graph in which every row has a head has shortfall at least `t + 1`
(that is, shortfall `t` there forces a row with no head). Averaging over
the deletions then gives shortfall at least two on `q t` labels: no host and
no graph with a single unit of shortfall. -/

/-- Averaging over single deletions, with the floor asked only of the graphs that occur. -/
theorem delete_average_on {t L : ℕ} {E : CH.Digraph} {U : Finset ℕ}
    (hyp : ∀ b ∈ U, L ≤ total t E (U.erase b)) :
    U.card * L + 2 * total t E U ≤ U.card * (total t E U + t) := by
  classical
  let ind : ℕ → ℕ → ℕ := fun u b => if E u b = true ∧ (outN E U u).card ≤ t then 1 else 0
  have each : ∀ b ∈ U, L ≤ ∑ u ∈ U.erase b, (cost t E U u + ind u b) := by
    intro b bu
    refine (hyp b bu).trans ?_
    unfold total
    exact sum_le_sum fun u _ => cost_erase_same
  have sumL : U.card * L ≤ ∑ b ∈ U, ∑ u ∈ U.erase b, (cost t E U u + ind u b) := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum each
  have split : ∑ b ∈ U, ∑ u ∈ U.erase b, (cost t E U u + ind u b) =
      ∑ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + ∑ b ∈ U, ∑ u ∈ U.erase b, ind u b := by
    simp_rw [sum_add_distrib]
  have first : ∑ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + total t E U =
      U.card * total t E U := by
    have row : ∀ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + cost t E U b = total t E U :=
      fun b bu => by
        unfold total
        rw [Nat.add_comm]
        exact add_sum_erase U _ bu
    calc ∑ b ∈ U, ∑ u ∈ U.erase b, cost t E U u + total t E U
        = ∑ b ∈ U, (∑ u ∈ U.erase b, cost t E U u + cost t E U b) := by
          rw [sum_add_distrib]; rfl
      _ = ∑ _b ∈ U, total t E U := sum_congr rfl row
      _ = U.card * total t E U := by rw [sum_const, smul_eq_mul]
  have second : ∑ b ∈ U, ∑ u ∈ U.erase b, ind u b + total t E U ≤ U.card * t := by
    have swap : ∑ b ∈ U, ∑ u ∈ U.erase b, ind u b = ∑ u ∈ U, ∑ b ∈ U.erase u, ind u b := by
      apply sum_comm'
      intro b u
      simp only [mem_erase]
      constructor
      · rintro ⟨bu, ne, uu⟩
        exact ⟨⟨fun e => ne e.symm, bu⟩, uu⟩
      · rintro ⟨⟨ne, bu⟩, uu⟩
        exact ⟨bu, fun e => ne e.symm, uu⟩
    rw [swap]
    unfold total
    rw [← sum_add_distrib, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun u _ => ?_
    by_cases low : (outN E U u).card ≤ t
    · have count : ∑ b ∈ U.erase u, ind u b ≤ (outN E U u).card := by
        calc ∑ b ∈ U.erase u, ind u b
            = ((U.erase u).filter (fun b => E u b = true)).card := by
              rw [card_filter]
              refine sum_congr rfl fun b _ => ?_
              simp [ind, low]
          _ ≤ (outN E U u).card := card_le_card fun b hb =>
              mem_outN.mpr ⟨(mem_erase.mp (mem_filter.mp hb).1).2, (mem_filter.mp hb).2⟩
      unfold cost
      omega
    · have none : ∑ b ∈ U.erase u, ind u b = 0 :=
        sum_eq_zero fun b _ => by simp [ind, low]
      unfold cost
      omega
  rw [Nat.mul_add]
  omega

/-- **Two units on `q t` labels from the sink case on `q t - 1` labels.** -/
theorem two_of_sink_case {q t : ℕ}
    (below : ∀ (E : CH.Digraph) (W : Finset ℕ), W.card + 1 = q * t → QFree E W q →
      (∀ u ∈ W, 1 ≤ (outN E W u).card) → t + 1 ≤ total t E W)
    {E : CH.Digraph} {U : Finset ℕ} (size : U.card = q * t) (live : U.Nonempty)
    (free : QFree E U q) (rows : ∀ u ∈ U, 2 ≤ (outN E U u).card) : 2 ≤ total t E U := by
  classical
  have pos := card_pos.mpr live
  have avg := delete_average_on (t := t) (L := t + 1) (E := E) (U := U) (fun b bu =>
    below E (U.erase b) (by rw [card_erase_of_mem bu]; omega)
      (free.mono_set (erase_subset _ _)) (fun u um => by
        have uu := (mem_erase.mp um).2
        have cover : outN E U u ⊆ insert b (outN E (U.erase b) u) := by
          intro x xm
          obtain ⟨xu, ux⟩ := mem_outN.mp xm
          by_cases e : x = b
          · exact e ▸ mem_insert_self _ _
          · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, xu⟩, ux⟩)
        have := (card_le_card cover).trans (card_insert_le _ _)
        have := rows u uu
        omega))
  by_contra few
  have small : total t E U = 0 ∨ total t E U = 1 := by omega
  rcases small with z | o
  · rw [z] at avg
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at avg
    omega
  · rw [o] at avg
    simp only [Nat.mul_add, Nat.mul_one] at avg
    omega

/-! ### The stacked-sink value

Put `m` sinks in a transitive stack under a host of degree `t - m` on
`q (t-m) + 1` labels, every row of the host pointing to every sink. The host
rows have `t` heads and the sinks are short by `t, t-1, …, t-m+1`. This
needs `N ≥ q (t-m) + m + 1` labels and has shortfall `m t - C(m,2)`.

`ExactFloor q` says that this is the minimum on every carrier with at least
`t + 1` labels. It is proved below for cutoff two and is a conjecture for
larger cutoffs. Small cases (cutoffs 3, 4, 5; quotas 2 to 4; at most 11
labels): the value equals the exhaustive minimum in 37 cases, and in 7 more
the search found a graph with this value but did not finish proving that
nothing smaller exists (two of these were settled by separate runs). Logs: `checkpoints/capstone_audit_20261123/floor/`. -/

/-- Shortfall of `m` stacked sinks at quota `t`. -/
def stacked (t m : ℕ) : ℕ := m * t - m.choose 2

/-- The least `m` with `q (t-m) + m + 1 ≤ N`, for `N ≤ q t + 1` and `2 ≤ q`. -/
def sinks (q t N : ℕ) : ℕ := (q * t + 1 - N + (q - 2)) / (q - 1)

/-- The conjectured exact floor on every carrier with at least `t + 1` labels. -/
def ExactFloor (q : ℕ) : Prop :=
  ∀ (t : ℕ) (E : CH.Digraph) (U : Finset ℕ), t + 1 ≤ U.card → QFree E U q →
    stacked t (sinks q t U.card) ≤ total t E U

/-- **Cutoff two.** The stacked-sink value is the exact floor. -/
theorem exactFloor_two : ExactFloor 2 := by
  intro t E U big free
  have arcs := arcs_le_pairs free
  have lower : U.card * t ≤ total t E U + ∑ u ∈ U, (outN E U u).card := by
    unfold total
    rw [← sum_add_distrib, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun u _ => by
      unfold cost
      omega
  unfold stacked sinks
  simp only [Nat.sub_self, Nat.add_zero, Nat.reduceSub, Nat.div_one]
  by_cases far : 2 * t + 1 ≤ U.card
  · have : 2 * t + 1 - U.card = 0 := by omega
    simp [this]
  · obtain ⟨M, hM⟩ : ∃ M, 2 * t + 1 = U.card + M := ⟨2 * t + 1 - U.card, by omega⟩
    have eM : 2 * t + 1 - U.card = M := by omega
    rw [eM]
    obtain ⟨n, hn⟩ : ∃ n, U.card = n + 1 := ⟨U.card - 1, by omega⟩
    rw [hn] at arcs lower hM
    have pn := two_choose n
    have key : 2 * (M * t) + (n + 1) * n = 2 * ((n + 1) * t) + M * (M - 1) := by
      rcases M with _ | k
      · have : n = 2 * t := by omega
        subst this
        simp
        ring
      · have : n + k + 1 = 2 * t := by omega
        have e : k + 1 - 1 = k := by omega
        rw [e]
        have t2 : 2 * t = n + k + 1 := this.symm
        nlinarith
    have pm : 2 * M.choose 2 = M * (M - 1) := by
      rcases M with _ | k
      · simp
      · have := two_choose k
        simpa using this
    have goal2 : 2 * (M * t) ≤ 2 * total t E U + 2 * M.choose 2 := by nlinarith
    omega

/-- End-to-end check of the route with a floor that is proved: quota one gives
the triangle case at degree two. No hypothesis is left. -/
theorem triangle_degree_two {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 3)
    (deg : ∀ v ∈ V, 2 ≤ (outN D V v).card) (live : V.Nonempty) : 7 ≤ V.card :=
  triangle_of_floor free deg live (by decide) (floor_one 3)

/-- The same check for the floor's own step: quota two on at most `q + 1` labels. -/
theorem floor_two_low {q : ℕ} (hq : 1 ≤ q) (E : CH.Digraph) (U : Finset ℕ) (live : U.Nonempty)
    (small : U.card ≤ q + 1) (free : QFree E U q) : 2 ≤ total 2 E U :=
  floor_low hq (by decide) (floor_one q) E U live (by simpa using small) free

#print axioms triangle_degree_two
#print axioms floor_two_low
#print axioms delete_average
#print axioms plateau_first
#print axioms exactFloor_two
#print axioms two_of_sink_case
#print axioms floor_one
#print axioms floor_cutoff_two
#print axioms one_short_row
end LeanCH.BR.FloorInduction
