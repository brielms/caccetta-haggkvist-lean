import checkpoints.shen_extension.UnitStateBoundary

/-! A boundary-order unit state cannot contain the last private clone.
Consequently a completion that needs at least two steps has a higher order. -/
namespace LeanCH.BR.Closure.PrivateCompletionOrder
open BRq2 BRq3 Finset DeficitLevels PrivateCompletion UnitState PackingFrontier

/-- The pair and domination rules forbid a vertex with a unique parent.
Only loops and digons need to be excluded in this argument. -/
theorem unit_no_private_parent {D : CH.Digraph} {U : Finset ℕ} {q d p v : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 2 ≤ q) (hd : 1 ≤ d)
    (unit : total (d+1) D U = 1) (size : U.card ≤ q*d+2)
    (hp : p ∈ U) (hv : v ∈ U) (onlyParent : ∀ x ∈ U, D x v = true ↔ x = p) : False := by
  obtain ⟨u,hu,short,full⟩ := unit_profile unit
  have short' : (outN D U u).card = d := by omega
  have pv := (onlyParent p hp).mpr rfl
  have distinct : v ≠ p := by rintro rfl; exact loopfree free (by omega) hv pv
  have pu : D p u = true := by
    by_cases vu : v = u
    · simpa [vu] using pv
    · obtain ⟨x,hx,xu,xv⟩ := unit_parents_dominate free lower (by omega) hd hu short' full size hv vu
      rwa [(onlyParent x hx).mp xv] at xu
  have up : D u p ≠ true := fun edge => digonfree free hq hp hu pu edge
  have uv : D u v ≠ true := by
    intro edge
    have same := (onlyParent u hu).mp edge
    exact loopfree free (by omega) hp (same ▸ pu)
  rcases unit_pair free lower (by omega) hd hu short' full size hv hp distinct with hit | hit | joint
  · exact uv hit
  · exact up hit
  · obtain ⟨x,hx,xv,xp⟩ := joint
    exact loopfree free (by omega) hp ((onlyParent x hx).mp xv ▸ xp)

/-- With at least two units to pay, the penultimate graph is itself the result
of a private step. The sum of current order and shortfall is invariant. -/
theorem completion_order_lower {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 2 ≤ q)
    (two : 2 ≤ total (d+1) D U) (small : total (d+1) D U < d+1) :
    q*d+4 ≤ U.card + total (d+1) D U := by
  suffices chain : ∀ k, ∀ (G : CH.Digraph) (W : Finset ℕ), QFree G W q →
      total (d+1) G W = k → 2 ≤ k → k < d+1 → q*d+4 ≤ W.card+k from
    chain _ D U free rfl two small
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G W safe value lo hi
    obtain ⟨p,hp,short⟩ : ∃ p ∈ W, 0 < cost (d+1) G W p := by
      by_contra! none
      have zero : total (d+1) G W = 0 := sum_eq_zero (fun x hx => by have := none x hx; omega)
      omega
    obtain ⟨E,v,fresh,safe',_,parents,paid⟩ := private_step safe (by omega) (by omega) hp short
    have card := card_insert_of_notMem fresh
    by_cases lastTwo : k = 2
    · by_contra! bad
      apply unit_no_private_parent safe' lower hq (by omega) (by omega) (by omega)
        (mem_insert_of_mem hp) (mem_insert_self v W)
      intro x hx
      rcases mem_insert.mp hx with rfl | old
      · have ne : x ≠ p := fun eq => fresh (eq ▸ hp)
        simp [ne,loopfree safe' (by omega) (mem_insert_self x W)]
      · exact parents x old
    · have next := ih (total (d+1) E (insert v W)) (by omega) E (insert v W) safe' rfl
        (by omega) (by omega)
      omega

/-- At any cutoff the overshoot g exceeds the distance e from the top order
by the amount imposed by the two-step completion bound. -/
theorem frontier_overshoot_bound {q d : ℕ} {O : Origin q (d+1)} {st : State}
    (fr : Frontier O st) (hq : 2 ≤ q) (short : total (d+1) st.H st.U < d+1)
    {g e : ℕ} (positive : 0 < g) (top : O.V.card + e = q*(d+1))
    (cost : O.V.card + g = st.U.card + total (d+1) st.H st.U) :
    e+4 ≤ q+g := by
  have proper := fr.proper
  have bound := completion_order_lower (rreach_valid O fr.reached).2.2 fr.lower hq
    (by omega) short
  rw [Nat.mul_add,Nat.mul_one] at top
  omega

/-- At triangle cutoff g ≥ e+1, in particular g ≥ 2 one vertex below the top. -/
theorem triangle_frontier_overshoot {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (short : total (d+1) st.H st.U < d+1)
    {g e : ℕ} (positive : 0 < g) (top : O.V.card + e = 3*(d+1))
    (cost : O.V.card + g = st.U.card + total (d+1) st.H st.U) :
    e < g := by
  have := frontier_overshoot_bound fr (by decide) short positive top cost
  omega

/-- Each deficit level is controlled even when it contains more than q rows.
Use the lower-degree order law on the reversed digraph of these same rows. -/
theorem reverse_level_bound {q d : ℕ} {O : Origin q (d+1)} {st : State}
    (fr : Frontier O st) (hq : 1 ≤ q) (small : total (d+1) st.H st.U < d+1)
    {j b : ℕ} (pos : 0 < j) (budget : st.U.card + total (d+1) st.H st.U ≤ q*d+1+b)
    {S : Finset ℕ} (sub : S ⊆ st.U) (live : S.Nonempty)
    (level : ∀ x ∈ S, j ≤ cost (d+1) st.H st.U x) :
    q*j + q*S.card + 1 ≤ q*b + S.card := by
  classical
  let D := st.H
  let rev : CH.Digraph := fun x y => D y x
  let a := cost (d+1) D st.U
  have safe : QFree D st.U q := (rreach_valid O fr.reached).2.2
  obtain ⟨v,hv,least⟩ := S.exists_min_image (fun x => (outN rev S x).card) live
  let P := outN rev S v
  let B := S.erase v \ P
  have ps : P ⊆ S.erase v := by
    intro x hx
    obtain ⟨xs,edge⟩ := mem_outN.mp hx
    exact mem_erase.mpr ⟨fun eq => loopfree safe hq (sub hv) (eq ▸ edge),xs⟩
  have count := sum_le_sum (s:=S) (f:=fun _ => 1) (g:=a)
    (fun x hx => by have := level x hx; change 1 ≤ cost (d+1) st.H st.U x; omega)
  simp only [sum_const,Nat.nsmul_eq_mul,Nat.mul_one] at count
  have extSum := sum_le_sum_of_subset_of_nonneg (f:=a) sub (fun _ _ _ => Nat.zero_le _)
  change _ ≤ total (d+1) st.H st.U at extSum
  have pc : P.card ≤ S.card := card_le_card outN_subset
  have pk : P.card < d+1 := by omega
  have lower := fr.lower_degrees P.card pk rev S (safe.reverse.mono_set sub) least live
  have cut := short_row_price (s:=d+1) safe (by simpa using fr.lower) hq small
    (sub hv) (by have := level v hv; change 0 < cost (d+1) st.H st.U v; omega)
    (show B ⊆ st.U.erase v from sdiff_subset.trans (erase_subset_erase v sub)) (by
      intro x hx
      obtain ⟨xe,miss⟩ := mem_sdiff.mp hx
      have xs := mem_of_mem_erase xe
      exact ⟨lt_of_lt_of_le pos (level x xs), fun e => miss (mem_outN.mpr ⟨xs,e⟩)⟩)
  have parts : B.card + P.card = (S.erase v).card := card_sdiff_add_card_eq_card ps
  rw [card_erase_of_mem hv] at parts
  have nonce := card_pos.mpr live
  have lev := level v hv
  change q*d+1+1+cost (d+1) st.H st.U v+B.card ≤ st.U.card + total (d+1) st.H st.U at cut
  have row : j+S.card ≤ b+P.card := by omega
  have scale := Nat.mul_le_mul_left q row
  simp only [Nat.mul_add] at scale
  omega

/-- A reachable state can lose at most one original head per missing label in any row. -/
theorem cost_le_holes {q s : ℕ} (O : Origin q s) {st : State}
    (reach : Reach (RStep q s) O.init st) {x : ℕ} (hx : x ∈ st.U) :
    cost s st.H st.U x ≤ O.V.card - st.U.card := by
  have sub := (rreach_valid O reach).1
  have keep := rstep_originalKept O reach
  have row : outN O.G O.V x ⊆ outN st.H st.U x ∪ (O.V \ st.U) := by
    intro y hy
    obtain ⟨yv,xy⟩ := mem_outN.mp hy
    by_cases yu : y ∈ st.U
    · exact mem_union_left _ (mem_outN.mpr ⟨yu,keep x hx y yu xy⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨yv,yu⟩)
  have count := (card_le_card row).trans (card_union_le _ _)
  rw [card_sdiff_of_subset sub] at count
  have := O.deg x (sub hx)
  unfold cost
  omega

/-- At budget 3 above the lower-degree order the positive levels have at most
two rows at level 1, one at level 2, and none at level 3. -/
theorem triangle_second_budget {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (budget : st.U.card + total (d+1) st.H st.U ≤ 3*d+4) :
    total (d+1) st.H st.U ≤ 3 ∧ total (d+1) st.H st.U ≤ O.V.card - st.U.card + 1 := by
  classical
  let a := cost (d+1) st.H st.U
  let L (j : ℕ) := st.U.filter (fun x => j ≤ a x)
  have width (j : ℕ) (pos : 0 < j) (live : (L j).Nonempty) :
      3*j+3*(L j).card+1 ≤ 3*3+(L j).card :=
    reverse_level_bound fr (by decide) small pos budget (filter_subset _ _) live
      (fun _ hx => (mem_filter.mp hx).2)
  have level1 : (L 1).card ≤ 2 := by
    by_contra! h
    have := width 1 (by decide) (card_pos.mp (by omega))
    omega
  have level2 : (L 2).card ≤ 1 := by
    by_contra! h
    have := width 2 (by decide) (card_pos.mp (by omega))
    omega
  have ceiling (x) (hx : x ∈ st.U) : a x ≤ 2 := by
    by_contra! h
    have hit : x ∈ L 3 := mem_filter.mpr ⟨hx,h⟩
    have nonempty : (L 3).Nonempty := ⟨x,hit⟩
    have := width 3 (by decide) nonempty
    have := card_pos.mpr nonempty
    omega
  have layers : total (d+1) st.H st.U = (L 1).card + (L 2).card := by
    change ∑ x ∈ st.U, a x = _ + _
    simp only [L,card_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    have := ceiling x hx
    split_ifs <;> omega
  constructor
  · omega
  · by_cases hi : 2 ≤ O.V.card - st.U.card
    · omega
    have zero : L 2 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hit
      obtain ⟨hx,h2⟩ := mem_filter.mp hit
      have bound := cost_le_holes O fr.reached hx
      change 2 ≤ cost (d+1) st.H st.U x at h2
      omega
    rw [zero,card_empty] at layers
    have := fr.proper
    omega

/-- At least three surplus vertices are necessary for any positive overshoot
one below the triangle top. This uses no tight-row conjecture. -/
theorem lower_order_overshoot_three {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (short : total (d+1) st.H st.U < d+1)
    (order : O.V.card+1 = 3*(d+1)) {g : ℕ} (positive : 0 < g)
    (cost : O.V.card + g = st.U.card + total (d+1) st.H st.U) :
    3 ≤ g := by
  have first := triangle_frontier_overshoot fr short positive order cost
  by_contra! small
  have second := (triangle_second_budget fr short (by omega)).2
  have := fr.proper
  omega

/-- The literal candidate supplies the same recursive frontier, with the two
small overshoots removed at the lower triangle order. -/
theorem candidate_alternatives_with_orders {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 1 ≤ q) (free : QFree D V q) (live : V.Nonempty) (bound : V.card ≤ q*s)
    (degree : ∀ x ∈ V, s ≤ (outN D V x).card) :
    ∃ d, d+1 ≤ s ∧ ∃ (O : Origin q (d+1)) (st : State), Frontier O st ∧
      Alternatives O st ∧
      (q = 3 → O.V.card+1 = q*(d+1) → total (d+1) st.H st.U < d+1 →
        ∀ g, 0 < g → O.V.card+g = st.U.card+total (d+1) st.H st.U → 3 ≤ g) := by
  obtain ⟨d,le,O,st,fr,alt⟩ := candidate_alternatives hq free live bound degree
  refine ⟨d,le,O,st,fr,alt,?_⟩
  rintro rfl order small g positive price
  exact lower_order_overshoot_three fr small order positive price

#print axioms unit_no_private_parent
#print axioms completion_order_lower
#print axioms frontier_overshoot_bound
#print axioms triangle_frontier_overshoot
#print axioms reverse_level_bound
#print axioms cost_le_holes
#print axioms triangle_second_budget
#print axioms lower_order_overshoot_three
#print axioms candidate_alternatives_with_orders
end LeanCH.BR.Closure.PrivateCompletionOrder
