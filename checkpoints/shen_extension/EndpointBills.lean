import checkpoints.shen_extension.CycleSpread

/-!
# Endpoint bills for `L` and its replacement `L' = insert v (L.erase t)` (20 November 2026)

Physical labels throughout: `L` is the alternative cycle, `r → t` its arc into `t`, `j` the successor of `t`,
`v ∉ L` the common head with `r → v` new and `v → j` old, `P = L.erase t` the common path, and
`L' = insert v P`.

* `uniform`, `col_uniform`, `uniform_dual`: weight `1/(q+1)` on a shortest cycle `K` is a dual of a subgraph
  `E` of `D` exactly when no vertex outside `K` has two `E`-parents on `K`.
* `uniform_attach`: if no vertex outside `K` has two F-parents on `K`, that weight is an old dual and also a
  dual after attaching `K`. So it pays the common path and every endpoint bill of `K`, each with equality.
* `endpoint_L'`, `endpoint_L`, `both_fail`: in the E1 geometry, `t` is never doubly fed by `L'` and, since
  `r → v` is new, `v` is never doubly fed by `L`. If neither `L` nor `L'` attaches, there are doubly fed
  vertices `z, z' ∉ L ∪ {v}`: `z` has two F-parents in `P ∪ {v}` and `z'` two in `P ∪ {t}`. `split_parents`
  says each has two F-parents on the common path itself or uses the swapped endpoint.
* `swap_targets`, `e1_fewer_targets`, `least_e1`: replacing `t` by `v` removes `t` and `j` from the targets
  and adds only `v`. A least-target alternative cycle therefore cannot have both `r → t` and `t → j` new.
* `swap_old_targets`: for a doubly fed `z` entered and left by old arcs, the swap loses both cycle vertices
  around the replaced one and adds nothing. Under the least choice, those two `L`-arcs are old.
-/

namespace LeanCH.BR.Closure.EndpointBills
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier
open ShenCycleSuccessor MarkedCyclePeeling

/-! ### The uniform cycle dual -/

/-- Weight `1/(q+1)` on every vertex of `K`. -/
noncomputable def uniform (q : ℕ) (K : Finset ℕ) (i : ℕ) : ℝ := if i ∈ K then 1 / ((q : ℝ) + 1) else 0

theorem col_uniform {q : ℕ} {E : CH.Digraph} {V K : Finset ℕ} (ks : K ⊆ V) (z : ℕ) :
    realCol q E V (uniform q K) z =
      ((if z ∈ K then 1 else 0) + q * (inN E K z).card) / ((q : ℝ) + 1) := by
  classical
  have meet : inN E V z ∩ K = inN E K z := by
    ext i
    simp only [mem_inter, mem_inN]
    exact ⟨fun ⟨⟨_, e⟩, ik⟩ => ⟨ik, e⟩, fun ⟨ik, e⟩ => ⟨⟨ks ik, e⟩, ik⟩⟩
  have inw : realInW E V (uniform q K) z = (inN E K z).card / ((q : ℝ) + 1) := by
    rw [realInW_eq_mass_inN]
    unfold realMass uniform
    rw [sum_ite_mem, meet, sum_const, nsmul_eq_mul]
    ring
  rw [realCol, inw]
  unfold uniform
  split_ifs <;> ring

/-- **Uniform cycle dual.** -/
theorem uniform_dual {q : ℕ} (hq : 2 ≤ q) {D E : CH.Digraph} {V K : Finset ℕ}
    (ck : Cycle D V q K) (sub : ∀ a b, E a b = true → D a b = true) :
    RealDual q E V 1 (uniform q K) ↔ ∀ z ∈ V, z ∉ K → (inN E K z).card ≤ 1 := by
  classical
  have den : (0 : ℝ) < q + 1 := by positivity
  have q2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have colle (z : ℕ) : realCol q E V (uniform q K) z ≤ 1 ↔
      (if z ∈ K then 1 else 0) + (q : ℝ) * (inN E K z).card ≤ q + 1 := by
    rw [col_uniform ck.sub, div_le_iff₀ den, one_mul]
  constructor
  · intro dual z zv zk
    have h := (colle z).mp (dual.columns z zv)
    simp only [zk, ↓reduceIte, zero_add] at h
    by_contra! two
    have : (2 : ℝ) ≤ (inN E K z).card := by exact_mod_cast two
    nlinarith
  · intro outside
    refine ⟨fun i _ => by unfold uniform; split_ifs <;> positivity, ?_,
      fun z zv => (colle z).mpr ?_⟩
    · unfold realMass uniform
      rw [sum_ite_mem, inter_eq_right.mpr ck.sub, sum_const, nsmul_eq_mul, ck.size]
      push_cast
      field_simp
    · by_cases zk : z ∈ K
      · have one : (inN E K z).card ≤ 1 := by
          have sub' : inN E K z ⊆ inN D K z := fun x hx =>
            mem_inN.mpr ⟨(mem_inN.mp hx).1, sub _ _ (mem_inN.mp hx).2⟩
          have c1 : (inN D K z).card = 1 := ck.incoming z zk
          have := card_le_card sub'
          omega
        have : ((inN E K z).card : ℝ) ≤ 1 := by exact_mod_cast one
        simp only [zk, ↓reduceIte]
        nlinarith
      · have : ((inN E K z).card : ℝ) ≤ 1 := by exact_mod_cast outside z zv zk
        simp only [zk, ↓reduceIte, zero_add]
        nlinarith

/-- **A cycle with no doubly fed outside vertex attaches.** The uniform weight is an old dual and remains a
dual after attaching `K`. By `SharedArcBudget.fits_iff` it pays every new arc of `K`. -/
theorem uniform_attach {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V K : Finset ℕ} {F : Family}
    (ck : Cycle D V q K) (single : ∀ z ∈ V, z ∉ K → (inN (graph D F) K z).card ≤ 1) :
    RealDual q (graph D F) V 1 (uniform q K) ∧
      RealDual q (graph D (insert K F)) V 1 (uniform q K) := by
  classical
  refine ⟨(uniform_dual hq ck (fun _ _ e => CrossValueOmissions.selected_sub e)).mpr single,
    (uniform_dual hq ck (fun _ _ e => CrossValueOmissions.selected_sub e)).mpr ?_⟩
  intro z zv zk
  refine (card_le_card ?_).trans (single z zv zk)
  intro x hx
  obtain ⟨xk, e⟩ := mem_inN.mp hx
  rcases SharedArcComponentExchange.union_arc.mp e with old | fresh
  · exact mem_inN.mpr ⟨xk, old⟩
  · exact (zk (SharedArcComponentExchange.mem_added.mp fresh).2.1).elim

/-- If `K` cannot be attached, some vertex outside `K` has two F-parents on `K`. -/
theorem doubly_fed {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V K : Finset ℕ} {F : Family}
    (ck : Cycle D V q K) (bad : ¬ SmallRow q (graph D (insert K F)) V) :
    ∃ z ∈ V, z ∉ K ∧ 2 ≤ (inN (graph D F) K z).card := by
  by_contra! none
  exact bad (smallRow_of_realDual (uniform_attach hq ck (fun z zv zk => by
    have := none z zv zk; omega)).2)

/-! ### The two endpoint choices in the E1 geometry -/

/-- **`L'` attaches** unless some vertex outside `L ∪ {v}` has two F-parents on `L'`. The removed vertex
`t` is never doubly fed: its only possible parents in `L'` lie in `L`, and `v ↛ t`. -/
theorem endpoint_L' {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V L : Finset ℕ} {F : Family} {t v : ℕ}
    (free : QFree D V q) (cy : Cycle D V q L) (cy' : Cycle D V q (insert v (L.erase t)))
    (tl : t ∈ L) (vv : v ∈ V) (tv : D t v = true)
    (single : ∀ z ∈ V, z ∉ L → z ≠ v → (inN (graph D F) (insert v (L.erase t)) z).card ≤ 1) :
    RealDual q (graph D F) V 1 (uniform q (insert v (L.erase t))) ∧
      RealDual q (graph D (insert (insert v (L.erase t)) F)) V 1 (uniform q (insert v (L.erase t))) := by
  classical
  apply uniform_attach hq cy'
  intro z zv zk
  by_cases zt : z = t
  · subst zt
    have sub : inN (graph D F) (insert v (L.erase z)) z ⊆ inN D L z := by
      intro x hx
      obtain ⟨xm, e⟩ := mem_inN.mp hx
      have de := CrossValueOmissions.selected_sub e
      rcases mem_insert.mp xm with rfl | xe
      · exact (digonfree free hq (cy.sub tl) vv tv de).elim
      · exact mem_inN.mpr ⟨(mem_erase.mp xe).2, de⟩
    have := card_le_card sub
    have c1 : (inN D L z).card = 1 := cy.incoming z tl
    omega
  · have zl : z ∉ L := fun m => zk (mem_insert_of_mem (mem_erase.mpr ⟨zt, m⟩))
    have zv' : z ≠ v := fun e => zk (e ▸ mem_insert_self _ _)
    exact single z zv zl zv'

/-- **`L` attaches** unless some vertex outside `L ∪ {v}` has two F-parents on `L`. Because `r → v` is
new and `v`'s parents on `L` are `r` and `t`, `v` has at most one F-parent on `L`. -/
theorem endpoint_L {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V L : Finset ℕ} {F : Family} {r t v : ℕ}
    (cy : Cycle D V q L) (parents : inN D L v ⊆ {r, t}) (newrv : graph D F r v = false)
    (single : ∀ z ∈ V, z ∉ L → z ≠ v → (inN (graph D F) L z).card ≤ 1) :
    RealDual q (graph D F) V 1 (uniform q L) ∧
      RealDual q (graph D (insert L F)) V 1 (uniform q L) := by
  classical
  apply uniform_attach hq cy
  intro z zv zl
  by_cases zv' : z = v
  · subst zv'
    have sub : inN (graph D F) L z ⊆ {t} := by
      intro x hx
      obtain ⟨xl, e⟩ := mem_inN.mp hx
      have hx' := parents (mem_inN.mpr ⟨xl, CrossValueOmissions.selected_sub e⟩)
      simp only [mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact (Bool.noConfusion (newrv.symm.trans e))
      · exact mem_singleton_self _
    simpa using card_le_card sub
  · exact single z zv zl zv'

/-- **Both endpoint choices fail only through two doubly fed vertices outside `L ∪ {v}`.** -/
theorem both_fail {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V L : Finset ℕ} {F : Family} {r t v : ℕ}
    (free : QFree D V q) (cy : Cycle D V q L) (cy' : Cycle D V q (insert v (L.erase t)))
    (tl : t ∈ L) (vv : v ∈ V) (tv : D t v = true) (parents : inN D L v ⊆ {r, t})
    (newrv : graph D F r v = false)
    (badL : ¬ SmallRow q (graph D (insert L F)) V)
    (badL' : ¬ SmallRow q (graph D (insert (insert v (L.erase t)) F)) V) :
    (∃ z ∈ V, z ∉ L ∧ z ≠ v ∧ 2 ≤ (inN (graph D F) (insert v (L.erase t)) z).card) ∧
      ∃ z ∈ V, z ∉ L ∧ z ≠ v ∧ 2 ≤ (inN (graph D F) L z).card := by
  constructor
  · by_contra! none
    exact badL' (smallRow_of_realDual (endpoint_L' hq free cy cy' tl vv tv (fun z zv zl zv' => by
      have := none z zv zl zv'; omega)).2)
  · by_contra! none
    exact badL (smallRow_of_realDual (endpoint_L hq cy parents newrv (fun z zv zl zv' => by
      have := none z zv zl zv'; omega)).2)

/-- Two F-parents on `insert x P` are either two on `P` or `x` together with one on `P`. -/
theorem split_parents {E : CH.Digraph} {P : Finset ℕ} {x z : ℕ}
    (two : 2 ≤ (inN E (insert x P) z).card) :
    2 ≤ (inN E P z).card ∨ (E x z = true ∧ 1 ≤ (inN E P z).card) := by
  classical
  by_cases xp : x ∈ P
  · left
    rwa [insert_eq_of_mem xp] at two
  · have eq : inN E (insert x P) z = if E x z = true then insert x (inN E P z) else inN E P z := by
      unfold inN
      rw [filter_insert]
    by_cases e : E x z = true
    · rw [eq, if_pos e, card_insert_of_notMem (fun m => xp (mem_inN.mp m).1)] at two
      by_cases two' : 2 ≤ (inN E P z).card
      · exact Or.inl two'
      · exact Or.inr ⟨e, by omega⟩
    · rw [eq, if_neg e] at two
      exact Or.inl two

/-! ### Targets under the swap, and the least-target choice -/

/-- Targets of the swapped cycle `M' = insert z (M.erase u)`, where `a → z → b` replaces `a → u → b`. -/
theorem swap_targets {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {F : Family} {a u z b : ℕ}
    (cm' : Cycle D V q (insert z (M.erase u)))
    (am : a ∈ M) (au : a ≠ u) (az : D a z = true) (bm : b ∈ M) (bu : b ≠ u) (zb : D z b = true)
    {y : ℕ} (hy : y ∈ SharedArcBarrier.targets D V F (insert z (M.erase u))) :
    (y ∈ SharedArcBarrier.targets D V F M ∧ y ≠ u ∧ y ≠ b) ∨
      (y = z ∧ graph D F a z = false) ∨ (y = b ∧ graph D F z b = false) := by
  classical
  obtain ⟨yv, ym', x, xm', xy, missing⟩ := mem_filter.mp hy
  have am' : a ∈ insert z (M.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨au, am⟩)
  have bm' : b ∈ insert z (M.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨bu, bm⟩)
  have zm' : z ∈ insert z (M.erase u) := mem_insert_self _ _
  by_cases yz : y = z
  · subst yz
    have xa : x = a := card_le_one.mp (cm'.incoming y ym').le x (mem_inN.mpr ⟨xm', xy⟩)
      a (mem_inN.mpr ⟨am', az⟩)
    subst xa
    exact Or.inr (Or.inl ⟨rfl, missing⟩)
  · by_cases yb : y = b
    · subst yb
      have xz : x = z := card_le_one.mp (cm'.incoming y ym').le x (mem_inN.mpr ⟨xm', xy⟩)
        z (mem_inN.mpr ⟨zm', zb⟩)
      subst xz
      exact Or.inr (Or.inr ⟨rfl, missing⟩)
    · left
      have ye := (mem_insert.mp ym').resolve_left yz
      obtain ⟨yu, ym⟩ := mem_erase.mp ye
      have xz : x ≠ z := by
        rintro rfl
        exact yb (card_le_one.mp (cm'.heads x xm').le y (mem_outN.mpr ⟨ym', xy⟩)
          b (mem_outN.mpr ⟨bm', zb⟩))
      have xm := (mem_erase.mp ((mem_insert.mp xm').resolve_left xz)).2
      exact ⟨mem_filter.mpr ⟨yv, ym, x, xm, xy, missing⟩, yu, yb⟩

/-- **E1 swap has fewer targets** when both `r → t` and `t → j` are new. -/
theorem e1_fewer_targets {q : ℕ} {D : CH.Digraph} {V L : Finset ℕ} {F : Family} {r t v j : ℕ}
    (cy' : Cycle D V q (insert v (L.erase t)))
    (rl : r ∈ L) (rt : r ≠ t) (rv : D r v = true) (jl : j ∈ L) (jt : j ≠ t) (vj : D v j = true)
    (oldvj : graph D F v j = true)
    (tT : t ∈ SharedArcBarrier.targets D V F L) (jT : j ∈ SharedArcBarrier.targets D V F L) :
    (SharedArcBarrier.targets D V F (insert v (L.erase t))).card <
      (SharedArcBarrier.targets D V F L).card := by
  classical
  have sub : SharedArcBarrier.targets D V F (insert v (L.erase t)) ⊆
      insert v (((SharedArcBarrier.targets D V F L).erase t).erase j) := by
    intro y hy
    rcases swap_targets cy' rl rt rv jl jt vj hy with ⟨yT, yt, yj⟩ | ⟨rfl, _⟩ | ⟨rfl, miss⟩
    · exact mem_insert_of_mem (mem_erase.mpr ⟨yj, mem_erase.mpr ⟨yt, yT⟩⟩)
    · exact mem_insert_self _ _
    · exact (Bool.noConfusion (miss.symm.trans oldvj))
  have c := card_le_card sub
  have e1 := card_insert_le v (((SharedArcBarrier.targets D V F L).erase t).erase j)
  rw [card_erase_of_mem (mem_erase.mpr ⟨jt, jT⟩), card_erase_of_mem tT] at e1
  have pos : 2 ≤ (SharedArcBarrier.targets D V F L).card := by
    have : ({t, j} : Finset ℕ) ⊆ SharedArcBarrier.targets D V F L :=
      insert_subset tT (singleton_subset_iff.mpr jT)
    have h2 : ({t, j} : Finset ℕ).card = 2 := by simp [jt.symm]
    exact h2 ▸ card_le_card this
  omega

/-- **The least-target choice and E1.** If `L` has the fewest targets among boundary cycles and the swap
`L'` is a boundary cycle, then `r → t` and `t → j` are not both new. -/
theorem least_e1 {q n : ℕ} (X : Model q n) {F : Family} {L : Finset ℕ} {r t v j : ℕ}
    (least : ∀ M, SharedArcBarrier.Boundary X F M →
      (SharedArcBarrier.targets X.D X.V F L).card ≤ (SharedArcBarrier.targets X.D X.V F M).card)
    (bd : SharedArcBarrier.Boundary X F (insert v (L.erase t)))
    (cy' : Cycle X.D X.V q (insert v (L.erase t)))
    (rl : r ∈ L) (rt : r ≠ t) (rv : X.D r v = true) (jl : j ∈ L) (jt : j ≠ t) (vj : X.D v j = true)
    (oldvj : graph X.D F v j = true) :
    ¬ (t ∈ SharedArcBarrier.targets X.D X.V F L ∧ j ∈ SharedArcBarrier.targets X.D X.V F L) := by
  rintro ⟨tT, jT⟩
  have lt := e1_fewer_targets cy' rl rt rv jl jt vj oldvj tT jT
  exact (least _ bd).not_gt lt

/-- **A doubly fed vertex swapped in by old arcs.** If `z ∉ M` is entered from `a` and leaves to `b` by old
arcs, the swap `insert z (M.erase u)` keeps only targets of `M` other than `u` and `b`. -/
theorem swap_old_targets {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {F : Family} {a u z b : ℕ}
    (cm' : Cycle D V q (insert z (M.erase u)))
    (am : a ∈ M) (au : a ≠ u) (az : D a z = true) (bm : b ∈ M) (bu : b ≠ u) (zb : D z b = true)
    (oldaz : graph D F a z = true) (oldzb : graph D F z b = true) :
    SharedArcBarrier.targets D V F (insert z (M.erase u)) ⊆
      ((SharedArcBarrier.targets D V F M).erase u).erase b := by
  intro y hy
  rcases swap_targets cm' am au az bm bu zb hy with ⟨yT, yu, yb⟩ | ⟨_, miss⟩ | ⟨_, miss⟩
  · exact mem_erase.mpr ⟨yb, mem_erase.mpr ⟨yu, yT⟩⟩
  · exact (Bool.noConfusion (miss.symm.trans oldaz))
  · exact (Bool.noConfusion (miss.symm.trans oldzb))

/-- **The least choice against a doubly fed vertex that points back into `L`.** If `z ∉ L` has two F-parents
on `L` and an old arc to `b ∈ L`, its parents are consecutive `a → u` with `u → b`, and swapping `z` in for `u`
gives a cycle. If `L` has the fewest targets and that swap is a boundary cycle, then `u` and `b` are not
targets of `L`: the arcs `a → u` and `u → b` are old. -/
theorem least_doubly_fed {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family} {L : Finset ℕ} {z b : ℕ}
    (cy : Cycle X.D X.V q L) (zv : z ∈ X.V) (zl : z ∉ L)
    (fed : 2 ≤ (inN (graph X.D F) L z).card) (bl : b ∈ L) (zb : X.D z b = true)
    (oldzb : graph X.D F z b = true)
    (least : ∀ M, SharedArcBarrier.Boundary X F M →
      (SharedArcBarrier.targets X.D X.V F L).card ≤ (SharedArcBarrier.targets X.D X.V F M).card) :
    ∃ a u, a ∈ L ∧ u ∈ L ∧ X.D a u = true ∧ X.D u b = true ∧ inN X.D L z = {a, u} ∧
      Cycle X.D X.V q (insert z (L.erase u)) ∧
      (SharedArcBarrier.Boundary X F (insert z (L.erase u)) →
        u ∉ SharedArcBarrier.targets X.D X.V F L ∧ b ∉ SharedArcBarrier.targets X.D X.V F L) := by
  classical
  have sub : inN (graph X.D F) L z ⊆ inN X.D L z := fun x hx =>
    mem_inN.mpr ⟨(mem_inN.mp hx).1, CrossValueOmissions.selected_sub (mem_inN.mp hx).2⟩
  have rich : 2 ≤ (inN X.D L z).card := fed.trans (card_le_card sub)
  obtain ⟨a, u, N, shift, cn, parents, _⟩ := CycleSquareTensor.replacement hq X.free cy
    (mem_sdiff.mpr ⟨zv, zl⟩) rich bl zb
  have labels := shift.labels
  subst labels
  have au : a ≠ u := fun e => loopfree X.free (by omega) (cy.sub shift.aM) (e ▸ shift.before₁)
  have bu : b ≠ u := fun e => loopfree X.free (by omega) (cy.sub shift.uM) (e ▸ shift.before₂)
  have same : inN (graph X.D F) L z = inN X.D L z := by
    apply eq_of_subset_of_card_le sub
    rw [parents]
    exact (card_insert_le a {u}).trans (by simpa using fed)
  have oldaz : graph X.D F a z = true := by
    have : a ∈ inN (graph X.D F) L z := by rw [same, parents]; exact mem_insert_self _ _
    exact (mem_inN.mp this).2
  refine ⟨a, u, shift.aM, shift.uM, shift.before₁, shift.before₂, parents, cn, fun bd => ?_⟩
  have fewer := swap_old_targets (V := X.V) (F := F) cn shift.aM au shift.after₁ shift.bM bu zb
    oldaz oldzb
  have le := (least _ bd).trans (card_le_card fewer)
  constructor
  · intro uT
    have := card_erase_le (s := (SharedArcBarrier.targets X.D X.V F L).erase u) (a := b)
    rw [card_erase_of_mem uT] at this
    have pos := card_pos.mpr ⟨u, uT⟩
    omega
  · intro bT
    have bT' : b ∈ (SharedArcBarrier.targets X.D X.V F L).erase u := mem_erase.mpr ⟨bu, bT⟩
    have e1 := card_erase_of_mem bT'
    have e2 := card_erase_le (s := SharedArcBarrier.targets X.D X.V F L) (a := u)
    have pos := card_pos.mpr ⟨b, bT'⟩
    omega

#print axioms uniform_dual
#print axioms uniform_attach
#print axioms doubly_fed
#print axioms endpoint_L'
#print axioms endpoint_L
#print axioms both_fail
#print axioms split_parents
#print axioms e1_fewer_targets
#print axioms least_e1
#print axioms swap_old_targets
#print axioms least_doubly_fed

end LeanCH.BR.Closure.EndpointBills
