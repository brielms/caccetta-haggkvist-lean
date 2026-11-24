import checkpoints.shen_extension.EndpointBills

/-!
# A third price from an old cycle through `v` (20 November 2026)

Physical labels as in `EndpointBills`: the alternative cycle `L`, `r → t` into `t`, the successor `j` of `t`,
`v ∉ L` with `r → v` new and `v → j` old, the common path `P = L.erase t`, and `L' = insert v P`.
Both witnesses are kept:

* `z_v` is fed by `v` and by one path row `x_v`;
* `z_t` is fed by `t` and by one path row `x_t`.

The third price is weight `1/(q+1)` on a shortest cycle `J` through `v`, for example an old cycle through
`v → j`.

* `third_price`: on a child `K`, this price pays exactly when no column `z` off `J` has two old parents on `J`
  ("already over budget in `F`"), and no column off `J` has one old parent on `J` together with a new arc
  `x → z` of `K` leaving `J` ("put over by that new arc").
* `added_L'`, `L'_of_L`: since `v ∈ J`, the arc `r → v` never matters, and every other new arc of `L'` is a
  new arc of the common path, hence of `L`. So the third price pays `L'` whenever it pays `L`.
* `forced_obstruction`: if `L'` cannot be attached, every such `J` has a labelled obstruction of one of the
  two kinds, and a new-arc obstruction sits on a new arc of the common path.
* `witness_on_J`: if `J` contains `v → j` and the path parent `x_v`, the witness `z_v` is itself an old
  obstruction for `J`.
* `new_obstruction_exchange`: a new-arc obstruction `x → z` with an old arc `z → b` back into an all-old `J`
  gives either (i) a boundary cycle `J - y + z` adding exactly the one arc `x → z`, or (ii) an all-old cycle
  `J - x + z` with `y → x → b` on `J`.
* `choose_third_price`: take `J` of maximum `μ`-mass among all-old shortest cycles through `v`, with
  `μ x < μ z` (for example position along `P`). Then (ii) is impossible. If the child is inclusion-minimal
  and adds an arc other than `x → z`, as `L'` does with `r → v`, then (i) is impossible too. So every
  surviving new-arc obstruction has no old arc back into `J`.
-/

namespace LeanCH.BR.Closure.ThirdPrice
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange
open EndpointBills

/-- A child adds at most one new arc into any column: it comes from that column's parent on the child. -/
theorem new_parent_unique {q : ℕ} {D : CH.Digraph} {V K : Finset ℕ} {F : Family}
    (ck : Cycle D V q K) {x x' z : ℕ} (hx : (x, z) ∈ added D F K) (hx' : (x', z) ∈ added D F K) :
    x = x' := by
  obtain ⟨xk, zk, xz, _⟩ := mem_added.mp hx
  obtain ⟨xk', _, xz', _⟩ := mem_added.mp hx'
  exact card_le_one.mp (ck.incoming z zk).le x (mem_inN.mpr ⟨xk, xz⟩) x' (mem_inN.mpr ⟨xk', xz'⟩)

/-- **The third price on a child.** -/
theorem third_price {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V J K : Finset ℕ} {F : Family}
    (cj : Cycle D V q J) (ck : Cycle D V q K) :
    RealDual q (graph D (insert K F)) V 1 (uniform q J) ↔
      ∀ z ∈ V, z ∉ J → (inN (graph D F) J z).card ≤ 1 ∧
        ∀ x ∈ J, (x, z) ∈ added D F K → ∀ y ∈ J, graph D F y z ≠ true := by
  classical
  rw [uniform_dual hq cj (fun _ _ e => CrossValueOmissions.selected_sub e)]
  constructor
  · intro all z zv zj
    have h := all z zv zj
    refine ⟨(card_le_card ?_).trans h, fun x xj hx y yj yz => ?_⟩
    · intro w hw
      obtain ⟨wj, e⟩ := mem_inN.mp hw
      exact mem_inN.mpr ⟨wj, union_arc.mpr (Or.inl e)⟩
    · have xn : x ∈ inN (graph D (insert K F)) J z := mem_inN.mpr ⟨xj, union_arc.mpr (Or.inr hx)⟩
      have yn : y ∈ inN (graph D (insert K F)) J z := mem_inN.mpr ⟨yj, union_arc.mpr (Or.inl yz)⟩
      have xy : x ≠ y := by
        rintro rfl
        exact Bool.noConfusion ((mem_added.mp hx).2.2.2.symm.trans yz)
      exact xy (card_le_one.mp h x xn y yn)
  · intro all z zv zj
    obtain ⟨old, fresh⟩ := all z zv zj
    by_contra! two
    obtain ⟨a, an, b, bn, ab⟩ := one_lt_card.mp two
    obtain ⟨aj, ea⟩ := mem_inN.mp an
    obtain ⟨bj, eb⟩ := mem_inN.mp bn
    rcases union_arc.mp ea with oa | na <;> rcases union_arc.mp eb with ob | nb
    · exact ab (card_le_one.mp old a (mem_inN.mpr ⟨aj, oa⟩) b (mem_inN.mpr ⟨bj, ob⟩))
    · exact fresh b bj nb a aj oa
    · exact fresh a aj na b bj ob
    · exact ab (new_parent_unique ck na nb)

/-! ### The two endpoint children -/

/-- A new arc of `L'` into a column other than `v` is a new arc of the common path. -/
theorem added_L' {q : ℕ} {D : CH.Digraph} {V L : Finset ℕ} {F : Family} {t v j : ℕ}
    (cy' : Cycle D V q (insert v (L.erase t))) (jl : j ∈ L.erase t) (vj : D v j = true)
    (oldvj : graph D F v j = true) {x z : ℕ} (hx : (x, z) ∈ added D F (insert v (L.erase t)))
    (zv : z ≠ v) : (x, z) ∈ added D F (L.erase t) := by
  obtain ⟨xm, zm, xz, miss⟩ := mem_added.mp hx
  have ze := (mem_insert.mp zm).resolve_left zv
  have xv : x ≠ v := by
    rintro rfl
    have eq := card_le_one.mp (cy'.heads x xm).le z (mem_outN.mpr ⟨zm, xz⟩) j
      (mem_outN.mpr ⟨mem_insert_of_mem jl, vj⟩)
    subst eq
    exact Bool.noConfusion (miss.symm.trans oldvj)
  exact mem_added.mpr ⟨(mem_insert.mp xm).resolve_left xv, ze, xz, miss⟩

theorem added_path {D : CH.Digraph} {F : Family} {L : Finset ℕ} {t x z : ℕ}
    (hx : (x, z) ∈ added D F (L.erase t)) : (x, z) ∈ added D F L := by
  obtain ⟨xm, zm, xz, miss⟩ := mem_added.mp hx
  exact mem_added.mpr ⟨mem_of_mem_erase xm, mem_of_mem_erase zm, xz, miss⟩

/-- **The third price pays `L'` whenever it pays `L`.** -/
theorem L'_of_L {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V L J : Finset ℕ} {F : Family} {t v j : ℕ}
    (cj : Cycle D V q J) (cy : Cycle D V q L) (cy' : Cycle D V q (insert v (L.erase t)))
    (vJ : v ∈ J) (jl : j ∈ L.erase t) (vj : D v j = true) (oldvj : graph D F v j = true)
    (paysL : RealDual q (graph D (insert L F)) V 1 (uniform q J)) :
    RealDual q (graph D (insert (insert v (L.erase t)) F)) V 1 (uniform q J) := by
  rw [third_price hq cj cy] at paysL
  rw [third_price hq cj cy']
  intro z zv zj
  obtain ⟨old, fresh⟩ := paysL z zv zj
  refine ⟨old, fun x xj hx => fresh x xj (added_path (added_L' cy' jl vj oldvj hx ?_))⟩
  rintro rfl
  exact zj vJ

/-- **Every third price through `v` meets a labelled obstruction when `L'` fails.** -/
theorem forced_obstruction {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V L J : Finset ℕ} {F : Family}
    {t v j : ℕ} (cj : Cycle D V q J) (cy' : Cycle D V q (insert v (L.erase t)))
    (vJ : v ∈ J) (jl : j ∈ L.erase t) (vj : D v j = true) (oldvj : graph D F v j = true)
    (badL' : ¬ SmallRow q (graph D (insert (insert v (L.erase t)) F)) V) :
    ∃ z ∈ V, z ∉ J ∧ (2 ≤ (inN (graph D F) J z).card ∨
      ∃ x ∈ J, (x, z) ∈ added D F (L.erase t) ∧ ∃ y ∈ J, graph D F y z = true) := by
  by_contra! none
  apply badL'
  apply smallRow_of_realDual (p := uniform q J)
  rw [third_price hq cj cy']
  intro z zv zj
  obtain ⟨one, clean⟩ := none z zv zj
  refine ⟨by omega, fun x xj hx y yj yz => ?_⟩
  have zv' : z ≠ v := fun e => zj (e ▸ vJ)
  exact (clean x xj (added_L' cy' jl vj oldvj hx zv') y yj) yz

/-- **The physical witness `z_v` obstructs `J`** when `J` carries `v → j` and the path parent `x_v`. -/
theorem witness_on_J {q : ℕ} {D : CH.Digraph} {V J : Finset ℕ} {F : Family} {v j z x : ℕ}
    (cj : Cycle D V q J) (vJ : v ∈ J) (jJ : j ∈ J) (vj : D v j = true) (zj : z ≠ j)
    (vz : graph D F v z = true) (xJ : x ∈ J) (xz : graph D F x z = true) (xv : x ≠ v) :
    z ∉ J ∧ 2 ≤ (inN (graph D F) J z).card := by
  classical
  have out : z ∉ J := fun zJ => zj (card_le_one.mp (cj.heads v vJ).le z
    (mem_outN.mpr ⟨zJ, CrossValueOmissions.selected_sub vz⟩) j (mem_outN.mpr ⟨jJ, vj⟩))
  refine ⟨out, ?_⟩
  have sub : ({v, x} : Finset ℕ) ⊆ inN (graph D F) J z :=
    insert_subset (mem_inN.mpr ⟨vJ, vz⟩) (singleton_subset_iff.mpr (mem_inN.mpr ⟨xJ, xz⟩))
  have two : ({v, x} : Finset ℕ).card = 2 := by simp [xv.symm]
  exact two ▸ card_le_card sub

/-! ### A new-arc obstruction with an old return -/

/-- **Exchange at a new-arc obstruction.** Let `J` have only old arcs. Suppose `z ∉ J` receives the new arc
`x → z` of a child from `x ∈ J` and an old arc from `y ∈ J`, and has an old arc back to `b ∈ J`. Then either

* (i) `J - y + z` is a boundary cycle adding exactly the one arc `x → z`; or
* (ii) `y → x → b` on `J`, and `J - x + z` is a cycle with only old arcs. -/
theorem new_obstruction_exchange {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family}
    {J K : Finset ℕ} (cj : Cycle X.D X.V q J)
    (oldJ : ∀ c ∈ J, ∀ d ∈ J, X.D c d = true → graph X.D F c d = true)
    {x y z b : ℕ} (zv : z ∈ X.V) (zj : z ∉ J) (xj : x ∈ J) (hx : (x, z) ∈ added X.D F K)
    (yj : y ∈ J) (yz : graph X.D F y z = true) (bj : b ∈ J) (zb : X.D z b = true)
    (oldzb : graph X.D F z b = true) :
    (Cycle X.D X.V q (insert z (J.erase y)) ∧ Boundary X F (insert z (J.erase y)) ∧
        added X.D F (insert z (J.erase y)) = {(x, z)}) ∨
      (X.D y x = true ∧ X.D x b = true ∧ Cycle X.D X.V q (insert z (J.erase x)) ∧
        added X.D F (insert z (J.erase x)) = ∅) := by
  classical
  obtain ⟨_, _, xz, missx⟩ := mem_added.mp hx
  have xy : x ≠ y := by
    rintro rfl
    exact Bool.noConfusion (missx.symm.trans yz)
  have xin : x ∈ inN X.D J z := mem_inN.mpr ⟨xj, xz⟩
  have yin : y ∈ inN X.D J z := mem_inN.mpr ⟨yj, CrossValueOmissions.selected_sub yz⟩
  have rich : 2 ≤ (inN X.D J z).card := by
    have sub : ({x, y} : Finset ℕ) ⊆ inN X.D J z := insert_subset xin (singleton_subset_iff.mpr yin)
    have two : ({x, y} : Finset ℕ).card = 2 := by simp [xy]
    exact two ▸ card_le_card sub
  obtain ⟨a, u, N, sh, cn, parents, _⟩ := CycleSquareTensor.replacement hq X.free cj
    (mem_sdiff.mpr ⟨zv, zj⟩) rich bj zb
  have labels := sh.labels
  have au : a ≠ u := fun e => loopfree X.free (by omega) (cj.sub sh.uM) (e ▸ sh.before₁)
  have bu : b ≠ u := fun e => loopfree X.free (by omega) (cj.sub sh.uM) (e ▸ sh.before₂)
  have zn : z ∈ N := labels ▸ mem_insert_self _ _
  have an : a ∈ N := labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨au, sh.aM⟩)
  have bn : b ∈ N := labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨bu, bj⟩)
  -- every new arc of N is the arc a → z
  have only : ∀ e ∈ added X.D F N, e = (a, z) := by
    intro e he
    obtain ⟨c, d⟩ := e
    obtain ⟨cn', dn', cd, miss⟩ := mem_added.mp he
    by_cases dz : d = z
    · subst dz
      have ca := card_le_one.mp (cn.incoming d dn').le c (mem_inN.mpr ⟨cn', cd⟩) a
        (mem_inN.mpr ⟨an, sh.after₁⟩)
      rw [ca]
    · by_cases cz : c = z
      · subst cz
        have db := card_le_one.mp (cn.heads c cn').le d (mem_outN.mpr ⟨dn', cd⟩) b
          (mem_outN.mpr ⟨bn, zb⟩)
        subst db
        exact (Bool.noConfusion (miss.symm.trans oldzb))
      · rw [labels] at cn' dn'
        have cJ := mem_of_mem_erase ((mem_insert.mp cn').resolve_left cz)
        have dJ := mem_of_mem_erase ((mem_insert.mp dn').resolve_left dz)
        exact (Bool.noConfusion (miss.symm.trans (oldJ c cJ d dJ cd)))
  have pair : (x = a ∧ y = u) ∨ (x = u ∧ y = a) := by
    have hx' : x ∈ ({a, u} : Finset ℕ) := parents ▸ xin
    have hy' : y ∈ ({a, u} : Finset ℕ) := parents ▸ yin
    simp only [mem_insert, mem_singleton] at hx' hy'
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact (xy rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (xy rfl).elim
  rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have fresh : (x, z) ∈ added X.D F N := mem_added.mpr ⟨an, zn, xz, missx⟩
    have eq : added X.D F N = {(x, z)} := by
      ext e
      simp only [mem_singleton]
      exact ⟨only e, fun h => h ▸ fresh⟩
    have out : N ∉ F := fun inside => Bool.noConfusion (missx.symm.trans
      (active.mpr ⟨N, mem_col.mpr ⟨inside, an, zn, xz⟩⟩))
    obtain ⟨A, ac⟩ := active.mp oldzb
    obtain ⟨af, za, ba, edge⟩ := mem_col.mp ac
    have bd : Boundary X F N := ⟨mem_filter.mpr ⟨mem_powerset.mpr cn.sub, cn⟩, out, A, af,
      z, mem_inter.mpr ⟨za, zn⟩, b, mem_inter.mpr ⟨ba, bn⟩, edge⟩
    rw [← labels]
    exact ⟨cn, bd, eq⟩
  · right
    have empty : added X.D F N = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have := only e he
      subst this
      exact Bool.noConfusion ((mem_added.mp he).2.2.2.symm.trans yz)
    rw [← labels]
    exact ⟨sh.before₁, sh.before₂, cn, empty⟩

/-- **Choosing the third price.** Let `J` maximize `μ`-mass among shortest cycles through `v` with only old
arcs, and let `μ x < μ z` with `x ≠ v`. A new-arc obstruction `x → z` with an old arc back into `J` then
yields a boundary cycle that adds exactly `x → z`. If the child `K` is inclusion-minimal and adds some arc
other than `x → z`, there is no such obstruction. -/
theorem choose_third_price {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family}
    {J K : Finset ℕ} {v : ℕ} (μ : ℕ → ℝ) (cj : Cycle X.D X.V q J) (vJ : v ∈ J)
    (oldJ : ∀ c ∈ J, ∀ d ∈ J, X.D c d = true → graph X.D F c d = true)
    (peak : ∀ J', Cycle X.D X.V q J' → v ∈ J' →
      (∀ c ∈ J', ∀ d ∈ J', X.D c d = true → graph X.D F c d = true) →
      realMass J' μ ≤ realMass J μ)
    {x y z b : ℕ} (zv : z ∈ X.V) (zj : z ∉ J) (xj : x ∈ J) (xv : x ≠ v)
    (hx : (x, z) ∈ added X.D F K) (yj : y ∈ J) (yz : graph X.D F y z = true)
    (bj : b ∈ J) (zb : X.D z b = true) (oldzb : graph X.D F z b = true) (gain : μ x < μ z) :
    Cycle X.D X.V q (insert z (J.erase y)) ∧ Boundary X F (insert z (J.erase y)) ∧
      added X.D F (insert z (J.erase y)) = {(x, z)} ∧
      ((∀ N, Boundary X F N → (added X.D F N).Nonempty → added X.D F N ⊆ added X.D F K →
          added X.D F N = added X.D F K) → added X.D F K = {(x, z)}) := by
  classical
  rcases new_obstruction_exchange X hq cj oldJ zv zj xj hx yj yz bj zb oldzb with
    ⟨cn, bd, eq⟩ | ⟨_, _, cn, empty⟩
  · refine ⟨cn, bd, eq, fun minimal => ?_⟩
    have sub : added X.D F (insert z (J.erase y)) ⊆ added X.D F K := by
      rw [eq]; exact singleton_subset_iff.mpr hx
    have ne : (added X.D F (insert z (J.erase y))).Nonempty := by rw [eq]; exact singleton_nonempty _
    exact (minimal _ bd ne sub).symm.trans eq
  · exfalso
    have vN : v ∈ insert z (J.erase x) := mem_insert_of_mem (mem_erase.mpr ⟨xv.symm, vJ⟩)
    have oldN : ∀ c ∈ insert z (J.erase x), ∀ d ∈ insert z (J.erase x), X.D c d = true →
        graph X.D F c d = true := by
      intro c cm d dm cd
      by_contra miss
      have : (c, d) ∈ added X.D F (insert z (J.erase x)) :=
        mem_added.mpr ⟨cm, dm, cd, Bool.eq_false_iff.mpr miss⟩
      rw [empty] at this
      exact notMem_empty _ this
    have le := peak _ cn vN oldN
    have xnot : z ∉ J.erase x := fun m => zj (mem_of_mem_erase m)
    have mN : realMass (insert z (J.erase x)) μ = μ z + realMass (J.erase x) μ := by
      rw [realMass, sum_insert xnot]; rfl
    have mJ : realMass J μ = μ x + realMass (J.erase x) μ := by
      rw [← insert_erase xj, realMass, sum_insert (notMem_erase x J), erase_insert_eq_erase,
        erase_idem]; rfl
    linarith

#print axioms third_price
#print axioms L'_of_L
#print axioms forced_obstruction
#print axioms witness_on_J
#print axioms new_obstruction_exchange
#print axioms choose_third_price

end LeanCH.BR.Closure.ThirdPrice
