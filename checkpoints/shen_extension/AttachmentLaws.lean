import checkpoints.shen_extension.ThirdPrice
import checkpoints.shen_extension.DepositTrace

/-!
# Drop-in attachment laws for the recursive capstone (20 November 2026)

In the attachment block of `Capstone.lean`, the context has:

* `attachFamily` with `hAttachSmall` (its graph satisfies SmallRow) and an old dual `attachDual`;
* `hEveryAttachment` (no boundary cycle attaches);
* `outsideCycle` with `hAttachBoundary` and the least-target property `hMinimumNewHeads`.

Each theorem below takes those hypotheses as they appear there.

* `closed_family`: every shortest cycle whose arcs are all family arcs already belongs to the family.
  Attaching such a cycle leaves the graph unchanged, so outside the family it would be a boundary cycle that
  does attach.
* `doubly_fed_all`: every boundary cycle has an outside vertex with two family parents on it. Otherwise
  weight `1/(q+1)` on the cycle would attach it.
* `least_swap`: for the least-target cycle and any doubly fed vertex with a family arc back into it, there
  are consecutive parents `a → u` and a swap cycle. Either all new arcs of the cycle lie in the turn
  `{a → u, u → b}`, or `u` and `b` are not targets.
* `price_cap`: the actual old dual has column maximum `C > 1` after attaching `outsideCycle`. This is the
  input for `DepositTrace.two_hit`, `DepositTrace.trace_dichotomy` and `CycleSpread.spread_obstruction`.

The `example` at the end restates the capstone hypotheses with their exact types from the saved goal context
and runs the one-line calls.
-/

namespace LeanCH.BR.Closure.AttachmentLaws
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

/-- **The family is closed under all-old shortest cycles.** -/
theorem closed_family {q n : ℕ} (X : Model q n) {F : Family}
    (small : SmallRow q (graph X.D F) X.V)
    (every : ∀ B, Boundary X F B → ¬ SmallRow q (graph X.D (insert B F)) X.V) :
    ∀ N, Cycle X.D X.V q N → (∀ c ∈ N, ∀ d ∈ N, X.D c d = true → graph X.D F c d = true) → N ∈ F := by
  classical
  intro N cn old
  by_contra off
  have same : graph X.D (insert N F) = graph X.D F := by
    funext c d
    apply Bool.eq_iff_iff.mpr
    rw [union_arc]
    constructor
    · rintro (h | h)
      · exact h
      · obtain ⟨cm, dm, cd, miss⟩ := mem_added.mp h
        exact (Bool.noConfusion (miss.symm.trans (old c cm d dm cd)))
    · exact Or.inl
  obtain ⟨c, cm⟩ := card_pos.mp (by rw [cn.size]; omega : 0 < N.card)
  obtain ⟨d, dm⟩ := card_pos.mp (by rw [cn.heads c cm]; omega : 0 < (outN X.D N c).card)
  obtain ⟨dN, cd⟩ := mem_outN.mp dm
  obtain ⟨A, ac⟩ := active.mp (old c cm d dN cd)
  obtain ⟨af, ca, da, edge⟩ := mem_col.mp ac
  have bd : Boundary X F N := ⟨mem_filter.mpr ⟨mem_powerset.mpr cn.sub, cn⟩, off, A, af,
    c, mem_inter.mpr ⟨ca, cm⟩, d, mem_inter.mpr ⟨da, dN⟩, edge⟩
  exact every N bd (by rw [same]; exact small)

/-- **Every boundary cycle is doubly fed by family arcs.** -/
theorem doubly_fed_all {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family}
    (every : ∀ B, Boundary X F B → ¬ SmallRow q (graph X.D (insert B F)) X.V) :
    ∀ B, Boundary X F B → ∃ z ∈ X.V, z ∉ B ∧ 2 ≤ (inN (graph X.D F) B z).card := by
  classical
  exact fun B b => EndpointBills.doubly_fed hq (mem_filter.mp b.1).2 (every B b)

/-- **The least-target swap at a doubly fed vertex with a family arc back.** -/
theorem least_swap {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family} {L : Finset ℕ}
    (bd : Boundary X F L)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    {z b : ℕ} (zv : z ∈ X.V) (zl : z ∉ L) (fed : 2 ≤ (inN (graph X.D F) L z).card)
    (bl : b ∈ L) (zb : X.D z b = true) (oldzb : graph X.D F z b = true) :
    ∃ a u, a ∈ L ∧ u ∈ L ∧ X.D a u = true ∧ X.D u b = true ∧ inN X.D L z = {a, u} ∧
      Cycle X.D X.V q (insert z (L.erase u)) ∧
      (added X.D F L ⊆ {(a, u), (u, b)} ∨
        (u ∉ targets X.D X.V F L ∧ b ∉ targets X.D X.V F L)) := by
  classical
  have cy : Cycle X.D X.V q L := (mem_filter.mp bd.1).2
  obtain ⟨a, u, am, um, au, ub, parents, cn, conseq⟩ :=
    EndpointBills.least_doubly_fed X hq cy zv zl fed bl zb oldzb least
  refine ⟨a, u, am, um, au, ub, parents, cn, ?_⟩
  have sub : inN (graph X.D F) L z ⊆ inN X.D L z := fun x hx =>
    mem_inN.mpr ⟨(mem_inN.mp hx).1, CrossValueOmissions.selected_sub (mem_inN.mp hx).2⟩
  have same : inN (graph X.D F) L z = inN X.D L z := by
    apply eq_of_subset_of_card_le sub
    rw [parents]
    exact (card_insert_le a {u}).trans (by simpa using fed)
  have oldaz : graph X.D F a z = true := by
    have : a ∈ inN (graph X.D F) L z := by rw [same, parents]; exact mem_insert_self _ _
    exact (mem_inN.mp this).2
  have uz : u ≠ z := fun e => zl (e ▸ um)
  have au' : a ≠ u := fun e => loopfree X.free (by omega) (cy.sub um) (e ▸ au)
  have an : a ∈ insert z (L.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨au', am⟩)
  have zn : z ∈ insert z (L.erase u) := mem_insert_self _ _
  by_cases inF : insert z (L.erase u) ∈ F
  · left
    intro e he
    obtain ⟨c, d⟩ := e
    obtain ⟨cm, dm, cd, miss⟩ := mem_added.mp he
    by_cases du : d = u
    · subst du
      have ca := card_le_one.mp (cy.incoming d dm).le c (mem_inN.mpr ⟨cm, cd⟩) a
        (mem_inN.mpr ⟨am, au⟩)
      simp [ca]
    · by_cases cu : c = u
      · subst cu
        have db := card_le_one.mp (cy.heads c cm).le d (mem_outN.mpr ⟨dm, cd⟩) b
          (mem_outN.mpr ⟨bl, ub⟩)
        simp [db]
      · exfalso
        have cN : c ∈ insert z (L.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨cu, cm⟩)
        have dN : d ∈ insert z (L.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨du, dm⟩)
        exact Bool.noConfusion (miss.symm.trans (active.mpr ⟨_, mem_col.mpr ⟨inF, cN, dN, cd⟩⟩))
  · right
    have bdN : Boundary X F (insert z (L.erase u)) := by
      obtain ⟨A, ac⟩ := active.mp oldaz
      obtain ⟨af, aa, za, edge⟩ := mem_col.mp ac
      exact ⟨mem_filter.mpr ⟨mem_powerset.mpr cn.sub, cn⟩, inF, A, af,
        a, mem_inter.mpr ⟨aa, an⟩, z, mem_inter.mpr ⟨za, zn⟩, edge⟩
    exact conseq bdN

/-- **The price ceiling of the actual old dual after attaching the boundary cycle.** -/
theorem price_cap {q n : ℕ} (X : Model q n) {F : Family} {L : Finset ℕ}
    (bad : ¬ SmallRow q (graph X.D (insert L F)) X.V)
    {p : ℕ → ℝ} (old : RealDual q (graph X.D F) X.V 1 p) :
    ∃ C : ℝ, 1 < C ∧ (∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C) ∧
      ∃ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j = C := by
  classical
  obtain ⟨b, bv, top⟩ := X.V.exists_max_image (realCol q (graph X.D (insert L F)) X.V p) X.live
  refine ⟨realCol q (graph X.D (insert L F)) X.V p b, ?_, top, b, bv, rfl⟩
  by_contra! low
  exact bad (smallRow_of_realDual ⟨old.nonneg, old.normalized, fun k kv => (top k kv).trans low⟩)

#print axioms closed_family
#print axioms doubly_fed_all
#print axioms least_swap
#print axioms price_cap

/-! ### Catalog form -/

/-- The attachment laws for every family whose graph is small and none of whose boundary cycles attaches. -/
def OnModel {q n : ℕ} (X : Model q n) : Prop :=
  ∀ F : Family, SmallRow q (graph X.D F) X.V →
    (∀ B, Boundary X F B → ¬ SmallRow q (graph X.D (insert B F)) X.V) →
    (∀ N, Cycle X.D X.V q N → (∀ c ∈ N, ∀ d ∈ N, X.D c d = true → graph X.D F c d = true) → N ∈ F) ∧
    (∀ B, Boundary X F B → ∃ z ∈ X.V, z ∉ B ∧ 2 ≤ (inN (graph X.D F) B z).card) ∧
    (∀ L, Boundary X F L →
      (∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card) →
      ∀ z b, z ∈ X.V → z ∉ L → 2 ≤ (inN (graph X.D F) L z).card → b ∈ L → X.D z b = true →
        graph X.D F z b = true →
        ∃ a u, a ∈ L ∧ u ∈ L ∧ X.D a u = true ∧ X.D u b = true ∧ inN X.D L z = {a, u} ∧
          Cycle X.D X.V q (insert z (L.erase u)) ∧
          (added X.D F L ⊆ {(a, u), (u, b)} ∨
            (u ∉ targets X.D X.V F L ∧ b ∉ targets X.D X.V F L))) ∧
    (∀ L, Boundary X F L → ∀ p : ℕ → ℝ, RealDual q (graph X.D F) X.V 1 p →
      ∃ C : ℝ, 1 < C ∧ (∀ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j ≤ C) ∧
        ∃ j ∈ X.V, realCol q (graph X.D (insert L F)) X.V p j = C)

theorem on_model {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) : OnModel X := by
  intro F small every
  refine ⟨closed_family X small every, doubly_fed_all X hq every, ?_, ?_⟩
  · intro L bd least z b zv zl fed bl zb oldzb
    exact least_swap X hq bd least zv zl fed bl zb oldzb
  · intro L bd p old
    exact price_cap X (every L bd) old

#print axioms on_model

/-! ### Interface test with the capstone's hypothesis types

The binders below copy the types of `attachFamily`, `hAttachSmall`, `attachDual`, `hAttachDual`,
`hEveryAttachment`, `outsideCycle`, `hAttachBoundary` and `hMinimumNewHeads` from the saved goal context of
`Capstone.lean`. The body is the proposed block of `all_goals have` lines. -/
example {q dualBudget : ℕ} (hq : 3 ≤ q) (dualSource : Model q dualBudget)
    (attachFamily : Family)
    (hAttachSmall : WeightedSD.SmallRow q (graph dualSource.D attachFamily) dualSource.V)
    (attachDual : ℕ → ℝ)
    (hAttachDual : WeightedSD.RealDual q (graph dualSource.D attachFamily) dualSource.V 1 attachDual)
    (hEveryAttachment : ∀ (B : Finset ℕ), Boundary dualSource attachFamily B →
      ¬WeightedSD.SmallRow q (graph dualSource.D (insert B attachFamily)) dualSource.V ∧
        ∀ (p : ℕ → ℝ), WeightedSD.RealDual q (graph dualSource.D attachFamily) dualSource.V 1 p →
          ∃ u ∈ B, ∃ v ∈ B, dualSource.D u v = true ∧ graph dualSource.D attachFamily u v = false ∧
            1 < WeightedSD.realCol q (graph dualSource.D attachFamily) dualSource.V p v + ↑q * p u)
    (outsideCycle : Finset ℕ)
    (hAttachBoundary : Boundary dualSource attachFamily outsideCycle)
    (hMinimumNewHeads : ∀ (M : Finset ℕ), Boundary dualSource attachFamily M →
      (targets dualSource.D dualSource.V attachFamily outsideCycle).card ≤
        (targets dualSource.D dualSource.V attachFamily M).card) : True := by
  have hClosedFamily := closed_family dualSource hAttachSmall (fun B b => (hEveryAttachment B b).1)
  have hDoublyFed := doubly_fed_all dualSource (by omega) (fun B b => (hEveryAttachment B b).1)
  have hLeastSwap := @least_swap q dualBudget dualSource (by omega) attachFamily outsideCycle
    hAttachBoundary hMinimumNewHeads
  have hOutsideFed := hDoublyFed outsideCycle hAttachBoundary
  obtain ⟨attachCap, hAttachCapHigh, hAttachCapBound, hAttachCapAttained⟩ :=
    price_cap dualSource (hEveryAttachment outsideCycle hAttachBoundary).1 hAttachDual
  have hTwoHit := fun K (ks : K ⊆ dualSource.V) big paid =>
    DepositTrace.two_hit dualSource attachDual hAttachDual (hEveryAttachment outsideCycle hAttachBoundary).1
      hAttachCapHigh.le hAttachCapBound (K := K) ks big paid
  have hBlockingTrace := fun v (vv : v ∈ dualSource.V) vpaid =>
    DepositTrace.trace_dichotomy dualSource (by omega) (by classical exact (mem_filter.mp hAttachBoundary.1).2) attachDual
      hAttachDual (hEveryAttachment outsideCycle hAttachBoundary).1 hAttachCapHigh.le hAttachCapBound
      hAttachCapAttained vv vpaid
  trivial

end LeanCH.BR.Closure.AttachmentLaws
