import checkpoints.shen_extension.LastArcMergePayment
import checkpoints.shen_extension.MenuEscapeGrowth

namespace LeanCH.BR.Closure.LastArcReturnMenu
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

/-- A menu containing the root and two different rows pointing to its
parents has a row with no head in the menu or in that parent set. -/
theorem dry_row {D : CH.Digraph} {V S T : Finset ℕ} {q v y z : ℕ}
    (hq : 3 ≤ q) (free : QFree D V q) (ss : S ⊆ V) (ts : T ⊆ V)
    (cap : S.card ≤ q) (start : v ∈ S) (parents : ∀ t ∈ T, D t v = true)
    (ym : y ∈ S) (zm : z ∈ S) (diff : y ≠ z)
    (ye : ∃ t ∈ T, D y t = true) (ze : ∃ t ∈ T, D z t = true) :
    ∃ i ∈ S, outN D (S ∪ T) i = ∅ := by
  classical
  by_contra! wet
  have budget (i) (hi : i ∈ S) : 1 ≤ (outN D (S ∪ T) i).card :=
    card_pos.mpr (wet i hi)
  have outside : v ∉ T := fun m => loopfree free (by omega) (ss start) (parents v m)
  have ret (t) (ht : t ∈ T) : v ∈ ball D V t 1 :=
    mem_ball.mpr ⟨ss start,1,le_rfl,.step (ss start) (parents t ht) (.refl v)⟩
  have grow := SATBoundaryPilot.short_returns_force_growth (r:=q-3) (t:=1) free ss ts cap
    start outside (by omega) budget ret
  rw [Nat.mul_one] at grow
  have first := budget v start
  let early := S ∩ ball D V v (q-3+1)
  have large : q-1 ≤ early.card := by change _ ≤ (S ∩ _).card; omega
  have left : (S \ early).card ≤ 1 := by
    rw [card_sdiff_of_subset (show early ⊆ S from inter_subset_left)]
    omega
  have late {b : ℕ} (hit : ∃ t ∈ T, D b t = true) : b ∉ early := by
    intro mem
    obtain ⟨_,j,room,walk⟩ := mem_ball.mp (mem_inter.mp mem).2
    obtain ⟨t,ht,arc⟩ := hit
    exact free v (j+1+1) (by omega) (by omega) ((walk.snoc (ts ht) arc).snoc (ss start) (parents t ht))
  exact diff (card_le_one.mp left _ (mem_sdiff.mpr ⟨ym,late ye⟩) _ (mem_sdiff.mpr ⟨zm,late ze⟩))

/-- Applying the menu test to the very two witnesses selected at the gate's
prices identifies a third row. Its entire selected out-weight goes outside
the menu and outside both missing parents. -/
theorem at_prices {q n} (X : Model q n) (hq : 3 ≤ q)
    {G : CH.Digraph} (sub : ∀ i j, G i j = true → X.D i j = true)
    {w ρ d} (flat : OmittedCycleProgress.Flat q G X.V w ρ d)
    {t r v y z : ℕ} (tv : t ∈ X.V) (rv : r ∈ X.V)
    (pt : X.D t v = true) (pr : X.D r v = true) (yz : y ≠ z)
    (py : LastArcMergePayment.Priced X G w y t r)
    (pz : LastArcMergePayment.Priced X G w z r t)
    (S : Finset ℕ) (ss : S ⊆ X.V) (cap : S.card ≤ q) (vm : v ∈ S) (ym : y ∈ S) (zm : z ∈ S) :
    ∃ i ∈ S, i ≠ y ∧ i ≠ z ∧ outN X.D (S ∪ {t,r}) i = ∅ ∧
      w i + (q:ℚ) * outW G (X.V \ (S ∪ {t,r})) w i = d := by
  classical
  have ts : ({t,r} : Finset ℕ) ⊆ X.V := by
    intro j hj
    simp only [mem_insert,mem_singleton] at hj
    exact hj.elim (fun h => h ▸ tv) (fun h => h ▸ rv)
  have pars (j) (hj : j ∈ ({t,r} : Finset ℕ)) : X.D j v = true := by
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with h|h <;> subst j <;> assumption
  obtain ⟨i,im,dry⟩ := dry_row hq X.free ss ts cap vm pars ym zm yz
    ⟨t,by simp,sub y t py.oldArc⟩ ⟨r,by simp,sub z r pz.oldArc⟩
  have no {j} (jm : j ∈ S ∪ {t,r}) : X.D i j ≠ true := by
    intro edge
    have mem := mem_outN.mpr ⟨jm,edge⟩
    rw [dry] at mem
    exact notMem_empty _ mem
  refine ⟨i,im,fun h => no (j:=t) (by simp) (h ▸ sub y t py.oldArc),
    fun h => no (j:=r) (by simp) (h ▸ sub z r pz.oldArc),dry,?_⟩
  have ext : outW G (X.V \ (S ∪ {t,r})) w i = outW G X.V w i := by
    unfold outW
    apply sum_subset sdiff_subset
    intro j jv missing
    have inside : j ∈ S ∪ {t,r} := by
      by_contra h
      exact missing (mem_sdiff.mpr ⟨jv,h⟩)
    have off : G i j ≠ true := fun h => no inside (sub i j h)
    simp [off]
  rw [ext]
  exact flat.2.2.2.2.2.1 i (ss im)

def OnGraph {q n} (X : Model q n) (G : CH.Digraph) : Prop :=
  ∀ w ρ d, OmittedCycleProgress.Flat q G X.V w ρ d →
    ∀ t r v y z, t ∈ X.V → r ∈ X.V → X.D t v = true → X.D r v = true → y ≠ z →
    LastArcMergePayment.Priced X G w y t r → LastArcMergePayment.Priced X G w z r t →
    ∀ S : Finset ℕ, S ⊆ X.V → S.card ≤ q → v ∈ S → y ∈ S → z ∈ S →
      ∃ i ∈ S, i ≠ y ∧ i ≠ z ∧ outN X.D (S ∪ {t,r}) i = ∅ ∧
        w i + (q:ℚ) * outW G (X.V \ (S ∪ {t,r})) w i = d

def OnModel {q n} (X : Model q n) : Prop :=
  ∀ F, OnGraph X (FirstPacketBarrier.graph X.D F)

theorem on_model {q n} (X : Model q n) (hq : 3 ≤ q) : OnModel X :=
  fun _ _ _ _ flat _ _ _ _ _ tv rv pt pr yz py pz =>
    at_prices X hq (fun _ _ h => CrossValueOmissions.selected_sub h) flat tv rv pt pr yz py pz

#print axioms dry_row
#print axioms at_prices
#print axioms on_model
end LeanCH.BR.Closure.LastArcReturnMenu
