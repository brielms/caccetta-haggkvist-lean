import checkpoints.shen_extension.FeederComparisonClosure
import checkpoints.shen_extension.TwoCycleTransfer
import checkpoints.shen_extension.MandatoryExcursion

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

noncomputable abbrev nextOn := TwoCycleTransfer.succHead

private theorem next_arc {D V q L a} (cy : Cycle D V q L) (ha : a ∈ L) :
    nextOn D L a ∈ outN D L a := by
  have h : (outN D L a).Nonempty := card_pos.mp (by rw [cy.heads a ha]; decide)
  simpa only [nextOn,TwoCycleTransfer.succHead,dite_eq_left h] using (outN D L a).min'_mem h

theorem walk_next {D V q L a b k} (cy : Cycle D V q L) (ha : a ∈ L)
    (path : Walk D L a b k) : (nextOn D L)^[k] a = b := by
  induction path with
  | refl => rfl
  | @step a j v k hj aj tail ih =>
    have eq := card_le_one.mp (cy.heads a ha).le _ (next_arc cy ha) _ (mem_outN.mpr ⟨hj,aj⟩)
    rw [iterate_succ_apply,eq]
    exact ih hj

/-- The labelled cyclic order, including its return to the original vertex. -/
theorem cycle_index {D V q L a} (hq : 1 ≤ q) (free : QFree D V q) (cy : Cycle D V q L)
    (ha : a ∈ L) :
    let s := fun i => (nextOn D L)^[i] a
    (∀ i, s i ∈ L) ∧ (∀ i, s (i+(q+1)) = s i) ∧
    (range (q+1)).image s = L ∧ Set.InjOn s (range (q+1) : Finset ℕ) := by
  classical
  intro s
  have inside (i) : s i ∈ L := by
    induction i with
    | zero => exact ha
    | succ i ih =>
      change (nextOn D L)^[i+1] a ∈ L
      rw [iterate_succ_apply']
      exact (mem_outN.mp (next_arc cy ih)).1
  have loop := (MandatoryExcursion.segments hq free cy ha ha).2.2.1
  have per : IsPeriodicPt (nextOn D L) (q+1) a :=
    walk_next cy ha (by simpa [MandatoryExcursion.span] using loop)
  have periodic (i) : s (i+(q+1)) = s i := by
    dsimp [s]
    rw [iterate_add_apply,per.eq]
  have onto : (range (q+1)).image s = L := by
    apply Subset.antisymm
    · exact image_subset_iff.mpr (fun i _ => inside i)
    · intro v hv
      let k := MandatoryExcursion.span D V q a v
      have seg := (MandatoryExcursion.segments hq free cy ha hv).2.2.1
      have visit : s k = v := walk_next cy ha seg
      exact mem_image.mpr ⟨k%(q+1),mem_range.mpr (Nat.mod_lt _ (by omega)),
        (per.iterate_mod_apply k).trans visit⟩
  exact ⟨inside,periodic,onto,card_image_iff.mp (by rw [onto,cy.size,card_range])⟩

private theorem next_private {D V q L a b} (cy : Cycle D V q L)
    (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b) :
    nextOn D L a ∈ exclusive D V a b := by
  obtain ⟨inside,arc⟩ := mem_outN.mp (next_arc cy ha)
  refine mem_sdiff.mpr ⟨mem_outN.mpr ⟨cy.sub inside,arc⟩,fun h => ne ?_⟩
  exact card_le_one.mp (cy.incoming _ inside).le _ (mem_inN.mpr ⟨ha,arc⟩) _
    (mem_inN.mpr ⟨hb,(mem_outN.mp h).2⟩)

/-- Synchronous rotation of a marked pair stays in the private comparison queue. -/
theorem cycle_rotations {D V q L a b} (cy : Cycle D V q L) (ha : a ∈ L) (hb : b ∈ L)
    (ne : a ≠ b) (i : ℕ) : Compared D V (a,b) ((nextOn D L)^[i] a,(nextOn D L)^[i] b) := by
  have aux (i) :
      let u := (nextOn D L)^[i] a
      let v := (nextOn D L)^[i] b
      Compared D V (a,b) (u,v) ∧ u ∈ L ∧ v ∈ L ∧ u ≠ v := by
    induction i with
    | zero => exact ⟨.refl,ha,hb,ne⟩
    | succ i ih =>
      obtain ⟨path,au,bv,diff⟩ := ih
      rw [iterate_succ_apply',iterate_succ_apply']
      have left := next_private cy au bv diff
      have right := next_private cy bv au diff.symm
      exact ⟨path.tail ⟨left,right⟩,(mem_outN.mp (next_arc cy au)).1,
        (mem_outN.mp (next_arc cy bv)).1,fun eq => (mem_sdiff.mp left).2 (eq ▸ (mem_sdiff.mp right).1)⟩
  exact (aux i).1

theorem period_gcd {α : Type*} {f : ℕ → α} {k m : ℕ}
    (pk : ∀ i, f (i+k) = f i) (pm : ∀ i, f (i+m) = f i) :
    ∀ i, f (i+Nat.gcd k m) = f i := by
  let shift (g : ℕ → α) := fun i => g (i+1)
  have calcShift (n i) : (shift^[n] f) i = f (i+n) := by
    induction n generalizing i with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      exact (ih (i+1)).trans (congrArg f (by omega))
  have per (n) (ok : ∀ i, f (i+n)=f i) : IsPeriodicPt shift n f :=
    funext (fun i => (calcShift n i).trans (ok i))
  intro i
  exact (calcShift _ i).symm.trans (congrFun ((per k pk).gcd (per m pm)).eq i)

/-- Record successor prices and head incidences at a common physical position.
Only columns whose prices differ from the next cycle price carry an incidence bit. -/
def cycleWord (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (a s : ℕ) :
    ℚ × ℕ × Finset ℕ :=
  (w a,(outN D V a).card,(outN D V a).filter (fun j => w j ≠ w s))

theorem tied_cycle_word {D V q L a b} (hq : 1 ≤ q) (free : QFree D V q)
    (cy : Cycle D V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b) (w : ℕ → ℚ)
    (tied : ∀ y, Compared D V (a,b) y → w y.1 = w y.2 ∧
      (outN D V y.1).card = (outN D V y.2).card ∧
      ∃ v > (0 : ℚ), ∀ i ∈ exclusive D V y.1 y.2 ∪ exclusive D V y.2 y.1, w i = v) :
    let s := fun i => (nextOn D L)^[i] a
    let d := Nat.gcd (MandatoryExcursion.span D V q a b) (q+1)
    ∀ i, cycleWord D V w (s (i+d)) (s (i+d+1)) = cycleWord D V w (s i) (s (i+1)) := by
  classical
  intro s d
  let k := MandatoryExcursion.span D V q a b
  have seg := (MandatoryExcursion.segments hq free cy ha hb).2.2.1
  have atb : s k = b := walk_next cy ha seg
  have right (i) : s (i+k) = (nextOn D L)^[i] b := by
    change (nextOn D L)^[i+k] a = _
    rw [iterate_add_apply,show (nextOn D L)^[k] a = b from atb]
  obtain ⟨inside,cyclic,_,_⟩ := cycle_index hq free cy ha
  change ∀ i, s (i+(q+1)) = s i at cyclic
  have step (i) : s (i+1) = nextOn D L (s i) := iterate_succ_apply' _ _ _
  have unequal (i) : s i ≠ s (i+k) := by
    have distinct {x y : Pair} (start : x.1 ≠ x.2) (path : Compared D V x y) : y.1 ≠ y.2 := by
      cases path with
      | refl => exact start
      | tail _ edge =>
        intro eq
        exact (mem_sdiff.mp edge.1).2 (eq ▸ (mem_sdiff.mp edge.2).1)
    rw [right]
    exact distinct ne (cycle_rotations cy ha hb ne i)
  apply period_gcd (f := fun i => cycleWord D V w (s i) (s (i+1))) (k := k) (m := q+1)
  · intro i
    have path : Compared D V (a,b) (s i,s (i+k)) := by
      rw [right]
      exact cycle_rotations cy ha hb ne i
    obtain ⟨prices,degs,v,_,same⟩ := tied _ path
    have l := next_private cy (inside i) (inside (i+k)) (unequal i)
    have r := next_private cy (inside (i+k)) (inside i) (unequal i).symm
    have sl : w (s (i+1)) = v := (step i) ▸ same _ (mem_union_left _ l)
    have sr : w (s (i+k+1)) = v := (step (i+k)) ▸ same _ (mem_union_right _ r)
    change w (s i) = w (s (i+k)) at prices
    change (outN D V (s i)).card = (outN D V (s (i+k))).card at degs
    unfold cycleWord
    rw [sl,sr,prices,degs]
    congr 2
    ext j
    simp only [mem_filter]
    constructor
    · rintro ⟨hit,off⟩
      refine ⟨?_,off⟩
      by_contra miss
      exact off (same j (mem_union_right _ (mem_sdiff.mpr ⟨hit,miss⟩)))
    · rintro ⟨hit,off⟩
      refine ⟨?_,off⟩
      by_contra miss
      exact off (same j (mem_union_left _ (mem_sdiff.mpr ⟨hit,miss⟩)))
  · intro i
    rw [cyclic,show i+(q+1)+1=i+1+(q+1) by omega,cyclic]

#print axioms cycle_index
#print axioms cycle_rotations
#print axioms tied_cycle_word
end LeanCH.BR.Closure.FeederPrivateHeadDescent
