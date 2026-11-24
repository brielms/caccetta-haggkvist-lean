import checkpoints.shen_extension.FirstPacketBarrier

namespace LeanCH.BR.Closure.CriticalCycleFamily
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier

/-- Dropping one witness removes exactly its private arcs. -/
theorem private_cut {D V q M C F} (c : Cycle D V q C) (cf : C∈F)
    (mf : M∈F) (cm : C≠M) {w : ℕ→ℕ}
    (yes : Strict q (graph D F) V w) (no : ¬Strict q (graph D (F.erase C)) V w) :
    Cut D M F (F.erase C) := by
  classical
  have sub := erase_subset C F
  have existsLost : ∃e : Arc,(col D F e).Nonempty ∧ col D (F.erase C) e=∅ := by
    by_contra! all
    apply no
    apply nat_strict.mpr
    intro x xv
    have old := nat_strict.mp yes x xv
    apply old.trans_le
    unfold score
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply sum_le_sum
    intro y _
    by_cases hit : graph D F x y=true
    · have pos := all (x,y) (active.mp hit)
      have kept : graph D (F.erase C) x y=true := active.mpr pos
      simp [hit,kept]
    · simp [hit]
  have privateCol (f : Arc) (live : (col D F f).Nonempty) :
      col D (F.erase C) f=∅ ↔ col D F f={C} := by
    constructor
    · intro none
      have only (A) (mem : A∈col D F f) : A=C := by
        by_contra ne
        have hit : A∈col D (F.erase C) f := mem_col.mpr ⟨mem_erase.mpr ⟨ne,(mem_col.mp mem).1⟩,(mem_col.mp mem).2⟩
        rw [none] at hit
        exact notMem_empty _ hit
      obtain ⟨A,hit⟩ := live
      exact Subset.antisymm (fun a ha => mem_singleton.mpr (only a ha)) (singleton_subset_iff.mpr (only A hit ▸ hit))
    · intro same
      apply eq_empty_iff_forall_notMem.mpr
      intro A hit
      obtain ⟨am,use⟩ := mem_col.mp hit
      have af : A∈col D F f := mem_col.mpr ⟨sub am,use⟩
      exact (mem_erase.mp am).1 (mem_singleton.mp (same ▸ af))
  obtain ⟨e,elive,empty⟩ := existsLost
  have ec := (privateCol e elive).mp empty
  refine ⟨mem_erase.mpr ⟨Ne.symm cm,mf⟩,erase_ssubset cf,e,elive,by rw [ec,sdiff_singleton_eq_erase],
    fun f live => ec.symm ▸ privateCol f live,?_⟩
  intro f g fe ge shared
  have data {a : Arc} (eq : col D F a=col D F e) : Uses D C a :=
    (mem_col.mp (show C∈col D F a by rw [eq,ec]; exact mem_singleton_self _)).2
  obtain ⟨fu,fv,fa⟩ := data fe
  obtain ⟨gu,gv,ga⟩ := data ge
  rcases shared with same|same
  · exact Prod.ext same (card_le_one.mp (c.heads f.1 fu).le _ (mem_outN.mpr ⟨fv,fa⟩) _ (mem_outN.mpr ⟨gv,same ▸ ga⟩))
  · exact Prod.ext (card_le_one.mp (c.incoming f.2 fv).le _ (mem_inN.mpr ⟨fu,fa⟩) _ (mem_inN.mpr ⟨gu,same ▸ ga⟩)) same

/-- Select one feasible family before choosing the protected cycle, the
discarded cycle, or the allocation. Every deletion is now an unpaid private
matching cut on the same graph. -/
theorem simultaneous {q n} (X : Model q n) (hq : 2≤q) :
    ∃F⊆family X, 2≤F.card ∧ Feasible q n X.D X.V F ∧
      (∀G,G ⊂ F → ¬Feasible q n X.D X.V G) ∧
      ∀C∈F,∀M∈F,C≠M → Cut X.D M F (F.erase C) := by
  classical
  let pool := (family X).powerset.filter (Feasible q n X.D X.V)
  have mem (G) : G∈pool ↔ G⊆family X ∧ Feasible q n X.D X.V G := by simp [pool]
  obtain ⟨F,fp,least⟩ := pool.exists_min_image Finset.card ⟨family X,(mem _).mpr ⟨Subset.rfl,full_feasible X hq⟩⟩
  obtain ⟨sub,yes⟩ := (mem _).mp fp
  have no (G) (lt : G ⊂ F) : ¬Feasible q n X.D X.V G :=
    fun win => (card_lt_card lt).not_ge (least G ((mem _).mpr ⟨lt.subset.trans sub,win⟩))
  obtain ⟨w,wp,budget,strict⟩ := yes
  have two : 2≤F.card := by
    by_contra! small
    rcases F.eq_empty_or_nonempty with rfl|⟨C,cf⟩
    · obtain ⟨p,pv⟩ := X.live
      have high := nat_strict.mp strict p pv
      have empty (y) : graph X.D ∅ p y=false := by classical simp [graph,col]
      simp [score,empty] at high
      exact (single_le_sum (f:=w) (fun _ _ => Nat.zero_le _) pv).not_gt high
    · have single : F={C} := eq_of_subset_of_card_le (singleton_subset_iff.mpr cf) (by simpa using (show F.card≤1 by omega)) |>.symm
      have c : Cycle X.D X.V q C := (mem_filter.mp (sub cf)).2
      rw [single] at strict
      exact singleton_fails c w strict
  refine ⟨F,sub,two,⟨w,wp,budget,strict⟩,no,?_⟩
  intro C cf M mf cm
  have original : Cycle X.D X.V q C := (mem_filter.mp (sub cf)).2
  exact private_cut original cf mf cm strict (fun good => no _ (erase_ssubset cf) ⟨w,wp,budget,good⟩)

#print axioms private_cut
#print axioms simultaneous
end LeanCH.BR.Closure.CriticalCycleFamily
