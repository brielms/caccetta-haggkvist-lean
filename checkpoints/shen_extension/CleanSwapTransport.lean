import checkpoints.shen_extension.CleanSwapKernel
import checkpoints.shen_extension.TripleBankSelection
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45 CleanSwap

/-- Choose a swap in the original labels. The new member has a path of
length at most two to d using outside rows, and every remaining row in
the given sets hits at most one of the new bank labels. -/
theorem clean_swap_kernel {D : CH.Digraph} {B T : Finset ℕ} {d : ℕ}
    (bc : B.card = 3) (dis : Disjoint B T) (dt : d ∈ T) (free : QFree D (B ∪ T) 3)
    (off : ∀ b ∈ B, D b d ≠ true) (colored : ∀ u ∈ T, (outN D B u).card = 1)
    (cap : ∀ b ∈ B, (inN D (B ∪ T) b).card ≤ 2) :
    ∃ u ∈ T, (u = d ∨ D u d = true ∨ ∃ v ∈ T, D u v = true ∧ D v d = true) ∧
      ∃ b ∈ B, ∀ y ∈ (B ∪ T) \ insert u (B.erase b),
        (outN D (insert u (B.erase b)) y).card ≤ 1 := by
  classical
  let A := B ∪ T
  have tsize : T.card ≤ 6 := by
    have sum : (∑ u ∈ T, (outN D B u).card) = ∑ b ∈ B, (inN D T b).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun u b => D u b = true)
    rw [sum_congr rfl colored] at sum
    have bound := sum_le_sum (s := B) (fun b bm => (card_le_card (show inN D T b ⊆ inN D A b from
      fun _ m => mem_inN.mpr ⟨mem_union_right _ (mem_inN.mp m).1,(mem_inN.mp m).2⟩)).trans (cap b bm))
    simp only [sum_const,Nat.nsmul_eq_mul,mul_one,bc] at sum bound
    omega
  let be := Fintype.equivFinOfCardEq (α := ↥B) (by simpa using bc : Fintype.card B = 3)
  obtain ⟨base⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card T ≤ Fintype.card (Fin 6) by simpa using tsize)
  let oe : ↥T ↪ Fin 6 := base.trans (Equiv.swap (base ⟨d,dt⟩) 0).toEmbedding
  have oe0 : oe ⟨d,dt⟩ = 0 := by simp [oe]
  let tag (x : ℕ) : Slot := if xb : x ∈ B then bankSlot (be ⟨x,xb⟩)
    else if xt : x ∈ T then outerSlot (oe ⟨x,xt⟩) else 0
  have tb {x} (xb : x ∈ B) : tag x = bankSlot (be ⟨x,xb⟩) := by simp [tag,xb]
  have tt {x} (xt : x ∈ T) : tag x = outerSlot (oe ⟨x,xt⟩) := by
    have nx : x ∉ B := fun xb => disjoint_left.mp dis xb xt
    simp [tag,xt,nx]
  have td : tag d = outerSlot 0 := (tt dt).trans (congrArg outerSlot oe0)
  have split (b : Fin 3) (u : Fin 6) : bankSlot b ≠ outerSlot u := by
    intro eq
    have ev := congrArg Fin.val eq
    change b.val = u.val + 3 at ev
    omega
  have bi : Function.Injective bankSlot := fun _ _ e => Fin.ext (congrArg (Fin.val : Slot → ℕ) e)
  have oi : Function.Injective outerSlot := by
    intro i j e
    apply Fin.ext
    have ev := congrArg Fin.val e
    change i.val + 3 = j.val + 3 at ev
    omega
  have inj {x y} (xa : x ∈ A) (ya : y ∈ A) (e : tag x = tag y) : x = y := by
    rcases mem_union.mp xa with xb | xt <;> rcases mem_union.mp ya with yb | yt
    · exact congrArg Subtype.val (be.injective (bi ((tb xb).symm.trans (e.trans (tb yb)))))
    · exact False.elim (split _ _ ((tb xb).symm.trans (e.trans (tt yt))))
    · exact False.elim (split _ _ ((tb yb).symm.trans (e.symm.trans (tt xt))))
    · exact congrArg Subtype.val (oe.injective (oi ((tt xt).symm.trans (e.trans (tt yt)))))
  let live (i : Slot) := ∃ x ∈ A, tag x = i
  let val (i : Slot) := if h : live i then Classical.choose h else d
  have decoded {i} (li : live i) : val i ∈ A ∧ tag (val i) = i := by
    simpa only [val,dite_eq_left li] using Classical.choose_spec li
  have actual {x} (xa : x ∈ A) : live (tag x) := ⟨x,xa,rfl⟩
  have vt {x} (xa : x ∈ A) : val (tag x) = x :=
    inj (decoded (actual xa)).1 xa (decoded (actual xa)).2
  let bank (j : Fin 3) : ℕ := (be.symm j).val
  have bb (j) : bank j ∈ B := (be.symm j).property
  have tagB (j) : tag (bank j) = bankSlot j := by
    rw [tb (bb _)]
    exact congrArg bankSlot (be.apply_symm_apply j)
  have bankVal (j) : val (bankSlot j) = bank j := tagB j ▸ vt (mem_union_left T (bb j))
  have rootVal : val (outerSlot 0) = d := td ▸ vt (mem_union_right B dt)
  have outerT {u} (lu : live (outerSlot u)) : val (outerSlot u) ∈ T := by
    rcases mem_union.mp (decoded lu).1 with vb | vt'
    · exact False.elim (split _ _ ((tb vb).symm.trans (decoded lu).2))
    · exact vt'
  let R (i j : Slot) := decide (live i ∧ live j ∧ D (val i) (val j) = true)
  have edge {i j} : R i j = true ↔ live i ∧ live j ∧ D (val i) (val j) = true :=
    decide_eq_true_iff
  have lift {x y} (xa : x ∈ A) (ya : y ∈ A) (xy : D x y = true) : R (tag x) (tag y) = true :=
    edge.mpr ⟨actual xa,actual ya,by simpa only [vt xa,vt ya] using xy⟩
  have vdiff {i j} (li : live i) (lj : live j) (ij : i ≠ j) : val i ≠ val j :=
    fun e => ij ((decoded li).2.symm.trans ((congrArg tag e).trans (decoded lj).2))
  have badBit : (true : Bool) ≠ false := by decide
  have bot {i j} (non : R i j = true → False) : R i j = false := Bool.eq_false_iff.mpr non
  have loops (i) : R i i = false := bot fun h =>
    loopfree free (by decide) (decoded (edge.mp h).1).1 (edge.mp h).2.2
  have digons (i j : Slot) (_ : i < j) (ij : R i j = true) : R j i = false := bot fun ji =>
    digonfree free (by decide) (decoded (edge.mp ij).1).1 (decoded (edge.mp ji).1).1
      (edge.mp ij).2.2 (edge.mp ji).2.2
  have tri (i j k : Slot) (_ : i < j) (_ : i < k) (_ : j ≠ k)
      (ij : R i j = true) (jk : R j k = true) : R k i = false := bot fun ki =>
    free (val i) 3 (by decide) (by decide)
      (.step (decoded (edge.mp jk).1).1 (edge.mp ij).2.2
        (.step (decoded (edge.mp ki).1).1 (edge.mp jk).2.2
          (.step (decoded (edge.mp ij).1).1 (edge.mp ki).2.2 (.refl _))))
  have incoming (b : Fin 3) (i j k : Slot) (ij : i < j) (jk : j < k)
      (hi : R i (bankSlot b) = true) (hj : R j (bankSlot b) = true) : R k (bankSlot b) = false := by
    apply bot
    intro hk
    have inc {l : Slot} (h : R l (bankSlot b) = true) : val l ∈ inN D A (bank b) :=
      mem_inN.mpr ⟨(decoded (edge.mp h).1).1,(bankVal b) ▸ (edge.mp h).2.2⟩
    have lim := (card_le_card (insert_subset (inc hi) (insert_subset (inc hj)
      (singleton_subset_iff.mpr (inc hk))))).trans (cap _ (bb b))
    have dist {u v : Slot} (hu : R u (bankSlot b) = true) (hv : R v (bankSlot b) = true)
        (lt : u < v) := vdiff (edge.mp hu).1 (edge.mp hv).1 lt.ne
    simp [dist hi hj ij,dist hj hk jk,dist hi hk (lt_trans ij jk)] at lim
  have colors (u : Fin 6) (i j : Fin 3) (ij : i < j) (hi : R (outerSlot u) (bankSlot i) = true) :
      R (outerSlot u) (bankSlot j) = false := by
    apply bot
    intro hj
    have inc {l : Fin 3} (h : R (outerSlot u) (bankSlot l) = true) : bank l ∈ outN D B (val (outerSlot u)) :=
      mem_outN.mpr ⟨bb l,(bankVal l) ▸ (edge.mp h).2.2⟩
    have eq := card_le_one.mp (colored _ (outerT (edge.mp hi).1)).le _ (inc hi) _ (inc hj)
    exact ij.ne (bi ((tagB i).symm.trans ((congrArg tag eq).trans (tagB j))))
  obtain ⟨b,hm⟩ := card_pos.mp (show 0 < (outN D B d).card by rw [colored d dt]; decide)
  obtain ⟨hb,db⟩ := mem_outN.mp hm
  have root : ∃ j, R (outerSlot 0) (bankSlot j) = true :=
    ⟨be ⟨b,hb⟩, td ▸ (tb hb) ▸ lift (mem_union_right B dt) (mem_union_left T hb) db⟩
  have none (j : Fin 3) : R (bankSlot j) (outerSlot 0) = false := bot fun e =>
    off _ (bb j) (by simpa only [bankVal,rootVal] using (edge.mp e).2.2)
  obtain ⟨u,⟨_,um⟩,reach,b,cleaned⟩ := nine_slots R loops digons tri incoming colors root none
  have ul := (edge.mp um).1
  have ut := outerT ul
  have ua := (decoded ul).1
  refine ⟨val (outerSlot u),ut,?_,bank b,bb b,?_⟩
  · rcases reach with eq | jump | ⟨v,uv,vd⟩
    · exact Or.inl (eq ▸ rootVal)
    · exact Or.inr (Or.inl (rootVal ▸ (edge.mp jump).2.2))
    · exact Or.inr (Or.inr ⟨_,outerT (edge.mp vd).1,(edge.mp uv).2.2,rootVal ▸ (edge.mp vd).2.2⟩)
  · intro y ym
    obtain ⟨ya,yoff⟩ := mem_sdiff.mp ym
    have out : outside u b (tag y) := by
      refine ⟨fun eq => yoff (mem_insert.mpr (Or.inl (inj ya ua (eq.trans (decoded ul).2.symm)))),?_⟩
      intro j eq
      have same := inj ya (mem_union_left T (bb j)) (eq.trans (tagB j).symm)
      by_contra jb
      exact yoff (mem_insert_of_mem (mem_erase.mpr ⟨fun e => jb (bi ((tagB j).symm.trans
        ((congrArg tag (same.symm.trans e)).trans (tagB b)))),same ▸ bb j⟩))
    obtain ⟨old,added⟩ := cleaned (tag y) out
    have oldHead {x} (xm : x ∈ B.erase (bank b)) (yx : D y x = true) :
        ∃ j : Fin 3, j ≠ b ∧ x = bank j ∧ R (tag y) (bankSlot j) = true := by
      obtain ⟨xb,hb'⟩ := mem_erase.mp xm
      let j := be ⟨x,hb'⟩
      have eq : x = bank j := (congrArg Subtype.val (be.symm_apply_apply ⟨x,hb'⟩)).symm
      exact ⟨j,fun jb => xb (jb ▸ eq),eq,(tb hb') ▸ lift ya (mem_union_left T hb') yx⟩
    have eNew (hit : D y (val (outerSlot u)) = true) : R (tag y) (outerSlot u) = true :=
      (decoded ul).2 ▸ lift ya ua hit
    have mixed {x} (xm : x ∈ B.erase (bank b)) (yx : D y x = true) (hit : D y (val (outerSlot u)) = true) : False := by
      obtain ⟨j,jb,_,edgeJ⟩ := oldHead xm yx
      exact badBit (edgeJ.symm.trans (added j jb (eNew hit)))
    apply card_le_one.mpr
    intro x hx z hz
    obtain ⟨xx,ex⟩ := mem_outN.mp hx
    obtain ⟨zz,ez⟩ := mem_outN.mp hz
    rcases mem_insert.mp xx with rfl | xb <;> rcases mem_insert.mp zz with rfl | zb
    · rfl
    · exact (mixed zb ez ex).elim
    · exact (mixed xb ex ez).elim
    · obtain ⟨i,ib,xi,ei⟩ := oldHead xb ex
      obtain ⟨j,jb,zj,ej⟩ := oldHead zb ez
      rcases lt_trichotomy i j with lt | eq | gt
      · exact (badBit (ej.symm.trans (old i j lt ib jb ei))).elim
      · exact xi.trans ((congrArg bank eq).trans zj.symm)
      · exact (badBit (ei.symm.trans (old j i gt jb ib ej))).elim

#print axioms clean_swap_kernel

end LeanCH.BR.TripleBank
