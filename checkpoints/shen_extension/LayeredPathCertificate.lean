import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

namespace LayeredPathCertificate
open Finset

/-- Paths whose edge relation can depend on the layer. -/
def Valid {α : Type*} (E : ℕ → α → α → Prop) (L : ℕ) (s t : α) (p : ℕ → α) : Prop :=
  p 0 = s ∧ p L = t ∧ ∀ i < L, E i (p i) (p (i+1))

private def join {α : Type*} (p r : ℕ → α) (k i : ℕ) : α :=
  if i ≤ k then p i else r i

private theorem join_valid {α : Type*} {E : ℕ → α → α → Prop} {L s t p r k}
    (hp : Valid E L s t p) (hr : Valid E L s t r) (eq : p k = r k) :
    Valid E L s t (join p r k) := by
  refine ⟨by simpa [join] using hp.1, ?_, ?_⟩
  · by_cases h : L ≤ k <;> simp [join,h,hp.2.1,hr.2.1]
  · intro i hi
    rcases lt_trichotomy i k with lt|same|gt
    · simpa [join,lt.le,show i+1≤k by omega] using hp.2.2 i hi
    · subst i
      simpa [join,eq,show ¬k+1≤k by omega] using hr.2.2 k hi
    · simpa [join,show ¬i≤k by omega,show ¬i+1≤k by omega] using hr.2.2 i hi

private def SamePair {α : Type*} (p r a b : ℕ → α) : Prop :=
  ∀ i, (p i = a i ∧ r i = b i) ∨ (p i = b i ∧ r i = a i)

private theorem orient {α : Type*} {E : ℕ → α → α → Prop} {L s t a b} (ha : Valid E L s t a)
    (hb : Valid E L s t b) {r : ℕ → α} {i} (hit : r i = a i ∨ r i = b i) :
    ∃ p z, Valid E L s t p ∧ Valid E L s t z ∧ r i = p i ∧ SamePair p z a b := by
  rcases hit with h|h
  · exact ⟨a,b,ha,hb,h,fun _ => Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨b,a,hb,ha,h,fun _ => Or.inr ⟨rfl,rfl⟩⟩

/-- A third path that avoids an agreement at k can remove it without
introducing an agreement at any previously different layer. -/
theorem remove_agreement {α : Type*} {E : ℕ → α → α → Prop} {L s t a b r k}
    (ha : Valid E L s t a) (hb : Valid E L s t b) (hr : Valid E L s t r)
    (hk : k ≤ L) (eq : a k = b k) (miss : r k ≠ a k) :
    ∃ p z, Valid E L s t p ∧ Valid E L s t z ∧ p k ≠ z k ∧
      ∀ i, p i = z i → a i = b i := by
  classical
  let hit := fun i => r i = a i ∨ r i = b i
  let left := (range (k+1)).filter hit
  let right := (Icc k L).filter hit
  have h0 : 0 ∈ left := mem_filter.mpr ⟨mem_range.mpr (by omega),Or.inl (hr.1.trans ha.1.symm)⟩
  have hL : L ∈ right := mem_filter.mpr ⟨mem_Icc.mpr ⟨hk,le_rfl⟩,Or.inl (hr.2.1.trans ha.2.1.symm)⟩
  let l := left.max' ⟨0,h0⟩
  let j := right.min' ⟨L,hL⟩
  have hl := mem_filter.mp (left.max'_mem ⟨0,h0⟩)
  have hj := mem_filter.mp (right.min'_mem ⟨L,hL⟩)
  change l ∈ range (k+1) ∧ hit l at hl
  change j ∈ Icc k L ∧ hit j at hj
  have missK : ¬ hit k := by simp [hit,←eq,miss]
  have lk : l < k := lt_of_le_of_ne (by have := mem_range.mp hl.1; omega) (fun e => missK (e ▸ hl.2))
  have kj : k < j := lt_of_le_of_ne (mem_Icc.mp hj.1).1 (fun e => missK (e ▸ hj.2))
  have clear (i) (lo : l < i) (hi : i < j) : ¬hit i := by
    intro yes
    by_cases ik : i ≤ k
    · exact lo.not_ge (le_max' left i (mem_filter.mpr ⟨mem_range.mpr (by omega),yes⟩))
    · exact hi.not_ge (min'_le right i (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hi.le.trans (mem_Icc.mp hj.1).2⟩,yes⟩))
  obtain ⟨p,z,hp,hz,atL,pairL⟩ := orient ha hb hl.2
  obtain ⟨f,g,hf,hg,atJ,pairR⟩ := orient ha hb hj.2
  have coincide (p z : ℕ → α) (h : SamePair p z a b) : p k = a k ∧ z k = a k := by
    rcases h k with h|h <;> simpa [←eq] using h
  let base := join p f k
  let other := join z g k
  have vp := join_valid hp hf ((coincide p z pairL).1.trans (coincide f g pairR).1.symm)
  have vo := join_valid hz hg ((coincide p z pairL).2.trans (coincide f g pairR).2.symm)
  have pair : SamePair base other a b := by
    intro i
    by_cases h : i ≤ k
    · simpa [base,other,join,h] using pairL i
    · simpa [base,other,join,h] using pairR i
  have atLeft : base l = r l := by simpa [base,join,lk.le] using atL.symm
  have atRight : join base r l j = base j := by
    simpa [join,base,show ¬j≤l by omega,show ¬j≤k by omega] using atJ
  let fixed := join (join base r l) base j
  have valid := join_valid (join_valid vp hr atLeft) vp atRight
  have outside (i) (h : i≤l ∨ j≤i) : fixed i = base i := by
    rcases h with h|h
    · simp [fixed,join,h,show i≤j by omega]
    · rcases eq_or_lt_of_le h with e|gt
      · subst i; simpa [fixed,join] using atRight
      · simp [fixed,join,gt.not_ge]
  have inside (i) (lo : l < i) (hi : i < j) : fixed i ≠ other i := by
    have fval : fixed i = r i := by simp [fixed,join,lo.not_ge,hi.le]
    intro bad
    have rr := fval.symm.trans bad
    exact clear i lo hi ((pair i).elim (fun h => Or.inr (rr.trans h.2)) (fun h => Or.inl (rr.trans h.2)))
  refine ⟨fixed,other,valid,vo,inside k lk kj,?_⟩
  intro i eqi
  by_cases ext : i≤l ∨ j≤i
  · rw [outside i ext] at eqi
    rcases pair i with h|h
    · exact h.1.symm.trans (eqi.trans h.2)
    · exact (h.1.symm.trans (eqi.trans h.2)).symm
  · exact (inside i (by omega) (by omega) eqi).elim

/-- Two fixed paths agree at exactly those layers at which all paths agree. -/
theorem two_paths {α : Type*} {E : ℕ → α → α → Prop} {L s t}
    (existsPath : ∃ p, Valid E L s t p) :
    ∃ a b, Valid E L s t a ∧ Valid E L s t b ∧
      ∀ k ≤ L, a k = b k → ∀ r, Valid E L s t r → r k = a k := by
  classical
  let overlap (a b : ℕ → α) := (range (L+1)).filter fun i => a i = b i
  let P (n : ℕ) := ∃ a b, Valid E L s t a ∧ Valid E L s t b ∧ (overlap a b).card = n
  obtain ⟨p,hp⟩ := existsPath
  have ex : ∃ n, P n := ⟨_,p,p,hp,hp,rfl⟩
  obtain ⟨a,b,ha,hb,cost⟩ := Nat.find_spec ex
  refine ⟨a,b,ha,hb,?_⟩
  intro k hk eq r hr
  by_contra miss
  obtain ⟨f,g,hf,hg,apart,subset⟩ := remove_agreement ha hb hr hk eq miss
  have small : overlap f g ⊂ overlap a b := by
    refine ⟨fun i hi => mem_filter.mpr ⟨(mem_filter.mp hi).1,subset i (mem_filter.mp hi).2⟩,?_⟩
    intro rev
    exact apart (mem_filter.mp (rev (mem_filter.mpr ⟨mem_range.mpr (by omega),eq⟩ : k ∈ overlap a b))).2
  have minimal := Nat.find_min' ex (show P (overlap f g).card from ⟨f,g,hf,hg,rfl⟩)
  have lt := card_lt_card small
  omega
end LayeredPathCertificate
