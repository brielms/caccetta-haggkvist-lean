import checkpoints.shen_extension.FlatChildExchange
import checkpoints.shen_extension.FlatChildClosure

namespace LeanCH.BR.Closure.FlatExchangeCycle
open Finset BRq2 BRq3 BR45 WeightedSD FlatChildExchange

/-- Keep an arc only when its tail distinguishes the target from its partner. -/
def distinguished (E : CH.Digraph) (partner : ℕ → ℕ) : CH.Digraph :=
  fun i j => E i j && !(E i (partner j))

private theorem project {E f K a b k} (w : Walk (distinguished E f) K a b k) : Walk E K a b k := by
  induction w with
  | refl => exact .refl _
  | step h edge _ ih => exact .step h (Bool.and_eq_true_iff.mp edge).1 ih

/-- A set of labels indistinguishable from partners to every outside
parent must itself support a closed walk of distinguishing arcs. -/
theorem cycle {q E V K} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (sub : K ⊆ V) (live : K.Nonempty) {x : ℕ→ℚ}
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (f : ℕ→ℕ) (dest : ∀i∈K,f i∈V ∧ i≠f i)
    (outside : ∀i∈K,∀j∈V\K,E j i=true → E j (f i)=true) :
    ∃v k,q<k ∧ k≤K.card ∧ Walk (distinguished E f) K v v k := by
  classical
  have parent (i) (hi : i∈K) : ∃j∈K,distinguished E f j i=true := by
    by_contra! none
    apply strict_no_incoming_domination (small.induced free) x xp strict (sub hi) (dest i hi).1 (dest i hi).2
    intro j hj hit
    by_cases jk : j∈K
    · have no := none j jk
      simpa [distinguished,hit] using no
    · exact outside i hi j (mem_sdiff.mpr ⟨mem_of_mem_erase hj,jk⟩) hit
  have fail : ¬ QFree (distinguished E f) K K.card := by
    intro safe
    obtain ⟨i,hi,none⟩ := exists_sink safe.reverse live le_rfl
    obtain ⟨j,hj,ji⟩ := parent i hi
    exact none j hj ji
  unfold QFree at fail
  push Not at fail
  obtain ⟨v,k,pos,short,w⟩ := fail
  exact ⟨v,k,lt_of_not_ge (fun le => free v k pos le ((project w).mono sub)),short,w⟩

/-- Partners under an isomorphism fixing the overlap. -/
def partner {S T : Finset ℕ} (e : ↥S ≃ ↥T) (i : ℕ) : ℕ :=
  if h : i∈S then e ⟨i,h⟩ else if h : i∈T then e.symm ⟨i,h⟩ else i

def moved (S T : Finset ℕ) := (S\T) ∪ (T\S)

/-- For every comparison covering the parent, either both kinds of arc
change occur or the exchanged labels contain a long distinguishing walk. -/
theorem frontier {q E V S T} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (sv : S⊆V) (tv : T⊆V) (cover : V⊆S∪T)
    (e : ↥S ≃ ↥T) (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (rule : ExchangePattern E e) :
    ((∃i j : ↥S,E i j=true ∧ E (e i) (e j)=false) ∧
     (∃i j : ↥S,E i j=false ∧ E (e i) (e j)=true)) ∨
    (∀i j : ↥S,E i j=E (e i) (e j)) ∧
      ∃v k,q<k ∧ k≤(moved S T).card ∧ Walk (distinguished E (partner e)) (moved S T) v v k := by
  classical
  rcases rule with trade | ⟨iso,⟨i,hi,_,_,_⟩,_⟩
  · exact Or.inl trade
  right
  refine ⟨iso,?_⟩
  have sub : moved S T ⊆ V := union_subset (sdiff_subset.trans sv) (sdiff_subset.trans tv)
  apply cycle free small sub ⟨i,mem_union_left _ hi⟩ xp strict
  · intro j hj
    rcases mem_union.mp hj with h | h
    · obtain ⟨js,jt⟩ := mem_sdiff.mp h
      simp only [partner,dite_eq_left js]
      exact ⟨tv (e ⟨j,js⟩).property,fun eq => jt (eq ▸ (e ⟨j,js⟩).property)⟩
    · obtain ⟨jt,js⟩ := mem_sdiff.mp h
      simp only [partner,dite_eq_right js,dite_eq_left jt]
      exact ⟨sv (e.symm ⟨j,jt⟩).property,fun eq => js (eq ▸ (e.symm ⟨j,jt⟩).property)⟩
  · intro j hj t ht hit
    have both : t∈S ∧ t∈T := by
      obtain ⟨inV,no⟩ := mem_sdiff.mp ht
      have someSide := mem_union.mp (cover inV)
      by_cases hs : t∈S <;> by_cases ht' : t∈T <;> simp_all [moved]
    let u : ↥S := ⟨t,both.1⟩
    rcases mem_union.mp hj with h | h
    · obtain ⟨js,_⟩ := mem_sdiff.mp h
      have eq := iso u ⟨j,js⟩
      rw [fix u both.2] at eq
      simpa only [partner,dite_eq_left js] using eq.symm.trans hit
    · obtain ⟨jt,js⟩ := mem_sdiff.mp h
      have eq := iso u (e.symm ⟨j,jt⟩)
      rw [fix u both.2,e.apply_symm_apply] at eq
      simpa only [partner,dite_eq_right js,dite_eq_left jt] using eq.trans hit


/-- The legal successive deletions have disjoint omitted sets. The walk
bound is twice their common omission size, independently of order. -/
theorem step {F q E V} {x : ℕ→ℚ} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    {go : PairedFamilyLoop.State F → PairedFamilyLoop.State F} (a : Function.periodicPts go)
    (joint : PairedFamilyLoop.previous (go a.val)=PairedFamilyLoop.current a.val)
    (size : (RawRepairAlternative.gone a.val).card=(RawRepairAlternative.gone (go a.val)).card) :
    let D := RawRepairAlternative.gone a.val
    let S := V\D
    let T := V\RawRepairAlternative.gone (go a.val)
    ∀e : ↥S ≃ ↥T,(∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → ExchangePattern E e →
     ((∃i j : ↥S,E i j=true ∧ E (e i) (e j)=false) ∧
      (∃i j : ↥S,E i j=false ∧ E (e i) (e j)=true)) ∨
      (∀i j : ↥S,E i j=E (e i) (e j)) ∧
        ∃v k,q<k ∧ k≤2*D.card ∧ Walk (distinguished E (partner e)) (moved S T) v v k := by
  classical
  intro D S T e fix rule
  let B := RawRepairAlternative.gone (go a.val)
  have covers : V⊆S∪T := by
    intro i iv
    by_cases h : i∈D
    · apply mem_union_right
      exact mem_sdiff.mpr ⟨iv,fun hb => (mem_sdiff.mp h).2 (joint ▸ (mem_sdiff.mp hb).1)⟩
    · exact mem_union_left _ (mem_sdiff.mpr ⟨iv,h⟩)
  rcases frontier free small xp strict (sv:=sdiff_subset) (tv:=sdiff_subset) covers e fix rule with h | ⟨iso,v,k,hk,le,w⟩
  · exact Or.inl h
  have sub : moved S T⊆D∪B := by
    intro i hi
    rcases mem_union.mp hi with h | h
    · have iv := (mem_sdiff.mp (mem_sdiff.mp h).1).1
      exact mem_union_right _ (by_contra fun no => (mem_sdiff.mp h).2 (mem_sdiff.mpr ⟨iv,no⟩))
    · have iv := (mem_sdiff.mp (mem_sdiff.mp h).1).1
      exact mem_union_left _ (by_contra fun no => (mem_sdiff.mp h).2 (mem_sdiff.mpr ⟨iv,no⟩))
  have count := (card_le_card sub).trans (card_union_le D B)
  change D.card=B.card at size
  change k ≤ (moved S T).card at le
  exact Or.inr ⟨iso,v,k,hk,by omega,w⟩

/-- Use the return theorem on the very row law used for exchange. -/
theorem child_geometry {q E V U p z} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (sub : U⊆V) (size : U.card<V.card)
    (hp : RealDual q E U 1 p) (flat : ∀i∈U,realCol q E U p i=1)
    (zm : realMass U z=1) (states : ∀i∈U,0<z i ∧ realRow q E U z i=1) :
    BRsub.Sat q E U ∧ (U.card+1<V.card → ∀a∈V\U,∀b∈V\U,
      1<(q:ℝ)*realOutW E U z a → 1<(q:ℝ)*realInW E U p b → a≠b ∧
      ∃o∈outN E U a,∃i∈inN E U b,∃k≤q-2,Walk E U o i k) := by
  classical
  have live : U.Nonempty := by
    by_contra! empty
    simp [empty,realMass] at zm
  refine ⟨FlatChildClosure.saturated hq small size (free.mono_set sub) live hp flat,?_⟩
  intro room a ha b hb heavyO heavyI
  have fresh := (mem_sdiff.mp ha).2
  have size' : (insert a U).card<V.card := by rwa [card_insert_of_notMem fresh]
  have path := FlatChildClosure.heavy_return hq small (free.mono_set sub) fresh size'
    (I:=inN E U b) (O:=outN E U a) (filter_subset _ _) (filter_subset _ _) hp flat zm
    (fun i hi => (states i hi).1) (fun i hi => (states i hi).2)
    (by simpa only [realMass,outN,sum_filter,realOutW] using heavyO)
    (by simpa only [realMass,inN,sum_filter,realInW] using heavyI)
  refine ⟨?_,path⟩
  obtain ⟨o,ho,i,hi,k,hk,w⟩ := path
  rintro rfl
  have tail : Walk E V i a 1 := .step (mem_sdiff.mp ha).1 (mem_inN.mp hi).2 (.refl _)
  have head : Walk E V a i (k+1) := .step (sub (mem_outN.mp ho).1) (mem_outN.mp ho).2 (w.mono sub)
  exact free a _ (by omega) (by omega) (head.append tail)

#print axioms step
#print axioms child_geometry

/-- Follow a walk in S. Until its first common vertex, the isomorphism can
carry the initial segment to T. From a common vertex its old suffix works. -/
private theorem switch_walk {E : CH.Digraph} {V S T : Finset ℕ} (sv : S⊆V) (tv : T⊆V) (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    {a b k} (w : Walk E S a b k) (ha : a∈S) :
    Walk E (S\T) a b k ∨ Walk E V (e ⟨a,ha⟩) b k := by
  induction w with
  | refl => exact Or.inl (.refl _)
  | @step a u b k hu au rest ih =>
    have eu : E (e ⟨a,ha⟩) (e ⟨u,hu⟩)=true := (iso ⟨a,ha⟩ ⟨u,hu⟩).symm.trans au
    by_cases ut : u∈T
    · rw [fix ⟨u,hu⟩ ut] at eu
      exact Or.inr (.step (sv hu) eu (rest.mono sv))
    · rcases ih hu with localWalk | switched
      · exact Or.inl (.step (mem_sdiff.mpr ⟨hu,ut⟩) au localWalk)
      · exact Or.inr (.step (tv (e ⟨u,hu⟩).property) eu switched)

/-- A cross arc absent from the aligned child forces a short return
entirely inside the exchanged block. No shared vertex is needed. -/
theorem confined {q E V S T} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E S)
    (sv : S⊆V) (tv : T⊆V) (e : ↥S ≃ ↥T) (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i)
    (iso : ∀i j : ↥S,E i j=E (e i) (e j)) (i j : ↥S)
    (cross : E i (e j)=true) (miss : E i j=false) :
    ∃k≤q-1,Walk E (S\T) j i k := by
  obtain ⟨_,k,hk,w⟩ := mem_ball.mp (sat j j.property i i.property (by simp [miss]))
  rcases switch_walk sv tv e fix iso w j.property with h | h
  · exact ⟨k,hk,h⟩
  · exact (free i (k+1) (by omega) (by omega) (.step (tv (e j).property) cross h)).elim

#print axioms confined

#print axioms cycle
#print axioms frontier
end LeanCH.BR.Closure.FlatExchangeCycle
