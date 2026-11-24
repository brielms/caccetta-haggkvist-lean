import checkpoints.shen_extension.TrianglePunctureClass
import LeanCH.BR.BRWeightedCycleStructure

namespace LeanCH.BR.Closure.TriangleMinimumPuncture
open Finset BRq2 BRq3 BR45 ShortestCycleClasses ShortestCycleWeights ShenPrimeTransition

theorem minimum_puncture {n} (X : Model 3 n) {h} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x) :
    ∀r∈X.V, X.D r h=true → carrier X.D (X.V\{h}) 3 r=X.V\{h} := by
  classical
  intro r rv rh
  let W := X.V\{h}
  let C := carrier X.D W 3 r
  let B := W\C
  have cw : C⊆W := filter_subset _ _
  have cv : C⊆X.V := cw.trans sdiff_subset
  have rwv : r∈W := mem_sdiff.mpr ⟨rv,fun eq => loopfree X.free (by decide) hv ((mem_singleton.mp eq) ▸ rh)⟩
  have rc : r∈C := contains rwv
  have hvw : h∉W := fun hh => (mem_sdiff.mp hh).2 (mem_singleton_self _)
  have hc : h∉C := fun hh => hvw (cw hh)
  have bsub : B⊆W := sdiff_subset
  have hb : h∉B := fun hh => hvw (bsub hh)
  have dis : Disjoint C B := disjoint_left.mpr (fun _ c b => (mem_sdiff.mp b).2 c)
  have partition : C∪B=W := union_sdiff_of_subset cw
  have full : insert h (C∪B)=X.V := by
    rw [partition]
    ext z
    by_cases e : z=h <;> simp [W,e,hv]
  have hcb : h∉C∪B := by simp [hc,hb]
  have nochild : ¬Strict 3 X.D C X.weights := by
    intro high
    have cmp := X.minimal X.D C X.weights ⟨r,rc⟩ (X.free.mono_set cv) (fun x hx => X.positive x (cv hx))
      ((sum_le_sum_of_subset_of_nonneg cv (by intros; omega)).trans X.bounded) high
    exact hc (eq_of_subset_of_card_le cv cmp ▸ hv)
  rw [nat_strict] at nochild
  push Not at nochild
  obtain ⟨a,ac,low⟩ := nochild
  have cl := (TrianglePunctureClass.closed X rv hv rh).2
  have none (a) (ac : a∈C) (b) (bb : b∈B) : X.D a b=false := by
    apply Bool.eq_false_iff.mpr
    exact fun edge => (mem_sdiff.mp bb).2 (cl a ac (mem_outN.mpr ⟨bsub bb,edge⟩))
  have strict := nat_strict.mp X.strict a (cv ac)
  unfold score at strict low
  rw [←full,sum_insert hcb,sum_insert hcb,sum_union dis,sum_union dis] at strict
  have zero : (∑y∈B,if X.D a y=true then X.weights y else 0)=0 :=
    sum_eq_zero fun y bym => by simp [none a ac y bym]
  rw [zero] at strict
  have bound : (∑y∈B,X.weights y)<2*X.weights h := by
    split at strict <;> omega
  have mass_lower (T : Finset ℕ) (tv : T⊆X.V) :
      T.card*X.weights h≤∑y∈T,X.weights y := by
    simpa using sum_le_sum (fun x (hx : x∈T) => minimum x (tv hx))
  have positive := X.positive h hv
  have bv := bsub.trans (sdiff_subset : W⊆X.V)
  have small : B.card≤1 := by
    by_contra! ge
    have big := Nat.mul_le_mul_right (X.weights h) (show 2≤B.card by omega)
    have le := mass_lower B bv
    omega
  by_contra diff
  change C≠W at diff
  have someB : B.Nonempty := by
    by_contra empty
    have e := not_nonempty_iff_eq_empty.mp empty
    change W\C=∅ at e
    exact diff (Subset.antisymm cw (sdiff_eq_empty_iff_subset.mp e))
  obtain ⟨b,bb⟩ := someB
  have beq : B={b} := eq_of_subset_of_card_le (fun z zm => mem_singleton.mpr
    (card_le_one.mp small z zm b bb)) (by simpa using (card_pos.mpr ⟨b,bb⟩ : 0<B.card))
  have forced (p) (pv : p∈X.V) (pb : X.D p b=true) : p=h := by
    by_contra neq
    have pw : p∈W := mem_sdiff.mpr ⟨pv,by simpa using neq⟩
    rw [←partition] at pw
    rcases mem_union.mp pw with pc | pB
    · simp [none p pc b bb] at pb
    · have eq := card_le_one.mp small p pB b bb
      exact loopfree X.free (by decide) (bv bb) (eq ▸ pb)
  have only (y) (yv : y∈X.V) (hy : X.D h y=true) : y=b := by
    by_contra neq
    obtain ⟨p,pv,pb,py⟩ := X.separated b (bv bb) y yv neq
    have ph := forced p pv pb
    simp [ph,hy] at py
  have cap : (∑y∈X.V,if X.D h y=true then X.weights y else 0)≤X.weights b := by
    calc
      _ ≤ ∑y∈X.V,if y=b then X.weights b else 0 := by
        apply sum_le_sum
        intro y yv
        by_cases edge : X.D h y=true
        · simp only [edge,ite_true]
          rw [only y yv edge]
          simp
        · simp [edge]
      _ = _ := by simp [bv bb]
  have high := nat_strict.mp X.strict h hv
  unfold score at high
  rw [←full,sum_insert hcb,sum_union dis,beq,sum_singleton] at high
  have bm : X.weights b<2*X.weights h := by simpa [beq] using bound
  have cm : (∑y∈C,X.weights y)<2*X.weights b := by
    rw [←full,beq] at cap
    omega
  have countC : C.card≤3 := by
    by_contra! ge
    have big := Nat.mul_le_mul_right (X.weights h) (show 4≤C.card by omega)
    have le := mass_lower C cv
    omega
  have order : X.V.card≤3+2 := by
    rw [←full,card_insert_of_notMem hcb,card_union_of_disjoint dis,beq,card_singleton]
    omega
  exact (WeightedSD.smallRow_of_card_le_add_two (by decide) X.free order).no_strict
    X.live _ (fun _ _ => Nat.cast_nonneg _) X.strict

/-- A nonvacuous puncture witness, with the very same parent and labels in
both the original incidence graph and the punctured overlap relation. -/
theorem puncture_exists {n} (X : Model 3 n) :
    ∃h∈X.V, (∀x∈X.V,X.weights h≤X.weights x) ∧ ∃r∈X.V,X.D r h=true ∧
      carrier X.D (X.V\{h}) 3 r=X.V\{h} := by
  classical
  obtain ⟨h,hv,minh⟩ := X.V.exists_min_image X.weights X.live
  have size : 5<X.V.card := by
    by_contra! sm
    exact (WeightedSD.smallRow_of_card_le_add_two (by decide) X.free sm).no_strict
      X.live _ (fun _ _ => Nat.cast_nonneg _) X.strict
  obtain ⟨y,yv,ne⟩ : ∃y∈X.V,y≠h := by
    by_contra! all
    have le := card_le_card (show X.V⊆{h} from fun i hi => mem_singleton.mpr (all i hi))
    simp at le
    omega
  obtain ⟨r,rv,rh,_⟩ := X.separated h hv y yv ne
  exact ⟨h,hv,minh,r,rv,rh,minimum_puncture X hv minh r rv rh⟩

#print axioms puncture_exists
#print axioms minimum_puncture
end LeanCH.BR.Closure.TriangleMinimumPuncture
