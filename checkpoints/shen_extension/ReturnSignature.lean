import checkpoints.shen_extension.OneArcReturnBudget
import checkpoints.shen_extension.EqualLayers

namespace LeanCH.BR.ReturnSignature
open Finset BRq2 BRq3 BR45 TripleBank ThirtySixClose

/-- Returns for which the middle cannot afford to cut its arc to the short row. -/
def tight (H : CH.Digraph) (U : Finset ℕ) (y w t : ℕ) :=
  (outN H U y ∩ inN H U w).filter (fun z => (outN H U z).card ≤ t)

/-- Equal punctured two-ball signatures on K forbid even a single two-step connection. -/
theorem signature_far {H : CH.Digraph} {U K : Finset ℕ} {a b : ℕ}
    (_ak : a∈K) (bk : b∈K) (ne : a≠b)
    (eq : seen H U K 2 a = seen H U K 2 b) : b∉ball H U a 2 := by
  intro near
  have mem : b∈seen H U K 2 a := mem_filter.mpr ⟨bk,ne.symm,near⟩
  rw [eq] at mem
  exact (mem_filter.mp mem).2.1 rfl

/-- An auxiliary graph J inside equal-signature classes promotes all its nonsinks.
Only the sinks among tight middles need to be paid for by the new head y. -/
theorem patch_pays {H J : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y)
    (off : H w y≠true) (back : H y w≠true) (need : t≤(outN H U w).card+1)
    (floor : ∀ v∈U, v≠w → t≤(outN H U v).card) (aux : QFree J U 3)
    (internal : ∀ a∈U, ∀ b∈outN J U a, a∈tight H U y w t ∧ b∈tight H U y w t ∧
      seen H U (tight H U y w t) 2 a = seen H U (tight H U y w t) 2 b)
    (budget : t+((tight H U y w t).filter (fun z => (outN J U z).card=0)).card≤(outN H U y).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ ∀ i∈U, t≤(outN E U i).card := by
  classical
  let K := tight H U y w t
  let A := outN J U
  let G := patch H A (fun _ => ∅)
  have nw : w∉K := fun m => back (mem_outN.mp (mem_inter.mp (mem_filter.mp m).1).1).2
  have ny : y∉K := fun m => back (mem_inN.mp (mem_inter.mp (mem_filter.mp m).1).2).2
  have short {a b} (au : a∈U) (bu : b∈U) (h : H a b=true) : b∈ball H U a 2 :=
    ball_mono_radius (by decide : 1≤2) (ball_step (self_mem_ball (k:=0) au) bu h)
  obtain ⟨clean,rows⟩ := patch_certificate (A:=A) (C:=fun _ => ∅) safe
    (fun a au b ab => by
      have bu := outN_subset ab
      have ne : a≠b := fun e => loopfree aux (by decide) au (e ▸ (mem_outN.mp ab).2)
      obtain ⟨ak,bk,eq⟩ := internal a au b ab
      exact ⟨bu,ne.symm,fun h => signature_far ak bk ne eq (short au bu h),
        fun h => signature_far bk ak ne.symm eq.symm (short bu au h)⟩)
    (fun a au b ab h hu bh ha => by
      obtain ⟨ak,bk,eq⟩ := internal a au b ab
      have ne : a≠b := fun e => loopfree aux (by decide) au (e ▸ (mem_outN.mp ab).2)
      have path := ball_step (ball_step (self_mem_ball (k:=0) (outN_subset ab)) hu bh) au ha
      exact (signature_far bk ak ne.symm eq.symm path).elim)
    (fun a au b ab c bc => by
      have bu := outN_subset ab
      have cu := outN_subset bc
      have jab := (mem_outN.mp ab).2
      have jbc := (mem_outN.mp bc).2
      have ca : c≠a := fun e => digonfree aux (by decide) au bu jab (e ▸ jbc)
      obtain ⟨ak,_,eq⟩ := internal a au b ab
      obtain ⟨_,ck,eq'⟩ := internal b bu c bc
      refine ⟨ca,fun patched => ?_⟩
      obtain ja | old := of_decide_eq_true patched
      · exact aux a 3 (by decide) (by decide) (.step bu jab (.step cu jbc (.step au (mem_outN.mp ja).2 (.refl _))))
      · exact signature_far ck ak ca (eq.trans eq').symm (short cu au old.1))
  have row (a) (au : a∈U) : (outN G U a).card=(outN H U a).card+(outN J U a).card := by
    simpa [G,A] using rows a au
  have sameY {i} (iu : i∈U) : G y i=true ↔ H y i=true := by
    change decide (_ ∨ _)=true ↔ _
    rw [decide_eq_true_eq]
    simp only [notMem_empty,not_false_eq_true,and_true]
    exact ⟨fun h => h.elim (fun m => (ny (internal y yu i m).1).elim) id,Or.inr⟩
  have sameW {i} (iu : i∈U) : G i w=true ↔ H i w=true := by
    change decide (_ ∨ _)=true ↔ _
    rw [decide_eq_true_eq]
    simp only [notMem_empty,not_false_eq_true,and_true]
    exact ⟨fun h => h.elim (fun m => (nw (internal i iu w m).2.1).elim) id,Or.inr⟩
  have sameWy : G w y≠true := by
    intro h
    obtain new | old := of_decide_eq_true h
    · exact nw (internal w wu y new).1
    · exact off old.1
  have retain : tight G U y w t ⊆ K.filter (fun z => (outN J U z).card=0) := by
    intro z zm
    obtain ⟨hit,low⟩ := mem_filter.mp zm
    obtain ⟨yz,zw⟩ := mem_inter.mp hit
    obtain ⟨zu,gyz⟩ := mem_outN.mp yz
    have hzw := (sameW zu).mp (mem_inN.mp zw).2
    have hyz := (sameY zu).mp gyz
    have zw' : z≠w := fun e => loopfree safe (by decide) wu (e ▸ hzw)
    have fl := floor z zu zw'
    rw [row z zu] at low
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_inter.mpr
      ⟨mem_outN.mpr ⟨zu,hyz⟩,mem_inN.mpr ⟨zu,hzw⟩⟩,by omega⟩,by omega⟩
  have bound := card_le_card retain
  have yrow := row y yu
  have wrow := row w wu
  refine one_arc_return_budget (D:=G) clean wu yu wy sameWy (fun h => back ((sameY wu).mp h))
    (by omega) (fun i iu diff => (floor i iu diff).trans (by have := row i iu; omega)) ?_
  change t+(tight G U y w t).card≤(outN G U y).card
  change _ ≤ (K.filter _).card at bound
  change t+(K.filter _).card≤_ at budget
  omega

/-- Count the different signatures occurring on one, two or three tight middles. -/
def smallClasses (K : Finset ℕ) (sig : ℕ → Finset ℕ) :=
  ((K.image sig).filter (fun l => (K.filter (fun z => sig z=l)).card≤3)).card

private def next (m i j : ℕ) : Prop :=
  if 4≤m then j=i+1 ∨ (i+1=m ∧ j=0) else i≠0 ∧ j=0

private theorem one_step (m i : ℕ) (valid : i<m) (go : 4≤m ∨ i≠0) :
    ∃ j<m, next m i j := by
  by_cases large : 4≤m
  · by_cases room : i+1<m
    · exact ⟨i+1,room,by simp [next,large]⟩
    · exact ⟨0,by omega,by simp [next,large,show i+1=m by omega]⟩
  · exact ⟨0,by omega,by simp [next,large,go.resolve_left large]⟩

private theorem past_loop {m i : ℕ} : ¬next m i i := by
  unfold next
  split_ifs <;> omega

private theorem past_digon {m i j : ℕ} : next m i j → ¬next m j i := by
  unfold next
  split_ifs <;> omega

private theorem past_triangle {m i j k : ℕ} : next m i j → next m j k → ¬next m k i := by
  unfold next
  split_ifs <;> omega

/-- Inside each class use a directed cycle if it has four or more labels;
on smaller classes all labels except one point to their representative. -/
private theorem plan {U K : Finset ℕ} (kv : K⊆U) (sig : ℕ → Finset ℕ) :
    ∃ J : CH.Digraph, QFree J U 3 ∧
      (∀ a∈U, ∀ b∈outN J U a, a∈K ∧ b∈K ∧ sig a=sig b) ∧
      (K.filter (fun z => (outN J U z).card=0)).card≤smallClasses K sig := by
  classical
  let C (l : Finset ℕ) := K.filter (fun z => sig z=l)
  let num (l : Finset ℕ) (a : ℕ) := if h : a∈C l then
    ((Fintype.equivFin ↥(C l)) ⟨a,h⟩).val else 0
  have realize (l : Finset ℕ) (j : ℕ) (hi : j<(C l).card) : ∃ b∈C l, num l b=j := by
    let i : Fin (Fintype.card ↥(C l)) := ⟨j,by simpa using hi⟩
    let b := (Fintype.equivFin ↥(C l)).symm i
    refine ⟨b.val,b.property,?_⟩
    change (if h : b.val∈C l then _ else _) = j
    rw [dite_eq_left b.property]
    exact congrArg Fin.val ((Fintype.equivFin ↥(C l)).apply_symm_apply i)
  have inj {l a b} (ac : a∈C l) (bc : b∈C l) (eq : num l a=num l b) : a=b := by
    dsimp only [num] at eq
    rw [dite_eq_left ac,dite_eq_left bc] at eq
    exact congrArg Subtype.val ((Fintype.equivFin ↥(C l)).injective (Fin.ext eq))
  let M (a : ℕ) := (C (sig a)).card
  let I (a : ℕ) := num (sig a) a
  let J : CH.Digraph := fun a b => decide (a∈K ∧ b∈K ∧ sig a=sig b ∧ next (M a) (I a) (I b))
  have get {a b} (ab : J a b=true) : a∈K ∧ b∈K ∧ sig a=sig b ∧ next (M a) (I a) (I b) :=
    of_decide_eq_true ab
  have mass {a b} (ab : J a b=true) : M a=M b := congrArg (fun l => (C l).card) (get ab).2.2.1
  have clean : QFree J U 3 := DotOriginalStarReturn.qfree_three_of_tests
    (fun _ _ ab => past_loop (get ab).2.2.2)
    (fun _ _ _ _ ab ba => past_digon (get ab).2.2.2 (mass ab ▸ (get ba).2.2.2))
    (fun _ _ _ _ _ _ ab bc ca => past_triangle (get ab).2.2.2
      (mass ab ▸ (get bc).2.2.2) ((mass ab).trans (mass bc) ▸ (get ca).2.2.2))
  refine ⟨J,clean,fun a _ b ab => ?_,?_⟩
  · obtain ⟨ak,bk,lbl,_⟩ := get (mem_outN.mp ab).2
    exact ⟨ak,bk,lbl⟩
  let S := K.filter (fun z => (outN J U z).card=0)
  have sink {a} (h : a∈S) : M a≤3 ∧ I a=0 := by
    obtain ⟨ak,zero⟩ := mem_filter.mp h
    have ac : a∈C (sig a) := mem_filter.mpr ⟨ak,rfl⟩
    have valid : I a<M a := by
      dsimp only [I,M,num]
      rw [dite_eq_left ac]
      simpa using ((Fintype.equivFin ↥(C (sig a))) ⟨a,ac⟩).isLt
    by_contra! bad
    have go : 4≤M a ∨ I a≠0 := by omega
    obtain ⟨j,jm,step⟩ := one_step _ _ valid go
    obtain ⟨b,bc,bj⟩ := realize (sig a) j jm
    obtain ⟨bk,eq⟩ := mem_filter.mp bc
    have ib : I b=j := by simpa only [I,eq] using bj
    have arc : J a b=true := decide_eq_true ⟨ak,bk,eq.symm,ib.symm ▸ step⟩
    have pos := card_pos.mpr (show (outN J U a).Nonempty from ⟨b,mem_outN.mpr ⟨kv bk,arc⟩⟩)
    omega
  have unique : Set.InjOn sig (S : Set ℕ) := by
    intro a ha b hb eq
    have ak := (mem_filter.mp ha).1
    have bk := (mem_filter.mp hb).1
    have ia := (sink ha).2
    have ib := (sink hb).2
    apply inj (l:=sig a) (mem_filter.mpr ⟨ak,rfl⟩) (mem_filter.mpr ⟨bk,eq.symm⟩)
    change num (sig a) a=0 at ia
    change num (sig b) b=0 at ib
    rw [←eq] at ib
    exact ia.trans ib.symm
  have imageIncl : S.image sig ⊆ (K.image sig).filter (fun l => (C l).card≤3) := by
    intro l lm
    obtain ⟨a,am,rfl⟩ := mem_image.mp lm
    exact mem_filter.mpr ⟨mem_image_of_mem sig (mem_filter.mp am).1,(sink am).1⟩
  have cnt := card_le_card imageIncl
  rw [card_image_of_injOn unique] at cnt
  exact cnt

/-- For the triangle witness repair, y pays once for each small class. -/
theorem small_classes_pay {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y)
    (off : H w y≠true) (back : H y w≠true) (need : t≤(outN H U w).card+1)
    (floor : ∀ v∈U, v≠w → t≤(outN H U v).card)
    (budget : let K := tight H U y w t; t+smallClasses K (seen H U K 2)≤(outN H U y).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ ∀ i∈U, t≤(outN E U i).card := by
  let K := tight H U y w t
  have inside : K⊆U := fun _ h => outN_subset (mem_inter.mp (mem_filter.mp h).1).1
  obtain ⟨J,clean,arcs,count⟩ := plan inside (seen H U K 2)
  exact patch_pays safe wu yu wy off back need floor clean arcs ((Nat.add_le_add_left count t).trans budget)

#print axioms small_classes_pay

#print axioms signature_far
#print axioms patch_pays
end LeanCH.BR.ReturnSignature
