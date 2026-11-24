import checkpoints.shen_extension.MarkedSquareFrontier

namespace LeanCH.BR.Closure.AnchoredShiftFlow
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor CycleSquareTensor

/-- For a stationary predecessor p, select only the moves through p.
Their replacement arcs again form a circulation. Every nonempty selection
therefore moves at least q+1 distinct original heads of p. -/
theorem stationary_parent {D W q} (hq : 1≤q) (free : QFree D W q) (M : ℕ→Finset ℕ)
    (a u v b : ℕ→ℕ) (l p : ℕ) (closed : M l=M 0)
    (cycle : ∀i,Cycle D W q (M i)) (move : ∀i,Shift D (M i) (M (i+1)) (a i) (u i) (v i) (b i))
    (fixed : p∉(range l).image u) :
    let I := (range l).filter (fun i => a i=p)
    I.Nonempty → I.image u=I.image v ∧ q+1≤(I.image u).card ∧ I.image u⊆outN D W p := by
  classical
  intro I present
  obtain ⟨i,ip⟩ := present
  have live : 0<l := by have := mem_range.mp (mem_filter.mp ip).1; omega
  have global := (MarkedSquareFrontier.active_labels hq free M a u v b l live closed cycle move).1
  have un (i) (hi : i∈range l) : u i≠p := fun eq => fixed (eq ▸ mem_image_of_mem u hi)
  have vn (i) (hi : i∈range l) : v i≠p := fun eq => fixed (global ▸ (eq ▸ mem_image_of_mem v hi))
  have counts (x : ℕ) : (∑i∈I,if v i=x then (1:ℤ) else 0) =
      ∑i∈I,if u i=x then (1:ℤ) else 0 := by
    let f := fun j k : ℕ => if j=p ∧ k=x then (1:ℤ) else 0
    have e := CycleSquareBalance.closed_balance hq free M a u v b l closed cycle move f
    have drop (g : ℕ→ℕ) (ng : ∀i∈range l,g i≠p) :
        (∑i∈range l,(f (a i) (g i)+f (g i) (b i))) = ∑i∈I,if g i=x then (1:ℤ) else 0 := by
      change _ = ∑i∈(range l).filter (fun i => a i=p),_
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      by_cases ap : a i=p <;> simp [f,ng i hi,ap]
    rwa [drop v vn,drop u un] at e
  have seen (g : ℕ→ℕ) (x : ℕ) : x∈I.image g ↔ 0<(∑i∈I,if g i=x then (1:ℤ) else 0) := by
    simp only [sum_boole, Int.natCast_pos,card_pos,Finset.Nonempty,mem_image,mem_filter]
  have same : I.image u=I.image v := by
    ext x
    rw [seen,seen,counts]
  have sub : I.image u⊆outN D W p := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
    exact mem_outN.mpr ⟨(cycle t).sub (move t).uM,(mem_filter.mp ht).2 ▸ (move t).before₁⟩
  have deg (x) (hx : x∈I.image u) : 1≤(outN D (I.image u) x).card := by
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
    exact card_pos.mpr ⟨v t,mem_outN.mpr ⟨by rw [same]; exact mem_image_of_mem v ht,(move t).move⟩⟩
  have size := dt_size hq (ball_q_one q hq) (free.mono_set (sub.trans (filter_subset _ _)))
    deg ⟨u i,mem_image_of_mem u ip⟩
  exact ⟨same,by simpa using size,sub⟩

/-- At the smallest possible positive period the moving labels themselves
form a shortest cycle. All moves use the same two stationary endpoints. -/
theorem least_period {D W q} (hq : 1≤q) (free : QFree D W q) (M : ℕ→Finset ℕ)
    (a u v b : ℕ→ℕ) (closed : M (q+1)=M 0)
    (cycle : ∀i,Cycle D W q (M i)) (move : ∀i,Shift D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) :
    let S := (range (q+1)).image u
    Cycle D W q S ∧ a 0∉S ∧ b 0∉S ∧
    (∀i<q+1,a i=a 0 ∧ b i=b 0) ∧
    (∀x∈S,D (a 0) x=true ∧ D x (b 0)=true) := by
  classical
  intro S
  have ⟨same,lower,_⟩ := MarkedSquareFrontier.active_labels hq free M a u v b (q+1) (by omega) closed cycle move
  have sz : S.card=q+1 := le_antisymm (card_image_le.trans (card_range _).le) lower
  have sub : S⊆W := by
    rintro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact (cycle i).sub (move i).uM
  have isU (i) (hi : i<q+1) : u i∈S := mem_image_of_mem u (mem_range.mpr hi)
  have isV (i) (hi : i<q+1) : v i∈S := by
    change v i∈(range (q+1)).image u
    rw [same]
    exact mem_image_of_mem v (mem_range.mpr hi)
  have deg (x) (hx : x∈S) : 1≤(outN D S x).card := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact card_pos.mpr ⟨v i,mem_outN.mpr ⟨isV i (mem_range.mp hi),(move i).move⟩⟩
  have reg := dt_reg hq (ball_q_one q hq) (free.mono_set sub) deg (by simpa using sz)
  have z : 0<q+1 := by omega
  have au : a 0≠u 0 := fun eq => loopfree free hq ((cycle 0).sub (move 0).uM) (eq ▸ (move 0).before₁)
  have ap : a 0∉S := fun ha => au (card_le_one.mp (reg.2 _ (isV 0 z)).le _
    (mem_inN.mpr ⟨ha,(move 0).after₁⟩) _ (mem_inN.mpr ⟨isU 0 z,(move 0).move⟩))
  have bp : b 0∉S := by
    intro hb
    have eq := card_le_one.mp (reg.1 _ (isU 0 z)).le _
      (mem_outN.mpr ⟨hb,(move 0).before₂⟩) _ (mem_outN.mpr ⟨isV 0 z,(move 0).move⟩)
    exact (move 0).exterior (eq ▸ (move 0).bM)
  let I := (range (q+1)).filter (fun i => a i=a 0)
  have live : I.Nonempty := ⟨0,mem_filter.mpr ⟨mem_range.mpr z,rfl⟩⟩
  have ⟨_,cap,_⟩ := stationary_parent hq free M a u v b (q+1) (a 0) closed cycle move ap live
  have allI : I=range (q+1) := eq_of_subset_of_card_le (filter_subset _ _)
    (by rw [card_range]; exact cap.trans card_image_le)
  have anchor (i) (hi : i<q+1) : a i=a 0 :=
    (mem_filter.mp (show i∈I from allI.symm ▸ mem_range.mpr hi)).2
  have next (i) (hi : i+1<q+1) : b (i+1)=b i := by
    let e := move i
    let t := move (i+1)
    have wn : v i∈M (i+1) := e.labels ▸ mem_insert_self _ _
    have an : a i∈M (i+1) := by rw [anchor i (by omega),←anchor (i+1) hi]; exact t.aM
    have nv : u (i+1)=v i := card_le_one.mp ((cycle (i+1)).heads _ an).le _
      (mem_outN.mpr ⟨t.uM,by rw [anchor i (by omega),←anchor (i+1) hi]; exact t.before₁⟩) _
      (mem_outN.mpr ⟨wn,e.after₁⟩)
    have bu : b i≠u i := fun eq => loopfree free hq ((cycle i).sub e.uM) (eq ▸ e.before₂)
    have bn : b i∈M (i+1) := e.labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨bu,e.bM⟩)
    exact card_le_one.mp ((cycle (i+1)).heads _ wn).le _
      (mem_outN.mpr ⟨t.bM,nv ▸ t.before₂⟩) _ (mem_outN.mpr ⟨bn,e.after₂⟩)
  have target (i) (hi : i<q+1) : b i=b 0 := by
    induction i with
    | zero => rfl
    | succ i ih => exact (next i hi).trans (ih (by omega))
  refine ⟨⟨sub,sz,reg.1,reg.2⟩,ap,bp,(fun i hi => ⟨anchor i hi,target i hi⟩),?_⟩
  intro x hx
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  exact ⟨anchor i (mem_range.mp hi) ▸ (move i).before₁,target i (mem_range.mp hi) ▸ (move i).before₂⟩

/-- A minimum-period shift loop produces a two-step rich loop on different
supports. Going out uses the initial replacement receiver. Coming back
uses a single vertex fed by the entire moving cycle and pointing to none of it. -/
theorem short_loop_crossing {D W q} (hq : 1≤q) (free : QFree D W q) (M : ℕ→Finset ℕ)
    (a u v b : ℕ→ℕ) (closed : M (q+1)=M 0)
    (cycle : ∀i,Cycle D W q (M i)) (move : ∀i,Shift D (M i) (M (i+1)) (a i) (u i) (v i) (b i))
    (noDigon : 2≤q) :
    ∃S, Cycle D W q S ∧ PunctureCycleLoop.Step D (M 0) S ∧ PunctureCycleLoop.Step D S (M 0) ∧
      b 0∈M 0\S ∧ inN D S (b 0)=S ∧ outN D S (b 0)=∅ := by
  classical
  let S := (range (q+1)).image u
  obtain ⟨cs,_,bp,_,arcs⟩ := least_period hq free M a u v b closed cycle move
  have vz : v 0∈S := by
    change v 0∈(range (q+1)).image u
    rw [(MarkedSquareFrontier.active_labels hq free M a u v b _ (by omega) closed cycle move).1]
    exact mem_image_of_mem v (mem_range.mpr (by omega))
  have au : a 0≠u 0 := fun eq => loopfree free hq ((cycle 0).sub (move 0).uM) (eq ▸ (move 0).before₁)
  have two := one_lt_card.mpr ⟨a 0,mem_inN.mpr ⟨(move 0).aM,(move 0).after₁⟩,
    u 0,mem_inN.mpr ⟨(move 0).uM,(move 0).move⟩,au⟩
  have full : inN D S (b 0)=S := Subset.antisymm (filter_subset _ _)
    (fun x xs => mem_inN.mpr ⟨xs,(arcs x xs).2⟩)
  have none : outN D S (b 0)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x xx
    obtain ⟨xs,bx⟩ := mem_outN.mp xx
    exact digonfree free noDigon (cs.sub xs) ((cycle 0).sub (move 0).bM) (arcs x xs).2 bx
  have outside := mem_sdiff.mpr ⟨(move 0).bM,bp⟩
  exact ⟨S,cs,⟨v 0,mem_sdiff.mpr ⟨vz,(move 0).exterior⟩,two⟩,
    ⟨b 0,outside,by rw [full,cs.size]; omega⟩,outside,full,none⟩

#print axioms short_loop_crossing
#print axioms least_period
#print axioms stationary_parent
end LeanCH.BR.Closure.AnchoredShiftFlow
