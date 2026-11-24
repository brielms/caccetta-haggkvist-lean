import checkpoints.shen_extension.RecursiveCutTransitions
import Mathlib.Combinatorics.Hall.Finite

namespace LeanCH.BR.ShenReturnCut
open BRq2 BRq3 BR45
open Classical

def closedRows (D : CH.Digraph) (A B : Finset ℕ) := B∪image D A B

private theorem closed_size (D : CH.Digraph) (A B : Finset ℕ) :
    (closedRows D A B).card=B.card+(boundary D A B).card := by
  have card := Finset.card_union_add_card_inter (image D A B) B
  have cut := Finset.card_sdiff_add_card_inter (image D A B) B
  unfold closedRows boundary; rw [Finset.union_comm B]; omega

private theorem closed_subset {D : CH.Digraph} {A B : Finset ℕ} (sub : B⊆A) : closedRows D A B⊆A := by
  intro z hz
  rcases Finset.mem_union.mp hz with h|h
  · exact sub h
  · obtain ⟨_,_,edge⟩ := Finset.mem_biUnion.mp h; exact (mem_outN.mp edge).1

/-- Weighted Hall inequality for one transition. The starting law can have
one unit of excess on any set, plus the slack of the terminal state.
The ending law may be any target with the given total and per-label cap. -/
theorem Terminal.transport_cut {D : CH.Digraph} {V A : Finset ℕ} {q s} (T : Terminal D V q s A)
    (hq : 1≤q) (start goal : ℕ → ℕ)
    (mass : (∑ x∈A,start x)=(q-1)*A.card) (target : (∑ x∈A,goal x)=(q-1)*A.card)
    (cap : ∀ x∈A,goal x≤q)
    (tilt : ∀ B⊆A,(∑ x∈B,start x)≤(q-1)*B.card+1+(q*s-(A.card+q*(boundary D V A).card)))
    (B) (ba : B⊆A) : (∑ x∈B,start x)≤∑ x∈closedRows D A B,goal x := by
  let G := closedRows D A B
  have ga : G⊆A := closed_subset ba
  by_cases empty : B=∅
  · subst B; simp
  by_cases full : B=A
  · have eq : G=A := Finset.Subset.antisymm ga (fun x hx => Finset.mem_union_left _ (full ▸ hx))
    change _≤∑ x∈G,goal x
    rw [eq,full,mass,target]
  have pay := T.drift ba (Finset.nonempty_iff_ne_empty.mpr empty) full
  have sizes := Finset.card_sdiff_add_card_eq_card ba
  have cs : G.card=B.card+(boundary D A B).card := closed_size D A B
  have cut := Finset.card_sdiff_add_card_eq_card ga
  have rest := Finset.sum_le_sum (fun x (hx : x∈A \ G) => cap x (Finset.mem_sdiff.mp hx).1)
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at rest
  have all := Finset.sum_sdiff ga (f:=goal)
  rw [target] at all
  have quota := tilt B ba
  have hq' : q-1+1=q := by omega
  have ac := congrArg (fun j : ℕ => j*A.card) hq'
  have bc := congrArg (fun j : ℕ => j*B.card) hq'
  have total := congrArg (fun j : ℕ => q*j) cut
  have front := congrArg (fun j : ℕ => q*j) cs
  change _≤∑ x∈G,goal x
  nlinarith only [pay,sizes,rest,all,quota,ac,bc,total,front,Nat.zero_le (q*(boundary D V A \ image D V B).card)]

/-- Labelled slots for a prescribed integer mass at each vertex. -/
def slots (A : Finset ℕ) (load : ℕ → ℕ) : Finset (ℕ×ℕ) :=
  A.biUnion (fun x => (Finset.range (load x)).image (fun j => (x,j)))

private theorem mem_slots {A : Finset ℕ} {load : ℕ → ℕ} {z : ℕ×ℕ} :
    z∈slots A load ↔ z.1∈A ∧ z.2<load z.1 := by
  rcases z with ⟨x,j⟩
  simp [slots]

private theorem card_slots (A : Finset ℕ) (load : ℕ → ℕ) : (slots A load).card=∑ x∈A,load x := by
  rw [slots,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),Finset.card_range]
  · intro x _ y _ ne
    apply Finset.disjoint_left.mpr
    intro z hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hy
    exact ne (Prod.mk.inj eq).1.symm

private theorem realize {D : CH.Digraph} {A : Finset ℕ} {start goal : ℕ → ℕ}
    (total : (∑ x∈A,start x)=∑ x∈A,goal x)
    (hall : ∀ B⊆A,(∑ x∈B,start x)≤∑ x∈closedRows D A B,goal x) :
    ∃ f : (slots A start) ≃ (slots A goal),
      ∀ i, (f i).val.1=i.val.1 ∨ D i.val.1 (f i).val.1=true := by
  let L := slots A start
  let R := slots A goal
  let choices := fun (i : L) => R.attach.filter (fun z => z.val.1=i.val.1 ∨ D i.val.1 z.val.1=true)
  have test (U : Finset L) : U.card≤(U.biUnion choices).card := by
    let B := U.image (fun i => i.val.1)
    have ba : B⊆A := by
      intro x hx; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_slots.mp i.property).1
    have starts : U.image Subtype.val⊆slots B start := by
      intro z hz; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      exact mem_slots.mpr ⟨Finset.mem_image_of_mem _ hi,(mem_slots.mp i.property).2⟩
    have dst : slots (closedRows D A B) goal⊆(U.biUnion choices).image Subtype.val := by
      intro z hz
      obtain ⟨hg,hj⟩ := mem_slots.mp hz
      let v : R := ⟨z,mem_slots.mpr ⟨closed_subset ba hg,hj⟩⟩
      have reach : ∃ i∈U,z.1=i.val.1 ∨ D i.val.1 z.1=true := by
        rcases Finset.mem_union.mp hg with hb|im
        · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp hb
          exact ⟨i,hi,Or.inl eq.symm⟩
        · obtain ⟨w,hw,arc⟩ := Finset.mem_biUnion.mp im
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
          exact ⟨i,hi,Or.inr (mem_outN.mp arc).2⟩
      obtain ⟨i,hi,edge⟩ := reach
      exact Finset.mem_image.mpr ⟨v,Finset.mem_biUnion.mpr
        ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,edge⟩⟩,rfl⟩
    have nstart := Finset.card_le_card starts
    rw [Finset.card_image_of_injective _ Subtype.val_injective,card_slots] at nstart
    have nend := Finset.card_le_card dst
    rw [Finset.card_image_of_injective _ Subtype.val_injective,card_slots] at nend
    exact nstart.trans ((hall B ba).trans nend)
  obtain ⟨f,inject,allowed⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp test
  have sizes : Fintype.card L=Fintype.card R := by simpa [L,R,card_slots] using total
  have bij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inject,sizes⟩
  exact ⟨Equiv.ofBijective f bij,fun i => (Finset.mem_filter.mp (allowed i)).2⟩

/-- The slot matching only uses the displayed Hall cuts and total masses. -/
theorem realize_of_cuts {D : CH.Digraph} {A : Finset ℕ} {start goal : ℕ → ℕ}
    (total : (∑ x∈A,start x)=∑ x∈A,goal x)
    (hall : ∀ B⊆A,(∑ x∈B,start x)≤∑ x∈closedRows D A B,goal x) :
    ∃ f : (slots A start) ≃ (slots A goal),
      ∀ i, (f i).val.1=i.val.1 ∨ D i.val.1 (f i).val.1=true :=
  realize total hall

theorem mem_slots_iff {A : Finset ℕ} {w : ℕ → ℕ} {z : ℕ×ℕ} :
    z∈slots A w ↔ z.1∈A ∧ z.2<w z.1 := mem_slots

theorem slots_card_eq (A : Finset ℕ) (w : ℕ → ℕ) :
    (slots A w).card=∑i∈A,w i := card_slots A w

theorem Terminal.transport {D : CH.Digraph} {V A : Finset ℕ} {q s} (T : Terminal D V q s A)
    (hq : 1≤q) (start goal : ℕ → ℕ)
    (mass : (∑ x∈A,start x)=(q-1)*A.card) (target : (∑ x∈A,goal x)=(q-1)*A.card)
    (cap : ∀ x∈A,goal x≤q)
    (tilt : ∀ B⊆A,(∑ x∈B,start x)≤(q-1)*B.card+1+(q*s-(A.card+q*(boundary D V A).card))) :
    ∃ f : (slots A start) ≃ (slots A goal),
      ∀ i, (f i).val.1=i.val.1 ∨ D i.val.1 (f i).val.1=true :=
  realize (mass.trans target.symm) (T.transport_cut hq start goal mass target cap tilt)

#print axioms Terminal.transport

/-- Compose one-step transports without losing individual slot identity.
At each time the bijection gives exactly the scheduled vertex loads. -/
theorem Terminal.itinerary {D : CH.Digraph} {V A : Finset ℕ} {q s} (T : Terminal D V q s A)
    (hq : 1≤q) (load : ℕ → ℕ → ℕ)
    (mass : ∀ t,(∑ x∈A,load t x)=(q-1)*A.card)
    (cap : ∀ t,∀ x∈A,load t x≤q)
    (tilt : ∀ t,∀ B⊆A,(∑ x∈B,load t x)≤(q-1)*B.card+1+(q*s-(A.card+q*(boundary D V A).card))) :
    ∃ path : ∀ t,(slots A (load 0)) ≃ (slots A (load t)),
      path 0=Equiv.refl _ ∧ ∀ t i,
        ((path (t+1)) i).val.1=((path t) i).val.1 ∨ D (((path t) i).val.1) (((path (t+1)) i).val.1)=true := by
  have step (t : ℕ) := T.transport hq (load t) (load (t+1)) (mass t) (mass (t+1)) (cap (t+1)) (tilt t)
  choose f walk using step
  let path : ∀ t,(slots A (load 0)) ≃ (slots A (load t)) :=
    fun t => Nat.rec (motive:=fun t => (slots A (load 0)) ≃ (slots A (load t)))
      (Equiv.refl _) (fun t prev => prev.trans (f t)) t
  exact ⟨path,rfl,fun t i => walk t (path t i)⟩

/-- Returning to the same vertex after a sequence of allowed transitions
within the cutoff forces this particular slot to have stayed there throughout. -/
theorem short_return_stays {D : CH.Digraph} {V : Finset ℕ} {q j : ℕ} (hf : QFree D V q)
    (track : ℕ → ℕ) (inside : ∀ i,track i∈V)
    (steps : ∀ i,track (i+1)=track i ∨ D (track i) (track (i+1))=true)
    (short : j≤q) (closed : track j=track 0) : ∀ k≤j,track k=track 0 := by
  have move (t : ℕ) : ∃ m≤t,Walk D V (track 0) (track t) m ∧ (m=0 → ∀ k≤t,track k=track 0) := by
    induction t with
    | zero => exact ⟨0,le_rfl,.refl _,fun _ k hk => congrArg track (Nat.eq_zero_of_le_zero hk)⟩
    | succ t ih =>
      obtain ⟨m,mt,walk,stays⟩ := ih
      rcases steps t with hold|edge
      · refine ⟨m,by omega,hold ▸ walk,?_⟩
        intro zero k hk
        by_cases old : k≤t
        · exact stays zero _ old
        · rw [show k=t+1 by omega,hold]; exact stays zero _ le_rfl
      · exact ⟨m+1,by omega,walk.snoc (inside _) edge,by omega⟩
  obtain ⟨m,mt,walk,stays⟩ := move j
  rw [closed] at walk
  apply stays
  by_contra! nonzero
  exact hf (track 0) m (by omega) (by omega) walk

#print axioms Terminal.itinerary
#print axioms short_return_stays


def oneShift (q plus minus x : ℕ) := (q-1+(if x=plus then 1 else 0))-(if x=minus then 1 else 0)

private theorem shift_count {q : ℕ} (hq : 2≤q) (plus minus : ℕ) (B : Finset ℕ) :
    (∑ x∈B,oneShift q plus minus x)+(if minus∈B then 1 else 0)=
      (q-1)*B.card+(if plus∈B then 1 else 0) := by
  have one (x : ℕ) (_ : x∈B) : oneShift q plus minus x+(if x=minus then 1 else 0)=
      q-1+(if x=plus then 1 else 0) := by
    unfold oneShift
    split_ifs <;> omega
  have count := Finset.sum_congr rfl one
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_const_nat (fun _ _ => rfl),
    Nat.mul_comm B.card (q-1)] using count

/-- Any prescribed sequence of single-unit displacements of the uniform
mass has a simultaneous labelled realization, for every time index. -/
theorem Terminal.shift_itinerary {D : CH.Digraph} {V A : Finset ℕ} {q s} (T : Terminal D V q s A)
    (hq : 2≤q) (plus minus : ℕ → ℕ) (pA : ∀ t,plus t∈A) (mA : ∀ t,minus t∈A) :
    let load := fun t => oneShift q (plus t) (minus t)
    ∃ path : ∀ t,(slots A (load 0)) ≃ (slots A (load t)),
      path 0=Equiv.refl _ ∧ ∀ t i,
        ((path (t+1)) i).val.1=((path t) i).val.1 ∨ D (((path t) i).val.1) (((path (t+1)) i).val.1)=true := by
  intro load
  apply T.itinerary (by omega) load
  · intro t
    have := shift_count hq (plus t) (minus t) A
    simpa [load,pA t,mA t] using this
  · intro t x _
    dsimp only [load,oneShift]; split_ifs <;> omega
  · intro t B _
    have := shift_count hq (plus t) (minus t) B
    dsimp only [load]; split_ifs at this <;> omega

#print axioms Terminal.shift_itinerary


/-- Single-unit tests alone are passed by every strongly connected graph
at q≥3. This comparison uses neither terminality nor a cycle assumption. -/
theorem shift_on_connected {D : CH.Digraph} {A : Finset ℕ} {q a b c d : ℕ}
    (hq : 3≤q) (connect : ∀ B⊆A,B.Nonempty → B≠A → B≠closedRows D A B)
    (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A) :
    ∃ f : (slots A (oneShift q a b)) ≃ (slots A (oneShift q c d)),
      ∀ i, (f i).val.1=i.val.1 ∨ D i.val.1 (f i).val.1=true := by
  have first := shift_count (by omega : 2≤q) a b A
  have last := shift_count (by omega : 2≤q) c d A
  simp only [ha,hb,hc,hd,ite_true] at first last
  apply realize (by omega)
  intro B ba
  by_cases empty : B=∅
  · subst B; simp
  by_cases full : B=A
  · have eq : closedRows D A B=A := Finset.Subset.antisymm (closed_subset ba)
      (fun x hx => Finset.mem_union_left _ (full ▸ hx))
    rw [eq,full]; omega
  let G := closedRows D A B
  have more : B.card<G.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_union_left,connect B ba (Finset.nonempty_iff_ne_empty.mpr empty) full⟩)
  have diff := Nat.mul_le_mul_left (q-1) (show B.card+1≤G.card by omega)
  have start := shift_count (by omega : 2≤q) a b B
  have finish := shift_count (by omega : 2≤q) c d G
  change _≤∑ x∈G,oneShift q c d x
  rw [Nat.mul_add,Nat.mul_one] at diff
  split_ifs at start <;> split_ifs at finish <;> omega

#print axioms shift_on_connected

end LeanCH.BR.ShenReturnCut
