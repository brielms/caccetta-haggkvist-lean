import checkpoints.shen_extension.SecondNeighbourTransport
import checkpoints.shen_extension.SeymourTransition

namespace LeanCH.BR.ShenUnitRowPacking
open BRq2 BRq3 Finset

/-- Closed forward neighbourhood of a set in the original graph. -/
def grow (D : CH.Digraph) (V S : Finset ℕ) := S ∪ S.biUnion (outN D V)

private theorem grow_sub {D V S} (sub : S ⊆ V) : grow D V S ⊆ V := by
  intro x hx
  rcases mem_union.mp hx with h | h
  · exact sub h
  · obtain ⟨_,_,arc⟩ := mem_biUnion.mp h
    exact outN_subset arc

/-- Expansion for every nonempty proper set, uniformly in the cutoff. -/
theorem grow_bound {q D V s S} (term : ShenRootedKernel.Terminal q D V s)
    (sub : S ⊆ V) (proper : S ≠ V) (live : S.Nonempty) :
    q*s + (q-1)*S.card + 1 ≤ q*(grow D V S).card := by
  obtain ⟨a,ha,low⟩ := S.exists_min_image (fun t => (outN D S t).card) live
  have light : q*(outN D S a).card < S.card := by
    by_contra! h
    have := term.stop S sub _ ⟨live,h,low⟩
    have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,proper⟩)
    omega
  have eq : S ∩ outN D V a = outN D S a := by
    ext z
    simp only [mem_inter,mem_outN]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,sub h.1,h.2⟩⟩
  have incl : S ∪ outN D V a ⊆ grow D V S := by
    intro z hz
    rcases mem_union.mp hz with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_biUnion.mpr ⟨a,ha,h⟩)
  have count := card_union_add_card_inter S (outN D V a)
  rw [eq] at count
  have upper := Nat.mul_le_mul_left q (card_le_card incl)
  have deg := Nat.mul_le_mul_left q (term.degree a (sub ha))
  have identity := congrArg (q * ·) count
  simp only [Nat.mul_add] at identity
  have positive : 0 < q := by
    have h := term.order
    have h' := term.nonempty.card_pos
    cases q <;> simp_all
  have scale : q*S.card = (q-1)*S.card + S.card := by
    nth_rw 1 [show q = (q-1)+1 by omega]
    simp [Nat.add_mul]
  omega

private theorem two_steps {D V s S} (term : ShenRootedKernel.Terminal 3 D V s)
    (sub : S ⊆ V) (live : S.Nonempty) :
    grow D V (grow D V S) = V ∨
    15*s + 4*S.card + 5 ≤ 9*(grow D V (grow D V S)).card := by
  have i : S ⊆ grow D V S := subset_union_left
  have j : grow D V S ⊆ grow D V (grow D V S) := subset_union_left
  by_cases h : grow D V S = V
  · exact Or.inl (Subset.antisymm (grow_sub (grow_sub sub)) (fun z hz => j (h.symm ▸ hz)))
  by_cases e : S = V
  · exact (h (Subset.antisymm (grow_sub sub) (e ▸ i))).elim
  have a := grow_bound term sub e live
  have b := grow_bound term (grow_sub sub) h (live.mono i)
  exact Or.inr (by omega)

private theorem head_count {D V s} (free : QFree D V 3)
    (term : ShenRootedKernel.Terminal 3 D V s) : 8*s + 4 ≤ 3*V.card := by
  obtain ⟨u,hu,big⟩ : ∃ u ∈ V, s ≤ (HalfRows.inN D V u).card := by
    by_contra! bad
    have up : ∑ x ∈ V, (HalfRows.inN D V x).card < ∑ _x ∈ V, s :=
      sum_lt_sum_of_nonempty term.nonempty bad
    have lo : ∑ _x ∈ V, s ≤ ∑ y ∈ V, (outN D V y).card := sum_le_sum term.degree
    have eq : ∑ x ∈ V, (HalfRows.inN D V x).card = ∑ y ∈ V, (outN D V y).card :=
      TightRow.sum_indeg_eq_sum_outdeg D V
    omega
  let O := outN D V u
  have deg : s ≤ O.card := term.degree u hu
  have pos := term.nonempty.card_pos
  have bound := term.order
  have alive : O.Nonempty := card_pos.mp (by omega)
  have noLoop := loopfree free (by decide) hu
  have proper : O ≠ V := fun e => noLoop (mem_outN.mp (show u ∈ O from e ▸ hu)).2
  have expand := grow_bound term (S:=O) outN_subset proper alive
  have exclude : Disjoint (grow D V O) (insert u (HalfRows.inN D V u)) := by
    apply disjoint_left.mpr
    intro z hz hbad
    have reach : z ∈ ball D V u 2 := by
      rcases mem_union.mp hz with h | h
      · exact ball_mono_radius (by decide : 1≤2) (mem_ball_one_of_out h)
      · obtain ⟨v,hv,arc⟩ := mem_biUnion.mp h
        exact ball_step (mem_ball_one_of_out hv) (outN_subset arc) (mem_outN.mp arc).2
    rcases mem_insert.mp hbad with rfl | back
    · rcases mem_union.mp hz with h | h
      · exact noLoop (mem_outN.mp h).2
      · obtain ⟨v,hv,arc⟩ := mem_biUnion.mp h
        exact digonfree free (by decide) hu (outN_subset hv) (mem_outN.mp hv).2 (mem_outN.mp arc).2
    · exact no_back_arc free hu reach (by decide) (mem_filter.mp back).2
  have upper : grow D V O ∪ insert u (HalfRows.inN D V u) ⊆ V :=
    union_subset (grow_sub outN_subset) (insert_subset hu (filter_subset _ _))
  have card := card_le_card upper
  have absent : u ∉ HalfRows.inN D V u := fun h => noLoop (mem_filter.mp h).2
  rw [card_union_of_disjoint exclude,card_insert_of_notMem absent] at card
  omega

private theorem reachable {D V S} (sub : S ⊆ V) {z} (hz : z ∈ grow D V (grow D V S)) :
    ∃ a ∈ S, z ∈ ball D V a 2 := by
  have one {v} (hv : v ∈ grow D V S) : ∃ a ∈ S, v ∈ ball D V a 1 := by
    rcases mem_union.mp hv with h | h
    · exact ⟨_,h,self_mem_ball (sub h)⟩
    · obtain ⟨a,ha,edge⟩ := mem_biUnion.mp h
      exact ⟨_,ha,mem_ball_one_of_out edge⟩
  rcases mem_union.mp hz with h | h
  · obtain ⟨a,ha,reach⟩ := one h
    exact ⟨_,ha,ball_mono_radius (by decide) reach⟩
  · obtain ⟨v,hv,edge⟩ := mem_biUnion.mp h
    obtain ⟨a,ha,reach⟩ := one hv
    exact ⟨_,ha,ball_step reach (outN_subset edge) (mem_outN.mp edge).2⟩

abbrev Tickets (A B C : Finset ℕ) := (A.disjSum B).disjSum C

def head : (ℕ ⊕ ℕ) ⊕ ℕ → ℕ := Sum.elim (Sum.elim id id) id

private theorem heads_in_host {A B C V : Finset ℕ} (aV : A ⊆ V)
    (bV : B ⊆ V) (cV : C ⊆ V) (U : Finset (Tickets A B C)) :
    U.image (fun i => head i.val) ⊆ V := by
  intro z hz
  obtain ⟨⟨i,hi⟩,_,rfl⟩ := mem_image.mp hz
  rcases i with (a|b)|c
  · exact @aV a (by simpa using hi)
  · exact @bV b (by simpa using hi)
  · exact @cV c (by simpa using hi)

private theorem cover_reach {A B C V : Finset ℕ} {D : CH.Digraph} (r : ℕ)
    (U : Finset (Tickets A B C)) (sub : U.image (fun i => head i.val) ⊆ V) :
    grow D V (grow D V (U.image (fun i => head i.val))) ⊆
      insert r (U.biUnion (fun i => (ball D V (head i.val) 2).erase r)) := by
  intro z hz
  by_cases same : z=r
  · simp [same]
  obtain ⟨a,ha,reach⟩ := reachable sub hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
  exact mem_insert_of_mem (mem_biUnion.mpr ⟨i,hi,mem_erase.mpr ⟨same,reach⟩⟩)

/-- Assign distinct vertices reachable in at most two steps, avoiding any one prescribed vertex. -/
def Packing (D : CH.Digraph) (V A B C : Finset ℕ) (r : ℕ) :=
  ∃ f : Tickets A B C → ℕ, Function.Injective f ∧
    ∀ i, f i ∈ (ball D V (head i.val) 2).erase r

theorem pack {D V s A B C} (free : QFree D V 3) (term : ShenRootedKernel.Terminal 3 D V s)
    (aV : A ⊆ V) (bV : B ⊆ V) (cV : C ⊆ V) (aSize : A.card=s) (bSize : B.card=s)
    (budget : 9*C.card + 4*(A ∩ B).card ≤ 5*s+4) (r : ℕ) : Packing D V A B C r := by
  classical
  let choices (i : Tickets A B C) := (ball D V (head i.val) 2).erase r
  apply (all_card_le_biUnion_card_iff_existsInjective' choices).mp
  intro U
  by_cases live : U.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp live]
  let T := U.image (fun i => head i.val)
  have sub : T ⊆ V := heads_in_host aV bV cV U
  have full : U.card ≤ 2*s+C.card := by
    have h := card_le_card (show U.image Subtype.val ⊆ Tickets A B C from by
      intro z hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      exact i.property)
    simp only [card_image_of_injective _ Subtype.val_injective,card_disjSum,aSize,bSize] at h
    omega
  have portion : U.image Subtype.val ⊆ Tickets (A ∩ T) (B ∩ T) C := by
    intro v hv
    obtain ⟨⟨i,hi⟩,hu,rfl⟩ := mem_image.mp hv
    have inside : head i ∈ T := mem_image_of_mem _ hu
    rcases i with (a|b)|c <;> simp only [Tickets,inl_mem_disjSum,inr_mem_disjSum] at hi ⊢ <;>
      first | exact mem_inter.mpr ⟨hi,inside⟩ | exact hi
  have overlap : U.card ≤ T.card+(A ∩ B).card+C.card := by
    have u := card_le_card portion
    simp only [card_image_of_injective _ Subtype.val_injective,card_disjSum] at u
    have v := card_union_add_card_inter (A ∩ T) (B ∩ T)
    have w := card_le_card (show (A ∩ T) ∪ (B ∩ T) ⊆ T from union_subset inter_subset_right inter_subset_right)
    have x := card_le_card (show (A ∩ T) ∩ (B ∩ T) ⊆ A ∩ B from inter_subset_inter inter_subset_left inter_subset_left)
    omega
  have incl : grow D V (grow D V T) ⊆ insert r (U.biUnion choices) := cover_reach r U sub
  have one := (card_le_card incl).trans (card_insert_le _ _)
  rcases two_steps term sub (live.image _) with sat | expand
  · rw [sat] at one
    have n := head_count free term
    omega
  · omega

theorem sparse_pack {D V s A B C} (free : QFree D V 3) (term : ShenRootedKernel.Terminal 3 D V s)
    (aV : A ⊆ V) (bV : B ⊆ V) (cV : C ⊆ V) (aSize : A.card=s) (bSize : B.card=s)
    (sparse : 3*(A ∩ B).card+1 ≤ s) (cap : C.card ≤ (11*s+16)/27) (r : ℕ) :
    Packing D V A B C r :=
  pack free term aV bV cV aSize bSize (by omega) r

/-- Choose which single request is left unpaid, keeping every other label and its destinations. -/
def Reroutable {ι : Type*} [DecidableEq ι] (U : Finset ι) (F : ι → Finset ℕ) : Prop :=
  ∀ i ∈ U, ∃ f : U.erase i → ℕ, Function.Injective f ∧ ∀ j, f j ∈ F j.val

/-- Choose a smallest deficient set of labelled requests. Its deficiency is
exactly one, and deleting any single request leaves every destination accessible. -/
private theorem least_defect {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → Finset ℕ)
    (failure : ∃ U : Finset ι, (U.biUnion F).card < U.card) :
    ∃ U : Finset ι, (U.biUnion F).card+1 = U.card ∧
      (∀ i ∈ U, (U.erase i).biUnion F = U.biUnion F) ∧ Reroutable U F := by
  classical
  let W := (univ : Finset (Finset ι)).filter (fun U => (U.biUnion F).card < U.card)
  have hit (U : Finset ι) : U ∈ W ↔ (U.biUnion F).card < U.card := by simp [W]
  obtain ⟨start,hstart⟩ := failure
  obtain ⟨U,hu,least⟩ := W.exists_min_image Finset.card ⟨start,(hit _).mpr hstart⟩
  have small := (hit _).mp hu
  have eraseInfo (i) (hi : i ∈ U) :
      (U.biUnion F).card+1=U.card ∧ (U.erase i).biUnion F=U.biUnion F := by
    have strict := card_erase_lt_of_mem hi
    have notBad : (U.erase i).card ≤ ((U.erase i).biUnion F).card := by
      by_contra! h
      exact strict.not_ge (least _ ((hit _).mpr h))
    have sub : (U.erase i).biUnion F ⊆ U.biUnion F := by
      intro z hz
      obtain ⟨j,hj,arc⟩ := mem_biUnion.mp hz
      exact mem_biUnion.mpr ⟨j,mem_of_mem_erase hj,arc⟩
    have lo := card_le_card sub
    rw [card_erase_of_mem hi] at notBad
    exact ⟨by omega,eq_of_subset_of_card_le sub (by omega)⟩
  obtain ⟨i,hi⟩ := card_pos.mp (show 0 < U.card by omega)
  refine ⟨U,(eraseInfo i hi).1,fun j hj => (eraseInfo j hj).2,?_⟩
  intro j hj
  let choices (t : U.erase j) := F t.val
  apply (all_card_le_biUnion_card_iff_existsInjective' choices).mp
  intro L
  let P := L.image Subtype.val
  have incl : P ⊆ U.erase j := by
    intro z hz
    obtain ⟨t,_,rfl⟩ := mem_image.mp hz
    exact t.property
  have less := (card_le_card incl).trans_lt (card_erase_lt_of_mem hj)
  have ok : P.card ≤ (P.biUnion F).card := by
    by_contra! no
    exact less.not_ge (least _ ((hit _).mpr no))
  have cover : P.biUnion F ⊆ L.biUnion choices := by
    intro z hz
    obtain ⟨a,ha,hz⟩ := mem_biUnion.mp hz
    obtain ⟨t,ht,rfl⟩ := mem_image.mp ha
    exact mem_biUnion.mpr ⟨t,ht,hz⟩
  have h := ok.trans (card_le_card cover)
  simpa only [P,card_image_of_injective _ Subtype.val_injective] using h

/-- Every failed choice of a third set has a *specific* Hall witness.
Its participating third-row labels already exceed the budget. -/
theorem obstruction {D V s A B C r} (free : QFree D V 3)
    (term : ShenRootedKernel.Terminal 3 D V s) (aV : A ⊆ V) (bV : B ⊆ V)
    (cV : C ⊆ V) (aSize : A.card=s) (bSize : B.card=s) (stuck : ¬ Packing D V A B C r) :
    ∃ U : Finset (Tickets A B C),
      (U.biUnion (fun i => (ball D V (head i.val) 2).erase r)).card+1 = U.card ∧
      (∀ i ∈ U, (U.erase i).biUnion (fun j => (ball D V (head j.val) 2).erase r) =
        U.biUnion (fun j => (ball D V (head j.val) 2).erase r)) ∧
      Reroutable U (fun i => (ball D V (head i.val) 2).erase r) ∧
      5*s+4 < 9*((U.image Subtype.val).toRight.card) + 4*(A ∩ B).card := by
  classical
  let choices (i : Tickets A B C) := (ball D V (head i.val) 2).erase r
  have failure : ∃ U : Finset (Tickets A B C), (U.biUnion choices).card < U.card := by
    by_contra! no
    exact stuck ((all_card_le_biUnion_card_iff_existsInjective' choices).mp no)
  obtain ⟨U,bad,shared,move⟩ := least_defect choices failure
  refine ⟨U,bad,shared,move,?_⟩
  let C' := (U.image Subtype.val).toRight
  have sub : C' ⊆ C := by
    intro x hx
    obtain ⟨i,_,eq⟩ := mem_image.mp (mem_toRight.mp hx)
    have h := i.property
    rw [eq] at h
    simpa using h
  by_contra! budget
  obtain ⟨f,inj,ok⟩ := pack free term aV bV (sub.trans cV) aSize bSize budget r
  have liftMem (i : ↥U) : i.val.val ∈ Tickets A B C' := by
    have h := i.val.property
    have hit := mem_image_of_mem Subtype.val i.property
    rcases eq : i.val.val with j | c
    · rw [eq] at h
      simpa using h
    · exact inr_mem_disjSum.mpr (mem_toRight.mpr (eq ▸ hit))
  let lift (i : ↥U) : Tickets A B C' := ⟨i.val.val,liftMem i⟩
  have liftInj : Function.Injective lift := fun _ _ eq =>
    Subtype.ext (Subtype.ext (congrArg (fun j : Tickets A B C' => j.val) eq))
  have cover : (univ : Finset ↥U).image (f ∘ lift) ⊆ U.biUnion choices := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    exact mem_biUnion.mpr ⟨i.val,i.property,ok (lift i)⟩
  have h := card_le_card cover
  rw [card_image_of_injective _ (inj.comp liftInj)] at h
  simp only [card_univ,Fintype.card_coe] at h
  omega

/-- This is the counting step a full third row would close. -/
theorem order_of_packing {D V A B C r} (hr : r ∈ V) (h : Packing D V A B C r) :
    A.card+B.card+C.card < V.card := by
  obtain ⟨f,inj,ok⟩ := h
  have sub : (univ : Finset (Tickets A B C)).image f ⊆ V.erase r := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    obtain ⟨different,reach⟩ := mem_erase.mp (ok i)
    exact mem_erase.mpr ⟨different,ball_subset reach⟩
  have size := (card_le_card sub).trans_lt (card_erase_lt_of_mem hr)
  simpa only [card_image_of_injective _ inj,card_univ,Fintype.card_coe,card_disjSum] using size

/-- If two-step reach misses a vertex, the Hall witness must carry a minimum
number of repeated head labels. Otherwise its destinations fill the host
apart from the reserved vertex. Both cases concern the same requests. -/
theorem location_of_defect {D V s A B C r} (term : ShenRootedKernel.Terminal 3 D V s)
    (aV : A ⊆ V) (bV : B ⊆ V) (cV : C ⊆ V) (hr : r ∈ V)
    (U : Finset (Tickets A B C))
    (gap : (U.biUnion (fun i => (ball D V (head i.val) 2).erase r)).card+1 = U.card) :
    U.card = V.card ∨
      15*s+5 ≤ 5*U.card + 4*(U.card-(U.image (fun i => head i.val)).card) := by
  let T := U.image (fun i => head i.val)
  let N := U.biUnion (fun i => (ball D V (head i.val) 2).erase r)
  have gap' : N.card+1 = U.card := gap
  have live : U.Nonempty := card_pos.mp (by omega)
  have sub : T ⊆ V := heads_in_host aV bV cV U
  have cover : grow D V (grow D V T) ⊆ insert r N := cover_reach r U sub
  have upper := (card_le_card cover).trans (card_insert_le _ _)
  rcases two_steps term sub (live.image _) with sat | expand
  · have inside : N ⊆ V.erase r := by
      intro z hz
      obtain ⟨i,_,reach⟩ := mem_biUnion.mp hz
      obtain ⟨diff,ball⟩ := mem_erase.mp reach
      exact mem_erase.mpr ⟨diff,ball_subset ball⟩
    have nlt := (card_le_card inside).trans_lt (card_erase_lt_of_mem hr)
    rw [sat] at upper
    exact Or.inl (by omega)
  · change _ ∨ 15*s+5 ≤ 5*U.card + 4*(U.card-T.card)
    have labels : T.card ≤ U.card := card_image_le
    exact Or.inr (by omega)

/-- On three complete rows a counterexample itself supplies an exchangeable
one-unit obstruction, with a quantitative condition on its third colour. -/
theorem full_rows {D V s A B C r} (free : QFree D V 3) (term : ShenRootedKernel.Terminal 3 D V s)
    (aV : A ⊆ V) (bV : B ⊆ V) (cV : C ⊆ V)
    (aSize : A.card=s) (bSize : B.card=s) (cSize : C.card=s) (hr : r ∈ V) :
    ∃ U : Finset (Tickets A B C),
      (U.biUnion (fun i => (ball D V (head i.val) 2).erase r)).card+1 = U.card ∧
      Reroutable U (fun i => (ball D V (head i.val) 2).erase r) ∧
      5*s+4 < 9*(U.image Subtype.val).toRight.card + 4*(A ∩ B).card ∧
      (U.card=V.card ∨ 15*s+5 ≤ 5*U.card+4*(U.card-(U.image (fun i => head i.val)).card)) := by
  have stuck : ¬ Packing D V A B C r := by
    intro h
    have n := order_of_packing hr h
    have bound := term.order
    omega
  obtain ⟨U,gap,_,move,load⟩ := obstruction free term aV bV cV aSize bSize stuck
  exact ⟨U,gap,move,load,location_of_defect term aV bV cV hr U gap⟩

/-- Once all other requests of a one-unit obstruction are paid, every
available destination in that obstruction has an actual owner. -/
theorem all_claimed {ι : Type*} [DecidableEq ι] (U : Finset ι) (F : ι → Finset ℕ)
    (gap : (U.biUnion F).card+1 = U.card) {i : ι} (hi : i ∈ U)
    (f : U.erase i → ℕ) (inj : Function.Injective f) (ok : ∀ j, f j ∈ F j.val) :
    ∀ z ∈ U.biUnion F, ∃ j, f j = z := by
  classical
  have sub : (univ : Finset ↥(U.erase i)).image f ⊆ U.biUnion F := by
    intro z hz
    obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact mem_biUnion.mpr ⟨j.val,mem_of_mem_erase j.property,ok j⟩
  have eq := eq_of_subset_of_card_le sub (by
    rw [card_image_of_injective _ inj,card_univ,Fintype.card_coe,card_erase_of_mem hi]
    omega)
  intro z hz
  rw [←eq] at hz
  obtain ⟨j,_,edge⟩ := mem_image.mp hz
  exact ⟨j,edge⟩

/-- Select a Seymour vertex among the actual head labels of any nonempty
subcollection of requests. A request with precisely that head can be left
unpaid while every other request of the original obstruction is paid. -/
theorem seymour_unpaid {D V A B C r q} (free : QFree D V q) (three : 3≤q)
    (aV : A ⊆ V) (bV : B ⊆ V) (cV : C ⊆ V)
    {U : Finset (Tickets A B C)} (move : Reroutable U (fun i => (ball D V (head i.val) 2).erase r))
    {P : Finset (Tickets A B C)} (sub : P ⊆ U) (live : P.Nonempty) :
    let T := P.image (fun i => head i.val)
    ∃ i ∈ P, (outN D T (head i.val)).card ≤ (ShenSeymour.second D T (head i.val)).card ∧
      2*(outN D T (head i.val)).card+(ShenSeymour.parents D T (head i.val)).card < T.card ∧
      ∃ f : U.erase i → ℕ, Function.Injective f ∧
        ∀ j, f j ∈ (ball D V (head j.val.val) 2).erase r := by
  obtain ⟨x,hx,good,low⟩ := ShenSeymour.surviving_row free three
    (heads_in_host aV bV cV P) (live.image _)
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  exact ⟨i,hi,good,low,move i (sub hi)⟩

/-- All conclusions hold on the same normalized host and the same supplied arc. -/
theorem source_with_packing {D V s} (free : QFree D V 3) (ne : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ a ∈ V, s ≤ (outN D V a).card) :
    ∃ d, ∃ X : ShenMinimumOrder.Source 3 d, X.V.card ≤ V.card ∧ X.V.card ≤ 3*d ∧
      OutEq d X.D X.V ∧ ShenRootedKernel.Terminal 3 X.D X.V d ∧
      ∃ u ∈ X.V, ∃ v ∈ outN X.D X.V u,
      (∀ a ∈ outN X.D X.V u, ∃ z ∈ outN X.D X.V a, z ∈ outN X.D X.V u) ∧
      (outN X.D X.V u ∩ outN X.D X.V v).Nonempty ∧
      3*(outN X.D X.V u ∩ outN X.D X.V v).card+1 ≤ d ∧
      ShenSecondNeighbour.JointAssignment X.D X.V u v ∧
      (∀ C ⊆ X.V, C.card ≤ (11*d+16)/27 → ∀ r,
        Packing X.D X.V (outN X.D X.V u) (outN X.D X.V v) C r) ∧
      ∃ N, ShenCycleSuccessor.Via X u N ∧ (v ∈ N ∨
        (v ∉ N ∧ 2 ≤ (ShenKernelHead.parents X.D N v).card ∧
          ∃ K, ShenCycleSuccessor.Via X v K ∧ v ∈ K)) := by
  obtain ⟨d,X,small,bound,reg,term,u,hu,v,hv,inner,common,over,joint,cycle⟩ :=
    ShenSecondNeighbour.common_source_terminal free ne order degree
  exact ⟨d,X,small,bound,reg,term,u,hu,v,hv,inner,common,over,joint,
    fun _ sub cap r => sparse_pack X.free term outN_subset outN_subset sub
      (reg u hu) (reg v (outN_subset hv)) over cap r,cycle⟩

#print axioms full_rows
#print axioms seymour_unpaid
#print axioms all_claimed
#print axioms location_of_defect
#print axioms order_of_packing
#print axioms obstruction
#print axioms source_with_packing
#print axioms grow_bound
#print axioms pack
#print axioms sparse_pack
end LeanCH.BR.ShenUnitRowPacking
