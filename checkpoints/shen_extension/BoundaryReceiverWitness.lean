import checkpoints.shen_extension.AttachmentLaws
import checkpoints.shen_extension.CyclePhaseFork
import checkpoints.shen_extension.SharedArcGrid

namespace LeanCH.BR.Closure.BoundaryReceiverWitness
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier

/-- All choices of shortest cycles supporting two different incoming arcs
at the same receiver have disjoint intersections with the boundary cycle. -/
theorem separate {D V q L A B z p t} (hq : 2 ≤ q) (safe : QFree D V q)
    (cycle : Cycle D V q L) (left : Cycle D V q A) (right : Cycle D V q B)
    (pl : p ∈ L) (tl : t ∈ L) (diff : p ≠ t) (pz : D p z = true) (tz : D t z = true)
    (pa : p ∈ A) (za : z ∈ A) (tb : t ∈ B) (zb : z ∈ B) :
    Disjoint (L ∩ A) (L ∩ B) :=
  CyclePhaseFork.disjoint_overlaps hq safe.reverse (SharedArcGrid.reverse_cycle cycle)
    (SharedArcGrid.reverse_cycle left) (SharedArcGrid.reverse_cycle right) pl tl
    pz tz diff za pa zb tb

/-- The physical parents, their old supporting cycles, and the separation
law all refer to one receiver on the given failed boundary attachment. -/
theorem on_boundary {q n} (X : Model q n) (hq : 2 ≤ q) {F : Family} {L}
    (native : F ⊆ family X) (boundary : Boundary X F L)
    (fed : ∃ z ∈ X.V, z ∉ L ∧ 2 ≤ (inN (graph X.D F) L z).card) :
    ∃ z ∈ X.V, z ∉ L ∧ ∃ p ∈ L, ∃ t ∈ L, p ≠ t ∧
      graph X.D F p z = true ∧ graph X.D F t z = true ∧
      (∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ p ∈ A ∧ z ∈ A ∧ t ∈ B ∧ z ∈ B) ∧
      (∀ A ∈ F, ∀ B ∈ F, p ∈ A → z ∈ A → t ∈ B → z ∈ B →
        Disjoint (L ∩ A) (L ∩ B)) := by
  classical
  obtain ⟨z,zv,zl,count⟩ := fed
  obtain ⟨p,ip,t,it,ne⟩ := one_lt_card.mp count
  obtain ⟨pl,pz⟩ := mem_inN.mp ip
  obtain ⟨tl,tz⟩ := mem_inN.mp it
  obtain ⟨A,ha⟩ := active.mp pz
  obtain ⟨B,hb⟩ := active.mp tz
  obtain ⟨af,pa,za,edgeP⟩ := mem_col.mp ha
  obtain ⟨bf,tb,zb,edgeT⟩ := mem_col.mp hb
  have cy (M) (mf : M ∈ F) : Cycle X.D X.V q M := (mem_filter.mp (native mf)).2
  have apart (I) (ifam : I ∈ F) (J) (jfam : J ∈ F) (pi : p ∈ I) (zi : z ∈ I)
      (tj : t ∈ J) (zj : z ∈ J) : Disjoint (L ∩ I) (L ∩ J) :=
    separate hq X.free (mem_filter.mp boundary.1).2 (cy I ifam) (cy J jfam)
      pl tl ne edgeP edgeT pi zi tj zj
  have diff : A ≠ B := by
    rintro rfl
    exact disjoint_left.mp (apart A af A bf pa za tb zb) (mem_inter.mpr ⟨pl,pa⟩)
      (mem_inter.mpr ⟨pl,pa⟩)
  exact ⟨z,zv,zl,p,pl,t,tl,ne,pz,tz,⟨A,af,B,bf,diff,pa,za,tb,zb⟩,apart⟩

noncomputable def avoiding (F : Family) (T : Finset ℕ) : Family := by
  classical exact F.filter (fun A => Disjoint A T)

/-- Delete every supporting cycle that touches a set of boundary vertices.
Each lost physical parent at the receiver requires a different deleted label. -/
theorem lost_parents {q n} (X : Model q n) (hq : 2 ≤ q) {F : Family} {L T : Finset ℕ}
    (native : F ⊆ family X) (cycle : Cycle X.D X.V q L) (inside : T ⊆ L) (z : ℕ) :
    ((inN (graph X.D F) L z) \ (inN (graph X.D (avoiding F T)) L z)).card ≤ T.card := by
  classical
  let lost := (inN (graph X.D F) L z) \ (inN (graph X.D (avoiding F T)) L z)
  have hit (p) (pm : p ∈ lost) :
      ∃ A ∈ F, p ∈ A ∧ z ∈ A ∧ X.D p z = true ∧ ∃ r ∈ T, r ∈ A := by
    obtain ⟨old,gone⟩ := mem_sdiff.mp pm
    obtain ⟨pl,pz⟩ := mem_inN.mp old
    obtain ⟨A,ha⟩ := active.mp pz
    obtain ⟨af,pa,za,arc⟩ := mem_col.mp ha
    have touches : ¬ Disjoint A T := by
      intro dis
      have kept : A ∈ avoiding F T := mem_filter.mpr ⟨af,dis⟩
      exact gone (mem_inN.mpr ⟨pl,active.mpr ⟨A,mem_col.mpr ⟨kept,pa,za,arc⟩⟩⟩)
    obtain ⟨r,ra,rt⟩ := not_disjoint_iff.mp touches
    exact ⟨A,af,pa,za,arc,r,rt,ra⟩
  choose! support member parent receiver edge label deleted belongs using hit
  apply card_le_card_of_injOn label (fun p pm => deleted p pm)
  intro p pm t tm eq
  by_contra ne
  have cy (A) (af : A ∈ F) : Cycle X.D X.V q A := (mem_filter.mp (native af)).2
  have part (a) (am : a ∈ lost) : a ∈ L := (mem_inN.mp (mem_sdiff.mp am).1).1
  have dis := separate hq X.free cycle (cy _ (member p pm)) (cy _ (member t tm))
    (part p pm) (part t tm) ne (edge p pm) (edge t tm)
    (parent p pm) (receiver p pm) (parent t tm) (receiver t tm)
  have rl := inside (deleted p pm)
  exact disjoint_left.mp dis (mem_inter.mpr ⟨rl,belongs p pm⟩)
    (mem_inter.mpr ⟨rl,eq ▸ belongs t tm⟩)

/-- Cut old cycles at specified old parents, then attach the boundary cycle.
At the exterior receiver the deleted parents are exactly the ones specified. -/
theorem cut_attach_column {q n} (X : Model q n) {F : Family} {L T : Finset ℕ} {z}
    (native : F ⊆ family X) (outside : z ∉ L) (cut : T ⊆ inN (graph X.D F) X.V z) :
    inN (graph X.D (insert L (avoiding F T))) X.V z = inN (graph X.D F) X.V z \ T := by
  classical
  ext p
  constructor
  · intro kept
    obtain ⟨pv,activeEdge⟩ := mem_inN.mp kept
    obtain ⟨A,ha⟩ := active.mp activeEdge
    obtain ⟨am,pa,za,edge⟩ := mem_col.mp ha
    rcases mem_insert.mp am with rfl | old
    · exact (outside za).elim
    obtain ⟨af,dis⟩ := mem_filter.mp (show A ∈ F.filter _ from old)
    exact mem_sdiff.mpr ⟨mem_inN.mpr ⟨pv,active.mpr ⟨A,mem_col.mpr ⟨af,pa,za,edge⟩⟩⟩,
      fun pt => disjoint_left.mp dis pa pt⟩
  · intro old
    obtain ⟨pm,pt⟩ := mem_sdiff.mp old
    obtain ⟨pv,pz⟩ := mem_inN.mp pm
    obtain ⟨A,ha⟩ := active.mp pz
    obtain ⟨af,pa,za,arc⟩ := mem_col.mp ha
    have cy : Cycle X.D X.V q A := (mem_filter.mp (native af)).2
    have dis : Disjoint A T := by
      apply disjoint_left.mpr
      intro t ta tt
      have tz := CrossValueOmissions.selected_sub (mem_inN.mp (cut tt)).2
      have eq := card_le_one.mp (cy.incoming z za).le p (mem_inN.mpr ⟨pa,arc⟩) t (mem_inN.mpr ⟨ta,tz⟩)
      exact pt (eq ▸ tt)
    have am : A ∈ avoiding F T := mem_filter.mpr ⟨af,dis⟩
    exact mem_inN.mpr ⟨pv,active.mpr ⟨A,mem_col.mpr ⟨mem_insert_of_mem am,pa,za,arc⟩⟩⟩

/-- The refund at the same physical column holds for any original prices. -/
theorem cut_attach_price {q n} (X : Model q n) {F : Family} {L T : Finset ℕ} {z}
    (native : F ⊆ family X) (outside : z ∉ L) (cut : T ⊆ inN (graph X.D F) X.V z)
    (p : ℕ → ℝ) :
    realCol q (graph X.D (insert L (avoiding F T))) X.V p z + (q : ℝ) * realMass T p =
      realCol q (graph X.D F) X.V p z := by
  classical
  have mass : realMass (inN (graph X.D F) X.V z \ T) p + realMass T p =
      realMass (inN (graph X.D F) X.V z) p := sum_sdiff cut
  simp only [realCol,realInW_eq_mass_inN,cut_attach_column X native outside cut]
  rw [add_assoc,← mul_add,mass]

#print axioms cut_attach_column
#print axioms cut_attach_price
#print axioms lost_parents
#print axioms separate
#print axioms on_boundary
end LeanCH.BR.Closure.BoundaryReceiverWitness
