import checkpoints.shen_extension.LastArcPriceTransport

namespace LeanCH.BR.Closure.LastArcCompetitor
open Finset BRq2 BRq3 BR45 WeightedSD FiniteCutInverse FirstPacketBarrier MarkedCyclePeeling
open OmittedCycleProgress LastArcGatePayment SharedArcBarrier SharedArcComponentExchange ShortestCycleWeights

/-- Replaying a native missing arc at a minimum original packet always produces
a boundary competitor: every vertex of a new cycle is incident to an edge
different from the new one. If none of those edges came from F, the two cycles
would have the same vertices. -/
theorem packet {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false) :
    let P := added X.D F B
    let e := (u.val,v.val)
    ∃M, Boundary X F M ∧ e∈added X.D F M ∧
      ((added X.D F M=insert e P ∧ ∃z∈B,z∉M ∧ ∀f∈P,f.1≠z ∧ f.2≠z) ∨
       ∃f∈P,added X.D F M=insert e (P.erase f)) := by
  classical
  intro P e
  let G := graph X.D (insert B F)
  let J := insertArc G u v
  have raw (i j) (h : J i j=true) : X.D i j=true := by
    by_cases eq : i=u.val ∧ j=v.val
    · simpa only [eq.1,eq.2] using uv
    · exact CrossValueOmissions.selected_sub (by simpa [J,insertArc,eq] using h)
  have safe := qfree_sub raw X.free
  have strict : ¬SmallRow q J X.V := by
    obtain ⟨w,wn,live,hi⟩ := strict_witness_of_not_smallRow bad
    intro weak
    apply weak.no_strict live w wn
    intro i iv
    apply (hi i iv).trans_le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun i _ j _=>insertArc_mono G u v i j) wn iv) (Nat.cast_nonneg q))
  obtain ⟨M,cm,um,vm⟩ := SharedArcMinimalPacket.cycle_at_arc hq small safe strict u.property v.property
    (show J u v=true by simp [J,insertArc])
  obtain ⟨cd,kept⟩ := SharedArcMinimalPacket.lift_cycle (by omega : 1≤q) X.free (fun h=>raw _ _ h) cm
  have cb := (mem_filter.mp step.1).2
  have oldOff : graph X.D F u v=false := Bool.eq_false_iff.mpr (fun h=>Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inl h))))
  have em : e∈added X.D F M := mem_added.mpr ⟨um,vm,uv,oldOff⟩
  have ep : e∉P := fun h=>Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr h)))
  have different : M≠B := fun same=>ep (by change e∈added X.D F B; rw [←same]; exact em)
  have outside : M∉F := fun mf=>Bool.noConfusion (oldOff.symm.trans (active.mpr ⟨M,mem_col.mpr ⟨mf,um,vm,uv⟩⟩))
  have bnd : Boundary X F M := by
    refine ⟨mem_filter.mpr ⟨mem_powerset.mpr cd.sub,cd⟩,outside,?_⟩
    by_contra no
    have oldEdges {i j} (im : i∈M) (jm : j∈M) (pre : G i j=true) : i∈B ∧ j∈B := by
      rcases union_arc.mp pre with old | new
      · obtain ⟨L,hl⟩ := active.mp old
        obtain ⟨lf,il,jl,ij⟩ := mem_col.mp hl
        exact (no ⟨L,lf,i,mem_inter.mpr ⟨il,im⟩,j,mem_inter.mpr ⟨jl,jm⟩,ij⟩).elim
      · exact ⟨(mem_added.mp new).1,(mem_added.mp new).2.1⟩
    apply different
    apply eq_of_subset_of_card_le _ (by rw [cd.size,cb.size])
    intro z zm
    by_cases isTail : z=u.val
    · obtain ⟨j,hj⟩ := card_pos.mp (show 0<(inN J M z).card by have h : (inN J M z).card=1 := cm.incoming z zm; omega)
      obtain ⟨jm,jz⟩ := mem_inN.mp hj
      have diff : ¬(j=u.val ∧ z=v.val) := by
        rintro ⟨_,zv⟩
        exact loopfree X.free (by omega) v.property ((isTail.symm.trans zv) ▸ uv)
      exact (oldEdges jm zm (by simpa [J,insertArc,diff] using jz)).2
    · obtain ⟨j,hj⟩ := card_pos.mp (show 0<(outN J M z).card by rw [cm.heads z zm]; decide)
      obtain ⟨jm,zj⟩ := mem_outN.mp hj
      exact (oldEdges zm jm (by simpa [J,insertArc,isTail] using zj)).1
  have upper : added X.D F M⊆insert e P := by
    intro f hf
    by_cases eq : f=e
    · exact mem_insert.mpr (Or.inl eq)
    obtain ⟨im,jm,ij,no⟩ := mem_added.mp hf
    have diff : ¬(f.1=u.val ∧ f.2=v.val) := fun h=>eq (Prod.ext h.1 h.2)
    have orig : G f.1 f.2=true := by simpa [J,insertArc,diff] using kept f.1 im f.2 jm ij
    exact mem_insert_of_mem ((union_arc.mp orig).resolve_left (by simp [no]))
  refine ⟨M,bnd,em,?_⟩
  by_cases full : P⊆added X.D F M
  · refine Or.inl ⟨Subset.antisymm upper (insert_subset em full),?_⟩
    obtain ⟨z,zb,om⟩ := not_subset.mp (show ¬B⊆M from
      fun incl=>different (eq_of_subset_of_card_le incl (by rw [cb.size,cd.size])).symm)
    exact ⟨z,zb,om,fun f hf=>⟨fun eq=>om (eq ▸ (mem_added.mp (full hf)).1),
      fun eq=>om (eq ▸ (mem_added.mp (full hf)).2.1)⟩⟩
  · obtain ⟨f,fp,miss⟩ := not_subset.mp full
    refine Or.inr ⟨f,fp,eq_of_subset_of_card_le ?_ ?_⟩
    · intro g gm
      rcases mem_insert.mp (upper gm) with eq | old
      · exact mem_insert.mpr (Or.inl eq)
      · exact mem_insert_of_mem (mem_erase.mpr ⟨fun eq=>miss (eq ▸ gm),old⟩)
    · rw [card_insert_of_notMem (fun h=>ep (mem_of_mem_erase h)),card_erase_add_one fp]
      exact (count cb).trans_le ((least M bnd).trans_eq (count cd).symm)

/-- The numerical exchange test for the competitor found by the graph itself.
The replacement branch has no incidence-connectivity premise. -/
def Alternative {q n} (X : Model q n) (F : Family) (B : Finset ℕ) (ρ : ℕ→ℚ) (d : ℚ)
    (H : Matrix X.V X.V ℝ) (u v : X.V) (c : ℚ) : Prop :=
  let P := added X.D F B
  let e := (u.val,v.val)
  ∃M, Boundary X F M ∧ e∈added X.D F M ∧
    ((added X.D F M=insert e P ∧ ∃z∈B,z∉M ∧ ∀f∈P,f.1≠z ∧ f.2≠z) ∨
    ∃a b : X.V,(a.val,b.val)∈P ∧ added X.D F M=insert e (P.erase (a.val,b.val)) ∧
      let debit := (q:ℝ)*((c:ℝ)-d)*H b u*H v a
      let credit := ((q:ℝ)*H b a-1)*(((d:ℝ)-1)*((c:ℝ)-1)*(∑i,H i u)*(∑j,H v j))
      credit<debit ∧ (SmallRow q (graph X.D (insert M F)) X.V ↔ debit≤credit) ∧
      (debit≤credit → SharedArcPivotGate.ProgressAt X F B H ρ d))

theorem fork {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {x ρ d} {H : Matrix X.V X.V ℝ} (old : Flat q (graph X.D (insert B F)) X.V x ρ d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false) :
    ∃w π c,Flat q (insertArc (graph X.D (insert B F)) u v) X.V w π c ∧
      (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*x v=c-d ∧ 0<c-d ∧ Alternative X F B ρ d H u v c := by
  classical
  obtain ⟨w,π,c,flat,p₁,p₂,gain,test⟩ := isolate X hq small old inv u v uv off
  obtain ⟨M,bm,em,allOld | ⟨f,mark,swap⟩⟩ := packet X hq small step least (stop B step) u v uv off
  · exact ⟨w,π,c,flat,p₁,p₂,gain,M,bm,em,Or.inl allOld⟩
  have cb := (mem_filter.mp step.1).2
  let a : X.V := ⟨f.1,cb.sub (mem_added.mp mark).1⟩
  let b : X.V := ⟨f.2,cb.sub (mem_added.mp mark).2.1⟩
  have ne : f≠(u.val,v.val) := fun eq=>Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr (eq ▸ mark))))
  have same := graph_swap mark ne swap
  let G := graph X.D (insert B F)
  have comm : eraseArc (insertArc G u v) a b=insertArc (eraseArc G a b) u v := by
    funext i j
    by_cases atA : i=a.val ∧ j=b.val
    · have other : ¬(i=u.val ∧ j=v.val) := fun e=>ne (Prod.ext (atA.1.symm.trans e.1) (atA.2.symm.trans e.2))
      simp only [insertArc,eraseArc,ite_eq_left atA,ite_eq_right other]
    · simp only [insertArc,eraseArc,ite_eq_right atA]
  have check := test a b (union_arc.mpr (Or.inr mark))
  change SmallRow q (eraseArc (insertArc G u v) a b) X.V ↔ _ at check
  rw [comm,←same] at check
  refine ⟨w,π,c,flat,p₁,p₂,gain,M,bm,em,Or.inr ⟨a,b,mark,swap,
    lt_of_not_ge (fun fit=>stop M bm (check.mpr fit)),check,?_⟩⟩
  intro paid
  exact Or.inl (Or.inl (Or.inr ⟨M,bm,(SharedArcCompression.winning_iff X small step (stop B step) M).mpr (check.mpr paid)⟩))

theorem final_step {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (A : Stage X) (same : graph X.D A.cycles=graph X.D (insert B F))
    {ρ d H} (ap : A.π=ρ) (av : A.value=d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (wanted : Family) (ws : wanted⊆family X) :
    wanted⊆A.cycles ∨ ∃P C : Stage X,Relation.ReflTransGen (Edge X wanted) A P ∧ Edge X wanted P C ∧
      wanted⊆C.cycles ∧ ∃N∈wanted,∃u v : X.V,u.val∈N ∧ v.val∈N ∧
      (u.val,v.val)∈CrossValueOmissions.lost (graph X.D C.cycles) (graph X.D P.cycles) X.V ∧
      X.D u v=true ∧ graph X.D (insert B F) u v=false ∧
      ∃w π c,Flat q (insertArc (graph X.D (insert B F)) u v) X.V w π c ∧
      (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*A.x v=c-d ∧ 0<c-d ∧ Alternative X F B ρ d H u v c ∧
      let scale := (P.value-1)*(C.value-1)
      let cap := (c-d)/((d-1)*(c-1))
      (q:ℚ)*P.π u*C.x v/scale≤cap ∧ (q:ℚ)*C.π u*P.x v/scale≤cap := by
  rcases LastArcPriceTransport.at_gate X hq small step least stop A same ap av inv wanted ws with done |
    ⟨P,C,path,last,full,N,nw,u,v,um,vm,hit,uv,off,_,bounds⟩
  · exact Or.inl done
  have initial := A.flat
  rw [same,ap,av] at initial
  obtain ⟨w,π,c,flat,p₁,p₂,gain,alt⟩ := fork X hq small step least stop initial inv u v uv off
  exact Or.inr ⟨P,C,path,last,full,N,nw,u,v,um,vm,hit,uv,off,w,π,c,flat,p₁,p₂,gain,alt,bounds w π c flat p₁ p₂⟩

def OnModel {q n} (X : Model q n) : Prop :=
  ∀ (F : Family) (B : Finset ℕ), Boundary X F B →
    (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) →
    (∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) →
    ∀ (x ρ : ℕ→ℚ) (d : ℚ) (H : Matrix X.V X.V ℝ),
    Flat q (graph X.D (insert B F)) X.V x ρ d →
    CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H →
    ∀u v : X.V,X.D u v=true → graph X.D (insert B F) u v=false →
    ∃w π c,Flat q (insertArc (graph X.D (insert B F)) u v) X.V w π c ∧
      (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*x v=c-d ∧ 0<c-d ∧ Alternative X F B ρ d H u v c

theorem on_model {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) : OnModel X :=
  fun _ _ step least stop _ _ _ _ old inv u v uv off=>fork X hq small step least stop old inv u v uv off

#print axioms on_model
#print axioms fork
#print axioms final_step

#print axioms packet
end LeanCH.BR.Closure.LastArcCompetitor
