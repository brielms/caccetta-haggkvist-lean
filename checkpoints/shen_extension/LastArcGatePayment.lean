import checkpoints.shen_extension.RestorationAtGate
import checkpoints.shen_extension.SharedArcPivotGate
import checkpoints.shen_extension.SharedArcExchangeReturn
import checkpoints.shen_extension.MenuEscapeGrowth
import LeanCH.BR.BRWeightedInverseTransport

namespace LeanCH.BR.Closure.LastArcGatePayment
open Finset BRq2 BRq3 BR45 WeightedSD FiniteCutInverse FirstPacketBarrier MarkedCyclePeeling
open OmittedCycleProgress SharedArcBarrier SharedArcComponentExchange ShortestCycleWeights
open scoped Matrix

/-- On the original labels, an isolated native insertion is legal. -/
private theorem legal {q n} (X : Model q n) (F : Family) (u v : X.V) (uv : X.D u v=true) :
    QFree (insertArc (graph X.D F) u v) X.V q := by
  apply qfree_sub (E:=X.D) _ X.free
  intro i j hit
  by_cases h : i=u.val ∧ j=v.val
  · simpa only [h.1,h.2] using uv
  · exact CrossValueOmissions.selected_sub (by simpa [insertArc,h] using hit)

/-- The two mixed prices for a single restored arc equal its isolated value gain. -/
private theorem prices {q : ℕ} {V : Finset ℕ} {G : CH.Digraph} {x ρ w π : ℕ→ℚ} {d c : ℚ} (u v : V) (off : G u v=false)
    (old : Flat q G V x ρ d) (newer : Flat q (insertArc G u v) V w π c) :
    (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*x v=c-d := by
  classical
  have lost : CrossValueOmissions.lost (insertArc G u v) G V={(u.val,v.val)} := by
    ext e
    rcases e with ⟨i,j⟩
    by_cases h : i=u.val ∧ j=v.val
    · rcases h with ⟨rfl,rfl⟩
      simp [CrossValueOmissions.lost,insertArc,off,u.property,v.property]
    · simp [CrossValueOmissions.lost,insertArc,h,Prod.ext_iff]
  obtain ⟨_,_,_,xm,rm,xr,rc⟩ := old
  obtain ⟨_,_,_,wm,pm,wr,pc⟩ := newer
  have h := CrossValueOmissions.exact_gap (fun i _ j _=>insertArc_mono G u v i j) wm pm xm rm wr pc xr rc
  simpa [lost,CrossValueOmissions.cost] using h

/-- The original inverse allocates the total price drop among the labelled rows
and columns. Keeping a particular packet repair paid is an exact entrywise test. -/
theorem isolate {q n F} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {x ρ d} {H : Matrix X.V X.V ℝ} (old : Flat q (graph X.D F) X.V x ρ d)
    (inv : CommonInverse (realMatrix q (graph X.D F) X.V) H)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D F u v=false) :
    let G := graph X.D F
    let J := insertArc G u v
    ∃w π c, Flat q J X.V w π c ∧
      (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*x v=c-d ∧ 0<c-d ∧
      ∀a b : X.V,G a b=true →
        (SmallRow q (eraseArc J a b) X.V ↔
          (q:ℝ)*((c:ℝ)-d)*H b u*H v a ≤
          ((q:ℝ)*H b a-1)*(((d:ℝ)-1)*((c:ℝ)-1)*(∑i,H i u)*(∑j,H v j))) := by
  classical
  intro G J
  have initial := old
  obtain ⟨dh,xp,rp,xm,rm,xr,rc⟩ := old
  have strong : StrictPositiveRows q G X.V := ⟨x,xp,xm,fun i hi=>(xr i hi) ▸ dh⟩
  have safe := legal X F u v uv
  obtain ⟨z,zp,zm,zh⟩ := strong.mono_graph (fun i _ j _=>insertArc_mono G u v i j)
  obtain ⟨w,π,c,ch,wp,pp,wm,pm,wr,pc⟩ := strict_pair_of_proper_smallRow (small.induced safe) X.live z
    (fun i hi=>(zp i hi).le) (fun i hi=>zm ▸ zh i hi)
  have newflat : Flat q J X.V w π c := ⟨ch,wp,pp,wm,pm,wr,pc⟩
  obtain ⟨p₁,p₂⟩ := prices u v off initial newflat
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have gain : 0<c-d := p₁ ▸ mul_pos (mul_pos qp (rp _ u.property)) (wp _ v.property)
  obtain ⟨K,invK⟩ := common_inverse_of_smaller_strict small safe ⟨w,wp,wm,fun i hi=>(wr i hi) ▸ ch⟩
  have denrow := single_increment_row inv invK u v (q:ℝ) (realMatrix_insert_difference u v (by simp [off]))
  have summed : (1+(q:ℝ)*H v u)*(∑j,K v j)=∑j,H v j := by
    rw [Finset.mul_sum]; exact sum_congr rfl (fun j _=>denrow j)
  have cm := (graph_inverse_transport inv x ρ xp xm rm d dh xr rc).2.1 u
  change ((d:ℝ)-1)*(∑i,H i u)=(ρ u:ℝ) at cm
  have wm' := inverse_row_sum_of_equalizer invK w wm c wr v
  have pg : (q:ℝ)*(ρ u:ℝ)*(w v:ℝ)=(c:ℝ)-d := by exact_mod_cast p₁
  have budget : ((c:ℝ)-d)*(1+(q:ℝ)*H v u)=
      (q:ℝ)*(((d:ℝ)-1)*((c:ℝ)-1)*(∑i,H i u)*(∑j,H v j)) := by
    rw [←pg,←cm,wm',←summed]
    ring
  refine ⟨w,π,c,newflat,p₁,p₂,gain,?_⟩
  intro a b ab
  rw [PacketCompression.one_exchange small strong inv a b u v ab (by simp [G,off]) safe]
  have qR : (0:ℝ)<q := by exact_mod_cast qp
  have gR : (0:ℝ)<(c:ℝ)-d := by exact_mod_cast gain
  have eq := congrArg (fun t : ℝ => ((q:ℝ)*H b a-1)*t) budget
  constructor
  · intro h
    apply (mul_le_mul_iff_left₀ qR).mp
    nlinarith only [mul_le_mul_of_nonneg_left h gR.le,eq]
  · intro h
    apply (mul_le_mul_iff_left₀ gR).mp
    nlinarith only [mul_le_mul_of_nonneg_left h qR.le,eq]

private theorem included {D : CH.Digraph} {F E : Family} (sub : F⊆E) {i j} :
    graph D F i j=true → graph D E i j=true := by
  rintro hit
  obtain ⟨M,m⟩ := active.mp hit
  exact active.mpr ⟨M,mem_col.mpr ⟨sub (mem_col.mp m).1,(mem_col.mp m).2⟩⟩

/-- A last step anywhere along the recursion restores an arc already missing
at the starting attachment. All original labels survive the pullback. -/
theorem last_arc {q n} {X : Model q n} {wanted A P B}
    (path : Relation.ReflTransGen (Edge X wanted) A P) (last : Edge X wanted P B) :
    ∃M∈wanted,∃u∈M,∃v∈M, (u,v)∈CrossValueOmissions.lost (graph X.D B.cycles) (graph X.D P.cycles) X.V ∧
      X.D u v=true ∧ graph X.D A.cycles u v=false := by
  have le : A.cycles⊆P.cycles := by
    clear last
    induction path with
    | refl => exact Subset.rfl
    | tail _ e ih =>
      obtain ⟨M,_,_,sub,_⟩ := e
      exact ih.trans (fun _ h=>sub (mem_insert_of_mem h))
  obtain ⟨M,mw,_,_,_,⟨u,um,v,vm,hit⟩,_⟩ := last
  have ed := (mem_filter.mp hit).2
  exact ⟨M,mw,u,um,v,vm,hit,CrossValueOmissions.selected_sub ed.1,
    Bool.eq_false_iff.mpr (fun g=>Bool.noConfusion (ed.2.symm.trans (included le g)))⟩

/-- Menu from the trace, now anchored at the new head v. Every chosen target
can return via the very same arc u→v. A failed growth count labels a short row. -/
theorem menu_at_arc {q n F} (X : Model q n) (u v : X.V) (uv : X.D u v=true)
    {S T : Finset ℕ} (ss : S⊆X.V) (ts : T⊆X.V) (size : S.card≤q)
    (head : v.val∈S) (outside : v.val∉T) {r t k : ℕ} (room : r+1+(t+1)≤q)
    (returns : ∀j∈T,u.val∈ball (insertArc (graph X.D F) u v) X.V j t)
    (exceeds : S.card < 1+(outN (insertArc (graph X.D F) u v) (S∪T) v).card+r*k) :
    ∃z∈S,(outN (insertArc (graph X.D F) u v) (S∪T) z).card<k := by
  by_contra! allRows
  have count := SATBoundaryPilot.short_returns_force_growth (r:=r) (t:=t+1)
    (legal X F u v uv) ss ts size head outside room allRows
    (fun j hj=>ball_step (returns j hj) v.property (by simp [insertArc]))
  exact exceeds.not_ge (count.trans (card_le_card inter_subset_left))

/-- Progress at the original pivot for an exchangeable original packet arc.
At a surviving pivot its strict reverse inequality is certified on the same labels. -/
def Bill {q n} (X : Model q n) (F : Family) (B : Finset ℕ) (x ρ : ℕ→ℚ) (d : ℚ)
    (H : Matrix X.V X.V ℝ) (u v : X.V) : Prop :=
    let J := insertArc (graph X.D (insert B F)) u v
    ∃w π c,Flat q J X.V w π c ∧ (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*x v=c-d ∧ 0<c-d ∧
      ∀a b : X.V,(a.val,b.val)∈added X.D F B →
      Relation.ReflTransGen (neighbor X F) (a.val,b.val) (u.val,v.val) →
      ∃M, Boundary X F M ∧
      let debit := (q:ℝ)*((c:ℝ)-d)*H b u*H v a
      let credit := ((q:ℝ)*H b a-1)*(((d:ℝ)-1)*((c:ℝ)-1)*(∑i,H i u)*(∑j,H v j))
      (credit<debit) ∧ (SmallRow q (graph X.D (insert M F)) X.V ↔ debit≤credit) ∧
      (debit≤credit → SharedArcPivotGate.ProgressAt X F B H ρ d)

theorem at_attachment {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {x ρ d} {H : Matrix X.V X.V ℝ} (old : Flat q (graph X.D (insert B F)) X.V x ρ d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false) :
    Bill X F B x ρ d H u v := by
  unfold Bill
  intro J
  obtain ⟨w,π,c,flat,p₁,p₂,gain,test⟩ := isolate X hq small old inv u v uv off
  refine ⟨w,π,c,flat,p₁,p₂,gain,?_⟩
  intro a b mark way
  have present := union_arc.mpr (Or.inr mark)
  have ne : (a.val,b.val)≠(u.val,v.val) := by
    rintro h
    have e₁ := congrArg Prod.fst h
    have e₂ := congrArg Prod.snd h
    change a.val=u.val at e₁
    change b.val=v.val at e₂
    exact Bool.noConfusion (off.symm.trans (e₁ ▸ e₂ ▸ present))
  obtain ⟨_,M,bm,swap⟩ := transport X hq small step least stop mark way
  have same := graph_swap mark ne swap
  have comm : eraseArc J a b=insertArc (eraseArc (graph X.D (insert B F)) a b) u v := by
    funext i j
    by_cases atA : i=a.val ∧ j=b.val
    · have other : ¬(i=u.val ∧ j=v.val) := fun e=>ne (Prod.ext (atA.1.symm.trans e.1) (atA.2.symm.trans e.2))
      simp only [J,insertArc,eraseArc,ite_eq_left atA,ite_eq_right other]
    · simp only [J,insertArc,eraseArc,ite_eq_right atA]
  have check := test a b present
  change SmallRow q (eraseArc J a b) X.V ↔ _ at check
  rw [comm,←same] at check
  refine ⟨M,bm,lt_of_not_ge (fun h=>stop M bm (check.mpr h)),check,?_⟩
  intro paid
  exact Or.inl (Or.inl (Or.inr ⟨M,bm,(SharedArcCompression.winning_iff X small step (stop B step) M).mpr (check.mpr paid)⟩))

/-- Either coverage holds already, or a genuine final step exists with a
labelled new arc. This distinguishes a zero-length restoration from a last edit. -/
theorem last_or_done {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (wanted : Family) (sub : wanted⊆family X) (A : Stage X) :
    wanted⊆A.cycles ∨ ∃P B : Stage X,Relation.ReflTransGen (Edge X wanted) A P ∧ Edge X wanted P B ∧
      wanted⊆B.cycles ∧ ∃M∈wanted,∃u∈M,∃v∈M,
      (u,v)∈CrossValueOmissions.lost (graph X.D B.cycles) (graph X.D P.cycles) X.V ∧
      X.D u v=true ∧ graph X.D A.cycles u v=false := by
  obtain ⟨B,path,full⟩ := saturate X hq small wanted sub A
  cases path with
  | refl => exact Or.inl full
  | tail before last => exact Or.inr ⟨_,_,before,last,full,last_arc before last⟩

/-- Apply the isolated exchange to an actual arc of the final step, with
both initial prices, value and inverse fixed at the original attachment. -/
theorem rooted {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (A : Stage X) (same : graph X.D A.cycles=graph X.D (insert B F))
    {ρ d H} (ap : A.π=ρ) (av : A.value=d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (wanted : Family) (ws : wanted⊆family X) :
    wanted⊆A.cycles ∨ ∃P C : Stage X,Relation.ReflTransGen (Edge X wanted) A P ∧ Edge X wanted P C ∧
      wanted⊆C.cycles ∧ ∃M∈wanted,∃u v : X.V,u.val∈M ∧ v.val∈M ∧
      (u.val,v.val)∈CrossValueOmissions.lost (graph X.D C.cycles) (graph X.D P.cycles) X.V ∧
      X.D u v=true ∧ graph X.D (insert B F) u v=false ∧ Bill X F B A.x ρ d H u v := by
  rcases last_or_done X hq small wanted ws A with done | ⟨P,C,path,last,full,M,mw,i,im,j,jm,hit,ij,off⟩
  · exact Or.inl done
  have labels := mem_product.mp (mem_filter.mp hit).1
  have old := A.flat
  rw [same,ap,av] at old
  rw [same] at off
  exact Or.inr ⟨P,C,path,last,full,M,mw,⟨i,labels.1⟩,⟨j,labels.2⟩,im,jm,hit,ij,off,
    at_attachment X hq small step least stop old inv _ _ ij off⟩

/-- The root catalog retains this rule on the same least source as restoration. -/
def OnModel {q n} (X : Model q n) : Prop :=
  ∀ (F : Family) (B : Finset ℕ), Boundary X F B →
    (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) →
    (∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) →
    ∀ (x ρ : ℕ→ℚ) (d : ℚ) (H : Matrix X.V X.V ℝ),
    Flat q (graph X.D (insert B F)) X.V x ρ d →
    CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H →
    ∀u v : X.V,X.D u v=true → graph X.D (insert B F) u v=false → Bill X F B x ρ d H u v

theorem on_model {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) :
    OnModel X := fun _ _ step least stop _ _ _ _ old inv u v uv off =>
      at_attachment X hq small step least stop old inv u v uv off

#print axioms on_model
#print axioms rooted
#print axioms at_attachment
#print axioms last_or_done

#print axioms isolate
#print axioms last_arc
#print axioms menu_at_arc
end LeanCH.BR.Closure.LastArcGatePayment
