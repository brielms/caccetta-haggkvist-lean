import checkpoints.shen_extension.SharedArcPacketPrices
import LeanCH.BR.BRWeightedFoldBoundary
import LeanCH.BR.BRWeightedOutUniformSaturation

namespace LeanCH.BR.Closure.SharedArcPacketReturns
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcMinimalPacket

private theorem cycle_of_return {D V q i j} (hq : 2≤q) (free : QFree D V q)
    (iv : i∈V) (jv : j∈V) (ij : D i j=true) (ret : i∈ball D V j q) :
    ∃M,Cycle D V q M ∧ i∈M ∧ j∈M := by
  obtain ⟨_,k,le,path⟩ := mem_ball.mp ret
  cases path with
  | refl => exact (loopfree free (by omega) iv ij).elim
  | step hv jh tail =>
    obtain ⟨M,cm,im,jm,_⟩ := FiniteHorizonHall.marked_of_port hq free jv (mem_outN.mpr ⟨hv,jh⟩)
      (mem_inN.mpr ⟨iv,ij⟩) (mem_ball.mpr ⟨iv,_,by omega,tail⟩)
    exact ⟨M,cm,im,jm⟩

/-- Removing one changed arc breaks every return of length at most q to
every other changed arc in the same minimum attachment. -/
theorem no_return {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    {a b i j : ℕ} (ab : a∈B) (bb : b∈B) (ed : X.D a b=true) (missing : graph X.D F a b=false)
    (ib : i∈B) (jb : j∈B) (ij : X.D i j=true) (no : graph X.D F i j=false) (ne : j≠b) :
    i∉ball (eraseArc (graph X.D (insert B F)) a b) X.V j q := by
  classical
  let G := graph X.D (insert B F)
  let T := targets X.D X.V F B
  let J := T.erase b
  let K := edit X.D F B J
  let D := eraseArc G a b
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have bt : b∈T := mem_filter.mpr ⟨cb.sub bb,bb,a,ab,ed,missing⟩
  have jt : j∈J := mem_erase.mpr ⟨ne,mem_filter.mpr ⟨cb.sub jb,jb,i,ib,ij,no⟩⟩
  have dg {u v} (e : D u v=true) := eraseArc_sub G a b u v e
  have dk {u v} (e : D u v=true) : K u v=true := by
    by_cases vj : v∈J
    · simpa [K,edit,vj] using dg e
    have orig := dg e
    obtain ⟨M,mk⟩ := active.mp orig
    obtain ⟨mf,um,vm,raw⟩ := mem_col.mp mk
    have old : graph X.D F u v=true := by
      rcases mem_insert.mp mf with eq|inF
      · subst M
        by_contra off
        have vt : v∈T := mem_filter.mpr ⟨cb.sub vm,vm,u,um,raw,Bool.eq_false_iff.mpr off⟩
        have ve : v=b := by by_contra neq; exact vj (mem_erase.mpr ⟨neq,vt⟩)
        subst v
        have one : (inN X.D B b).card≤1 := (cb.incoming b bb).le
        have ue : u=a := card_le_one.mp one _ (mem_inN.mpr ⟨um,raw⟩) _ (mem_inN.mpr ⟨ab,ed⟩)
        simp [D,eraseArc,ue] at e
      · exact active.mpr ⟨M,mem_col.mpr ⟨inF,um,vm,raw⟩⟩
    simpa [K,edit,vj] using old
  have kg (u v) (e : K u v=true) : G u v=true := by
    by_cases vj : v∈J
    · simpa [K,edit,vj] using e
    have old : graph X.D F u v=true := by simpa [K,edit,vj] using e
    obtain ⟨M,mk⟩ := active.mp old
    obtain ⟨mf,um,vm,raw⟩ := mem_col.mp mk
    exact active.mpr ⟨M,mem_col.mpr ⟨mem_insert_of_mem mf,um,vm,raw⟩⟩
  have free := qfree_sub kg (PrivateArcEndpoints.graph_free X (insert B F))
  have lift {u v l} (path : Walk D X.V u v l) : Walk K X.V u v l := by
    induction path with
    | refl => exact .refl _
    | step hv uv _ ih => exact .step hv (dk uv) ih
  intro ret
  obtain ⟨_,k,le,path⟩ := mem_ball.mp ret
  have edge : K i j=true := by
    simpa [K,edit,jt] using (active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ib,jb,ij⟩⟩ : G i j=true)
  obtain ⟨M,cm,im,jm⟩ := cycle_of_return hq free (cb.sub ib) (cb.sub jb) edge (mem_ball.mpr ⟨cb.sub ib,k,le,lift path⟩)
  exact no_cycle_edit X hq step least (erase_ssubset bt) ij no cm im jm

/-- A surviving weak primal on the deletion has zero weight at the tail
of every other changed arc. This also rules out the exact inverse threshold. -/
theorem zero_and_strict {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a)
    (a b : X.V) (ab : (a:ℕ)∈B) (bb : (b:ℕ)∈B) (ed : X.D a b=true) (missing : graph X.D F a b=false)
    {i j : ℕ} (ib : i∈B) (jb : j∈B) (ij : X.D i j=true) (no : graph X.D F i j=false) (ne : j≠(b:ℕ)) :
    (∀w : ℕ→ℚ,(∀v∈X.V,0≤w v) →
      (∀v∈X.V,mass X.V w≤WeightedSD.row q (eraseArc (graph X.D (insert B F)) a b) X.V w v) → w i=0) ∧
      1<(q:ℝ)*H b a := by
  classical
  let G := graph X.D (insert B F)
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have free := qfree_sub (eraseArc_sub G a b) (PrivateArcEndpoints.graph_free X (insert B F))
  have zero (w : ℕ→ℚ) (wn : ∀v∈X.V,0≤w v) (rows : ∀v∈X.V,mass X.V w≤WeightedSD.row q (eraseArc G a b) X.V w v) :
      w i=0 := by
    apply le_antisymm _ (wn i (cb.sub ib))
    by_contra! pos
    exact no_return X hq step least ab bb ed missing ib jb ij no ne
      (feasible_reach_positive_within hq free small w wn rows (cb.sub jb) (cb.sub ib) pos)
  refine ⟨zero,lt_of_le_of_ne (charge a b ab bb ed missing) (fun eq => ?_)⟩
  have edge : G a b=true := active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ab,bb,ed⟩⟩
  obtain ⟨w,_,wp,wm,wr,_⟩ := exact_arc_threshold_two_laws hq inv a b edge eq.symm
  exact (wp i (cb.sub ib)).ne' (zero w (fun v vv => (wp v vv).le) (fun v vv => by rw [wm,wr v vv]))

/-- If one charge is exactly one, its arc is the entire difference from
the old spanning graph. The old graph itself then has both positive unit
laws, bounded diameter, and no proper one-sided module. -/
theorem exact_parent {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a)
    (a b : X.V) (ab : (a:ℕ)∈B) (bb : (b:ℕ)∈B) (ed : X.D a b=true) (off : graph X.D F a b=false)
    (threshold : (q:ℝ)*H b a=1) :
    let E := graph X.D F
    targets X.D X.V F B={b.val} ∧ eraseArc (graph X.D (insert B F)) a b=E ∧
    (∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,WeightedSD.row q E X.V w i=1) ∧ (∀i∈X.V,WeightedSD.col q E X.V p i=1)) ∧
    (∀u∈X.V,∀v∈X.V,v∈ball E X.V u q) ∧ ¬BRsub.Sat q E X.V ∧
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.OutUniform E X.V U) ∧
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.InUniform E X.V U) := by
  classical
  intro E
  let G := graph X.D (insert B F)
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have edge : G a b=true := active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ab,bb,ed⟩⟩
  have only : targets X.D X.V F B={b.val} := by
    apply Subset.antisymm _ (singleton_subset_iff.mpr (mem_filter.mpr ⟨b.property,bb,a,ab,ed,off⟩))
    intro j hit
    obtain ⟨_,jb,i,ib,ij,no⟩ := mem_filter.mp hit
    by_contra out
    have ne : j≠(b:ℕ) := fun eq => out (mem_singleton.mpr eq)
    exact threshold.not_gt (zero_and_strict X hq small step least inv charge a b ab bb ed off ib jb ij no ne).2
  have eq : eraseArc G a b=E := by
    funext u v
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro keep
      obtain ⟨M,mk⟩ := active.mp (eraseArc_sub G a b u v keep)
      obtain ⟨mf,um,vm,raw⟩ := mem_col.mp mk
      rcases mem_insert.mp mf with eq|af
      · subst M
        by_contra no
        have hit : v∈targets X.D X.V F B := mem_filter.mpr ⟨cb.sub vm,vm,u,um,raw,Bool.eq_false_iff.mpr no⟩
        have vb : v=(b:ℕ) := mem_singleton.mp (only ▸ hit)
        have one : (inN X.D B b).card≤1 := (cb.incoming b bb).le
        have ua : u=(a:ℕ) := card_le_one.mp one _ (mem_inN.mpr ⟨um,vb ▸ raw⟩) _ (mem_inN.mpr ⟨ab,ed⟩)
        simp [eraseArc,ua,vb] at keep
      · exact active.mpr ⟨M,mem_col.mpr ⟨af,um,vm,raw⟩⟩
    · intro keep
      have ne : ¬(u=(a:ℕ) ∧ v=(b:ℕ)) := by rintro ⟨rfl,rfl⟩; exact Bool.noConfusion (off.symm.trans keep)
      obtain ⟨M,mk⟩ := active.mp keep
      obtain ⟨mf,um,vm,raw⟩ := mem_col.mp mk
      simpa [eraseArc,ne] using (active.mpr ⟨M,mem_col.mpr ⟨mem_insert_of_mem mf,um,vm,raw⟩⟩ : G u v=true)
  have gf := PrivateArcEndpoints.graph_free X (insert B F)
  have ef := PrivateArcEndpoints.graph_free X F
  obtain ⟨w,p,wp,wm,wr,_,pp,pm,pc,_⟩ := exact_arc_threshold_two_laws hq inv a b edge threshold
  change ∀i∈X.V,WeightedSD.row q (eraseArc G a b) X.V w i=1 at wr
  change ∀i∈X.V,WeightedSD.col q (eraseArc G a b) X.V p i=1 at pc
  rw [eq] at wr pc
  have prime := exact_threshold_deletion_two_sided_prime hq small gf inv a b edge threshold
  have unsat := erase_actual_arc_not_sat (by omega : 1≤q) gf a b edge
  refine ⟨only,eq,⟨w,p,fun i hi => ⟨wp i hi,pp i hi⟩,wm,pm,wr,pc⟩,
    positive_feasible_diameter hq ef small w wp (fun i hi => by rw [wm,wr i hi]),?_,?_⟩
  · exact eq ▸ unsat
  · exact eq ▸ prime

/-- The local goal on the selected source. Exact charges call for saturation
of the old graph. Strict charges call for one affordable alternative cycle. -/
def ExitAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ) (H : Matrix X.V X.V ℝ) : Prop :=
  ((∃a b : X.V,(a:ℕ)∈B ∧ (b:ℕ)∈B ∧ X.D a b=true ∧ graph X.D F a b=false ∧ (q:ℝ)*H b a=1) ∧
    BRsub.Sat q (graph X.D F) X.V) ∨
  ((∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1<(q:ℝ)*H b a) ∧
    ∃M,Boundary X F M ∧ ∃t : ℕ→ℝ,(∀v∈X.V,0≤t v) ∧ (∃v∈X.V,0<t v) ∧
      (∀v∈X.V,v∉targets X.D X.V F B → t v=0) ∧ SharedArcPacketPrices.compareTails (q:=q) X.D F B M H t)

theorem blocks_exit {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) : ¬ExitAt X F B H := by
  rintro (⟨⟨a,b,ab,bb,ed,off,eq⟩,sat⟩|⟨_,M,comp,t,tn,live,supp,fit⟩)
  · obtain ⟨_,_,_,_,unsat,_⟩ := exact_parent X hq small step least inv charge a b ab bb ed off eq
    exact unsat sat
  · exact SharedArcPacketPrices.barrier X step inv charge stop t tn live supp comp fit

#print axioms blocks_exit

/-- The equality branch concerns a spanning family built through shared arcs.
The desired conclusion says its positive unit laws force saturation. -/
def FlatLaw {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → Boundary X F B →
    (targets X.D X.V F B).card=1 →
    (∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧ (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)) →
    (∀u∈X.V,∀v∈X.V,v∈ball (graph X.D F) X.V u q) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.OutUniform (graph X.D F) X.V U) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.InUniform (graph X.D F) X.V U) → BRsub.Sat q (graph X.D F) X.V

/-- Away from equality, the second sufficient law seeks one competing cycle
and one nonnegative profile passing its explicit tail comparisons. -/
def StrictLaw {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → SmallRow q (graph X.D F) X.V →
    Boundary X F B → (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) →
    ∀H : Matrix X.V X.V ℝ,FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H →
    (∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1<(q:ℝ)*H b a) →
    ∃M,Boundary X F M ∧ ∃t : ℕ→ℝ,(∀v∈X.V,0≤t v) ∧ (∃v∈X.V,0<t v) ∧
      (∀v∈X.V,v∉targets X.D X.V F B → t v=0) ∧ SharedArcPacketPrices.compareTails (q:=q) X.D F B M H t

theorem obstructs_laws {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) :
    ¬(FlatLaw X ∧ StrictLaw X) := by
  classical
  rintro ⟨flat,strict⟩
  obtain ⟨u,uv⟩ := X.live
  obtain ⟨C,_,cc,_,_,_,_⟩ := ShortestReturnCertificate.on_model X hq uv
  have cf : C∈family X := mem_filter.mpr ⟨mem_powerset.mpr cc.sub,cc⟩
  obtain ⟨F,built,sub,_,spans,old,_,next,stop⟩ := SharedArcBarrier.on_source X hq small cf
  obtain ⟨B,step,least⟩ := SharedArcMinimalPacket.select X next
  obtain ⟨H,inv,charge⟩ := charges X hq small old step least (stop B step).1
  by_cases allHigh : ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1<(q:ℝ)*H b a
  · obtain ⟨M,comp,t,tn,live,supp,fit⟩ := strict C F B built sub spans old step least H inv allHigh
    exact SharedArcPacketPrices.barrier X step inv charge (fun M h => (stop M h).1) t tn live supp comp fit
  · push Not at allHigh
    obtain ⟨a,b,ab,bb,ed,off,low⟩ := allHigh
    obtain ⟨single,_,pair,diam,unsat,op,ip⟩ := exact_parent X hq small step least inv charge a b ab bb ed off
      (le_antisymm low (charge a b ab bb ed off))
    exact unsat (flat C F B built sub spans step (by rw [single,card_singleton]) pair diam op ip)

/-- These two all-orders laws would settle literal CH. -/
theorem ch_of_packet_laws (laws : ∀q n,∀X : Model q n,2≤q → SmallerSmallRow q X.V.card → FlatLaw X ∧ StrictLaw X) :
    CH.CaccettaHaggkvistConjecture :=
  SharedArcInduction.ch_of_extension (fun q n X hq small => False.elim (obstructs_laws X hq small (laws q n X hq small)))

#print axioms obstructs_laws
#print axioms ch_of_packet_laws

#print axioms exact_parent

#print axioms no_return
#print axioms zero_and_strict
end LeanCH.BR.Closure.SharedArcPacketReturns
