import checkpoints.shen_extension.SharedArcFlatChain

namespace LeanCH.BR.Closure.SharedArcCover
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcComponentExchange

/-- Pay for all native missing arcs incident with a selected tail or head. -/
def onStars (D E : CH.Digraph) (L R : Finset ℕ) : CH.Digraph :=
  fun i j => if i∈L ∨ j∈R then D i j else E i j

private theorem native {q n} (X : Model q n) (F : Family) (L R : Finset ℕ) {i j}
    (ed : onStars X.D (graph X.D F) L R i j=true) : X.D i j=true := by
  by_cases h : i∈L ∨ j∈R
  · simpa [onStars,h] using ed
  have orig : graph X.D F i j=true := by simpa [onStars,h] using ed
  obtain ⟨A,hit⟩ := active.mp orig
  exact (mem_col.mp hit).2.2.2

private theorem count_cover {D V q M F} (cyc : Cycle D V q M) (L R : Finset ℕ)
    (cover : ∀e∈added D F M,e.1∈L ∨ e.2∈R) : (added D F M).card≤L.card+R.card := by
  classical
  let P := added D F M
  let S := P.filter (fun e => e.1∈L)
  let T := P\S
  have sm {e} (h : e∈S) : e∈P := (mem_filter.mp h).1
  have tm {e} (h : e∈T) : e∈P := (mem_sdiff.mp h).1
  have left : S.card≤L.card := by
    have sub : S.image Prod.fst ⊆ L := by
      intro v mem; obtain ⟨e,h,rfl⟩ := mem_image.mp mem; exact (mem_filter.mp h).2
    have inj : Set.InjOn Prod.fst (S : Set (ℕ×ℕ)) := fun _ he _ hf eq =>
      matching cyc (sm he) (sm hf) (Or.inl eq)
    simpa only [card_image_of_injOn inj] using card_le_card sub
  have right : T.card≤R.card := by
    have sub : T.image Prod.snd ⊆ R := by
      intro v mem
      obtain ⟨e,h,rfl⟩ := mem_image.mp mem
      exact (cover e (tm h)).resolve_left (fun l => (mem_sdiff.mp h).2 (mem_filter.mpr ⟨tm h,l⟩))
    have inj : Set.InjOn Prod.snd (T : Set (ℕ×ℕ)) := fun _ he _ hf eq =>
      matching cyc (tm he) (tm hf) (Or.inr eq)
    simpa only [card_image_of_injOn inj] using card_le_card sub
  have size := card_sdiff_add_card_eq_card (show S⊆P from fun _ h => sm h)
  change T.card+S.card=P.card at size
  change P.card≤_
  omega

/-- If fewer endpoint roles are activated than the minimum boundary
requires, no shortest cycle of the edited graph uses a new arc. -/
theorem no_cycle {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (L R : Finset ℕ) (low : L.card+R.card<(targets X.D X.V F B).card)
    {f : SharedArcComponentExchange.Arc} (fresh : Fresh X F f) {M}
    (cyc : Cycle (onStars X.D (graph X.D F) L R) X.V q M) (fm : f.1∈M) (fn : f.2∈M) : False := by
  classical
  let E := graph X.D F
  let J := onStars X.D E L R
  obtain ⟨_,_,fd,off⟩ := fresh
  have sub {i j} (ed : J i j=true) := native X F L R ed
  obtain ⟨cm,kept⟩ := SharedArcMinimalPacket.lift_cycle (by omega : 1≤q) X.free (fun ed => sub ed) cyc
  have bound := count_cover (F:=F) cm L R (by
    intro e mark
    obtain ⟨a,b,d,no⟩ := mem_added.mp mark
    by_contra out
    have keep := kept e.1 a e.2 b d
    change onStars X.D (graph X.D F) L R e.1 e.2=true at keep
    simp [onStars,out,no] at keep)
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have lim : (targets X.D X.V F B).card≤q+1 := by
    rw [←cb.size]; exact card_le_card (fun _ h => (mem_filter.mp h).2.1)
  have unmarked : ∃v∈M,v∉targets X.D X.V F M := by
    by_contra! incl
    have num := card_le_card incl
    rw [←count cm,cm.size] at num
    omega
  obtain ⟨v,vm,no⟩ := unmarked
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<(inN X.D M v).card by
    have := cm.incoming v vm; change (inN X.D M v).card=1 at this; omega)
  obtain ⟨um,uv⟩ := mem_inN.mp hu
  have old : E u v=true := by
    by_contra miss
    exact no (mem_filter.mpr ⟨cm.sub vm,vm,u,um,uv,Bool.eq_false_iff.mpr miss⟩)
  obtain ⟨A,hit⟩ := active.mp old
  obtain ⟨af,ua,va,arc⟩ := mem_col.mp hit
  have outside : M∉F := fun h => Bool.noConfusion (off.symm.trans (active.mpr ⟨M,mem_col.mpr ⟨h,fm,fn,fd⟩⟩))
  have bm : Boundary X F M := ⟨mem_filter.mpr ⟨mem_powerset.mpr cm.sub,cm⟩,outside,A,af,
    u,mem_inter.mpr ⟨ua,um⟩,v,mem_inter.mpr ⟨va,vm⟩,arc⟩
  have num := least M bm
  rw [←count cm] at num
  omega

/-- The certificate pays every native arc at every selected star at once,
including new arcs outside the minimizing cycle. -/
theorem simultaneous {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (old : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (L R : Finset ℕ) (low : L.card+R.card<(targets X.D X.V F B).card) :
    ∃p,RealDual q (onStars X.D (graph X.D F) L R) X.V 1 p := by
  classical
  let E := graph X.D F
  let J := onStars X.D E L R
  apply realDual_of_smallRow _ X.live
  by_contra bad
  have sub {i j} (ed : J i j=true) := native X F L R ed
  have anyNew : ∃i∈X.V,∃j∈X.V,J i j=true ∧ E i j=false := by
    by_contra! no
    obtain ⟨w,wn,_,hi⟩ := strict_witness_of_not_smallRow bad
    apply old.no_strict X.live w wn
    intro v vv
    apply (hi v vv).trans_le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun i iv j jv edge => by simpa using no i iv j jv edge) wn vv) (Nat.cast_nonneg q))
  obtain ⟨i,iv,j,jv,ed,miss⟩ := anyNew
  obtain ⟨M,cyc,im,jm⟩ := SharedArcMinimalPacket.cycle_at_arc hq small
    (qfree_sub (fun _ _ h => sub h) X.free) bad iv jv ed
  exact no_cycle X hq step least L R low (f:=(i,j)) ⟨iv,jv,sub ed,miss⟩ cyc im jm


theorem no_return {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (L R : Finset ℕ) (low : L.card+R.card<(targets X.D X.V F B).card)
    {i j} (fresh : Fresh X F (i,j)) (chosen : i∈L ∨ j∈R) :
    i∉ball (onStars X.D (graph X.D F) L R) X.V j q := by
  let J := onStars X.D (graph X.D F) L R
  have free := qfree_sub (fun _ _ e => native X F L R e) X.free
  obtain ⟨iv,jv,ij,off⟩ := fresh
  have arc : J i j=true := by simpa [J,onStars,chosen] using ij
  intro ret
  obtain ⟨_,k,le,path⟩ := mem_ball.mp ret
  cases path with
  | refl => exact loopfree free (by omega) iv arc
  | step hv jh tail =>
    obtain ⟨M,cm,im,jm,_⟩ := FiniteHorizonHall.marked_of_port hq free jv
      (mem_outN.mpr ⟨hv,jh⟩) (mem_inN.mpr ⟨iv,arc⟩) (mem_ball.mpr ⟨iv,_,by omega,tail⟩)
    exact no_cycle X hq step least L R low (f:=(i,j)) ⟨iv,jv,ij,off⟩ cm im jm

/-- At a multi-head minimum, any weak primal on the old graph is zero
at every fresh native tail, even outside all chosen incidence components. -/
theorem all_tails_zero {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card)
    {w : ℕ→ℚ} (wn : ∀v∈X.V,0≤w v) (rows : ∀v∈X.V,mass X.V w≤WeightedSD.row q (graph X.D F) X.V w v)
    {i j} (fresh : Fresh X F (i,j)) : w i=0 := by
  let J := onStars X.D (graph X.D F) ∅ {j}
  have sub : ∀u∈X.V,∀v∈X.V,graph X.D F u v=true → J u v=true := by
    intro u _ v _ ed
    by_cases e : v=j
    · obtain ⟨A,hit⟩ := active.mp ed
      simpa [J,onStars,e] using (mem_col.mp hit).2.2.2
    · simpa [J,onStars,e] using ed
  apply le_antisymm _ (wn i fresh.1)
  by_contra! pos
  apply no_return X hq step least ∅ {j} (by simpa using multi) fresh (by simp)
  apply feasible_reach_positive_within hq (qfree_sub (fun _ _ e => native X F ∅ {j} e) X.free)
    small w wn _ fresh.2.1 fresh.1 pos
  intro v vv
  exact (rows v vv).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (outW_mono_graph sub wn vv) (Nat.cast_nonneg q)))

#print axioms all_tails_zero
#print axioms simultaneous
end LeanCH.BR.Closure.SharedArcCover
