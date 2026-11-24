import checkpoints.shen_extension.RankedUnitDescent
import checkpoints.shen_extension.CommonExitReplacement

namespace LeanCH.BR.RemoteHeadRectangle
open Finset BRq2 BRq3 BR45 Closure

def install (D : CH.Digraph) (W H : Finset ℕ) : CH.Digraph := fun i j=>
  D i j || decide (i∈W ∧ j∈H)

private theorem first_insert {D V W H i j k} (p : Walk (install D W H) V i j k) :
    Walk D V i j k ∨ ∃x∈W,∃y∈H,∃l m,l+1+m=k ∧ Walk D V i x l ∧ Walk (install D W H) V y j m := by
  induction p with
  | refl => exact Or.inl (.refl _)
  | @step a b c n bv ab _ ih =>
    by_cases old : D a b=true
    · rcases ih with clean|⟨x,xw,y,yh,l,m,eq,pre,post⟩
      · exact Or.inl (.step bv old clean)
      · exact Or.inr ⟨x,xw,y,yh,l+1,m,by omega,.step bv old pre,post⟩
    · have cross : a∈W ∧ b∈H := by simpa [install,Bool.eq_false_iff.mpr old] using ab
      exact Or.inr ⟨a,cross.1,b,cross.2,0,n,by omega,.refl _,by assumption⟩

/-- After the whole rectangle is added, a walk of length at most the cutoff
    cannot use two new arcs: the intervening native prefix is too short. -/
theorem install_free {D V W H q} (free : QFree D V q) (ws : W⊆V)
    (remote : ∀h∈H,Disjoint (ball D V h (q-1)) W) : QFree (install D W H) V q := by
  have impossible {h w l} (hh : h∈H) (ww : w∈W) (len : l<q) (p : Walk D V h w l) : False :=
    disjoint_left.mp (remote h hh) (mem_ball.mpr ⟨ws ww,l,by omega,p⟩) ww
  intro i k positive bound p
  rcases first_insert p with clean|⟨x,xw,y,yh,l,m,eq,pre,post⟩
  · exact free i k positive bound clean
  · rcases first_insert post with clean|⟨x',xw',_,_,j,_,eq',segment,_⟩
    · exact impossible yh xw (show m+l<q by omega) (clean.append pre)
    · exact impossible yh xw' (show j<q by omega) segment

/-- A full native tight parent or a smaller actual host at the same degree.
    Only the reach between the labelled sets is assumed. -/
@[aesop safe forward (immediate := [free,hq,degree,ws,hs,remote,width]) (rule_sets := [CHGraphFamilies])]
theorem cover_or_descend {D V W H q r} (free : QFree D V q) (hq : 1≤q)
    (degree : ∀i∈V,r≤(outN D V i).card) (ws : W⊆V) (hs : H⊆V)
    (remote : ∀h∈H,Disjoint (ball D V h (q-1)) W) (width : q*(r-H.card)+2≤W.card) :
    (∃i∈V\W,(outN D V i).card=r ∧ W⊆outN D V i) ∨
    ∃ E U,U.Nonempty ∧ U.card+1=V.card ∧ QFree E U q ∧ ∀i∈U,r≤(outN E U i).card := by
  classical
  by_cases parent : ∃i∈V\W,(outN D V i).card=r ∧ W⊆outN D V i
  · exact Or.inl parent
  right
  let G := install D W H
  let U := V\W
  let k := W.card-1
  have hu : H⊆U := fun h hh=>mem_sdiff.mpr ⟨hs hh,disjoint_left.mp (remote h hh) (self_mem_ball (hs hh))⟩
  have old {i} (iu : i∈U) (S : Finset ℕ) : outN G S i=outN D S i := by
    ext j; simp [mem_outN,G,install,(mem_sdiff.mp iu).2]
  have funded (i) (iu : i∈U) : r≤(outN G U i).card+(if (outN G W i).Nonempty then k else 0) := by
    rw [old iu,old iu]
    have eq : outN D U i=outN D V i\outN D W i := by ext j; simp only [U,mem_sdiff,mem_outN]; tauto
    have incl : outN D W i⊆outN D V i := fun j jm=>mem_outN.mpr ⟨ws (outN_subset jm),(mem_outN.mp jm).2⟩
    have count := card_sdiff_add_card_eq_card incl
    rw [←eq] at count
    have deg := degree i (mem_sdiff.mp iu).1
    have cap := card_le_card (show outN D W i⊆W from outN_subset)
    split_ifs with hit
    · by_contra! short
      dsimp only [k] at short
      have all := eq_of_subset_of_card_le (show outN D W i⊆W from outN_subset) (by omega)
      exact parent ⟨i,iu,by omega,all ▸ incl⟩
    · rw [not_nonempty_iff_eq_empty.mp hit,card_empty] at count
      omega
  obtain ⟨E,B,live,size,safe,quota⟩ := CommonExitReplacement.funded (install_free free ws remote) hq ws
    (show U⊆V from sdiff_subset) hu (fun i iw h hh=>by simp [install,iw,hh])
    (show q*(r-H.card)<k by dsimp [k]; omega) funded
  have count := card_sdiff_add_card_eq_card ws
  change U.card+W.card=V.card at count
  dsimp only [k] at size
  exact ⟨E,B,live,by omega,safe,quota⟩

ch_family_split_result cover_or_descend

structure Law {q r} (X : ShenMinimumOrder.Source q r) : Prop where
  cover : ∀W⊆X.V,∀H⊆X.V,(∀h∈H,Disjoint (ball X.D X.V h (q-1)) W) → q*(r-H.card)+2≤W.card →
    ∃i∈X.V\W,(outN X.D X.V i).card=r ∧ W⊆outN X.D X.V i

@[aesop safe forward (immediate := [X,hq]) (rule_sets := [CHGraphFamilies])]
theorem register {q r} (X : ShenMinimumOrder.Source q r) (hq : 2≤q) : Law X := by
  refine ⟨fun W ws H hs remote width=>?_⟩
  rcases cover_or_descend X.free (by omega) X.degree ws hs remote width with parent|⟨E,U,live,size,safe,quota⟩
  · exact parent
  · have := X.least E U safe quota live
    omega

@[aesop safe forward (immediate := [law,ws,hs,remote,width]) (rule_sets := [CHGraphFamilies])]
theorem marked_parent {q r} {X : ShenMinimumOrder.Source q r} (law : Law X) {W H : Finset ℕ}
    (ws : W⊆X.V) (hs : H⊆X.V) (remote : ∀h∈H,Disjoint (ball X.D X.V h (q-1)) W)
    (width : q*(r-H.card)+2≤W.card) : ∃i∈X.V\W,(outN X.D X.V i).card=r ∧ W⊆outN X.D X.V i :=
  law.cover W ws H hs remote width

ch_family_split_result marked_parent

@[aesop safe forward (immediate := [law,ws,hs,remote,wide]) (rule_sets := [CHGraphFamilies])]
theorem missed_bound {q r} {X : ShenMinimumOrder.Source q r} (law : Law X) {W H : Finset ℕ}
    (ws : W⊆X.V) (hs : H⊆X.V) (remote : ∀h∈H,Disjoint (ball X.D X.V h (q-1)) W) (wide : r<W.card) :
    W.card≤q*(r-H.card)+1 := by
  by_contra! fail
  obtain ⟨i,_,degree,all⟩ := law.cover W ws H hs remote (by omega)
  have count := card_le_card all
  omega

/-- All heads use the same missed labels. Taking the whole complement makes
    this a bound on every head set, with no proposed erased set required. -/
structure ReachLaw {q r} (X : ShenMinimumOrder.Source q r) : Prop where
  bound : ∀H⊆X.V,
    (X.V\BRsub.ballSet X.D X.V H (q-1)).card ≤ max r (q*(r-H.card)+1)

@[aesop safe forward (immediate := [law]) (rule_sets := [CHGraphFamilies])]
theorem reach_rule {q r} {X : ShenMinimumOrder.Source q r} (law : Law X) : ReachLaw X := by
  refine ⟨fun H hs=>?_⟩
  let W := X.V\BRsub.ballSet X.D X.V H (q-1)
  change W.card≤_
  by_cases small : W.card≤r
  · exact small.trans (le_max_left ..)
  have remote (h) (hh : h∈H) : Disjoint (ball X.D X.V h (q-1)) W :=
    disjoint_left.mpr (fun x hit xw=>(mem_sdiff.mp xw).2 (BRsub.mem_ballSet.mpr ⟨h,hh,hit⟩))
  exact (missed_bound (W:=W) law sdiff_subset hs remote (lt_of_not_ge small)).trans (le_max_right ..)

#print axioms install_free
#print axioms cover_or_descend
#print axioms register
#print axioms missed_bound
#print axioms reach_rule
end LeanCH.BR.RemoteHeadRectangle
