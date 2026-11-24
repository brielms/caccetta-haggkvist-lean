import checkpoints.shen_extension.TransferHeadChoices

namespace LeanCH.BR.Closure.CyclePhaseFork
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier
open MandatoryExcursion

/-- Before twice the girth, every position of a positive closed walk is a
different label. In particular each of the two spliced walks pays its length. -/
theorem room {D V q u k} (free : QFree D V q) (uv : u∈V) (small : k<2*(q+1))
    (w : Walk D V u u k) : k≤V.card := by
  classical
  obtain ⟨f,start,last,edges⟩ := w.toFun
  have distinct {i j} (lt : i<j) (jk : j<k) (same : f i=f j) : False := by
    have mid := walk_between edges lt.le jk.le
    rw [←same] at mid
    have many : q<j-i := by by_contra! bad; exact free _ _ (by omega) bad mid
    have endPath := walk_between edges jk.le le_rfl
    have front := walk_between edges (Nat.zero_le i) (by omega : i≤k)
    rw [start,Nat.sub_zero] at front
    rw [last] at endPath
    exact free _ ((k-j)+i) (by omega) (by omega) (same ▸ endPath.append front)
  have inj : Set.InjOn f (range k) := by
    intro i im j jm eq
    by_contra neq
    rcases Nat.lt_or_gt_of_ne neq with lt|lt
    · exact distinct lt (mem_range.mp jm) eq
    · exact distinct lt (mem_range.mp im) eq.symm
  have sub : (range k).image f⊆V := by
    intro x xm
    obtain ⟨i,im,rfl⟩ := mem_image.mp xm
    cases i with
    | zero => exact start ▸ uv
    | succ i => exact (edges i (by have := mem_range.mp im; omega)).1
  simpa only [card_image_of_injOn inj,card_range] using card_le_card sub

private theorem arc_back {D V q C p z} (hq : 2≤q) (free : QFree D V q)
    (c : Cycle D V q C) (pc : p∈C) (zc : z∈C) (edge : D p z=true) : Walk D V z p q := by
  obtain ⟨lo,_,_,back⟩ := segments (by omega : 1≤q) free c pc zc
  have ne : p≠z := by rintro rfl; exact loopfree free (by omega) (c.sub pc) edge
  have one := PuncturedDistance.depth_le_walk (Walk.step (c.sub zc) edge (.refl z))
  change PuncturedDistance.depth D V p z≤0+1 at one
  simp only [span,ite_eq_right ne] at lo back
  simpa [show PuncturedDistance.depth D V p z=1 by omega] using back.mono c.sub

/-- Two different positions on C predict the same phase for a common target.
The two actual closed walks have complementary excess over q+1. -/
theorem incoming {D V q C A B p t z} (hq : 2≤q) (free : QFree D V q)
    (c : Cycle D V q C) (a : Cycle D V q A) (b : Cycle D V q B)
    (pc : p∈C) (tc : t∈C) (ne : p≠t) (pa : p∈A) (za : z∈A) (tb : t∈B) (zb : z∈B)
    (pz : D p z=true) (tz : D t z=true) :
    ∃d,1≤d ∧ d≤q ∧ Walk D V z z (q+1+d) ∧ Walk D V z z (q+1+(q+1-d)) ∧
      q+1+d≤V.card ∧ q+1+(q+1-d)≤V.card := by
  obtain ⟨l,h,forward,backward⟩ := segments (by omega : 1≤q) free c pc tc
  let d := span D V q p t
  have hi : d≤q := by
    by_contra! fail
    have e : q+1-span D V q p t=0 := by change q+1-d=0; omega
    rw [e] at backward
    cases backward; exact ne rfl
  have r1 := arc_back hq free a pa za pz
  have r2 := arc_back hq free b tb zb tz
  have w1 : Walk D V z z (q+1+d) := by
    convert (r1.append (forward.mono c.sub)).snoc (a.sub za) tz using 1
    dsimp only [d]
    omega
  have w2 : Walk D V z z (q+1+(q+1-d)) := by
    convert (r2.append (backward.mono c.sub)).snoc (a.sub za) pz using 1
    dsimp only [d]
    omega
  change 1≤d at l
  exact ⟨d,l,hi,w1,w2,room free (a.sub za) (by omega) w1,room free (a.sub za) (by omega) w2⟩

/-- Through every member of every feasible witness family there is a
three-member phase conflict. Its common head is selected by the original
strict rows evaluated on the full family. -/
theorem forced {q n} (X : Model q n) (hq : 2≤q) {F C}
    (sub : F⊆family X) (feas : Feasible q n X.D X.V F) (cf : C∈F) :
    let E := graph X.D F
    ∃z∈X.V\C,∃p∈C,∃t∈C,p≠t ∧ E p z=true ∧ E t z=true ∧
      ∃A∈F,∃B∈F,A≠C ∧ B≠C ∧ A≠B ∧ p∈A ∧ z∈A ∧ t∈B ∧ z∈B ∧
        ∃d,1≤d ∧ d≤q ∧ Walk E X.V z z (q+1+d) ∧ Walk E X.V z z (q+1+(q+1-d)) ∧
          q+1+d≤X.V.card ∧ q+1+(q+1-d)≤X.V.card := by
  classical
  intro E
  have actual (A) (af : A∈F) : Cycle E X.V q A :=
    retain_cycle (show Cycle X.D X.V q A from (mem_filter.mp (sub af)).2) af
  have c := actual C cf
  obtain ⟨w,_,_,s⟩ := feas
  have rich : ∃z∈X.V\C,1<(inN E C z).card := by
    by_contra! all
    have cap (z) (zv : z∈X.V) : (inN E C z).card≤1 := by
      by_cases zc : z∈C
      · exact (c.incoming z zc).le
      · exact all z (mem_sdiff.mpr ⟨zv,zc⟩)
    let W := ∑z∈X.V,w z
    have tab : (∑x∈C,∑z∈X.V,if E x z=true then w z else 0)≤W := by
      rw [sum_comm]
      apply sum_le_sum
      intro z zv
      calc
        _ = ∑_x∈inN E C z,w z := by simp only [inN,sum_filter]
        _ = (inN E C z).card*w z := by simp
        _ ≤ w z := by simpa using Nat.mul_le_mul_right (w z) (cap z zv)
    have hi := sum_lt_sum_of_nonempty (card_pos.mp (show 0<C.card by rw [c.size];omega))
      (fun x xc => nat_strict.mp s x (c.sub xc))
    change (∑_x∈C,W)<(∑x∈C,score q E X.V w x) at hi
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,score,sum_add_distrib,←mul_sum,c.size,Nat.succ_mul] at hi
    have cap' := Nat.mul_le_mul_left q tab
    have diag : (∑x∈C,w x)≤W := sum_le_sum_of_subset_of_nonneg c.sub (by intros;omega)
    omega
  obtain ⟨z,zm,two⟩ := rich
  obtain ⟨p,pi,t,ti,ne⟩ := one_lt_card.mp two
  obtain ⟨pc,pz⟩ := mem_inN.mp pi
  obtain ⟨tc,tz⟩ := mem_inN.mp ti
  obtain ⟨A,usedA⟩ := active.mp pz
  obtain ⟨B,usedB⟩ := active.mp tz
  obtain ⟨af,pa,za,_⟩ := mem_col.mp usedA
  obtain ⟨bf,tb,zb,_⟩ := mem_col.mp usedB
  have diff : A≠B := fun eq => ne (card_le_one.mp ((actual A af).incoming z za).le _
    (mem_inN.mpr ⟨pa,pz⟩) _ (mem_inN.mpr ⟨eq ▸ tb,tz⟩))
  exact ⟨z,zm,p,pc,t,tc,ne,pz,tz,A,af,B,bf,fun e => (mem_sdiff.mp zm).2 (e ▸ za),
    fun e => (mem_sdiff.mp zm).2 (e ▸ zb),diff,pa,za,tb,zb,
    incoming hq (PrivateArcEndpoints.graph_free X F) c (actual A af) (actual B bf) pc tc ne pa za tb zb pz tz⟩

/-- Both splices fit in the original normalized support; their lengths add
to three times the shortest cycle length. -/
theorem support_bound {q n} (X : Model q n) (hq : 2≤q) : 3*(q+1)≤2*X.V.card := by
  classical
  obtain ⟨v,vv⟩ := X.live
  obtain ⟨C,_,c,_,_,_,_⟩ := ShortestReturnCertificate.on_model X hq vv
  have cf : C∈family X := mem_filter.mpr ⟨mem_powerset.mpr c.sub,c⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,d,_,hi,_,_,r1,r2⟩ :=
    forced X hq Subset.rfl (full_feasible X hq) cf
  omega

/-- If a row reaches two different positions on C, their two arc witnesses
meet C in disjoint sets. This controls every target of the row simultaneously. -/
theorem disjoint_overlaps {D V q C A B p x y} (hq : 2≤q) (free : QFree D V q)
    (c : Cycle D V q C) (a : Cycle D V q A) (b : Cycle D V q B) (xc : x∈C) (yc : y∈C)
    (px : D p x=true) (py : D p y=true) (ne : x≠y)
    (pa : p∈A) (xa : x∈A) (pb : p∈B) (yb : y∈B) :
    Disjoint (C∩A) (C∩B) := by
  apply disjoint_left.mpr
  intro r ra rb
  obtain ⟨rc,ar⟩ := mem_inter.mp ra
  have br := (mem_inter.mp rb).2
  have xr : x≠r := by
    rintro rfl
    exact ne (card_le_one.mp (b.heads p pb).le _ (mem_outN.mpr ⟨br,px⟩) _ (mem_outN.mpr ⟨yb,py⟩))
  have yr : y≠r := by
    rintro rfl
    exact ne (card_le_one.mp (a.heads p pa).le _ (mem_outN.mpr ⟨xa,px⟩) _ (mem_outN.mpr ⟨ar,py⟩))
  have first := PuncturedDistance.rise_on_cycle free a ar pa xa xr px
  have second := PuncturedDistance.rise_on_cycle free b br pb yb yr py
  obtain ⟨_,_,f,_⟩ := segments (by omega : 1≤q) free c rc xc
  obtain ⟨_,_,g,_⟩ := segments (by omega : 1≤q) free c rc yc
  simp only [span,ite_eq_right (Ne.symm xr),ite_eq_right (Ne.symm yr)] at f g
  exact ne (ConsecutiveBlockerPool.same_end c rc f ((first.trans second.symm).symm ▸ g))

/-- The outside labels available to an arbitrary witness family limit the
number of different heads a row can have on any one of its cycles. -/
theorem head_capacity {q n} (X : Model q n) (hq : 2≤q) {F A}
    (sub : F⊆family X) (af : A∈F) (p : ℕ) :
    (outN (graph X.D F) A p).card * (2*(q+1)-X.V.card) ≤ q+1 := by
  classical
  let E := graph X.D F
  let H := outN E A p
  have actual (C) (cf : C∈F) : Cycle E X.V q C :=
    retain_cycle (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have ca := actual A af
  have witness (z) (zh : z∈H) : ∃B∈F,p∈B ∧ z∈B := by
    obtain ⟨B,hit⟩ := active.mp (mem_outN.mp zh).2
    obtain ⟨bf,pb,zb,_⟩ := mem_col.mp hit
    exact ⟨B,bf,pb,zb⟩
  choose! dest df cert using witness
  let block (z : ℕ) := A∩dest z
  have pair : (H : Set ℕ).PairwiseDisjoint block := by
    intro x hx y hy ne
    exact disjoint_overlaps hq (PrivateArcEndpoints.graph_free X F) ca (actual _ (df _ hx)) (actual _ (df _ hy))
      (mem_outN.mp hx).1 (mem_outN.mp hy).1 (mem_outN.mp hx).2 (mem_outN.mp hy).2 ne
      (cert _ hx).1 (cert _ hx).2 (cert _ hy).1 (cert _ hy).2
  have lower (z) (zh : z∈H) : 2*(q+1)-X.V.card≤(block z).card := by
    have bz := actual _ (df _ zh)
    have small := card_le_card (union_subset ca.sub bz.sub)
    have eq := card_union_add_card_inter A (dest z)
    rw [ca.size,bz.size] at eq
    change _≤(A∩dest z).card
    omega
  have all := sum_le_sum lower
  have upper := card_le_card (show H.biUnion block⊆A by
    intro z mem
    obtain ⟨_,_,hit⟩ := mem_biUnion.mp mem
    exact (mem_inter.mp hit).1)
  rw [card_biUnion pair,ca.size] at upper
  exact (by simpa [H] using all.trans upper)

#print axioms head_capacity
#print axioms disjoint_overlaps
#print axioms support_bound
#print axioms room
#print axioms incoming
#print axioms forced
end LeanCH.BR.Closure.CyclePhaseFork
