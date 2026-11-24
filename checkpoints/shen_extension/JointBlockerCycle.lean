import checkpoints.shen_extension.EqualColumnRepair
import checkpoints.shen_extension.ShortestReturnCertificate

namespace LeanCH.BR.Closure.JointBlockerCycle
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MandatoryTwoStep RootedSplice EqualColumnRepair

private theorem trace {D V u v i} (uv : u∈V) (path : Walk D V u v i) :
    ∃U⊆V,U.card ≤ i+1 ∧ u∈U ∧ v∈U ∧ Walk D U u v i := by
  classical
  induction path with
  | refl x => exact ⟨{x},singleton_subset_iff.mpr uv,by simp,mem_singleton_self _,mem_singleton_self _,.refl _⟩
  | @step a b c k bv ab tail ih =>
    obtain ⟨U,sub,sz,bu,cu,inner⟩ := ih bv
    exact ⟨insert a U,insert_subset uv sub,(card_insert_le a U).trans (by omega),
      mem_insert_self _ _,mem_insert_of_mem cu,.step (mem_insert_of_mem bu) ab (inner.mono (subset_insert _ _))⟩

private theorem assemble {D V q x y p r i j} (hq : 1≤q) (free : QFree D V q)
    (xv : x∈V) (yv : y∈V) (px : D p x=true) (ry : D r y=true)
    (front : Walk D V x r i) (back : Walk D V y p j) (len : i+j+2=q+1) :
    ∃C,Cycle D V q C ∧ x∈C ∧ y∈C ∧ p∈C ∧ r∈C := by
  classical
  obtain ⟨F,fv,fs,xf,rf,f⟩ := trace xv front
  obtain ⟨B,bv,bs,yb,pb,b⟩ := trace yv back
  let U := F∪B
  have fu : F⊆U := subset_union_left
  have bu : B⊆U := subset_union_right
  have uv : U⊆V := union_subset fv bv
  have walk := ((f.mono fu).snoc (bu yb) ry).append ((b.mono bu).snoc (fu xf) px)
  have l : (i+1)+(j+1)=q+1 := by omega
  rw [l] at walk
  obtain ⟨C,cu,sz,deg⟩ := boundary_closed_walk_support (free.mono_set uv) walk
  have small : U.card≤q+1 := (card_union_le F B).trans (by omega)
  obtain rfl : C=U := eq_of_subset_of_card_le cu (sz ▸ small)
  have reg := dt_reg hq (ball_q_one q hq) (free.mono_set uv) deg (by simpa using sz)
  exact ⟨U,⟨uv,sz,reg.1,reg.2⟩,fu xf,bu yb,bu pb,fu rf⟩

private theorem prefix_to_parent {D V C q x y r k} (cycle : Cycle D V q C)
    (xc : x∈C) (yc : y∈C) (rc : r∈C) (ry : D r y=true) (path : Walk D C x y (k+1)) :
    Walk D V x r k := by
  obtain ⟨r',front,_,last⟩ := path.unsnoc
  have r'c : r'∈C := front.end_mem_or.elim (fun eq => eq ▸ xc) id
  obtain rfl : r'=r := card_le_one.mp (cycle.incoming y yc).le _
    (mem_inN.mpr ⟨r'c,last⟩) _ (mem_inN.mpr ⟨rc,ry⟩)
  exact front.mono cycle.sub

/-- Prescribed parents at two different anchors of the same incidence class
can be realized simultaneously on one shortest cycle. -/
theorem parents_together {q n} (X : Model q n) (hq : 2≤q) {x y p r}
    (xv : x∈X.V) (yv : y∈X.V) (pv : p∈X.V) (rv : r∈X.V) (xy : x≠y)
    (px : X.D p x=true) (ry : X.D r y=true)
    (fxy : Forces X.D X.V q x y) (fyx : Forces X.D X.V q y x) :
    ∃C,Cycle X.D X.V q C ∧ x∈C ∧ y∈C ∧ p∈C ∧ r∈C := by
  obtain ⟨A,ca,pa,xa⟩ := edge_cycle X hq pv xv px
  obtain ⟨B,cb,rb,yb⟩ := edge_cycle X hq rv yv ry
  have ya := fxy A ca xa
  have xb := fyx B cb yb
  have split {C} (c : Cycle X.D X.V q C) (xc : x∈C) (yc : y∈C) :
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ q ∧ Walk X.D C x y i ∧ Walk X.D C y x (q+1-i) := by
    apply WeightedSD.tight_cycle_complementary_walks (X.free.mono_set c.sub) c.size _ xc yc xy
    intro z zc
    obtain ⟨k,kh⟩ := card_pos.mp (show 0<(outN X.D C z).card by rw [c.heads z zc]; decide)
    exact ⟨k,mem_outN.mp kh⟩
  obtain ⟨i,pos,bd,f,g⟩ := split ca xa ya
  obtain ⟨j,jp,jb,f',g'⟩ := split cb xb yb
  obtain rfl : i=j := ShortestCyclePeeling.aligned X.free bd jb (f.mono ca.sub) (g.mono ca.sub)
    (f'.mono cb.sub) (g'.mono cb.sub)
  have il : i=(i-1)+1 := by omega
  have jl : q+1-i=(q-i)+1 := by omega
  have front := prefix_to_parent cb xb yb rb ry (il ▸ f')
  have back := prefix_to_parent ca ya xa pa px (jl ▸ g)
  exact assemble (by omega) X.free xv yv px ry front back (by omega)

theorem paid_pair_on_cycle {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∃C p x r y,Cycle X.D X.V q C ∧ K⊆C ∧ p∈C ∧ r∈C ∧ x≠y ∧ p≠r ∧
      Blocks X K p x ∧ Blocks X K r y := by
  obtain ⟨p,x,r,y,xy,pr,bx,by'⟩ := two_blockers X hq sub hk many equal minimum size
  have get {v z} (b : Blocks X K v z) : X.D v z=true := by
    have e : z∈outN X.D K v := b.2.2.1 ▸ mem_singleton_self _
    exact (mem_outN.mp e).2
  obtain ⟨C,c,xc,_,pc,rc⟩ := parents_together X hq (sub bx.2.1) (sub by'.2.1)
    (mem_sdiff.mp bx.1).1 (mem_sdiff.mp by'.1).1 xy (get bx) (get by')
    (equal x bx.2.1 y by'.2.1) (equal y by'.2.1 x bx.2.1)
  exact ⟨C,p,x,r,y,c,fun z zk => equal x bx.2.1 z zk C c xc,pc,rc,xy,pr,bx,by'⟩

#print axioms parents_together
#print axioms paid_pair_on_cycle
end LeanCH.BR.Closure.JointBlockerCycle
