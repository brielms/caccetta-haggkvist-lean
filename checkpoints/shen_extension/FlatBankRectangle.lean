import checkpoints.shen_extension.FlatMinimumExterior

namespace LeanCH.BR.Closure.FlatBankRectangle
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor FlatExchangeTriangle FlatPairedExcursion
open FirstPacketBarrier MarkedCyclePeeling PairedFamilyLoop

/-- A walk avoiding a set after its start, or its two pieces at a visit. -/
theorem split_set {E V a b k} (T : Finset ℕ) (p : Walk E V a b k) :
    Walk E (V\T) a b k ∨ ∃u∈T,∃r l,r+l=k ∧ Walk E V a u r ∧ Walk E V u b l := by
  induction p with
  | refl => exact Or.inl (.refl _)
  | @step a b c k bv edge tail ih =>
    by_cases bt : b∈T
    · exact Or.inr ⟨b,bt,1,k,by omega,.step bv edge (.refl _),tail⟩
    · rcases ih with short|⟨u,ut,r,l,eq,front,back⟩
      · exact Or.inl (.step (mem_sdiff.mpr ⟨bv,bt⟩) edge short)
      · exact Or.inr ⟨u,ut,r+1,l,by omega,.step bv edge front,back⟩

def Delay (E : CH.Digraph) (V T : Finset ℕ) (m : ℕ) :=
  ∀h∈V\T,(inN E T h).Nonempty → ∀v∈T,∀k,Walk E V h v k → m≤k

theorem other_delay {E V T m} (tv : T⊆V) (delay : Delay E V T m) {a z l}
    (walk : Walk E V a z l) (atop : a∈T) (zw : z∈V\T) (out : (outN E T z).Nonempty) : m≤l := by
  induction walk with
  | refl => exact ((mem_sdiff.mp zw).2 atop).elim
  | @step a b z k bv edge tail ih =>
    by_cases bt : b∈T
    · exact (ih bt zw out).trans (Nat.le_succ _)
    · obtain ⟨v,vh⟩ := out
      obtain ⟨vt,zv⟩ := mem_outN.mp vh
      exact delay b (mem_sdiff.mpr ⟨bv,bt⟩) ⟨a,mem_inN.mpr ⟨atop,edge⟩⟩ v vt _
        (tail.snoc (tv vt) zv)

private theorem drop_head {E N z h u d} (heads : (outN E N z).card=1)
    (hn : h∈N) (arc : E z h=true) (ne : z≠u) (w : Walk E N z u d) :
    ∃k,d=k+1 ∧ Walk E N h u k := by
  cases w with
  | refl => exact (ne rfl).elim
  | step bv edge tail =>
    have eq := card_le_one.mp heads.le _ (mem_outN.mpr ⟨bv,edge⟩) _ (mem_outN.mpr ⟨hn,arc⟩)
    exact ⟨_,rfl,eq ▸ tail⟩

/-- Every exit-to-entry edge is carried by a cycle wholly in the exterior. -/
theorem edge_outside {q D V F T m} (hq : 1≤q) (bal : q+1=2*m) (tv : T⊆V)
    (free : QFree (graph D F) V q) (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (delay : Delay (graph D F) V T m) {h z} (hw : h∈V\T) (zw : z∈V\T)
    (ins : (inN (graph D F) T h).Nonempty) (out : (outN (graph D F) T z).Nonempty)
    (arc : graph D F z h=true) : ∃N∈F,N⊆V\T ∧ z∈N ∧ h∈N := by
  obtain ⟨N,nh⟩ := active.mp arc
  obtain ⟨nf,zn,hn,_⟩ := mem_col.mp nh
  have cn := cycles N nf
  refine ⟨N,nf,?_,zn,hn⟩
  intro u un
  refine mem_sdiff.mpr ⟨cn.sub un,?_⟩
  intro ut
  obtain ⟨_,hi,first,second⟩ := MandatoryExcursion.segments hq free cn un zn
  have d1 := other_delay tv delay (first.mono cn.sub) ut zw out
  obtain ⟨k,sz,back⟩ := drop_head (cn.heads _ zn) hn arc (show z≠u from fun eq => (mem_sdiff.mp zw).2 (eq.symm ▸ ut)) second
  have d2 := delay h hw ins u ut k (back.mono cn.sub)
  omega

/-- If the selected family has no exterior cycle, every entry reaches every exit
inside the exterior. All these short walks pass through the same thin bank. -/
theorem rectangle {q D V F T m} (hq : 1≤q) (bal : q+1=2*m) (tv : T⊆V)
    (free : QFree (graph D F) V q) (sat : BRsub.Sat q (graph D F) V)
    (cycles : ∀I∈F,Cycle (graph D F) V q I) (delay : Delay (graph D F) V T m)
    (none : ¬∃N∈F,N⊆V\T) {S} (cut : FlatReturnLayers.Cuts (graph D F) V T S)
    {h z} (hw : h∈V\T) (ins : (inN (graph D F) T h).Nonempty)
    (zw : z∈V\T) (out : (outN (graph D F) T z).Nonempty) :
    ∃v∈S,∃r l,m≤r+l+1 ∧ r+l<q ∧
      Walk (graph D F) (V\T) h v r ∧ Walk (graph D F) (V\T) v z l := by
  have miss : ¬graph D F z h=true := by
    intro arc
    obtain ⟨N,nf,sub,_,_⟩ := edge_outside hq bal tv free cycles delay hw zw ins out arc
    exact none ⟨N,nf,sub⟩
  obtain ⟨_,k,le,w⟩ := mem_ball.mp (sat _ (mem_sdiff.mp hw).1 _ (mem_sdiff.mp zw).1 miss)
  have short : k<q := by omega
  have extW : Walk (graph D F) (V\T) h z k := by
    rcases split_set T w with walk|⟨u,ut,r,l,eq,front,back⟩
    · exact walk
    · have d1 := delay h hw ins u ut r front
      have d2 := other_delay tv delay back ut zw out
      omega
  obtain ⟨u,uh⟩ := (show (outN (graph D F) T z).Nonempty from out)
  obtain ⟨ut,zu⟩ := mem_outN.mp uh
  have lo := delay h hw ins u ut _ (w.snoc (tv ut) zu)
  by_cases hs : h∈S
  · exact ⟨h,hs,0,k,by omega,by omega,.refl _,extW⟩
  · rcases split_set S extW with avoids|⟨v,vs,r,l,eq,front,back⟩
    · exact (cut h hw ins hs z zw out k avoids).elim
    · exact ⟨v,vs,r,l,by omega,by omega,front,back⟩

#print axioms rectangle
end LeanCH.BR.Closure.FlatBankRectangle
