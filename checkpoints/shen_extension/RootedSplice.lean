import checkpoints.shen_extension.AllCutoffPacketEscape
import checkpoints.shen_extension.RootedCycleLayers
import LeanCH.BR.BRTightCycleReversal

namespace LeanCH.BR.Closure.RootedSplice
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights

def Covered (D : CH.Digraph) (V : Finset ℕ) (q h t : ℕ) : Prop :=
  ∃C,Cycle D (V.erase h) q C ∧ t∈C

private theorem root_mem {D V q h t C} (c : Cycle D V q C) (tc : t∈C)
    (absent : ¬Covered D V q h t) : h∈C := by
  by_contra no
  exact absent ⟨C,⟨fun x xc => mem_erase.mpr ⟨fun e => no (e ▸ xc),c.sub xc⟩,
    c.size,c.heads,c.incoming⟩,tc⟩

private theorem segments {D V q M h t} (safe : QFree D V q) (c : Cycle D V q M)
    (hm : h∈M) (tm : t∈M) (ht : h≠t) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ q ∧ Walk D M h t i ∧ Walk D M t h (q+1-i) := by
  apply WeightedSD.tight_cycle_complementary_walks (safe.mono_set c.sub) c.size _ hm tm ht
  intro x xm
  obtain ⟨y,yh⟩ := card_pos.mp (show 0<(outN D M x).card by rw [c.heads x xm]; decide)
  exact ⟨y,mem_outN.mp yh⟩

/-- The two geodesics can be chosen independently for an arbitrary
incoming arc and an arbitrary outgoing arc of the missing retained label. -/
theorem turn {q n} (X : Model q n) (hq : 2≤q) {h p t y}
    (tw : t∈X.V.erase h) (pv : p∈X.V) (yv : y∈X.V)
    (pt : X.D p t=true) (ty : X.D t y=true) (absent : ¬Covered X.D X.V q h t) :
    ∃i j,i+j+2=q+1 ∧ Walk X.D X.V h p i ∧ Walk X.D X.V y h j := by
  have tv := mem_of_mem_erase tw
  have ht := Ne.symm (mem_erase.mp tw).1
  obtain ⟨A,ca,pa,ta⟩ := edge_cycle X hq pv tv pt
  obtain ⟨B,cb,tb,yb⟩ := edge_cycle X hq tv yv ty
  obtain ⟨i,ip,iq,f,g⟩ := segments X.free ca (root_mem ca ta absent) ta ht
  obtain ⟨j,jp,jq,f',g'⟩ := segments X.free cb (root_mem cb tb absent) tb ht
  obtain rfl : i=j := ShortestCyclePeeling.aligned X.free iq jq (f.mono ca.sub) (g.mono ca.sub)
    (f'.mono cb.sub) (g'.mono cb.sub)
  cases i with
  | zero => omega
  | succ k =>
    obtain ⟨p',pref,_,pt'⟩ := f.unsnoc
    have p'a : p'∈A := (pref.end_mem_or).elim (fun e => e ▸ root_mem ca ta absent) id
    have one : (inN X.D A t).card=1 := ca.incoming t ta
    obtain rfl : p'=p := card_le_one.mp one.le _ (mem_inN.mpr ⟨p'a,pt'⟩) _ (mem_inN.mpr ⟨pa,pt⟩)
    have len : q+1-(k+1)=(q-(k+1))+1 := by omega
    rw [len] at g'
    cases g' with
    | step zmem tz tail =>
      obtain rfl := card_le_one.mp (cb.heads t tb).le _ (mem_outN.mpr ⟨zmem,tz⟩) _ (mem_outN.mpr ⟨yb,ty⟩)
      exact ⟨k,_,by omega,pref.mono ca.sub,tail.mono cb.sub⟩

theorem missing_arc {q n} (X : Model q n) (hq : 2≤q) {h p t y}
    (tw : t∈X.V.erase h) (pv : p∈X.V) (yv : y∈X.V)
    (pt : X.D p t=true) (ty : X.D t y=true) (absent : ¬Covered X.D X.V q h t) :
    X.D p y=false := by
  obtain ⟨i,j,l,f,g⟩ := turn X hq tw pv yv pt ty absent
  exact Bool.eq_false_iff.mpr (fun py => X.free h (i+1+j) (by omega) (by omega) ((f.snoc yv py).append g))

/-- A missing retained vertex which is a parent of h has no other head. -/
theorem sole_head {q n} (X : Model q n) (hq : 2≤q) {h t y}
    (tw : t∈X.V.erase h) (yv : y∈X.V) (th : X.D t h=true) (ty : X.D t y=true)
    (absent : ¬Covered X.D X.V q h t) : y=h := by
  obtain ⟨C,c,tc,yc⟩ := edge_cycle X hq (mem_of_mem_erase tw) yv ty
  exact card_le_one.mp (c.heads t tc).le _ (mem_outN.mpr ⟨yc,ty⟩) _ (mem_outN.mpr ⟨root_mem c tc absent,th⟩)

theorem sole_parent {q n} (X : Model q n) (hq : 2≤q) {h t p}
    (tw : t∈X.V.erase h) (pv : p∈X.V) (ht : X.D h t=true) (pt : X.D p t=true)
    (absent : ¬Covered X.D X.V q h t) : p=h := by
  obtain ⟨C,c,pc,tc⟩ := edge_cycle X hq pv (mem_of_mem_erase tw) pt
  exact card_le_one.mp (c.incoming t tc).le _ (mem_inN.mpr ⟨pc,pt⟩) _ (mem_inN.mpr ⟨root_mem c tc absent,ht⟩)

#print axioms turn
#print axioms missing_arc
end LeanCH.BR.Closure.RootedSplice
