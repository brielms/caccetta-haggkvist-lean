import checkpoints.shen_extension.RerootTerminalRows

namespace LeanCH.BR.Closure.TwoHeadForcedMiss
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoHeadRepairReplay TwoHeadRepairReroot

/-- A single target for both origins of a missed repair. The price in the
first legal repair is exactly the starting price for its cut-carrier trace. -/
def MissAt (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∃a∈V,∃ (x y : ℕ) (z : ℕ→ℚ),x≠y ∧ CommonParentHeadRepair.Step q E V (outN E V a) (∅,w) ({x},z) ∧
    Missed q E V (outN E V a) (region q E V a) a x y z

theorem first_miss {q E V w c} {s : Seeds q E V w c} (m : Missing s) : MissAt q E V w := by
  rcases m with l|r
  · exact ⟨s.a,s.av,s.x,s.y,s.price,s.ne,s.first _ (mem_insert_self _ _),l⟩
  · exact ⟨s.a,s.av,s.y,s.x,s.price,s.ne.symm,s.first _ (by simp),r⟩

theorem after_reroot {q n w c} (X : ShortestCycleWeights.Model q n) (two : 2≤q)
    {s : Seeds q X.D X.V w c} (r : Rerooted s) : MissAt q X.D X.V w := by
  obtain ⟨b,bv,_,returns,u,_,_,live,z,start,runs⟩ := r
  obtain ⟨p,pp⟩ := live
  obtain one|⟨y,_,ne,_,miss⟩ := runs p pp
  · exact (OneParentReroot.impossible X two bv returns one).elim
  · exact ⟨b,bv,p,y,z,ne.symm,start p pp,miss⟩

/-- Keep the original seeds, every returning parent, the paying row and its
price. Every chosen return t permits a cut whose deleted parent misses t. -/
def ExactReroot {q E V w c} (s : Seeds q E V w c) : Prop :=
  ∃b∈V,b≠s.a ∧ (∀x∈inN E V b,∃t∈region q E V b,E x t=true) ∧
    ∃u∈region q E V b,
      let O := outN E (V\region q E V b) u
      c-mass (region q E V b) w≤q*mass O w ∧ O.Nonempty ∧
      ∃z : ℕ→ℚ,(∀x∈O,CommonParentHeadRepair.Step q E V (outN E V b) (∅,w) ({x},z)) ∧
        ∀x∈O,x∈inN E V b ∧ ∀t∈region q E V b,E x t=true →
          ∃y∈inN E V b,y≠x ∧ E y t=false ∧
            CommonParentReplay.Edge q E (outN E V b) ⟨V,{x},z⟩ ⟨V\{b,y},{x},z⟩ ∧
            Missed q E V (outN E V b) (region q E V b) b x y z

theorem refine_reroot {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) {s : Seeds q X.D X.V w c}
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) (wp : ∀i∈X.V,0<w i)
    (high : 1<c) (r : Rerooted s) : ExactReroot s := by
  obtain ⟨b,bv,ne,returns,u,ur,bill,live,z,start,_⟩ := r
  refine ⟨b,bv,ne,returns,u,ur,bill,live,z,start,?_⟩
  intro x xx
  obtain ⟨xd,ux⟩ := mem_outN.mp xx
  obtain ⟨xv,xr⟩ := mem_sdiff.mp xd
  have two : 2≤q := by omega
  have ub := ((saturated_region two X.free X.sat bv (BRsub.ballSet_subset ur)).mp ur).2
  have xb : x≠b := fun eq=>ub (eq ▸ ux)
  have par : x∈inN X.D X.V b := by
    refine mem_inN.mpr ⟨xv,?_⟩
    by_contra no
    exact xr ((saturated_region two X.free X.sat bv xv).mpr ⟨xb,no⟩)
  exact ⟨par,fun _ tr pt=>OneParentReroot.distinguished_cut X hq small bv par tr pt
    rows wp high s.diffuse (start x xx)⟩

/-- Projection to the earlier reroot statement keeps the same seed pair,
root, paying row, first price, returned vertex and chosen cut. -/
theorem recover_reroot {q E V w c} {s : Seeds q E V w c} (r : ExactReroot s) : Rerooted s := by
  obtain ⟨b,bv,ne,returns,u,ur,bill,live,z,start,run⟩ := r
  refine ⟨b,bv,ne,returns,u,ur,bill,live,z,start,?_⟩
  intro x xx
  obtain ⟨par,cut⟩ := run x xx
  obtain ⟨t,tr,pt⟩ := returns x par
  obtain ⟨y,yp,ne,_,edge,miss⟩ := cut t tr pt
  exact Or.inr ⟨y,yp,ne,edge,miss⟩

/-- Locate the missed rows on the terminal heads and prices already open
in the capstone, without extracting another existential terminal trace. -/
theorem terminal_location {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    {b p y T v} (bv : b∈X.V) (par : p∈inN X.D X.V b) (pT : p∈T) (count : T.card+1=q)
    (checks : CommonParentReplay.Checks q X.D (outN X.D X.V b) (region q X.D X.V b)
      (X.V\{b,y}) ⟨X.V\{b,y},T,v⟩) :
    (∃i∈T∩region q X.D X.V b,RerootTerminalRows.Misses X.D i T) ∨
      (∀h∈outN X.D X.V b,RerootTerminalRows.Misses X.D h T) ∨
      (∀t∈region q X.D X.V b,X.D p t=true → RerootTerminalRows.Misses X.D t T) := by
  have outside : p∉region q X.D X.V b := fun hit=>
    ((saturated_region (by omega) X.free X.sat bv (mem_inN.mp par).1).mp hit).2 (mem_inN.mp par).2
  exact RerootTerminalRows.locate hq (X.free.mono_set sdiff_subset) checks.1.selected
    (by omega) checks.1.same.symm (mem_sdiff.mpr ⟨pT,outside⟩)

def Outcome {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∃w c,mass X.V w=1 ∧ 1<c ∧ (∀i∈X.V,0<w i) ∧ (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) ∧
    ((∃h∈X.V,1<(q:ℚ)^2*w h) ∨ (∃s : Seeds q X.D X.V w c,Missing s) ∨
      ∃s : Seeds q X.D X.V w c,Covered s ∧ ExactReroot s)

theorem on_frontier {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (prior : TwoHeadRepairReroot.Result X) : Outcome X := by
  obtain ⟨w,c,wm,high,pos,flat,heavy|⟨s,m⟩|⟨s,cov,r⟩⟩ := prior
  · exact ⟨w,c,wm,high,pos,flat,Or.inl heavy⟩
  · exact ⟨w,c,wm,high,pos,flat,Or.inr (Or.inl ⟨s,m⟩)⟩
  · exact ⟨w,c,wm,high,pos,flat,Or.inr (Or.inr ⟨s,cov,refine_reroot X hq small flat pos high r⟩)⟩

theorem recover_previous {q n} {X : ShortestCycleWeights.Model q n} (out : Outcome X) :
    TwoHeadRepairReroot.Result X := by
  obtain ⟨w,c,wm,high,pos,flat,heavy|⟨s,m⟩|⟨s,cov,r⟩⟩ := out
  · exact ⟨w,c,wm,high,pos,flat,Or.inl heavy⟩
  · exact ⟨w,c,wm,high,pos,flat,Or.inr (Or.inl ⟨s,m⟩)⟩
  · exact ⟨w,c,wm,high,pos,flat,Or.inr (Or.inr ⟨s,cov,recover_reroot r⟩)⟩

#print axioms first_miss
#print axioms after_reroot
#print axioms refine_reroot
#print axioms recover_reroot
#print axioms terminal_location
#print axioms on_frontier
#print axioms recover_previous
end LeanCH.BR.Closure.TwoHeadForcedMiss
