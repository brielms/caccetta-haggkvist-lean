import checkpoints.shen_extension.TwoHeadRepairReplay

namespace LeanCH.BR.Closure.TwoHeadRepairReroot
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoHeadRepairLanes TwoHeadRepairReplay

/-- A dead parent of a root has no arc into that root's inner region. -/
def DeadParent (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (x a : ℕ) : Prop :=
  E x a=true ∧ ∀r∈region q E V a,E x r=false

theorem unique_root {q E V a b x} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (av : a∈V) (bv : b∈V) (left : DeadParent q E V x a) (right : DeadParent q E V x b) : a=b := by
  by_contra ne
  have back {u v} (uv : u∈V) (vv : v∈V) (n : u≠v) (dead : DeadParent q E V x v) (xu : E x u=true) :
      E u v=true := by
    by_contra no
    have inside := (saturated_region hq free sat vv uv).2 ⟨n,no⟩
    exact Bool.noConfusion ((dead.2 _ inside).symm.trans xu)
  exact free a 2 (by decide) hq
    (.step bv (back av bv ne right left.1) (.step av (back bv av (Ne.symm ne) left right.1) (.refl _)))

theorem other_root {q E V w c} {s : Seeds q E V w c} (hq : 2≤q)
    (free : QFree E V q) (sat : BRsub.Sat q E V) (both : Covered s) :
    ∃b∈V,b≠s.a ∧ ∀x∈inN E V b,∃r∈region q E V b,E x r=true := by
  classical
  obtain ⟨_,_,X,par,_⟩ := both
  have first : DeadParent q E V s.x s.a :=
    ⟨(mem_outN.mp (mem_inter.mp par).1).2,fun i ir=>X.dead₁ i (mem_insert_of_mem ir)⟩
  have second : DeadParent q E V s.y s.a :=
    ⟨(mem_outN.mp (mem_inter.mp par).2).2,fun i ir=>X.dead₂ i (mem_insert_of_mem ir)⟩
  have omitted : ∃b : V,∀x : V,¬DeadParent q E V x b := by
    by_contra! all
    choose f hf using all
    have inj : Function.Injective f := by
      intro j k eq
      exact Subtype.ext (unique_root hq free sat j.property k.property (hf j) (eq.symm ▸ hf k))
    have onto := Finite.surjective_of_injective inj
    obtain ⟨j,hj⟩ := onto ⟨s.x,X.z₁v⟩
    obtain ⟨k,hk⟩ := onto ⟨s.y,X.z₂v⟩
    have jroot : j.val=s.a := unique_root hq free sat j.property s.av (by have h := hf j; rw [hj] at h; exact h) first
    have kroot : k.val=s.a := unique_root hq free sat k.property s.av (by have h := hf k; rw [hk] at h; exact h) second
    have eq : j=k := Subtype.ext (jroot.trans kroot.symm)
    exact s.ne (congrArg Subtype.val (hj.symm.trans ((congrArg f eq).trans hk)))
  obtain ⟨b,absent⟩ := omitted
  refine ⟨b,b.property,fun eq=>absent ⟨s.x,X.z₁v⟩ (eq.symm ▸ first),?_⟩
  intro x xp
  obtain ⟨xv,xb⟩ := mem_inN.mp xp
  by_contra! no
  exact absent ⟨x,xv⟩ ⟨xb,fun r rr=>Bool.eq_false_iff.mpr (no r rr)⟩

/-- Reopen the repair at the root with no dead parent. If a second parent is
available to delete, the covered alternative of this next trace is impossible. -/
def Rerooted {q E V w c} (s : Seeds q E V w c) : Prop :=
  ∃b∈V,b≠s.a ∧ (∀x∈inN E V b,∃r∈region q E V b,E x r=true) ∧
    ∃u∈region q E V b,
      let O := outN E (V\region q E V b) u
      c-mass (region q E V b) w≤q*mass O w ∧ O.Nonempty ∧
      ∃z : ℕ→ℚ,(∀x∈O,CommonParentHeadRepair.Step q E V (outN E V b) (∅,w) ({x},z)) ∧
        ∀x∈O, inN E V b={x} ∨ ∃y∈inN E V b,y≠x ∧
          CommonParentReplay.Edge q E (outN E V b) ⟨V,{x},z⟩ ⟨V\{b,y},{x},z⟩ ∧
          Missed q E V (outN E V b) (region q E V b) b x y z

theorem reroot {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) {s : Seeds q X.D X.V w c}
    (wm : mass X.V w=1) (hi : 1<c) (wp : ∀a∈X.V,0<w a)
    (rows : ∀a∈X.V,WeightedSD.row q X.D X.V w a=c) (both : Covered s) : Rerooted s := by
  classical
  let E := X.D
  let V := X.V
  obtain ⟨b,bv,ne,backs⟩ := other_root (by omega : 2≤q) X.free X.sat both
  obtain ⟨_,p,d,_,dh,_,pm,_,pp,_,cols,_⟩ := LabelledLeakageCapacity.native X hq small
  have live {G t d'} (tp : ∀i∈V,0<t i) (tm : mass V t=1) (high : 1<d')
      (row : WeightedSD.row q G V t b=d') : (outN G V b).Nonempty := by
    by_contra! empty
    rw [WeightedSD.row,outW_eq_mass,empty] at row
    have le : t b≤mass V t := single_le_sum (fun i iv=>(tp i iv).le) bv
    simp [mass] at row
    linarith
  have hl := live wp wm hi (rows b bv)
  obtain ⟨par,ppar⟩ := live (G:=fun i j=>E j i) pp pm dh (cols b bv)
  obtain ⟨pv,pb⟩ := mem_outN.mp ppar
  obtain ⟨u,ur,far,all⟩ := PortParentInvariant.common_leaking_row hq X.free bv ⟨par,pv,pb⟩ hl small w wp (wm ▸ hi) rows
  obtain ⟨_,bill⟩ := all par pv pb
  rw [(PortParentInvariant.same_ball (d:=q-2) X.free bv pv pb (by omega)).2] at bill
  let R := region q E V b
  let H := outN E V b
  let O := outN E (V\R) u
  change c-mass R w≤q*mass O w at bill
  have rs : R⊆V := BRsub.ballSet_subset
  have present : O.Nonempty := by
    by_contra! empty
    rw [empty] at bill
    have le := mass_mono rs (fun j jv=>(wp j jv).le)
    simp only [mass,sum_empty,mul_zero] at bill
    change c-mass R w≤0 at bill
    linarith
  have uh : u∉H := fun h=>far (BRsub.subset_ballSet outN_subset h)
  obtain ⟨z,zp,heavy,_,first⟩ := open_seeds hq (H:=H) outN_subset ur uh X.free w wp
  refine ⟨b,bv,ne,backs,u,ur,bill,present,z,fun x xx=>first x (mem_outN.mpr
    ⟨(mem_sdiff.mp (mem_outN.mp xx).1).1,(mem_outN.mp xx).2⟩),?_⟩
  intro x xx
  obtain ⟨xd,ux⟩ := mem_outN.mp xx
  obtain ⟨xv,xr⟩ := mem_sdiff.mp xd
  have roots : b∈V.filter (fun a=>u∈region q E V a ∧ x∉region q E V a) := mem_filter.mpr ⟨bv,ur,xr⟩
  rw [crossing (by omega : 2≤q) X.free X.sat (rs ur) xv ux] at roots
  have xb := (mem_outN.mp (mem_sdiff.mp roots).1).2
  have xp : x∈inN E V b := mem_inN.mpr ⟨xv,xb⟩
  by_cases one : inN E V b={x}
  · exact Or.inl one
  · have other : ∃y∈inN E V b,y≠x := by
      by_contra! only
      exact one (Subset.antisymm (fun j hj=>mem_singleton.mpr (only j hj)) (singleton_subset_iff.mpr xp))
    obtain ⟨y,yp,yx⟩ := other
    obtain ⟨yv,yb⟩ := mem_inN.mp yp
    have nloop := loopfree X.free (by omega : 1≤q) bv
    have by' : b≠y := fun eq=>nloop (eq.symm ▸ yb)
    have bx : x≠b := fun eq=>nloop (eq ▸ xb)
    have bo : b∉R := fun br=>(saturated_region (by omega) X.free X.sat bv bv |>.mp br).1 rfl
    have yo : y∉R := fun yr=>(saturated_region (by omega) X.free X.sat bv yv |>.mp yr).2 yb
    have cut : ({b,y}:Finset ℕ)⊆V\R := insert_subset (mem_sdiff.mpr ⟨bv,bo⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨yv,yo⟩))
    have hs : H⊆V\{b,y} := fun h hh=>by
      have rh : h∈R := BRsub.subset_ballSet (Y:=H) outN_subset hh
      exact mem_sdiff.mpr ⟨rs rh,fun k=>(mem_sdiff.mp (cut k)).2 rh⟩
    have keep : x∈V\{b,y} := mem_sdiff.mpr ⟨xv,by simp [bx,yx.symm]⟩
    have run := lane hq X.free small by' cut keep xr hs hl rfl
      (fun r rr=>live_after_two hq wp rows hi s.diffuse bv yv by' (rs rr)) z zp heavy
    refine Or.inr ⟨y,yp,yx,run.1,?_⟩
    rcases replay_lane run with m|e
    · exact m
    · obtain ⟨j,jr,hit⟩ := backs x xp
      obtain ⟨_,_,_,_,_,_,_,_,_,dead⟩ := e
      exact False.elim (Bool.noConfusion ((dead j (mem_insert_of_mem jr)).symm.trans hit))

#print axioms unique_root
#print axioms other_root
#print axioms reroot

def Result {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∃w c,mass X.V w=1 ∧ 1<c ∧ (∀i∈X.V,0<w i) ∧ (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) ∧
    ((∃h∈X.V,1<(q:ℚ)^2*w h) ∨ (∃s : Seeds q X.D X.V w c,Missing s) ∨
      ∃s : Seeds q X.D X.V w c,Covered s ∧ Rerooted s)

theorem on_frontier {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (data : Outcome X) : Result X := by
  obtain ⟨w,c,wm,hi,wp,rows,out⟩ := data
  refine ⟨w,c,wm,hi,wp,rows,out.imp_right (Or.imp_right ?_)⟩
  rintro ⟨s,h⟩
  exact ⟨s,h,reroot X hq small wm hi wp rows h⟩

#print axioms on_frontier
end LeanCH.BR.Closure.TwoHeadRepairReroot
