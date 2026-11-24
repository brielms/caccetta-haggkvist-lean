import checkpoints.shen_extension.TwoHeadRepairReroot

namespace LeanCH.BR.Closure.OneParentReroot
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity
open TwoHeadRepairLanes TwoHeadRepairReplay TwoHeadRepairReroot

/-- The parent separating b from the specified return t is a legal second deletion. -/
theorem other_parent {q n b p t} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (bv : b∈X.V) (tr : t∈region q X.D X.V b) (pt : X.D p t=true) :
    ∃y∈inN X.D X.V b,y≠p ∧ X.D y t=false := by
  have tv : t∈X.V := BRsub.ballSet_subset tr
  have ne := ((saturated_region hq X.free X.sat bv tv).mp tr).1
  obtain ⟨y,yv,yb,yt⟩ := X.separated b bv t tv ne
  exact ⟨y,mem_inN.mpr ⟨yv,yb⟩,fun eq=>Bool.noConfusion ((eq ▸ yt).symm.trans pt),yt⟩

/-- This consumes exactly the singleton and return hypotheses of the recursive frontier. -/
theorem impossible {q n b p} (X : ShortestCycleWeights.Model q n) (hq : 2≤q) (bv : b∈X.V)
    (backs : ∀x∈inN X.D X.V b,∃t∈region q X.D X.V b,X.D x t=true)
    (one : inN X.D X.V b={p}) : False := by
  obtain ⟨t,tr,pt⟩ := backs p (one ▸ mem_singleton_self p)
  obtain ⟨y,yp,ne,_⟩ := other_parent X hq bv tr pt
  exact ne (mem_singleton.mp (one ▸ yp))

/-- The predicted forward bill and reverse law, with independent weights and constants. -/
theorem singleton_accounts {q E V b p i w c} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (bv : b∈V) (one : inN E V b={p}) (ir : i∈region q E V b)
    (live : (outN E (V\region q E V b) i).Nonempty)
    (bill : c-mass (region q E V b) w ≤ q*mass (outN E (V\region q E V b) i) w)
    (π : ℕ→ℚ) {d : ℚ} (col : WeightedSD.col q E V π b=d) :
    region q E V b=V\{b,p} ∧ outN E (V\region q E V b) i={p} ∧
      c-mass V w+w b≤((q:ℚ)-1)*w p ∧ π b+q*π p=d := by
  have iv : i∈V := BRsub.ballSet_subset ir
  have reg : region q E V b=V\{b,p} := by
    ext k
    by_cases kv : k∈V
    · have parent : E k b=true ↔ k=p := by
        simpa [mem_inN,kv] using (show k∈inN E V b ↔ k∈({p}:Finset ℕ) from one ▸ Iff.rfl)
      simp [saturated_region hq free sat bv kv,kv,parent]
    · exact iff_of_false (fun h=>kv (BRsub.ballSet_subset h)) (fun h=>kv (mem_sdiff.mp h).1)
  have only (k) (hit : k∈outN E (V\region q E V b) i) : k=p := by
    obtain ⟨kd,ik⟩ := mem_outN.mp hit
    obtain ⟨kv,kr⟩ := mem_sdiff.mp kd
    have cross : b∈V.filter (fun a=>i∈region q E V a ∧ k∉region q E V a) := mem_filter.mpr ⟨bv,ir,kr⟩
    rw [crossing hq free sat iv kv ik] at cross
    exact mem_singleton.mp (one ▸ mem_inN.mpr ⟨kv,(mem_outN.mp (mem_sdiff.mp cross).1).2⟩)
  obtain ⟨k,hk⟩ := live
  have exits : outN E (V\region q E V b) i={p} := Subset.antisymm
    (fun j hj=>mem_singleton.mpr (only j hj)) (singleton_subset_iff.mpr (only k hk ▸ hk))
  have f := (SoleExitWeightGap.parent_bill hq free sat bv ⟨i,ir,exits,bill⟩).2
  have inc : inW E V π b=mass (inN E V b) π := by simp [inW,mass,inN,sum_filter]
  exact ⟨reg,exits,by simpa [one,mass] using f,by simpa [WeightedSD.col,inc,one,mass] using col⟩

/-- Run on the displayed cut, using the original seed prices and the parent
which misses the displayed return label. -/
theorem distinguished_cut {q n b p t z w c} (X : ShortestCycleWeights.Model q n)
    (hq : 3≤q) (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (par : p∈inN X.D X.V b)
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) (wp : ∀i∈X.V,0<w i)
    (high : 1<c) (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    (first : CommonParentHeadRepair.Step q X.D X.V (outN X.D X.V b) (∅,w) ({p},z)) :
    ∃y∈inN X.D X.V b,y≠p ∧ X.D y t=false ∧
      CommonParentReplay.Edge q X.D (outN X.D X.V b) ⟨X.V,{p},z⟩ ⟨X.V\{b,y},{p},z⟩ ∧
      Missed q X.D X.V (outN X.D X.V b) (region q X.D X.V b) b p y z := by
  obtain ⟨y,parY,ne,yt⟩ := other_parent X (by omega) bv tr pt
  obtain ⟨pv,pb⟩ := mem_inN.mp par
  obtain ⟨yv,yb⟩ := mem_inN.mp parY
  have two : 2≤q := by omega
  have banned {k} (kv : k∈X.V) (kb : X.D k b=true) : k∉region q X.D X.V b :=
    fun h=>((saturated_region two X.free X.sat bv kv).mp h).2 kb
  have br : b∉region q X.D X.V b := fun h=>((saturated_region two X.free X.sat bv bv).mp h).1 rfl
  have cut : ({b,y}:Finset ℕ)⊆X.V\region q X.D X.V b := insert_subset (mem_sdiff.mpr ⟨bv,br⟩)
    (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨yv,banned yv yb⟩))
  have byNe : b≠y := fun eq=>loopfree X.free (by omega) bv (eq ▸ yb)
  have pbNe : p≠b := fun eq=>loopfree X.free (by omega) bv (eq ▸ pb)
  have keep : p∈X.V\{b,y} := by simp [pv,pbNe,ne.symm]
  have hs : outN X.D X.V b⊆X.V\{b,y} := by
    intro h hh
    have hr : h∈region q X.D X.V b := BRsub.subset_ballSet outN_subset hh
    exact mem_sdiff.mpr ⟨(mem_outN.mp hh).1,fun hd=>(mem_sdiff.mp (cut hd)).2 hr⟩
  obtain ⟨h,hh,_⟩ := BRsub.mem_ballSet.mp tr
  have run := lane hq X.free small byNe cut keep (banned pv pb) hs ⟨h,hh⟩ rfl
    (fun i ir=>live_after_two hq wp rows high diffuse bv yv byNe (BRsub.ballSet_subset ir))
    z first.2.1 first.2.2.1
  refine ⟨y,parY,ne,yt,run.1,?_⟩
  rcases replay_lane run with miss|terminal
  · exact miss
  · obtain ⟨_,_,_,_,_,_,_,_,_,dead⟩ := terminal
    exact False.elim (Bool.noConfusion ((dead t (mem_insert_of_mem tr)).symm.trans pt))

#print axioms other_parent
#print axioms impossible
#print axioms singleton_accounts
#print axioms distinguished_cut
end LeanCH.BR.Closure.OneParentReroot
