import checkpoints.shen_extension.UniversalSlackPair
import checkpoints.shen_extension.FlatTransientReturn

namespace LeanCH.BR.Closure.SlackPairOrbit
open Finset Function BRq2 BRq3 BR45 WeightedSD PairedFamilyLoop RawRepairAlternative FlatTransientReturn

/-- A single labeled slack certificate pays a quantitative light-row
bound simultaneously for every nonnegative choice of row weights. -/
theorem margin {q E U p z} (law : RealDual q E U 1 p)
    (zu : z∈U) (lo : realCol q E U p z<1) :
    ∃δ : ℝ,0<δ ∧ ∀w : ℕ→ℝ,(∀i∈U,0≤w i) →
      ∃u∈U,realRow q E U w u+δ*w z≤realMass U w := by
  classical
  let δ := 1-realCol q E U p z
  refine ⟨δ,sub_pos.mpr lo,?_⟩
  intro w wn
  let loss := fun i => w i*(1-realCol q E U p i)
  have sumLoss : δ*w z≤∑i∈U,loss i := by
    rw [mul_comm]
    exact single_le_sum (fun i hi => mul_nonneg (wn i hi) (sub_nonneg.mpr (law.columns i hi))) zu
  have balance := real_cross_rows q E U w p
  have defect : (∑i∈U,p i*realRow q E U w i)+(∑i∈U,loss i)=realMass U w := by
    rw [balance,←sum_add_distrib]
    exact sum_congr rfl (fun i _ => by dsimp [loss]; ring)
  by_contra! high
  have positive : ∃i∈U,0<p i := by
    by_contra! none
    have zero : realMass U p=0 := sum_eq_zero (fun i hi => le_antisymm (none i hi) (law.nonneg i hi))
    linarith [law.normalized]
  obtain ⟨j,ju,jp⟩ := positive
  let target := realMass U w-δ*w z
  have each (i) (iu : i∈U) : target<realRow q E U w i := by dsimp [target]; linarith [high i iu]
  have total := sum_lt_sum (fun i hi => mul_le_mul_of_nonneg_left (each i hi).le (law.nonneg i hi))
    ⟨j,ju,mul_lt_mul_of_pos_left (each j ju) jp⟩
  rw [←sum_mul] at total
  change realMass U p * target < _ at total
  rw [law.normalized,one_mul] at total
  dsimp [target] at total
  linarith

private theorem slack_or_tight {F q E V} {raw : PairedFamilyLoop.State F → ℕ→ℝ} (s : PairedFamilyLoop.State F)
    (law : RealDual q E (V\gone s) 1 (raw s)) :
    Slack q E V raw s ∨ Tight q E V raw s := by
  classical
  by_cases yes : Slack q E V raw s
  · exact Or.inl yes
  · exact Or.inr (fun z hz => le_antisymm (law.columns z hz) (le_of_not_gt (fun lt => yes ⟨z,hz,lt⟩)))

/-- The same selected repair schedule is started at a forced-slack pair.
Either its orbit reaches a recurrent slack child, or it has a genuine last
slack-to-flat edge before first arrival at a tight child. -/
theorem from_seed {F q E V} (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (raw : PairedFamilyLoop.State F → ℕ→ℝ) (laws : ∀s,RealDual q E (V\gone s) 1 (raw s))
    (seed : PairedFamilyLoop.State F) (must : FlatOverlapDescent.ForcedSlack q E (V\gone seed)) :
    (∃i,go^[i] seed∈periodicPts go ∧ Slack q E V raw (go^[i] seed)) ∨
      (seed∉periodicPts go ∧ ∃j,(∀i≤j,Slack q E V raw (go^[i] seed)) ∧ Tight q E V raw (go (go^[j] seed))) := by
  classical
  by_cases recur : ∃i,go^[i] seed∈periodicPts go ∧ Slack q E V raw (go^[i] seed)
  · exact Or.inl recur
  right
  have start : Slack q E V raw seed := must (raw seed) (laws seed)
  have trans : seed∉periodicPts go := fun per => recur ⟨0,per,start⟩
  have no : ¬Tight q E V raw seed := by
    obtain ⟨z,zu,lt⟩ := start
    exact fun eq => lt.ne (eq z zu)
  obtain ⟨t,per⟩ := CycleSlotOrbit.recurrent go seed
  have hit : ∃j,Tight q E V raw (go^[j] seed) := ⟨t,(slack_or_tight _ (laws _)).resolve_left
    (fun slack => recur ⟨t,per,slack⟩)⟩
  have ht := Nat.find_spec hit
  have pos : 0<Nat.find hit := by
    by_contra! zero
    rw [show Nat.find hit=0 by omega] at ht
    exact no ht
  refine ⟨trans,Nat.find hit-1,?_,?_⟩
  · intro i le
    exact (slack_or_tight _ (laws _)).resolve_right (Nat.find_min hit (by omega))
  · rw [←iterate_succ_apply' go (Nat.find hit-1) seed,show (Nat.find hit-1).succ=Nat.find hit by omega]
    exact ht

#print axioms margin
#print axioms from_seed
/-- On a slack-to-flat edge, every surjection from the flat child back
to the slack child breaks an arc. One whole fiber has a broken outgoing
arc at every preimage, irrespective of the sizes of the two children. -/
theorem broken_fiber {q E S T p z b} (law : RealDual q E S 1 p) (bs : b∈S)
    (low : realCol q E S p b<1) (unit : realMass T z=1) (pos : ∀i∈T,0<z i)
    (rows : ∀i∈T,realRow q E T z i=1) (f : ℕ→ℕ) (maps : ∀i∈T,f i∈S)
    (onto : ∀u∈S,∃t∈T,f t=u) :
    ∃u∈S,(∃t∈T,f t=u) ∧ ∀t∈T,f t=u → ∃j∈T,E t j=true ∧ E u (f j)=false := by
  classical
  let w := fun v => ∑i∈T.filter (fun j => f j=v),z i
  have nonneg (u) : 0≤w u := sum_nonneg (fun _ hi => (pos _ (mem_filter.mp hi).1).le)
  have atom {t u} (tt : t∈T) (atU : f t=u) : z t≤w u := single_le_sum
    (fun _ hi => (pos _ (mem_filter.mp hi).1).le) (mem_filter.mpr ⟨tt,atU⟩)
  have massEq : realMass S w=1 := (sum_fiberwise_of_maps_to maps z).trans unit
  obtain ⟨δ,dp,probe⟩ := margin law bs low
  obtain ⟨u,us,light⟩ := probe w (fun i _ => nonneg i)
  obtain ⟨k,kt,fk⟩ := onto b bs
  have gain := mul_pos dp ((pos k kt).trans_le (atom kt fk))
  refine ⟨u,us,onto u us,?_⟩
  intro t tt ft
  by_contra! all
  have heads (j) (jh : j∈outN E T t) : f j∈outN E S u := by
    obtain ⟨jt,edge⟩ := mem_outN.mp jh
    exact mem_outN.mpr ⟨maps j jt,by cases e : E u (f j) <;> simp_all⟩
  have sumHeads : (∑j∈outN E T t,z j)≤∑i∈outN E S u,w i := by
    rw [←sum_fiberwise_of_maps_to heads z]
    apply sum_le_sum
    intro i _
    apply sum_le_sum_of_subset_of_nonneg
    · exact fun j hj => mem_filter.mpr ⟨(mem_outN.mp (mem_filter.mp hj).1).1,(mem_filter.mp hj).2⟩
    · exact fun j hj _ => (pos j (mem_filter.mp hj).1).le
  have outEq (L : Finset ℕ) (a : ℕ→ℝ) (i) : realOutW E L a i=∑j∈outN E L i,a j := by
    simp only [realOutW,outN,sum_filter]
  have cmp := add_le_add (atom tt ft) (mul_le_mul_of_nonneg_left sumHeads (Nat.cast_nonneg q : (0:ℝ)≤q))
  have tgt := rows t tt
  rw [realRow,outEq] at tgt light
  rw [massEq] at light
  linarith

theorem on_edge {F q E V} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (cycles : ∀M∈F,ShenCycleSuccessor.Cycle E V q M)
    {raw : PairedFamilyLoop.State F → ℕ→ℝ} (laws : ∀s,RealDual q E (V\gone s) 1 (raw s))
    {a d : PairedFamilyLoop.State F} (slack : Slack q E V raw a) (flat : Tight q E V raw d) :
    let S := V\gone a
    let T := V\gone d
    ∀f : ℕ→ℕ,(∀i∈T,f i∈S) → (∀u∈S,∃t∈T,f t=u) →
      ∃u∈S,(∃t∈T,f t=u) ∧ ∀t∈T,f t=u → ∃j∈T,E t j=true ∧ E u (f j)=false := by
  classical
  intro S T
  have mem := mem_product.mp (mem_filter.mp d.property).1
  have ca := cycles _ mem.1
  have cb := cycles _ mem.2
  have ne : previous d≠current d := (mem_filter.mp d.property).2
  obtain ⟨v,vh⟩ := sdiff_nonempty.mpr (show ¬previous d⊆current d from fun sub =>
    ne (eq_of_subset_of_card_le sub (cb.size.trans ca.size.symm).le))
  have sub : T⊆V := sdiff_subset
  have proper : T⊂V := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq =>
    (mem_sdiff.mp (show v∈T from eq.symm ▸ ca.sub (mem_sdiff.mp vh).1)).2 vh⟩
  have live : T.Nonempty := by
    by_contra! zero
    have one := (laws d).normalized
    change realMass T (raw d)=1 at one
    simp [zero,realMass] at one
  obtain ⟨z,unit,pos,rows,_⟩ := FlatChildClosure.rigidity hq small (card_lt_card proper) (free.mono_set sub) live (laws d) flat
  obtain ⟨b,bs,lo⟩ := slack
  exact broken_fiber (laws a) bs lo unit pos rows

#print axioms broken_fiber
#print axioms on_edge

end LeanCH.BR.Closure.SlackPairOrbit
