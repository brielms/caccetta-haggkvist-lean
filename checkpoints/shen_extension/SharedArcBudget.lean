import checkpoints.shen_extension.SharedArcInduction

namespace LeanCH.BR.Closure.SharedArcBudget
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier

/-- For a fixed old certificate the per-arc tests are necessary and sufficient.
A single cycle adds at most one incoming arc at each head. -/
theorem fits_iff {D V q F B} (cb : Cycle D V q B) {p} (hp : RealDual q (graph D F) V 1 p) :
    RealDual q (graph D (insert B F)) V 1 p ↔
      ∀u∈B,∀v∈B,D u v=true → graph D F u v=false → realCol q (graph D F) V p v+q*p u≤1 := by
  classical
  constructor
  · intro after u ub v vb uv missing
    have hit : v∈targets D V F B := mem_filter.mpr ⟨cb.sub vb,vb,u,ub,uv,missing⟩
    obtain ⟨i,ib,_,iv,_,eq⟩ := (column (q:=q) (F:=F) cb p (cb.sub vb)).2 hit
    have one : (inN D B v).card≤1 := (cb.incoming v vb).le
    obtain rfl : i=u := card_le_one.mp one _ (mem_inN.mpr ⟨ib,iv⟩) _ (mem_inN.mpr ⟨ub,uv⟩)
    exact eq ▸ after.columns v (cb.sub vb)
  · intro fits
    refine ⟨hp.nonneg,hp.normalized,fun v vv => ?_⟩
    have law := column (q:=q) (F:=F) cb p vv
    by_cases hit : v∈targets D V F B
    · obtain ⟨i,ib,vb,iv,miss,eq⟩ := law.2 hit
      rw [eq]
      exact fits i ib v vb iv miss
    · rw [law.1 hit]
      exact hp.columns v vv

#print axioms fits_iff

/-- For every old dual, the added head with the largest new column must
carry the entire strict margin after rescaling by the total mass of all
changed heads. The same positive child weights work for every old dual. -/
theorem gap {q n} (X : Model q n) (_hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (native : F⊆family X) (spans : support F=X.V) (step : Boundary X F B) (old : SmallRow q (graph X.D F) X.V)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) :
    let E := graph X.D F
    let G := graph X.D (insert B F)
    let T := targets X.D X.V F B
    ∃x : ℕ→ℝ,∃c : ℝ,1<c ∧ realMass X.V x=1 ∧ (∀v∈X.V,0<x v) ∧
      (∀v∈X.V,realRow q G X.V x v=c) ∧ 0<realMass T x ∧ realMass T x<1 ∧ c-1≤realMass T x ∧
      ∀p,RealDual q E X.V 1 p → ∃u∈B,∃v∈T,X.D u v=true ∧ E u v=false ∧
        c < realCol q E X.V p v+q*p u ∧
        c-1 ≤ realMass T x * (realCol q E X.V p v+q*p u-1) := by
  classical
  intro E G T
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have free := PrivateArcEndpoints.graph_free X (insert B F)
  obtain ⟨w,wn,_,hi⟩ := strict_witness_of_not_smallRow bad
  obtain ⟨a,_,k,kh,ap,_,am,_,ar,_⟩ := strict_pair_of_proper_smallRow (small.induced free) X.live w wn hi
  let x := fun v => (a v:ℝ)
  let c := (k:ℝ)
  have high : 1<c := by dsimp [c]; exact_mod_cast kh
  have xm : realMass X.V x=1 := by rw [realMass_rat,am]; norm_num
  have xp (v) (vv : v∈X.V) : 0<x v := by dsimp [x]; exact_mod_cast ap v vv
  have rows (v) (vv : v∈X.V) : realRow q G X.V x v=c := by rw [realRow_rat,ar v vv]
  have sub : T⊆X.V := filter_subset _ _
  obtain ⟨A,af,h,ah,j,aj,hj⟩ := step.2.2
  have jv := cb.sub (mem_inter.mp aj).2
  have kept : j∉T := by
    rintro jt
    obtain ⟨_,jb,i,ib,ij,miss⟩ := mem_filter.mp jt
    have one : (inN X.D B j).card≤1 := (cb.incoming j jb).le
    obtain rfl : i=h := card_le_one.mp one _ (mem_inN.mpr ⟨ib,ij⟩) _ (mem_inN.mpr ⟨(mem_inter.mp ah).2,hj⟩)
    have ed : E i j=true := active.mpr ⟨A,mem_col.mpr ⟨af,(mem_inter.mp ah).1,(mem_inter.mp aj).1,hj⟩⟩
    exact Bool.noConfusion (miss.symm.trans ed)
  have cap : realMass T x<1 := by
    have split := sum_sdiff sub (f:=x)
    have positive := sum_pos (s:=X.V\T) (fun v hv => xp v (mem_sdiff.mp hv).1) ⟨j,mem_sdiff.mpr ⟨jv,kept⟩⟩
    change realMass (X.V\T) x+realMass T x=realMass X.V x at split
    change 0<realMass (X.V\T) x at positive
    linarith
  have witness (p) (hp : RealDual q E X.V 1 p) :
      ∃v∈T,c<realCol q G X.V p v ∧ c-1≤realMass T x*(realCol q G X.V p v-1) := by
    let val := realCol q G X.V p
    obtain ⟨v,vv,top⟩ := X.V.exists_max_image val X.live
    have total : (∑z∈X.V,x z*val z)=c := by
      rw [←real_cross_rows]
      calc
        _ = ∑i∈X.V,p i*c := sum_congr rfl (fun i iv => by rw [rows i iv])
        _ = c := by rw [←sum_mul]; change realMass X.V p*c=c; rw [hp.normalized,one_mul]
    have maxHi : 1<val v := by
      by_contra! lo
      have cmp := sum_le_sum (s:=X.V) (fun z zv => mul_le_mul_of_nonneg_left ((top z zv).trans lo) (xp z zv).le)
      simp only [mul_one] at cmp
      change _≤realMass X.V x at cmp
      rw [xm,total] at cmp
      linarith
    have stable (z) (zv : z∈X.V) (nt : z∉T) : val z≤1 := by
      change realCol q (graph X.D (insert B F)) X.V p z≤1
      rw [(column (q:=q) (F:=F) cb p zv).1 nt]
      exact hp.columns z zv
    have vt : v∈T := by by_contra no; exact maxHi.not_ge (stable v vv no)
    have onT := sum_le_sum (s:=T) (fun z zt => mul_le_mul_of_nonneg_left (top z (sub zt)) (xp z (sub zt)).le)
    rw [←sum_mul] at onT
    have offT := sum_le_sum (s:=X.V\T) (fun z zd => mul_le_mul_of_nonneg_left
      (stable z (mem_sdiff.mp zd).1 (mem_sdiff.mp zd).2) (xp z (mem_sdiff.mp zd).1).le)
    simp only [mul_one] at offT
    have split := sum_sdiff sub (f:=fun z => x z*val z)
    have splitM := sum_sdiff sub (f:=x)
    change realMass (X.V\T) x + realMass T x=realMass X.V x at splitM
    change (∑z∈X.V\T,x z*val z)≤realMass (X.V\T) x at offT
    change (∑z∈T,x z*val z)≤realMass T x*val v at onT
    rw [total] at split
    rw [xm] at splitM
    have bound : c-1≤realMass T x*(val v-1) := by linarith only [split,splitM,onT,offT]
    have strict := mul_lt_mul_of_pos_right cap (sub_pos.mpr maxHi)
    exact ⟨v,vt,by linarith,bound⟩
  obtain ⟨p,dual⟩ := realDual_of_smallRow old X.live
  obtain ⟨v,vt,_,_⟩ := witness p dual
  have massFloor : c-1≤realMass T x := by
    obtain ⟨z,zt,_,bound⟩ := witness p dual
    obtain ⟨u,ub,_,_,_,eq⟩ := (column (q:=q) (F:=F) cb p (sub zt)).2 zt
    have uv := cb.sub ub
    obtain ⟨M,mf,um⟩ := mem_biUnion.mp (spans.symm ▸ uv : u∈support F)
    have cm : Cycle X.D X.V q M := (mem_filter.mp (native mf)).2
    obtain ⟨j,jh⟩ := card_pos.mp (show 0<(outN X.D M u).card by rw [cm.heads u um]; decide)
    obtain ⟨jm,uj⟩ := mem_outN.mp jh
    have oldArc : E u j=true := active.mpr ⟨M,mem_col.mpr ⟨mf,um,jm,uj⟩⟩
    have tail := (realCol_edge_floor (q:=q) p dual.nonneg uv (cm.sub jm) oldArc).trans (dual.columns j (cm.sub jm))
    have limit : realCol q G X.V p z-1≤1 := by rw [eq]; linarith [dual.columns z (sub zt)]
    have nonneg : 0≤realMass T x := sum_nonneg (fun i it => (xp i (sub it)).le)
    exact bound.trans (by simpa using mul_le_mul_of_nonneg_left limit nonneg)
  refine ⟨x,c,high,xm,xp,rows,sum_pos (fun i it => xp i (sub it)) ⟨v,vt⟩,cap,massFloor,?_⟩
  intro p hp
  obtain ⟨v,vt,strict,bound⟩ := witness p hp
  obtain ⟨u,ub,_,uv,miss,eq⟩ := (column (q:=q) (F:=F) cb p (sub vt)).2 vt
  exact ⟨u,ub,v,vt,uv,miss,eq ▸ strict,eq ▸ bound⟩

#print axioms gap
end LeanCH.BR.Closure.SharedArcBudget
