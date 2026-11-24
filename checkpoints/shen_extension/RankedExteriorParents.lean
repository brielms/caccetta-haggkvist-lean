import checkpoints.shen_extension.FreshMenuExitRules
import checkpoints.shen_extension.DeleteRepairUnlock

namespace LeanCH.BR.RankedExteriorParents
open Finset BRq2 BRq3 BR45 BRsub WeightedSD Closure
open Closure.LabelledLeakageCapacity

/-- A row with greater loss on a deleted bank has a physical head there
    missed by the comparator. The bank can have any size. -/
theorem distinguishing_head {D W w i e} (nonneg : ∀t∈W,0≤w t)
    (lt : outW D W w i < outW D W w e) : ∃t∈W, D e t=true ∧ D i t=false := by
  classical
  by_contra! none
  apply lt.not_ge
  apply sum_le_sum
  intro t ht
  cases he : D e t <;> cases hi : D i t <;> simp [nonneg t ht]
  exact False.elim (none t ht he hi)

/-- If the inner minimum pays, the failed pair bills are exactly the
    rows hitting both erased labels. The inner rows need only hit each
    erased label somewhere. Positivity, flat rows and the atom floor are
    required only in the forms appearing below. -/
theorem failing_iff_both {q : ℕ} {D V B w c a d b} (hq : 2≤q)
    (ad : a≠d) (sub : ({a,d}:Finset ℕ)⊆V) (au : 0≤w a) (du : 0≤w d)
    (flat : ∀i∈V,row q D V w i=c) (bs : B⊆V\{a,d})
    (hitA : ∃i∈B,D i a=true) (hitD : ∃i∈B,D i d=true)
    (floorA : c-mass V w<((q:ℚ)-1)*w a)
    (bb : b∈B) (least : ∀i∈B,row q D (V\{a,d}) w b≤row q D (V\{a,d}) w i)
    (paid : mass (V\{a,d}) w<row q D (V\{a,d}) w b) :
    ∀e∈V\{a,d},
      (((q:ℚ)-1)*(row q D (V\{a,d}) w b-mass (V\{a,d}) w)+row q D (V\{a,d}) w e
        <mass (V\{a,d}) w ↔ D e a=true ∧ D e d=true) := by
  classical
  let U := V\{a,d}
  let loss := outW D {a,d} w
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have one : (1:ℚ)≤q := by exact_mod_cast (show 1≤q by omega)
  have q1 := sub_nonneg.mpr one
  have fromB : B⊆V := bs.trans sdiff_subset
  have worst (i) (ib : i∈B) : loss i≤loss b := by
    have le := least i ib
    rw [FreshMenuExitRules.restricted_row sub (flat b (fromB bb)),
        FreshMenuExitRules.restricted_row sub (flat i (fromB ib))] at le
    exact (mul_le_mul_iff_right₀ qp).mp (by linarith only [le])
  obtain ⟨i,ib,ia⟩ := hitA
  obtain ⟨j,jb,jd⟩ := hitD
  have la : w a≤loss b := le_trans (b:=loss i) (by
    cases ed : D i d <;> simp [loss,outW,sum_pair ad,ia,ed,du]) (worst i ib)
  have nn (t) (ht : t∈({a,d}:Finset ℕ)) : 0≤w t := by
    rcases mem_insert.mp ht with rfl|single
    · exact au
    · simpa [mem_singleton.mp single] using du
  have split : mass U w+(w a+w d)=mass V w := by
    simpa [U,mass,sum_pair ad] using sum_sdiff sub (f:=w)
  intro e eu
  have ev := (mem_sdiff.mp eu).1
  have cb := FreshMenuExitRules.ranked_costs (q:=q) (by omega : 0<q) sub
    (flat b (fromB bb)) (flat e ev)
  rw [←not_le,cb.2,not_le]
  change c-mass U w < ((q:ℚ)-1)*loss b+loss e ↔ _
  constructor
  · intro under
    have higher : loss b<loss e := by
      have enough := cb.1.mp paid
      change (q:ℚ)*loss b<c-mass U w at enough
      linarith only [enough,under]
    obtain ⟨u,um,eu,ju⟩ := distinguishing_head nn ((worst j jb).trans_lt higher)
    obtain ⟨v,vm,ev,iv⟩ := distinguishing_head nn ((worst i ib).trans_lt higher)
    have ua : u=a := (mem_insert.mp um).resolve_right (by
      intro s
      rw [mem_singleton.mp s,jd] at ju
      contradiction)
    have vd : v=d := mem_singleton.mp ((mem_insert.mp vm).resolve_left (by
      intro eq
      rw [eq,ia] at iv
      contradiction))
    exact ⟨ua ▸ eu,vd ▸ ev⟩
  · rintro ⟨ea,ed⟩
    have he : loss e=w a+w d := by simp [loss,outW,sum_pair ad,ea,ed]
    rw [he]
    linarith only [split,floorA,mul_le_mul_of_nonneg_left la q1]

/-- Both inner witnesses on an arbitrary enlarged head bank. Separation
    supplies a parent of the dropped label that misses the root. -/
theorem marked_inner_separation {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    {a d keep M} (av : a∈X.V) (dp : d∈inN X.D X.V a) (kp : keep∈inN X.D X.V a)
    (km : keep∈M) (ms : M⊆X.V\{a,d}) :
    let B := ballSet X.D (X.V\{a,d}) (outN X.D X.V a ∪ M) (q-2)
    (∃i∈B,X.D i a=true) ∧ (∃j∈B,X.D j d=true ∧ X.D j a=false) := by
  intro B
  obtain ⟨dv,da⟩ := mem_inN.mp dp
  have dr : d≠a := fun eq=>loopfree X.free (by omega) av (eq ▸ da)
  obtain ⟨j,jv,jd,ja⟩ := X.separated d dv a av dr.symm
  have jr : j∈region q X.D X.V a :=
    (saturated_region hq X.free X.sat av jv).mpr
      ⟨fun eq=>digonfree X.free (by omega) dv av da (eq ▸ jd),by simp [ja]⟩
  have cut : ({a,d}:Finset ℕ)⊆X.V\region q X.D X.V a :=
    insert_subset (mem_sdiff.mpr ⟨av,fun h=>((saturated_region hq X.free X.sat av av).mp h).1 rfl⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨dv,fun h=>((saturated_region hq X.free X.sat av dv).mp h).2 da⟩))
  have same := RankedMerge.ball_delete cut
  unfold region at jr
  rw [←same] at jr
  obtain ⟨t,tt,walk⟩ := mem_ballSet.mp jr
  exact ⟨⟨keep,mem_ballSet.mpr ⟨keep,mem_union_right _ km,self_mem_ball (ms km)⟩,(mem_inN.mp kp).2⟩,
    ⟨j,mem_ballSet.mpr ⟨t,mem_union_left _ tt,walk⟩,jd,ja⟩⟩

theorem marked_inner_hits {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    {a d keep M} (av : a∈X.V) (dp : d∈inN X.D X.V a) (kp : keep∈inN X.D X.V a)
    (km : keep∈M) (ms : M⊆X.V\{a,d}) :
    let B := ballSet X.D (X.V\{a,d}) (outN X.D X.V a ∪ M) (q-2)
    (∃i∈B,X.D i a=true) ∧ (∃j∈B,X.D j d=true) := by
  obtain ⟨first,j,jb,jd,_⟩ := marked_inner_separation X hq av dp kp km ms
  exact ⟨first,j,jb,jd⟩

/-- The two rows use the same flat allocation. Every extra head of e
    outside a's heads contributes its full weight to the missing bank. -/
theorem private_head_account {q D V w c a e} (fa : row q D V w a=c)
    (fe : row q D V w e=c) :
    (q:ℚ)*mass (outN D V a\outN D V e) w =
      w e-w a+q*mass (outN D V e\outN D V a) w := by
  rw [WeightedSD.row,outW_eq_mass] at fa fe
  have l := sum_inter_add_sum_sdiff (outN D V a) (outN D V e) w
  have r := sum_inter_add_sum_sdiff (outN D V e) (outN D V a) w
  rw [inter_comm (outN D V e)] at r
  unfold mass at *
  linear_combination fa - fe + (q:ℚ)*l - (q:ℚ)*r

/-- At a common parent outside the whole marked ball, each menu label it
    misses has an exact last-layer return in the punctured carrier. More
    generally the erased bank can be any subset of this parent's heads. -/
theorem exact_return {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    {W H e t} (erase : W⊆outN X.D X.V e) (tv : t∈X.V) (th : t∈H)
    (outside : e∈(X.V\W)\ballSet X.D (X.V\W) H (q-2)) (miss : X.D e t=false) :
    Walk X.D (X.V\W) t e (q-1) ∧ ∀k<q-1,¬Walk X.D X.V t e k := by
  obtain ⟨eu,off⟩ := mem_sdiff.mp outside
  have ev := (mem_sdiff.mp eu).1
  have avoid {k} (short : k≤q-1) (p : Walk X.D X.V t e k) :=
    DeleteRepair.near_deletion_avoided (R:=W) X.free (fun x hx=>
      ⟨1,le_rfl,by omega,Walk.step (outN_subset (erase hx)) (mem_outN.mp (erase hx)).2 (.refl _)⟩)
      p (by omega)
  have no (k) (short : k<q-1) (p : Walk X.D X.V t e k) : False :=
    off (mem_ballSet.mpr ⟨t,th,mem_ball.mpr ⟨eu,k,by omega,avoid short.le p⟩⟩)
  obtain ⟨_,k,le,p⟩ := mem_ball.mp (X.sat t tv e ev (by simp [miss]))
  have eq : k=q-1 := le_antisymm le (le_of_not_gt (fun h=>no k h p))
  exact ⟨eq ▸ avoid le p,no⟩

structure ExteriorTest (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (a d : ℕ)
    (M : Finset ℕ) (w : ℕ→ℚ) (b : ℕ) : Prop where
  exact_bill :
    let U := V\{a,d}
    let m := mass U w
    let ρ := row q D U w
    m<ρ b → ∀e∈U, (((q:ℚ)-1)*(ρ b-m)+ρ e<m ↔ D e a=true ∧ D e d=true)
  obstruction :
    let U := V\{a,d}
    let B := ballSet D U (outN D V a ∪ M) (q-2)
    let m := mass U w
    let ρ := row q D U w
    m<ρ b →
      (ρ b≤m ∨ ∃e∈U\B,((q:ℚ)-1)*(ρ b-m)+ρ e<m) →
      ∃e∈U\B,D e a=true ∧ D e d=true
  returns :
    let U := V\{a,d}
    let H := outN D V a ∪ M
    let B := ballSet D U H (q-2)
    ∀e∈U\B,D e a=true → D e d=true →
      ((q:ℚ)-1)*w a+w e+q*w d ≤ q*mass (outN D V a\outN D V e) w ∧
      ∀t∈H,D e t=false → Walk D U t e (q-1) ∧ ∀k<q-1,¬Walk D V t e k

@[aesop safe forward (immediate := [side,hq,small,pos,high,flat,unit,km,ms,bb,least])
  (rule_sets := [CHGraphFamilies])]
theorem replay {q n w c a keep d M b} {X : ShortestCycleWeights.Model q n}
    (side : FreshMenuExitRules.PricedParents X w a keep d) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card)
    (pos : ∀i∈X.V,0<w i) (high : 1<c) (flat : ∀i∈X.V,row q X.D X.V w i=c)
    (unit : mass X.V w=1) (km : keep∈M) (ms : M⊆X.V\{a,d})
    (bb : b∈ballSet X.D (X.V\{a,d}) (outN X.D X.V a ∪ M) (q-2))
    (least : ∀i∈ballSet X.D (X.V\{a,d}) (outN X.D X.V a ∪ M) (q-2),
      row q X.D (X.V\{a,d}) w b≤row q X.D (X.V\{a,d}) w i) :
    ExteriorTest q X.D X.V a d M w b := by
  obtain ⟨dv,da⟩ := mem_inN.mp side.second
  have ad : a≠d := fun eq=>loopfree X.free (by omega) side.root (eq.symm ▸ da)
  have hits := marked_inner_hits X hq side.root side.second side.first km ms
  have floor := strict_atom_floor_of_proper hq X.free (small.induced X.free)
    w (fun j jv=>(pos j jv).le) c (unit ▸ high) (fun j jv=>(flat j jv).ge) a side.root
  have bill := failing_iff_both hq ad (insert_subset side.root (singleton_subset_iff.mpr dv))
    (pos a side.root).le (pos d dv).le flat ballSet_subset hits.1 hits.2 floor bb least
  refine ⟨bill,?_,?_⟩
  · dsimp only
    intro paid bad
    rcases bad with low|⟨e,ee,low⟩
    · exact (paid.not_ge low).elim
    · exact ⟨e,ee,(bill paid e (mem_sdiff.mp ee).1).mp low⟩
  · dsimp only
    intro e ee ea ed
    have ev := (mem_sdiff.mp (mem_sdiff.mp ee).1).1
    have erase : ({a,d}:Finset ℕ)⊆outN X.D X.V e :=
      insert_subset (mem_outN.mpr ⟨side.root,ea⟩) (singleton_subset_iff.mpr (mem_outN.mpr ⟨dv,ed⟩))
    have excluded : ({a,d}:Finset ℕ)⊆outN X.D X.V e\outN X.D X.V a :=
      insert_subset (mem_sdiff.mpr ⟨mem_outN.mpr ⟨side.root,ea⟩,
        fun h=>loopfree X.free (by omega) side.root (mem_outN.mp h).2⟩)
        (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_outN.mpr ⟨dv,ed⟩,
          fun h=>digonfree X.free (by omega) dv side.root da (mem_outN.mp h).2⟩))
    have le := sum_le_sum_of_subset_of_nonneg (f:=w) excluded
      (fun j hj _=>(pos j (outN_subset (mem_sdiff.mp hj).1)).le)
    rw [sum_pair ad] at le
    constructor
    · rw [private_head_account (flat a side.root) (flat e ev)]
      change w a+w d≤mass _ w at le
      linarith only [mul_le_mul_of_nonneg_left le (Nat.cast_nonneg (α:=ℚ) q)]
    · intro t th miss
      have tv : t∈X.V := (mem_union.mp th).elim (fun ta=>outN_subset ta)
        (fun tm=>(mem_sdiff.mp (ms tm)).1)
      exact exact_return X hq erase tv th ee miss

#print axioms distinguishing_head
#print axioms failing_iff_both
#print axioms replay
end LeanCH.BR.RankedExteriorParents
