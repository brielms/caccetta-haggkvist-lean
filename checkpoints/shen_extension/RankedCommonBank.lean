import checkpoints.shen_extension.RankedExteriorParents

namespace LeanCH.BR.RankedCommonBank
open Finset BRq2 BRq3 BR45 BRsub WeightedSD Closure

def commonParents (D : CH.Digraph) (U : Finset ℕ) (a d : ℕ) :=
  U.filter (fun i=>D i a=true ∧ D i d=true)

private theorem loss_le_max {D w a d i} (ad : a≠d) (wa : 0≤w a)
    (miss : ¬(D i a=true ∧ D i d=true)) :
    outW D {a,d} w i ≤ max (w a) (w d) := by
  cases ha : D i a <;> cases hd : D i d <;>
    simp [outW,sum_pair ad,ha,hd] at miss ⊢
  exact Or.inl wa

/-- The restricted minimum depends only on whether the inner set
    contains a common parent, provided the two single hits are present.
    No reach, minimum degree, or induction hypothesis is needed. -/
theorem minimum_value {q D V B w c a d b} (qp : 0<q)
    (ad : a≠d) (sub : ({a,d}:Finset ℕ)⊆V) (wa : 0≤w a) (wd : 0≤w d)
    (flat : ∀i∈V,row q D V w i=c) (bs : B⊆V\{a,d}) (bb : b∈B)
    (ha : ∃i∈B,D i a=true) (hd : ∃j∈B,D j d=true)
    (least : ∀i∈B,row q D (V\{a,d}) w b≤row q D (V\{a,d}) w i) :
    let U := V\{a,d}
    let C := commonParents D U a d
    row q D U w b = c-(q:ℚ)*(if Disjoint B C then max (w a) (w d) else w a+w d) := by
  intro U C
  let L := outW D {a,d} w
  have pos : (0:ℚ)<q := by exact_mod_cast qp
  have sv : B⊆V := bs.trans sdiff_subset
  have worst (i) (ib : i∈B) : L i≤L b := by
    have le := least i ib
    rw [FreshMenuExitRules.restricted_row sub (flat b (sv bb)),
      FreshMenuExitRules.restricted_row sub (flat i (sv ib))] at le
    exact (mul_le_mul_iff_right₀ pos).mp (by linarith only [le])
  rw [FreshMenuExitRules.restricted_row sub (flat b (sv bb))]
  congr 2
  by_cases dis : Disjoint B C
  · simp only [dis,ite_true]
    apply le_antisymm (loss_le_max ad wa (fun hits=>disjoint_left.mp dis bb (mem_filter.mpr ⟨bs bb,hits⟩)))
    obtain ⟨i,ib,ia⟩ := ha
    obtain ⟨j,jb,jd⟩ := hd
    apply max_le
    · apply le_trans (b:=L i) _ (worst i ib)
      cases h : D i d <;> simp [L,outW,sum_pair ad,ia,h,wd]
    · apply le_trans (b:=L j) _ (worst j jb)
      cases h : D j a <;> simp [L,outW,sum_pair ad,jd,h,wa]
  · simp only [dis,ite_false]
    obtain ⟨i,ib,ic⟩ := not_disjoint_iff.mp dis
    obtain ⟨ia,id⟩ := (mem_filter.mp ic).2
    apply le_antisymm
    · cases ha : D b a <;> cases hd : D b d <;> simp [outW,sum_pair ad,ha,hd,wa,wd,add_nonneg wa wd]
    · exact (show w a+w d=L i by simp [L,outW,sum_pair ad,ia,id]).trans_le (worst i ib)

/-- Apply SmallRow again after deleting any marked bank on the same
    carrier and allocation. The surviving row pays the bank's mass
    and its own previous surplus through actual heads in that bank. -/
theorem second_cut {q D U K w} (sub : K⊆U) (live : (U\K).Nonempty)
    (nonneg : ∀i∈U\K,0≤w i) (small : SmallRow q D (U\K)) :
    ∃r∈U\K,row q D (U\K) w r≤mass (U\K) w ∧
      mass K w+(row q D U w r-mass U w)≤(q:ℚ)*outW D K w r := by
  obtain ⟨r,rr,low⟩ := small w nonneg live
  have same := FreshMenuExitRules.restricted_row (q:=q) (D:=D) (i:=r) (w:=w) sub rfl
  have split : mass (U\K) w+mass K w=mass U w := sum_sdiff sub
  exact ⟨r,rr,low,by linarith only [low,same,split]⟩

structure BankTest (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (a d : ℕ)
    (H : Finset ℕ) (radius : ℕ) (w : ℕ→ℚ) (c : ℚ) (b : ℕ) : Prop where
  tests :
    let U := V\{a,d}
    let B := ballSet D U H radius
    let C := commonParents D U a d
    let m := mass U w
    let ρ := row q D U w
    let g := c-m-q*max (w a) (w d)
    (m<ρ b ↔ 0<g ∧ Disjoint B C) ∧
    ((m<ρ b ∧ ∀e∈U\B,m≤((q:ℚ)-1)*(ρ b-m)+ρ e) ↔ 0<g ∧ C=∅) ∧
    ∃r∈U\C,row q D (U\C) w r≤mass (U\C) w ∧
      mass C w+g ≤ (q:ℚ)*outW D C w r ∧
      (m<ρ b → ballSet D (U\C) H radius=B ∧ ∀k<radius,r∉ballSet D U H k)

/-- A table on any ball, at any radius, whose inner witnesses see both
    marked labels. The second application of SmallRow keeps the labels of
    the surviving row and the bank to which it sends weight. -/
theorem on_ball {q D V H radius w c a d b} (hq : 2≤q) (ad : a≠d)
    (sub : ({a,d}:Finset ℕ)⊆V) (flat : ∀i∈V,row q D V w i=c) (wp : ∀i∈V,0<w i)
    (floorA : c-mass V w<((q:ℚ)-1)*w a)
    (ha : ∃i∈ballSet D (V\{a,d}) H radius,D i a=true)
    (hd : ∃i∈ballSet D (V\{a,d}) H radius,D i d=true ∧ D i a=false)
    (bb : b∈ballSet D (V\{a,d}) H radius)
    (least : ∀i∈ballSet D (V\{a,d}) H radius,row q D (V\{a,d}) w b≤row q D (V\{a,d}) w i)
    (small : SmallRow q D ((V\{a,d})\commonParents D (V\{a,d}) a d)) :
    BankTest q D V a d H radius w c b := by
  constructor
  intro U B C m ρ g
  have bs : B⊆U := ballSet_subset
  have us : U⊆V := sdiff_subset
  have cs : C⊆U := filter_subset _ _
  have wa := wp a (sub (mem_insert_self ..))
  have wd := wp d (sub (mem_insert_of_mem (mem_singleton_self _)))
  have q1 : (1:ℚ)≤q := by exact_mod_cast (show 1≤q by omega)
  have split : m+(w a+w d)=mass V w := by simpa [m,U,mass,sum_pair ad] using sum_sdiff sub (f:=w)
  obtain ⟨j,jb,jd,ja⟩ := hd
  have hit := (show ∃i∈B,D i d=true from ⟨j,jb,jd⟩)
  have val := minimum_value (by omega : 0<q) ad sub wa.le wd.le flat bs bb ha hit least
  change ρ b=c-q*(if Disjoint B C then max (w a) (w d) else w a+w d) at val
  have inner : m<ρ b ↔ 0<g ∧ Disjoint B C := by
    by_cases dis : Disjoint B C
    · simp only [dis,ite_true] at val
      simp only [dis,and_true,g,val]
      constructor <;> intro h <;> linarith only [h]
    · simp only [dis,ite_false] at val
      have neg : ρ b<m := by
        nlinarith only [val,split,floorA,mul_nonneg (sub_nonneg.mpr q1) wd.le]
      simp [dis,neg.not_gt]
  have pair := RankedExteriorParents.failing_iff_both hq ad sub wa.le wd.le flat bs ha hit floorA bb least
  refine ⟨inner,?_,?_⟩
  · constructor
    · rintro ⟨paid,all⟩
      obtain ⟨cheap,dis⟩ := inner.mp paid
      refine ⟨cheap,eq_empty_iff_forall_notMem.mpr (fun e ec=>?_)⟩
      have eb := fun (ib : e∈B)=>disjoint_left.mp dis ib ec
      exact ((pair paid e (cs ec)).mpr (mem_filter.mp ec).2).not_ge (all e (mem_sdiff.mpr ⟨cs ec,eb⟩))
    · rintro ⟨cheap,empty⟩
      have paid := inner.mpr ⟨cheap,by simp [empty]⟩
      refine ⟨paid,fun e ee=>le_of_not_gt (fun fails=>?_)⟩
      have ec : e∈C := mem_filter.mpr ⟨(mem_sdiff.mp ee).1,(pair paid e (mem_sdiff.mp ee).1).mp fails⟩
      simp [empty] at ec
  · have jc : j∉C := fun h=>Bool.noConfusion (ja.symm.trans (mem_filter.mp h).2.1)
    obtain ⟨r,rr,low,charge⟩ := second_cut cs ⟨j,mem_sdiff.mpr ⟨bs jb,jc⟩⟩
      (fun i ii=>(wp i (us (mem_sdiff.mp ii).1)).le) small
    obtain ⟨ru,off⟩ := mem_sdiff.mp rr
    have cap := loss_le_max (w:=w) ad wa.le (fun hits=>off (mem_filter.mpr ⟨ru,hits⟩))
    have valr := FreshMenuExitRules.restricted_row sub (flat r (us ru))
    have bill : mass C w+g ≤ (q:ℚ)*outW D C w r := by
      dsimp only [g,m,U]
      linarith only [charge,valr,mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℚ) q)]
    refine ⟨r,rr,low,bill,?_⟩
    intro paid
    obtain ⟨cheap,dis⟩ := inner.mp paid
    have extC : C⊆U\B := fun i ic=>mem_sdiff.mpr ⟨cs ic,fun ib=>disjoint_left.mp dis ib ic⟩
    have positive := add_pos_of_nonneg_of_pos (mass_nonneg (fun i ic=>(wp i (us (cs ic))).le)) cheap
    have someHead : (outN D C r).Nonempty := by
      by_contra! empty
      rw [outW_eq_mass,empty] at bill
      simp [mass] at bill
      exact positive.not_ge bill
    obtain ⟨e,er⟩ := someHead
    have ec := outN_subset er
    refine ⟨RankedMerge.ball_delete extC,?_⟩
    intro k before reached
    have near := outN_subset_ballSet_succ reached (mem_outN.mpr ⟨cs ec,(mem_outN.mp er).2⟩)
    exact (mem_sdiff.mp (extC ec)).2 (ballSet_mono before near)

@[aesop safe forward (immediate := [side,hq,small,pos,unit,high,flat,km,ms,bb,least])
  (rule_sets := [CHGraphFamilies])]
theorem replay {q n w c a keep d M b} {X : ShortestCycleWeights.Model q n}
    (side : FreshMenuExitRules.PricedParents X w a keep d) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (pos : ∀i∈X.V,0<w i)
    (unit : mass X.V w=1) (high : 1<c) (flat : ∀i∈X.V,row q X.D X.V w i=c)
    (km : keep∈M) (ms : M⊆X.V\{a,d})
    (bb : b∈ballSet X.D (X.V\{a,d}) (outN X.D X.V a ∪ M) (q-2))
    (least : ∀i∈ballSet X.D (X.V\{a,d}) (outN X.D X.V a ∪ M) (q-2),
      row q X.D (X.V\{a,d}) w b≤row q X.D (X.V\{a,d}) w i) :
    BankTest q X.D X.V a d (outN X.D X.V a ∪ M) (q-2) w c b := by
  have av := side.root
  obtain ⟨dv,da⟩ := mem_inN.mp side.second
  have ad : a≠d := fun eq=>loopfree X.free (by omega) av (eq.symm ▸ da)
  have hits := RankedExteriorParents.marked_inner_separation X hq av side.second side.first km ms
  have floor := strict_atom_floor_of_proper hq X.free (small.induced X.free) w
    (fun i iv=>(pos i iv).le) c (unit ▸ high) (fun i iv=>(flat i iv).ge) a av
  apply on_ball hq ad (insert_subset av (singleton_subset_iff.mpr dv)) flat pos floor
    hits.1 hits.2 bb least
  apply small.induced X.free _ (sdiff_subset.trans sdiff_subset)
  intro eq
  have lost := mem_sdiff.mp (eq ▸ av)
  exact (mem_sdiff.mp lost.1).2 (mem_insert_self ..)

#print axioms minimum_value
#print axioms second_cut
#print axioms replay
end LeanCH.BR.RankedCommonBank
