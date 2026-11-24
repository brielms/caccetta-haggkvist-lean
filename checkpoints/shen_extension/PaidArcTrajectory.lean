import checkpoints.shen_extension.ResidualRepairOrbit
import checkpoints.shen_extension.ClosedArcDrift

namespace LeanCH.BR.Closure.PaidArcTrajectory
open Finset Function Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor
open ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier PairedFamilyLoop FullFamilySchedule CycleSlotOrbit OpposedPairPrices
open CanonicalCycleLaw

def sees (E : CH.Digraph) (b y : ℕ) : ℝ := if E b y=true then 1 else 0

private theorem local_charge {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    (ne : A≠M) {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {x : ℕ→ℝ} {d : ℝ} (xp : ∀b∈V,0<x b) (dp : 0<d) (massK : ∀i : V,x i=d*∑b,K i b)
    (u : ℕ→ℝ) (nn : ∀b∈V\A,0≤u b) (norm : realMass (V\A) u=1)
    {y r} (ya : y∈A) (rm : r∈M) :
    let D := A\M
    let T := V\A
    let t := d/realMass D x
    let l := law K D t
    let h := price q E V (fun b => maskReal T u b-l b)
    x y*(h y-h r) ≤ ∑b∈V,x y*maskReal T u b*
      ((q:ℝ)*(sees E b y-sees E b r) - (if y∈D then t else 0)) := by
  classical
  intro D T t l h
  have tv : T⊆V := sdiff_subset
  have dv : D⊆V := sdiff_subset.trans a.sub
  have live : D.Nonempty := by
    by_contra! empty
    exact ne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp empty) (by rw [a.size,m.size]))
  have p := (two_levels hK dv (sum_pos (fun z hz => xp z (dv hz)) live) dp massK).2.2
  let v := maskReal T u
  have delta (z) (zv : z∈V) : h z=(v z+(q:ℝ)*realInW E V v z)-(1+(if z∈D then t else 0)) := by
    have lin : realInW E V (fun b => v b-l b) z=realInW E V v z-realInW E V l z := by
      unfold realInW
      rw [←sum_sub_distrib]
      exact sum_congr rfl (fun b _ => by cases E b z <;> simp)
    have pr : l z+(q:ℝ)*realInW E V l z=1+(if z∈D then t else 0) := by
      simpa only [price,ite_eq_left zv] using p z zv
    change (if z∈V then v z-l z else 0)+(q:ℝ)*realInW E V (fun b => v b-l b) z=_
    rw [ite_eq_left zv,lin]
    linarith only [pr]
  have y0 : v y=0 := ite_eq_right (fun h => (mem_sdiff.mp h).2 ya)
  have rn : 0≤v r := by dsimp [v,maskReal]; split_ifs with h; exact nn r h; exact le_rfl
  have no : r∉D := fun h => (mem_sdiff.mp h).2 rm
  have total : (∑b∈V,v b)=1 := (maskReal_mass tv u).trans norm
  have arcs (z) : (∑b∈V,v b*sees E b z)=realInW E V v z :=
    sum_congr rfl (fun b _ => by cases e : E b z <;> simp [sees,e])
  let z := if y∈D then t else 0
  have split (b) : x y*v b*((q:ℝ)*(sees E b y-sees E b r)-z)=
      x y*((q:ℝ)*(v b*sees E b y)-(q:ℝ)*(v b*sees E b r)-v b*z) := by ring
  change _ ≤ ∑b∈V,x y*v b*((q:ℝ)*(sees E b y-sees E b r)-z)
  simp_rw [split]
  rw [←mul_sum,sum_sub_distrib,sum_sub_distrib,←mul_sum,←mul_sum,arcs,arcs,←sum_mul,total,one_mul]
  rw [delta y (a.sub ya),delta r (m.sub rm),ite_eq_right no,y0]
  apply mul_le_mul_of_nonneg_left _ (xp y (a.sub ya)).le
  dsimp only [z]
  linarith only [rn]

/-- Some fixed actual row earns more on a closed label trajectory from losing
heads than it spends gaining heads, even after charging its own share of the
canonical baseline on every moving slot. -/
theorem with_child {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F x c} (sub : F⊆family X) (two : 2≤F.card) (pos : ∀z∈X.V,0<x z) (unit : mass X.V x=1)
    (high : 1<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c) :
    let E := graph X.D F
    let w := fun z => (x z : ℝ)
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (u : PairedFamilyLoop.State F → ℕ→ℝ),
      (∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a), E b r=false ∧ E b (send a r)=true ∧
        Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
      (∀a, FromChild q E X.V (previous a) (current a) (u a)) ∧
      (∀a, (∀b∈X.V\previous a,0≤u a b) ∧ realMass (X.V\previous a) (u a)=1) ∧
      ∃s : Slot go previous,∃k,∃b∈X.V, 0<k ∧ (lift go previous send)^[k] s=s ∧
        let charge := fun z : Slot go previous =>
          let a := z.1.val
          let D := previous a\current a
          w z.2*maskReal (X.V\previous a) (u a) b*
            ((q:ℝ)*(sees E b z.2-sees E b (send a z.2))-
              (if (z.2 : ℕ)∈D then ((c:ℝ)-1)/realMass D w else 0))
        let visit := fun i : ℕ => (lift go previous send)^[i] s
        let m := fun i : ℕ => w (visit i).2*maskReal (X.V\previous (visit i).1.val) (u (visit i).1.val) b
        (0<∑i∈range k,charge (visit i)) ∧
          (∃i∈range k,E b (visit (i+1)).2=true ∧ m i<m (i+1)) ∧
          ∃j∈range k,E b (visit (j+1)).2=false ∧ m (j+1)<m j := by
  classical
  intro E w
  obtain ⟨K,inv,go,send,u,mark,raw,probs,s,k,kpos,closed,bill⟩ :=
    ResidualRepairOrbit.on_family_with_child X hq small sub two pos unit high rows
  let step := lift go previous send
  let weight (z : Slot go previous) (b : ℕ) := w z.2*maskReal (X.V\previous z.1.val) (u z.1.val) b
  let score (z : Slot go previous) (b : ℕ) :=
    let a := z.1.val
    let D := previous a\current a
    weight z b*((q:ℝ)*(sees E b z.2-sees E b (send a z.2))-
        (if (z.2 : ℕ)∈D then ((c:ℝ)-1)/realMass D w else 0))
  have actual {C} (cf : C∈F) : ShenCycleSuccessor.Cycle E X.V q C := retain_cycle
    (show ShenCycleSuccessor.Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have massK := inverse_row_sum_of_equalizer inv x unit c rows
  have lower (z : Slot go previous) := by
    let a := z.1.val
    obtain ⟨mem,ne⟩ := mem_filter.mp a.property
    obtain ⟨af,mf⟩ := mem_product.mp mem
    have ca : ShenCycleSuccessor.Cycle E X.V q (previous a) := actual af
    have cm : ShenCycleSuccessor.Cycle E X.V q (current a) := actual mf
    have rm : (send a z.2 : ℕ)∈current a := (mark a).1 ▸ (send a z.2).property
    exact local_charge ca cm ne inv (x:=w) (fun i hi => by dsimp only [w]; exact_mod_cast pos i hi)
      (sub_pos.mpr (by exact_mod_cast high : (1:ℝ)<c)) massK (u a) (probs a).1 (probs a).2 z.2.property rm
  have large : 0<∑i∈range k,∑b∈X.V,score (step^[i] s) b :=
    lt_of_lt_of_le bill (sum_le_sum (fun i _ => lower (step^[i] s)))
  rw [sum_comm] at large
  have found : ∃b∈X.V,0<∑i∈range k,score (step^[i] s) b := by
    by_contra! no
    exact large.not_ge (sum_nonpos no)
  obtain ⟨b,bv,earned⟩ := found
  let visit := fun i : ℕ => step^[i] s
  let m := fun i => weight (visit i) b
  let head := fun i => E b (visit i).2
  let gone := fun i => previous (visit i).1.val\current (visit i).1.val
  let fee := fun i => if ((visit i).2 : ℕ)∈gone i then ((c:ℝ)-1)/realMass (gone i) w else 0
  have vk : visit k=visit 0 := closed
  have lives (i) : ((visit i).2 : ℕ)∈X.V :=
    (actual (mem_product.mp (mem_filter.mp (visit i).1.val.property).1).1).sub (visit i).2.property
  have xp (v) (hv : v∈X.V) : 0<w v := by dsimp only [w]; exact_mod_cast pos v hv
  have nn (i) (_ : i∈range k) : 0≤m i*fee i := by
    have law : 0≤maskReal (X.V\previous (visit i).1.val) (u (visit i).1.val) b := by
      unfold maskReal
      split_ifs with yes
      · exact (probs _).1 b yes
      · exact le_rfl
    apply mul_nonneg (mul_nonneg (xp _ (lives i)).le law)
    dsimp only [fee]
    split_ifs
    · apply div_nonneg (sub_nonneg.mpr (by exact_mod_cast high.le))
      exact sum_nonneg (fun z hz => (xp z ((actual (mem_product.mp (mem_filter.mp
        (visit i).1.val.property).1).1).sub (mem_sdiff.mp hz).1)).le)
    · exact le_rfl
  have nx (i) : (visit (i+1)).2.val=(send (visit i).1.val (visit i).2).val := by
    dsimp only [visit]
    rw [Function.iterate_succ_apply']
    rfl
  have ev (i) : head (i+1)=E b (send (visit i).1.val (visit i).2) := congrArg (E b) (nx i)
  have earned' : 0<∑i∈range k,m i*((q:ℝ)*((if head i=true then 1 else 0)-
      (if head (i+1)=true then 1 else 0))-fee i) := by
    simp_rw [ev]
    exact earned
  have facts := ClosedArcDrift.drift m fee head k (q:=(q:ℝ)) (by exact_mod_cast (show 0<q by omega))
    (congrArg (fun z => weight z b) vk) (congrArg (fun z : Slot go previous => E b z.2) vk) nn earned'
  exact ⟨go,send,u,mark,raw,probs,s,k,b,bv,kpos,closed,earned,facts.2⟩

theorem exists_paid {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F x c} (sub : F⊆family X) (two : 2≤F.card) (pos : ∀z∈X.V,0<x z) (unit : mass X.V x=1)
    (high : 1<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c) :
    let E := graph X.D F
    let w := fun z => (x z : ℝ)
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (u : PairedFamilyLoop.State F → ℕ→ℝ),
      (∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a), E b r=false ∧ E b (send a r)=true ∧
        Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
      (∀a, (∀b∈X.V\previous a,0≤u a b) ∧ realMass (X.V\previous a) (u a)=1) ∧
      ∃s : Slot go previous,∃k,∃b∈X.V, 0<k ∧ (lift go previous send)^[k] s=s ∧
        let charge := fun z : Slot go previous =>
          let a := z.1.val
          let D := previous a\current a
          w z.2*maskReal (X.V\previous a) (u a) b*
            ((q:ℝ)*(sees E b z.2-sees E b (send a z.2))-
              (if (z.2 : ℕ)∈D then ((c:ℝ)-1)/realMass D w else 0))
        let visit := fun i : ℕ => (lift go previous send)^[i] s
        let m := fun i : ℕ => w (visit i).2*maskReal (X.V\previous (visit i).1.val) (u (visit i).1.val) b
        (0<∑i∈range k,charge (visit i)) ∧
          (∃i∈range k,E b (visit (i+1)).2=true ∧ m i<m (i+1)) ∧
          ∃j∈range k,E b (visit (j+1)).2=false ∧ m (j+1)<m j := by
  obtain ⟨go,send,u,mark,_,probs,orbit⟩ := with_child X hq small sub two pos unit high rows
  exact ⟨go,send,u,mark,probs,orbit⟩

#print axioms with_child
#print axioms exists_paid
end LeanCH.BR.Closure.PaidArcTrajectory
