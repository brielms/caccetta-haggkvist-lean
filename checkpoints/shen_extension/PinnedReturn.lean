import checkpoints.shen_extension.CyclePortNative

namespace LeanCH.BR.Closure.PinnedReturn
open Finset BRq2 BRq3 BR45 WeightedSD ShenReturnCut CyclePortMatching FiniteHorizonHall

/-- A reservation at h is kept separately from the bijection on the
remaining slots. Together they give the full labelled routing. -/
def takeAt (a : ℕ→ℕ) (k m i : ℕ) := a i - if i=k then m else 0

private theorem take_sum (S : Finset ℕ) (a : ℕ→ℕ) {k m} (fit : m≤a k) :
    (∑i∈S,takeAt a k m i)+(if k∈S then m else 0)=∑i∈S,a i := by
  classical
  rw [←show (∑i∈S,if i=k then m else 0)=(if k∈S then m else 0) by simp,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases eq : i=k
  · subst i; simpa [takeAt] using Nat.sub_add_cancel fit
  · simp [takeAt,eq]

noncomputable def reachGraph (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) : CH.Digraph := by
  classical exact fun k h => decide (k∈ball E V h (q-1))

def Residual (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (y k h : ℕ) (w : ℕ→ℕ) (b m : ℕ) : Prop :=
  ∃f : ↥(slots (V.erase y) (takeAt (demand w b k) k m)) ≃
    ↥(slots (V.erase y) (takeAt (supply E w q y) h m)),
    ∀i,E y (f i).val.1=true ∧ i.val.1∈ball E V (f i).val.1 (q-1)

/-- A cut avoiding the reserved target is the only obstruction to extending
a prescribed block. The capacity and target-size guards are explicit. -/
theorem extend {q E V y k h w b m} (ku : k∈V.erase y) (hu : h∈V.erase y)
    (hit : k∈ball E V h (q-1))
    (fromFit : m≤demand w b k k) (toFit : m≤supply E w q y h)
    (total : (∑i∈V.erase y,demand w b k i)=∑j∈V.erase y,supply E w q y j)
    (hall : ∀B⊆V.erase y,(∑i∈B,demand w b k i)≤
      ∑j∈closedRows (reachGraph q E V) (V.erase y) B,supply E w q y j)
    (spare : ∀B⊆V.erase y,k∉B → h∈closedRows (reachGraph q E V) (V.erase y) B →
      (∑i∈B,w i)+m≤∑j∈closedRows (reachGraph q E V) (V.erase y) B,supply E w q y j) :
    Residual q E V y k h w b m := by
  classical
  let U := V.erase y
  let A := reachGraph q E V
  let d := demand w b k
  let s := supply E w q y
  have td := take_sum U d fromFit
  have ts := take_sum U s toFit
  simp only [U,ku,hu,ite_true] at td ts
  have eq : (∑i∈U,takeAt d k m i)=∑j∈U,takeAt s h m j := by dsimp [U,d,s] at *; omega
  have cuts (B : Finset ℕ) (sub : B⊆U) :
      (∑i∈B,takeAt d k m i)≤∑j∈closedRows A U B,takeAt s h m j := by
    let H := closedRows A U B
    have ld := take_sum B d fromFit
    have ls := take_sum H s toFit
    have base : (∑i∈B,d i)≤∑j∈H,s j := hall B sub
    change _≤∑j∈H,takeAt s h m j
    by_cases kb : k∈B
    · have hh : h∈H := mem_union_right _ (mem_biUnion.mpr
        ⟨k,kb,mem_outN.mpr ⟨hu,decide_eq_true hit⟩⟩)
      simp only [kb,hh,ite_true] at ld ls
      omega
    · have de : (∑i∈B,d i)=∑i∈B,w i := by simp [d,demand,sum_add_distrib,kb]
      by_cases hh : h∈H
      · have extra : (∑i∈B,w i)+m≤∑j∈H,s j := spare B sub kb hh
        simp only [kb,hh,ite_false,ite_true,add_zero] at ld ls
        omega
      · simp only [kb,hh,ite_false,add_zero] at ld ls
        omega
  obtain ⟨f,allowed⟩ := realize_of_cuts eq cuts
  refine ⟨f,fun i => ?_⟩
  have hu' := mem_slots_iff.mp (f i).property
  have ok : E y (f i).val.1=true := by
    by_contra no
    have z : takeAt s h m (f i).val.1=0 := by simp [takeAt,s,supply,no]
    exact (Nat.not_lt_zero _ (z ▸ hu'.2))
  refine ⟨ok,?_⟩
  rcases allowed i with same|arc
  · have iv := (mem_erase.mp (mem_slots_iff.mp i.property).1).2
    exact mem_ball.mpr ⟨iv,0,Nat.zero_le _,same.symm ▸ .refl _⟩
  · exact of_decide_eq_true arc

#print axioms extend
/-- The strict Hall margin pays the entire bonus plus one ordinary slot
on any prescribed compatible turn. A larger exact demand either extends
or names the proper target set that prevents it. -/
theorem on_source {q E V} {x : ℕ→ℚ} {c : ℚ} (hq : 2≤q) (high : 1<c)
    (small : SmallerSmallRow q V.card) (free : QFree E V q)
    (pos : ∀i∈V,0<x i) (xm : mass V x=1) (rows : ∀i∈V,WeightedSD.row q E V x i=c)
    {D b : ℕ} (dp : 0<D) (bonus : (b:ℚ)=D*(c-1)) {w : ℕ→ℕ} (scale : ∀i∈V,(w i : ℚ)=D*x i)
    (y) (yv : y∈V) (k) (ku : k∈V.erase y) (h) (hh : h∈outN E V y)
    (hit : k∈ball E V h (q-1)) :
    Residual q E V y k h w b (b+1) ∧
    ∀m,m≤w k+b → m≤q*w h →
      Residual q E V y k h w b m ∨
        ∃B⊆V.erase y,B.Nonempty ∧ k∉B ∧ h∈ports q E V y B ∧
          (∑i∈B,w i)+b < q*(∑i∈ports q E V y B,w i) ∧
          q*(∑i∈ports q E V y B,w i)<(∑i∈B,w i)+m := by
  classical
  let U := V.erase y
  let A := reachGraph q E V
  let d := demand w b k
  let s := supply E w q y
  have ed := (mem_outN.mp hh).2
  have hv := (mem_outN.mp hh).1
  have noloop := loopfree free (by omega : 1≤q) yv
  have hu : h∈U := mem_erase.mpr ⟨fun e => noloop (e ▸ ed),hv⟩
  have uv : U⊆V := erase_subset _ _
  have dr : (0:ℚ)<D := by exact_mod_cast dp
  have wp (i) (iv : i∈V) : 0<w i := by exact_mod_cast (scale i iv ▸ mul_pos dr (pos i iv) : (0:ℚ)<w i)
  have wm (B : Finset ℕ) (bv : B⊆V) : (↑(∑i∈B,w i) : ℚ)=D*mass B x := by
    rw [Nat.cast_sum,mass,mul_sum]
    exact sum_congr rfl fun i hi => scale i (bv hi)
  have load (B : Finset ℕ) : (∑i∈B,d i)=(∑i∈B,w i)+(if k∈B then b else 0) := by
    simp [d,demand,sum_add_distrib]
  have cap (B : Finset ℕ) : (∑i∈B,s i)=q*(∑i∈B.filter (fun h => E y h=true),w i) := by
    simp only [s,supply,sum_filter,mul_sum,mul_ite,mul_zero]
  have headU : U.filter (fun h => E y h=true)=outN E V y := by
    ext i
    simp only [U,mem_filter,mem_erase,mem_outN]
    exact ⟨fun t => ⟨t.1.2,t.2⟩,fun t => ⟨⟨fun e => noloop (e ▸ t.2),t.1⟩,t.2⟩⟩
  have portSet (B : Finset ℕ) (bu : B⊆U) :
      (closedRows A U B).filter (fun i => E y i=true)=ports q E V y B := by
    ext i
    constructor
    · intro mem
      obtain ⟨hc,edge⟩ := mem_filter.mp mem
      rcases mem_union.mp hc with ib|im
      · have iv := uv (bu ib)
        exact mem_filter.mpr ⟨mem_outN.mpr ⟨iv,edge⟩,i,ib,mem_ball.mpr ⟨iv,0,Nat.zero_le _,.refl _⟩⟩
      · obtain ⟨j,jb,arc⟩ := mem_biUnion.mp im
        have a := mem_outN.mp arc
        exact mem_filter.mpr ⟨mem_outN.mpr ⟨uv a.1,edge⟩,j,jb,of_decide_eq_true a.2⟩
    · intro mem
      obtain ⟨yh,j,jb,dist⟩ := mem_filter.mp mem
      have hd := mem_outN.mp yh
      have iu : i∈U := mem_erase.mpr ⟨fun e => noloop (e ▸ hd.2),hd.1⟩
      exact mem_filter.mpr ⟨mem_union_right _ (mem_biUnion.mpr ⟨j,jb,mem_outN.mpr ⟨iu,decide_eq_true dist⟩⟩),hd.2⟩
  have portCap (B : Finset ℕ) (bu : B⊆U) :
      (∑j∈closedRows A U B,s j)=q*(∑j∈ports q E V y B,w j) := by rw [cap,portSet B bu]
  have total : (∑i∈U,d i)=∑i∈U,s i := by
    rw [load,cap,headU,ite_eq_left ku]
    have mu : mass U x+x y=1 := (sum_erase_add V x yv).trans xm
    have row := rows y yv
    have out : outW E V x y=mass (outN E V y) x := by simp only [outW,mass,outN,sum_filter]
    rw [WeightedSD.row,out] at row
    have eq : (↑(∑i∈U,w i):ℚ)+(b:ℚ)=(q:ℚ)*↑(∑i∈outN E V y,w i) := by
      rw [wm U uv,bonus,wm _ (show outN E V y⊆V from filter_subset _ _)]
      linear_combination D*mu-D*row
    exact_mod_cast eq
  have strict (B : Finset ℕ) (bu : B⊆U) (live : B.Nonempty) (ne : B≠U) :
      (∑i∈B,w i)+b<q*(∑i∈ports q E V y B,w i) := by
    have sh := (capacity (c:=(c:ℝ)) (z:=fun i => (x i : ℝ)) hq (by exact_mod_cast high) small free
      (by rw [realMass_rat,xm]; norm_num) (fun i hi => by exact_mod_cast pos i hi)
      (fun i hi => by rw [realRow_rat,rows i hi]) yv bu live).2 ne
    simp only [realMass_rat] at sh
    have r : mass B x+(c-1)<(q:ℚ)*mass (ports q E V y B) x := by exact_mod_cast sh
    have a : (↑(∑i∈B,w i):ℚ)+(b:ℚ)<(q:ℚ)*↑(∑i∈ports q E V y B,w i) := by
      rw [wm B (bu.trans uv),bonus,wm (ports q E V y B) (fun j hj => (mem_outN.mp (mem_filter.mp hj).1).1)]
      nlinarith only [mul_lt_mul_of_pos_left r dr]
    exact_mod_cast a
  have hall (B : Finset ℕ) (bu : B⊆U) : (∑i∈B,d i)≤∑j∈closedRows A U B,s j := by
    by_cases empty : B=∅
    · simp [empty]
    by_cases all : B=U
    · rw [all,total]
      exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun i _ _ => Nat.zero_le (s i))
    rw [load,portCap B bu]
    have a := strict B bu (nonempty_iff_ne_empty.mpr empty) all
    split_ifs <;> omega
  have decision (m) (mk : m≤w k+b) (mh : m≤q*w h) := by
    classical
    let Bad := ∃B⊆U,B.Nonempty ∧ k∉B ∧ h∈ports q E V y B ∧
      (∑i∈B,w i)+b<q*(∑i∈ports q E V y B,w i) ∧ q*(∑i∈ports q E V y B,w i)<(∑i∈B,w i)+m
    show Residual q E V y k h w b m ∨ Bad
    by_cases bad : Bad
    · exact Or.inr bad
    left
    apply extend ku hu hit (by simpa [demand] using mk) (by simpa [supply,ed] using mh) total hall
    intro B bu kb hr
    have hp : h∈ports q E V y B := portSet B bu ▸ mem_filter.mpr ⟨hr,ed⟩
    obtain ⟨_,j,jb,_⟩ := mem_filter.mp hp
    have live : B.Nonempty := ⟨j,jb⟩
    have ne : B≠U := fun e => kb (e.symm ▸ ku)
    rw [portCap B bu]
    exact le_of_not_gt (fun fail => bad ⟨B,bu,live,kb,hp,strict B bu live ne,fail⟩)
  refine ⟨?_,decision⟩
  have atom := strict_atom_floor_of_proper hq free (small.induced free) x (fun i hi => (pos i hi).le)
    c (xm ▸ high) (fun i hi => (rows i hi).ge) h hv
  rw [xm] at atom
  have bb : b<q*w h := by
    have cmp : (b:ℚ)<(q:ℚ)*w h := by
      rw [bonus,scale h hv]
      nlinarith only [mul_lt_mul_of_pos_left atom dr,mul_pos dr (pos h hv)]
    exact_mod_cast cmp
  have fits : b+1≤w k+b := by have := wp k (uv ku); omega
  rcases decision (b+1) fits (by omega) with ok|⟨B,_,_,_,_,lo,hi⟩
  · exact ok
  · omega

#print axioms on_source
end LeanCH.BR.Closure.PinnedReturn
