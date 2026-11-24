import checkpoints.shen_extension.FiniteHorizonHall
import checkpoints.shen_extension.TerminalTransport

namespace LeanCH.BR.Closure.CyclePortMatching
open Finset BRq2 BRq3 BR45 WeightedSD ShenReturnCut FiniteHorizonHall

private theorem scale {V : Finset ℕ} {x : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈V,0<x i) :
    ∃D b : ℕ,0<D ∧ 0<b ∧ (b:ℚ)=D*(c-1) ∧ ∃w : ℕ→ℕ,∀i∈V,(w i : ℚ)=D*x i := by
  classical
  obtain ⟨v,fresh⟩ := Infinite.exists_notMem_finset V
  let S := insert v V
  let a := fun i => if i=v then c-1 else x i
  let D := ∏i∈S,(a i).den
  let w := fun i => (a i).num.toNat * (∏j∈S.erase i,(a j).den)
  have dp : 0<D := prod_pos fun i _ => (a i).den_pos
  have all (i) (hi : i∈S) : (w i : ℚ)=D*a i := by
    have ap : 0≤a i := by
      rcases mem_insert.mp hi with rfl | h
      · simp [a,high.le]
      · simp [a,show i≠v from fun e => fresh (e ▸ h),(xp i h).le]
    have prod := mul_prod_erase S (fun j => (a j).den) hi
    change (↑((a i).num.toNat * _) : ℚ) = (↑(∏ j ∈ S, (a j).den) : ℚ) * a i
    rw [←prod,Nat.cast_mul,Nat.cast_mul,←Int.cast_natCast,Int.toNat_of_nonneg (Rat.num_nonneg.mpr ap)]
    have h := (div_eq_iff (show ((a i).den : ℚ)≠0 by exact_mod_cast (a i).den_ne_zero)).mp (a i).num_div_den
    linarith only [congrArg (fun t : ℚ => t * (∏j∈S.erase i,(a j).den : ℕ)) h]
  have bonus : (w v : ℚ)=D*(c-1) := by simpa [a] using all v (mem_insert_self v V)
  have dp' : (0:ℚ)<D := by exact_mod_cast dp
  have bp : (0:ℚ)<w v := bonus ▸ mul_pos dp' (sub_pos.mpr high)
  refine ⟨D,w v,dp,by exact_mod_cast bp,bonus,w,fun i hi => ?_⟩
  simpa [a,show i≠v from fun e => fresh (e ▸ hi)] using all i (mem_insert_of_mem hi)

def demand (w : ℕ→ℕ) (b t i : ℕ) := w i+if i=t then b else 0
def supply (E : CH.Digraph) (w : ℕ→ℕ) (q y h : ℕ) := if E y h then q*w h else 0

/-- All target slots are routed simultaneously, including the full surplus
at any prescribed target. Each chosen head is an actual first arc. -/
theorem matching {q E V} {x : ℕ→ℚ} {c : ℚ} (hq : 2≤q) (high : 1<c)
    (small : SmallerSmallRow q V.card) (free : QFree E V q)
    (xp : ∀i∈V,0<x i) (xm : mass V x=1) (rows : ∀i∈V,WeightedSD.row q E V x i=c) :
    ∃D b : ℕ,0<D ∧ 0<b ∧ (b:ℚ)=D*(c-1) ∧ ∃w : ℕ→ℕ,(∀i∈V,(w i : ℚ)=D*x i) ∧
      ∀y∈V,∀t∈V.erase y,∃f : ↥(slots (V.erase y) (demand w b t)) ≃ ↥(slots (V.erase y) (supply E w q y)),
      ∀i,E y (f i).val.1=true ∧ i.val.1∈ball E V (f i).val.1 (q-1) := by
  classical
  obtain ⟨D,b,dp,bp,bonus,w,each⟩ := scale high xp
  refine ⟨D,b,dp,bp,bonus,w,each,?_⟩
  intro y yv t tv
  let U := V.erase y
  let d := demand w b t
  let s := supply E w q y
  let A : CH.Digraph := fun k h => decide (k∈ball E V h (q-1))
  have uv : U⊆V := erase_subset _ _
  have dp' : (0:ℚ)<D := by exact_mod_cast dp
  have wm (K : Finset ℕ) (sub : K⊆V) : (↑(∑i∈K,w i) : ℚ)=D*mass K x := by
    rw [Nat.cast_sum,mass,mul_sum]
    exact sum_congr rfl fun i hi => each i (sub hi)
  have loads (B : Finset ℕ) : (∑i∈B,d i)=(∑i∈B,w i)+(if t∈B then b else 0) := by
    simp [d,demand,sum_add_distrib]
  have caps (B : Finset ℕ) : (∑i∈B,s i)=q*(∑i∈B.filter (fun h => E y h=true),w i) := by
    simp only [s,supply,sum_filter,mul_sum,mul_ite,mul_zero]
  have noloop : E y y=false := by
    cases e : E y y
    · rfl
    · exact (free y 1 (by omega) (by omega) (.step yv e (.refl _))).elim
  have heads : U.filter (fun h => E y h=true)=outN E V y := by
    ext h
    simp only [mem_filter,mem_outN,U,mem_erase]
    exact ⟨fun t => ⟨t.1.2,t.2⟩,fun t => ⟨⟨fun e => by simpa [e,noloop] using t.2,t.1⟩,t.2⟩⟩
  have total : (∑i∈U,d i)=∑i∈U,s i := by
    rw [loads,caps,heads,ite_eq_left tv]
    have m : mass U x+x y=1 := (sum_erase_add V x yv).trans xm
    have r := rows y yv
    change x y+(q:ℚ)*outW E V x y=c at r
    have out : outW E V x y=mass (outN E V y) x := by simp only [outW,mass,outN,sum_filter]
    rw [out] at r
    have scaled : ((∑i∈U,w i):ℚ)+(b:ℚ)=(q:ℚ)*((∑i∈outN E V y,w i):ℕ) := by
      rw [←Nat.cast_sum,wm U uv,bonus,wm (outN E V y) (fun i hi => (mem_outN.mp hi).1)]
      linear_combination D*m-D*r
    exact_mod_cast scaled
  have hall (K : Finset ℕ) (ks : K⊆U) : (∑i∈K,d i)≤∑i∈closedRows A U K,s i := by
    by_cases live : K.Nonempty
    · let P := ports q E V y K
      have ps : P⊆V := fun i hi => (mem_outN.mp (mem_filter.mp hi).1).1
      have into : P⊆(closedRows A U K).filter (fun h => E y h=true) := by
        intro h hi
        obtain ⟨edge,k,kk,hit⟩ := mem_filter.mp hi
        have hv := mem_outN.mp edge
        have hu : h∈U := mem_erase.mpr ⟨fun e => by simpa [e,noloop] using hv.2,hv.1⟩
        exact mem_filter.mpr ⟨mem_union_right _ (mem_biUnion.mpr
          ⟨k,kk,mem_outN.mpr ⟨hu,decide_eq_true hit⟩⟩),hv.2⟩
      have hc := (FiniteHorizonHall.capacity (c:=(c:ℝ)) (z:=fun i => (x i : ℝ)) hq
        (by exact_mod_cast high) small free (by rw [realMass_rat,xm]; norm_num)
        (fun i hi => by exact_mod_cast xp i hi) (fun i hi => by rw [realRow_rat,rows i hi]) yv ks live).1
      simp only [realMass_rat] at hc
      have rat : mass K x+(c-1)≤(q:ℚ)*mass P x := by exact_mod_cast hc
      have scaled : (↑(∑i∈K,w i) : ℚ)+(b:ℚ)≤(q:ℚ)*↑(∑i∈P,w i) := by
        rw [wm K (ks.trans uv),bonus,wm P ps]
        nlinarith only [mul_le_mul_of_nonneg_left rat dp'.le]
      have a : (∑i∈K,w i)+b≤q*(∑i∈P,w i) := by exact_mod_cast scaled
      rw [loads,caps]
      have fit := Nat.mul_le_mul_left q (sum_le_sum_of_subset_of_nonneg into (fun i _ _ => Nat.zero_le (w i)))
      split_ifs <;> omega
    · simp [not_nonempty_iff_eq_empty.mp live]
  obtain ⟨f,allowed⟩ := realize_of_cuts total hall
  refine ⟨f,fun i => ?_⟩
  have fs := mem_slots_iff.mp (f i).property
  have is := mem_slots_iff.mp i.property
  have ok : E y (f i).val.1=true := by
    by_contra no
    have zero : s (f i).val.1=0 := by simp [s,supply,no]
    exact (Nat.not_lt_zero _ (zero ▸ fs.2))
  refine ⟨ok,?_⟩
  rcases allowed i with eq|ed
  · exact mem_ball.mpr ⟨uv is.1,0,Nat.zero_le _,eq.symm ▸ .refl _⟩
  · exact of_decide_eq_true ed

#print axioms matching
/-- The same bijection assigns shortest-cycle witnesses simultaneously on
every incoming-arc slot, while still servicing all other target slots. -/
theorem on_family {q E V} {F : Finset (Finset ℕ)} {x : ℕ→ℚ} {c : ℚ} (hq : 2≤q)
    (high : 1<c) (small : SmallerSmallRow q V.card) (free : QFree E V q)
    (xp : ∀i∈V,0<x i) (xm : mass V x=1) (rows : ∀i∈V,WeightedSD.row q E V x i=c)
    (complete : ∀M,ShenCycleSuccessor.Cycle E V q M → M∈F) :
    ∃D b : ℕ,0<D ∧ 0<b ∧ (b:ℚ)=D*(c-1) ∧ ∃w : ℕ→ℕ,(∀i∈V,(w i : ℚ)=D*x i) ∧
      ∀y∈V,∀t∈V.erase y,∃f : ↥(slots (V.erase y) (demand w b t)) ≃ ↥(slots (V.erase y) (supply E w q y)),
      ∀i,E y (f i).val.1=true ∧ i.val.1∈ball E V (f i).val.1 (q-1) ∧
        (E i.val.1 y=true → ∃M∈F,i.val.1∈M ∧ y∈M ∧ (f i).val.1∈M) := by
  obtain ⟨D,b,dp,bp,bonus,w,scale,law⟩ := matching hq high small free xp xm rows
  refine ⟨D,b,dp,bp,bonus,w,scale,fun y yv t tv => ?_⟩
  obtain ⟨f,allowed⟩ := law y yv t tv
  refine ⟨f,fun i => ⟨(allowed i).1,(allowed i).2,fun ky => ?_⟩⟩
  have kv := (mem_erase.mp (mem_slots_iff.mp i.property).1).2
  have ov := (mem_erase.mp (mem_slots_iff.mp (f i).property).1).2
  obtain ⟨M,cm,km,ym,om⟩ := marked_of_port hq free yv (mem_outN.mpr ⟨ov,(allowed i).1⟩)
    (mem_inN.mpr ⟨kv,ky⟩) (allowed i).2
  exact ⟨M,complete M cm,km,ym,om⟩

#print axioms on_family
end LeanCH.BR.Closure.CyclePortMatching
