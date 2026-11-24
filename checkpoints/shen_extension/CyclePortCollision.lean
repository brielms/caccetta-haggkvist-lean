import checkpoints.shen_extension.CyclePortMatching

namespace LeanCH.BR.Closure.CyclePortCollision
open Finset BRq2 BRq3 BR45 WeightedSD ShenReturnCut CyclePortMatching

/-- After forgetting the copy number, the remaining two labels are the head
and the position inside one copy of its weight. -/
def position (w : ℕ→ℕ) (a : ℕ×ℕ) := (a.1,a.2 % w a.1)

private theorem pivot {E : CH.Digraph} {V : Finset ℕ} {w : ℕ→ℕ}
    (live : V.Nonempty) (wp : ∀i∈V,0<w i) :
    ∃y∈V,(∑h∈outN E V y,w h)≤∑k∈inN E V y,w k := by
  classical
  have balance : (∑i∈V,w i*(∑j∈outN E V i,w j))=∑j∈V,w j*(∑i∈inN E V j,w i) := by
    simp only [outN,inN,sum_filter,mul_sum,mul_ite,mul_zero]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by split_ifs <;> first | rfl | exact Nat.mul_comm _ _
  by_contra! lt
  have strict := sum_lt_sum (fun i hi => (Nat.mul_lt_mul_of_pos_left (lt i hi) (wp i hi)).le)
    (live.imp (fun i hi => ⟨hi,Nat.mul_lt_mul_of_pos_left (lt i hi) (wp i hi)⟩))
  exact strict.ne balance.symm

theorem collision {q E V x c} (hq : 2≤q) (high : (1:ℚ)<c) (free : QFree E V q)
    (xp : ∀i∈V,0<(x i : ℚ)) (xm : mass V x=1) (rows : ∀i∈V,WeightedSD.row q E V x i=c)
    {D b : ℕ} (dp : 0<D) (bp : 0<b) {w : ℕ→ℕ} (scale : ∀i∈V,(w i : ℚ)=D*x i) :
    ∃y∈V,(inN E V y).Nonempty ∧ ∀t∈inN E V y,
      (slots (outN E V y) w).card+b≤(slots (inN E V y) (demand w b t)).card ∧
      ∀f : ↥(slots (V.erase y) (demand w b t)) ≃ ↥(slots (V.erase y) (supply E w q y)),
      ∃i j,i≠j ∧ E i.val.1 y=true ∧ E j.val.1 y=true ∧ position w (f i).val=position w (f j).val := by
  classical
  have live : V.Nonempty := by
    by_contra! em
    simp [em,mass] at xm
  have wp (i) (hi : i∈V) : 0<w i := by
    have dk : (0:ℚ)<D := by exact_mod_cast dp
    exact_mod_cast (scale i hi ▸ mul_pos dk (xp i hi) : (0:ℚ)<w i)
  obtain ⟨y,yv,heavy⟩ := pivot (E:=E) live wp
  have ol : (outN E V y).Nonempty := by
    by_contra! em
    have r := rows y yv
    have out : outW E V x y=mass (outN E V y) x := by simp only [outW,mass,outN,sum_filter]
    have cap : x y≤mass V x := single_le_sum (fun i hi => (xp i hi).le) yv
    simp [WeightedSD.row,out,em,mass] at r
    linarith
  have il : (inN E V y).Nonempty := by
    by_contra! em
    have pos := sum_pos (fun i hi => wp i (mem_outN.mp hi).1) ol
    rw [em,sum_empty] at heavy
    exact pos.not_ge heavy
  refine ⟨y,yv,il,fun t ht => ?_⟩
  have count : (slots (outN E V y) w).card+b≤(slots (inN E V y) (demand w b t)).card := by
    simpa [slots_card_eq,demand,sum_add_distrib,ht] using Nat.add_le_add_right heavy b
  refine ⟨count,fun f => ?_⟩
  let S := slots (V.erase y) (demand w b t)
  let P := S.attach.filter (fun i => E i.val.1 y=true)
  let L := slots (inN E V y) (demand w b t)
  let R := slots (outN E V y) w
  have no : E y y≠true := fun ed => free y 1 (by omega) (by omega) (.step yv ed (.refl _))
  have setEq : P.image Subtype.val=L := by
    ext a
    rw [mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      have li := mem_slots_iff.mp i.property
      exact mem_slots_iff.mpr ⟨mem_inN.mpr ⟨(mem_erase.mp li.1).2,(mem_filter.mp hi).2⟩,li.2⟩
    · intro h
      obtain ⟨kin,lim⟩ := mem_slots_iff.mp h
      obtain ⟨kv,back⟩ := mem_inN.mp kin
      have mem : a∈S := mem_slots_iff.mpr ⟨mem_erase.mpr ⟨fun eq => no (eq ▸ back),kv⟩,lim⟩
      exact ⟨⟨a,mem⟩,mem_filter.mpr ⟨mem_attach _ _,back⟩,rfl⟩
  have cardP : P.card=L.card := by rw [←setEq,card_image_of_injective _ Subtype.val_injective]
  have lt : R.card<P.card := by change R.card+b≤L.card at count; omega
  let g := fun i : ↥S => position w (f i).val
  have maps (i) (_ : i∈P) : g i∈R := by
    obtain ⟨hv,lim⟩ := mem_slots_iff.mp (f i).property
    have ed : E y (f i).val.1=true := by
      by_contra bad
      simp [supply,bad] at lim
    exact mem_slots_iff.mpr ⟨mem_outN.mpr ⟨(mem_erase.mp hv).2,ed⟩,
      Nat.mod_lt _ (wp _ (mem_erase.mp hv).2)⟩
  obtain ⟨i,hi,j,hj,ne,eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (f:=g) lt maps
  exact ⟨i,j,ne,(mem_filter.mp hi).2,(mem_filter.mp hj).2,eq⟩

#print axioms collision
end LeanCH.BR.Closure.CyclePortCollision
