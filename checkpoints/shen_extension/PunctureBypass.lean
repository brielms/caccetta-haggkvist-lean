import checkpoints.shen_extension.AllCutoffPacketEscape
import checkpoints.shen_extension.DeleteRepairUnlock

namespace LeanCH.BR.Closure.PunctureBypass
open Finset BRq2 BRq3 BR45 DeleteRepair ShenCycleSuccessor ShenPrimeTransition ShortestCycleWeights

/-- Replace all two-edge paths through t by their direct arcs on the
remaining labels. Absence of a boundary cycle through t makes the entire
rectangle safe simultaneously. -/
theorem safe {D W q t} (hq : 2≤q) (free : QFree D W q) (tw : t∈W)
    (absent : ¬∃C,Cycle D W q C ∧ t∈C) :
    let U := W.erase t
    QFree (repair D (inN D U t) (fun _ => outN D U t)) U q := by
  classical
  intro U
  apply repair_qfree (free.mono_set (erase_subset _ _))
  intro p _ y yh x xp k bound path
  have yc := mem_outN.mp yh
  have xc := mem_inN.mp xp
  have len : k=q-1 := by
    by_contra ne
    exact free t (k+1+1) (by omega) (by omega) (.step (mem_of_mem_erase yc.1) yc.2
      ((path.mono (erase_subset t W)).snoc tw xc.2))
  subst k
  have sub : U⊆W\{t} := fun z zu => mem_sdiff.mpr ⟨mem_of_mem_erase zu,by simpa using (mem_erase.mp zu).1⟩
  obtain ⟨C,c,_,tc,_⟩ := marked_cycle hq free tw (mem_of_mem_erase yc.1) xc.2 yc.2 (path.mono sub)
  exact absent ⟨C,c,tc⟩

private def headMass (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℕ) (i : ℕ) :=
  ∑x∈V, if D i x=true then w x else 0

/-- The exact amount deleted from the total is q*w(h). All parents of t
receive the entire previously missing head set of t plus any redeposit.
This comparison uses the bounded, integral minimality of the actual source. -/
theorem cannot_pay {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h)
    (absent : ¬∃C,Cycle X.D (X.V.erase h) q C ∧ t∈C)
    (missing : ∀p∈(X.V.erase h).erase t,X.D p t=true →
      ∀y∈outN X.D ((X.V.erase h).erase t) t,X.D p y=false)
    (heads : (q-1)*X.weights h≤∑y∈outN X.D ((X.V.erase h).erase t) t,X.weights y)
    (heavy : (q-1)*X.weights h≤X.weights t) : False := by
  classical
  let W := X.V.erase h
  let U := W.erase t
  let H := outN X.D U t
  let c := (q-1)*X.weights h
  let d := X.weights t-c
  have hpos : 0<c := Nat.mul_pos (by omega) (X.positive h hv)
  obtain ⟨y,yh⟩ : H.Nonempty := by
    by_contra! empty
    have zero : H=∅ := not_nonempty_iff_eq_empty.mp (by simpa using empty)
    change c≤∑z∈H,X.weights z at heads
    rw [zero,sum_empty] at heads
    omega
  have yu : y∈U := (mem_outN.mp yh).1
  let w := fun z => X.weights z+(if z=y then d else 0)
  let E := repair X.D (inN X.D U t) (fun _ => H)
  have uv : U⊆X.V := (erase_subset _ _).trans (erase_subset _ _)
  have dsum : (∑z∈U,w z)=(∑z∈U,X.weights z)+d := by simp [w,sum_add_distrib,yu]
  have total (f : ℕ→ℕ) : (∑z∈U,f z)+f t+f h=∑z∈X.V,f z := by
    rw [sum_erase_add W f tw,sum_erase_add X.V f hv]
  have cm : c+X.weights h=q*X.weights h := by
    dsimp [c]; rw [←Nat.succ_mul]; congr 1; omega
  have dec : d+c=X.weights t := Nat.sub_add_cancel heavy
  have paid : (∑z∈U,w z)+q*X.weights h=∑z∈X.V,X.weights z := by
    have e := total X.weights
    omega
  have strict (p) (pu : p∈U) : (∑z∈U,w z)<score q E U w p := by
    have old := nat_strict.mp X.strict p (uv pu)
    let O := outN X.D U p
    let G := outN E U p
    have inc : O⊆G := fun z zo => mem_outN.mpr ⟨(mem_outN.mp zo).1,repair_old (mem_outN.mp zo).2⟩
    have split := total (fun z => if X.D p z=true then X.weights z else 0)
    have orig : (∑z∈O,X.weights z)+(if X.D p t=true then X.weights t else 0)+
        (if X.D p h=true then X.weights h else 0)=headMass X.D X.V X.weights p := by
      simpa only [O,outN,headMass,sum_filter] using split
    have target : score q E U w p=w p+q*(∑z∈G,w z) := by simp only [G,score,outN,sum_filter]
    have hp : (if X.D p h=true then X.weights h else 0)≤X.weights h := by split <;> omega
    have retained : headMass X.D X.V X.weights p≤(∑z∈G,w z)+X.weights h := by
      by_cases pt : X.D p t=true
      · have pp : p∈inN X.D U t := mem_inN.mpr ⟨pu,pt⟩
        have more : H⊆G := fun z zh => mem_outN.mpr ⟨(mem_outN.mp zh).1,repair_new pp zh⟩
        have sep : Disjoint O H := disjoint_left.mpr (fun z zo zh => by
          have yes := (mem_outN.mp zo).2
          rw [missing p pu pt z zh] at yes; contradiction)
        have lower := sum_le_sum_of_subset_of_nonneg (union_subset inc more) (f:=X.weights) (by intros; omega)
        rw [sum_union sep] at lower
        have splitw : (∑z∈G,w z)=(∑z∈G,X.weights z)+d := by simp [w,sum_add_distrib,more yh]
        change c≤∑z∈H,X.weights z at heads
        simp only [pt,ite_true] at orig
        omega
      · have lower := sum_le_sum_of_subset_of_nonneg inc (f:=X.weights) (by intros; omega)
        have grow := sum_le_sum (s:=G) (fun i _ => (show X.weights i≤w i from Nat.le_add_right _ _))
        simp [pt] at orig
        omega
    change _ < X.weights p+q*headMass X.D X.V X.weights p at old
    have gain := Nat.mul_le_mul_left q retained
    rw [Nat.mul_add] at gain
    rw [target]
    have wp : X.weights p≤w p := Nat.le_add_right _ _
    omega
  have child := X.minimal E U w ⟨y,yu⟩ (safe hq (X.free.mono_set (erase_subset h X.V)) tw absent)
    (fun z zu => (X.positive z (uv zu)).trans_le (Nat.le_add_right _ _))
    ((show (∑z∈U,w z)≤∑z∈X.V,X.weights z by omega).trans X.bounded) (nat_strict.mpr strict)
  exact (lt_of_le_of_lt (card_le_card (erase_subset t W)) (card_erase_lt_of_mem hv)).not_ge child

#print axioms safe
#print axioms cannot_pay
end LeanCH.BR.Closure.PunctureBypass
