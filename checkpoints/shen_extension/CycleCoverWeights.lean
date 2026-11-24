import checkpoints.shen_extension.FlatOverlapDescent
import LeanCH.BR.BRDeficiencyRigidity

namespace LeanCH.BR.Closure.CycleCoverWeights
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor MarkedCyclePeeling

/-- If every arc is carried by a selected cycle through h, summation
over the phases of one such cycle contradicts a strict weighted source. -/
theorem common_false {q E V x h C} (hq : 2≤q) (free : QFree E V q) (cy : Cycle E V q C)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (through : ∀u∈V,∀v∈V,E u v=true → ∃M,Cycle E V q M ∧ h∈M ∧ u∈M ∧ v∈M) : False := by
  classical
  obtain ⟨phase,step,walk⟩ := FlatOverlapDescent.phases hq free through
  have inj : Set.InjOn phase (C : Set ℕ) := by
    intro u uc v vc eq
    by_contra ne
    obtain ⟨lo,hi,p,r⟩ := MandatoryExcursion.segments (by omega) free cy uc vc
    let k := MandatoryExcursion.span E V q u v
    change 1≤k at lo
    change k≤q+1 at hi
    have positive : q+1-k≠0 := by
      intro zero
      change Walk E C v u (q+1-k) at r
      rw [zero] at r
      cases r
      exact ne rfl
    have ph : phase v=phase u+(k:ℕ) := walk (p.mono cy.sub) (cy.sub uc)
    have kz : (k:ZMod (q+1))=0 := add_left_cancel (show phase u+(k:ℕ)=phase u+0 by simpa using ph.symm.trans eq.symm)
    have rem := (ZMod.natCast_eq_natCast_iff k 0 (q+1)).mp (by simpa using kz)
    change k%(q+1)=0%(q+1) at rem
    rw [Nat.mod_eq_of_lt (by omega),Nat.zero_mod] at rem
    omega
  let fiber (a : ZMod (q+1)) := V.filter (fun v => phase v=a)
  have bound (f : ℕ→ZMod (q+1)) (fi : Set.InjOn f (C : Set ℕ)) :
      (∑u∈C,mass (fiber (f u)) x)≤mass V x := by
    have dis : (C : Set ℕ).PairwiseDisjoint (fun u => fiber (f u)) := by
      intro u uc v vc ne
      apply disjoint_left.mpr
      intro t tu tv
      exact ne (fi uc vc ((mem_filter.mp tu).2.symm.trans (mem_filter.mp tv).2))
    unfold mass
    rw [← sum_biUnion dis]
    exact sum_le_sum_of_subset_of_nonneg (biUnion_subset.mpr (fun i _ => filter_subset _ _)) (fun i hi _ => xp i hi)
  have one := bound phase inj
  have two := bound (fun u => phase u+1) (fun u uc v vc eq => inj uc vc (add_right_cancel eq))
  have high (u) (uc : u∈C) :
      mass V x < mass (fiber (phase u)) x + q*mass (fiber (phase u+1)) x := by
    have own : x u≤mass (fiber (phase u)) x := single_le_sum (fun i hi => xp i (mem_filter.mp hi).1)
      (mem_filter.mpr ⟨cy.sub uc,rfl⟩)
    have sub : outN E V u⊆fiber (phase u+1) := fun v vh => mem_filter.mpr ⟨(mem_outN.mp vh).1,
      step u (cy.sub uc) v (mem_outN.mp vh).1 (mem_outN.mp vh).2⟩
    have dest : mass (outN E V u) x≤mass (fiber (phase u+1)) x :=
      sum_le_sum_of_subset_of_nonneg sub (fun i hi _ => xp i (mem_filter.mp hi).1)
    have hi := strict u (cy.sub uc)
    rw [WeightedSD.row,outW_eq_mass] at hi
    exact hi.trans_le (add_le_add own (mul_le_mul_of_nonneg_left dest (Nat.cast_nonneg q)))
  have nonempty : C.Nonempty := card_pos.mp (by rw [cy.size]; omega)
  have total := sum_lt_sum_of_nonempty nonempty high
  rw [sum_const,nsmul_eq_mul,cy.size,sum_add_distrib,←mul_sum] at total
  push_cast at total
  nlinarith only [one,mul_le_mul_of_nonneg_left two (Nat.cast_nonneg q : (0:ℚ)≤q),total]

/-- A twofold incidence cover gives this integer column certificate.
Equality in the degree-two deficiency bound handles the last possible unit. -/
theorem dual_two {q E V} (hq : 2≤q) (free : QFree E V q) (live : V.Nonempty)
    (minOut : ∀u∈V,1≤(outN E V u).card)
    (incoming : ∀v∈V,(∑u∈inN E V v,(1+(2-(outN E V u).card)))=2) :
    let y := fun u => ((1+(2-(outN E V u).card) : ℕ) : ℚ)
    ∀v∈V,col q E V y v≤mass V y := by
  classical
  intro y v vv
  have form : inW E V y v=2 := by
    change outW (fun a b => E b a) V y v=2
    rw [outW_eq_mass]
    change (∑u∈inN E V v,((1+(2-(outN E V u).card) : ℕ) : ℚ))=2
    rw [←Nat.cast_sum,incoming v vv]
    norm_num
  let total := V.card + ∑u∈V,(2-(outN E V u).card)
  have ym : mass V y=(total:ℕ) := by
    dsimp only [mass,y,total]
    push_cast
    rw [sum_add_distrib]
    simp
  have lo := BRsGen.degree_two_deficiency (by omega : 1≤q) free minOut live
  change 2*q+1≤total at lo
  rw [WeightedSD.col,form,ym]
  change (((1+(2-(outN E V v).card)):ℕ):ℚ)+(q:ℚ)*2≤(total:ℕ)
  exact_mod_cast (show 1+(2-(outN E V v).card)+q*2≤total from by
    by_cases reg : OutEq 2 E V
    · rw [reg v vv]; omega
    · have b : Ball q 2 := by
        intro G W hf hout z hz
        exact ball_growth q (by omega) G W hf (fun w hw => (hout w hw).ge) z hz (q-1) (by omega)
      have greater := BRsGen.deficiency_strict_of_not_regular (by omega) b free minOut live reg
      change q*2+2≤total at greater
      have atLeast := minOut v vv
      omega)

#print axioms common_false
#print axioms dual_two
private def multiplicity (G : Family) (u v : ℕ) :=
  (G.filter (fun M => u∈M ∧ v∈M)).card

private theorem incidence {q E V} {G : Family} (cycles : ∀M∈G,Cycle E V q M) (u : ℕ) :
    (∑v∈outN E V u,multiplicity G u v)=(G.filter (u∈·)).card := by
  classical
  simp only [multiplicity,card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro M mg
  by_cases um : u∈M
  · have eq : ((outN E V u).filter (·∈M))=outN E M u := by
      ext v
      simp only [mem_filter,mem_outN]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨(cycles M mg).sub h.1,h.2⟩,h.1⟩⟩
    simpa only [um,true_and,ite_true,←card_filter,eq] using (cycles M mg).heads u um
  · simp [um]

/-- A family containing each vertex on exactly two cycles distributes two
units over the heads at each row. Each arc in that row has the same
multiplicity, either one or two. -/
theorem twofold_false {q E V x} {G : Family} (hq : 2≤q) (free : QFree E V q) (live : V.Nonempty)
    (cycles : ∀M∈G,Cycle E V q M)
    (wit : ∀u∈V,∀v∈V,E u v=true → ∃M∈G,u∈M ∧ v∈M)
    (two : ∀v∈V,(G.filter (v∈·)).card=2)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i) : False := by
  classical
  have positive (u) (uv : u∈V) (v) (vh : v∈outN E V u) : 1≤multiplicity G u v := by
    obtain ⟨M,mg,um,vm⟩ := wit u uv v (mem_outN.mp vh).1 (mem_outN.mp vh).2
    exact card_pos.mpr ⟨M,mem_filter.mpr ⟨mg,um,vm⟩⟩
  have sumOut (u) (uv : u∈V) := (incidence cycles u).trans (two u uv)
  have minOut (u) (uv : u∈V) : 1≤(outN E V u).card := by
    by_contra! no
    have empty := card_eq_zero.mp (show (outN E V u).card=0 by omega)
    have eq := sumOut u uv
    simp [empty] at eq
  have weight (u) (uv : u∈V) (v) (vh : v∈outN E V u) :
      multiplicity G u v=1+(2-(outN E V u).card) := by
    let S := outN E V u
    have cnt := card_erase_add_one vh
    have sum := sum_erase_add S (multiplicity G u) vh
    change (∑i∈S.erase v,multiplicity G u i)+multiplicity G u v=∑i∈S,multiplicity G u i at sum
    have small : (S.erase v).card≤∑i∈S.erase v,multiplicity G u i := by
      simpa only [sum_const_nat (fun _ _ => rfl),Nat.mul_one] using sum_le_sum (s:=S.erase v)
        (fun i hi => positive u uv i (mem_of_mem_erase hi))
    have val := positive u uv v vh
    have all : (∑i∈S,multiplicity G u i)=2 := sumOut u uv
    change (S.erase v).card+1=S.card at cnt
    change multiplicity G u v=1+(2-S.card)
    by_cases single : S.card=1
    · have em : S.erase v=∅ := card_eq_zero.mp (by omega)
      rw [em,sum_empty] at sum
      omega
    · omega
  have rev (M) (mg : M∈G) : Cycle (fun i j => E j i) V q M := by
    have c := cycles M mg
    exact ⟨c.sub,c.size,c.incoming,c.heads⟩
  have incoming (v) (vv : v∈V) : (∑u∈inN E V v,(1+(2-(outN E V u).card)))=2 := by
    have eq := (incidence rev v).trans (two v vv)
    change (∑u∈inN E V v,multiplicity G v u)=2 at eq
    refine Eq.trans ?_ eq
    apply sum_congr rfl
    intro u uh
    obtain ⟨uv,edge⟩ := mem_inN.mp uh
    have same : multiplicity G v u=multiplicity G u v := by simp only [multiplicity,and_comm]
    rw [same,weight u uv v (mem_outN.mpr ⟨vv,edge⟩)]
  let y := fun u => ((1+(2-(outN E V u).card) : ℕ) : ℚ)
  have colBound := dual_two hq free live minOut incoming
  have low := sum_le_sum (s:=V) (fun i hi => mul_le_mul_of_nonneg_left (colBound i hi) (xp i hi))
  have high := sum_lt_sum_of_nonempty live (fun i hi => mul_lt_mul_of_pos_left (strict i hi)
    (show 0<y i by dsimp [y]; positivity))
  rw [←sum_mul,rational_cross_rows] at high
  change (∑i∈V,x i*col q E V y i)≤∑i∈V,x i*mass V y at low
  rw [←sum_mul] at low
  change mass V y*mass V x<_ at high
  change _≤mass V x*mass V y at low
  linarith

#print axioms twofold_false

end LeanCH.BR.Closure.CycleCoverWeights
