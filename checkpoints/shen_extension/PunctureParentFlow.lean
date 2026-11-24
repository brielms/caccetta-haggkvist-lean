import checkpoints.shen_extension.PunctureLawMixture

namespace LeanCH.BR.Closure.PunctureParentFlow
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse
open scoped Matrix

def Punctures {V : Finset ℕ} (R M : Matrix V V ℝ) : Prop :=
  ∀ i : V, CutCertificate R (univ.erase i) (M i)

/-- Amount from the omission of y charged to the actual parent b. -/
def flow {V : Finset ℕ} (E : CH.Digraph) (M : Matrix V V ℝ) (l : V→ℝ) (y b : V) :=
  if E b y=true then l y*M y b else 0

private theorem diagonal {V : Finset ℕ} {R M : Matrix V V ℝ} (cert : Punctures R M) (i : V) :
    M i i=0 := (cert i).outside i (notMem_erase _ _)

theorem score_at_omission {V : Finset ℕ} {q E M} (C : Punctures (realMatrix q E V) M) (i : V) :
    ((M i) ᵥ* realMatrix q E V) i = (q:ℝ)*∑b : V, if E b i=true then M i b else 0 := by
  change (∑b : V,M i b*realMatrix q E V b i)=_
  simp_rw [realMatrix_entry,mul_add]
  rw [sum_add_distrib,mul_sum]
  have d : (∑b : V,M i b*(if b=i then (1:ℝ) else 0))=0 := by
    simp [mul_ite,diagonal C i]
  rw [d,zero_add]
  exact sum_congr rfl (fun b _ => by cases E b i <;> simp [mul_comm])

/-- Choose all deletion certificates independently. Each has positive
mixture weight. Their arc-supported parts share the same global column
capacities, and every deleted label demands a fixed positive extra amount. -/
theorem laws {q E V} (free : QFree E V q) (small : SmallerSmallRow q V.card) (two : 2≤V.card)
    {x p : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈V,0<x i) (xm : mass V x=1) (pm : mass V p=1)
    (rows : ∀i∈V,WeightedSD.row q E V x i=c) (cols : ∀i∈V,WeightedSD.col q E V p i=c) :
    let R := realMatrix q E V
    (∃ M,Punctures R M) ∧ ∀ M,Punctures R M →
      IsUnit M ∧ ∃l : V→ℝ, (∀i,0<l i) ∧ (∑i,l i)=1 ∧
        (∀b : V,(∑y,l y*M y b)=(p b : ℝ)) ∧
        (∀i : V,l i+((c:ℝ)-1) ≤ (q:ℝ)*∑b,flow E M l i b) ∧
        (∀b : V,(∑i,flow E M l i b)≤(p b : ℝ)) := by
  classical
  intro R
  have proper := small.induced free
  have highRows (i) (iv : i∈V) : mass V x<WeightedSD.row q E V x i := by rw [xm,rows i iv]; exact high
  obtain ⟨H,inv,cuts⟩ := all_cut_certificates_of_proper_smallRow proper x (fun i hi => (xp i hi).le) highRows
  constructor
  · have chooseOne (i : V) : ∃m,CutCertificate R (univ.erase i) m := by
      obtain ⟨m,ok⟩ := cuts (V.erase i) (erase_subset _ _) (card_pos.mp (by rw [card_erase_of_mem i.property]; omega))
        (fun eq => notMem_erase i.val V (by rw [eq]; exact i.property))
      have cut : hostCut V (V.erase i.val)=univ.erase i := by
        ext j
        simp only [hostCut,mem_filter,mem_univ,true_and,mem_erase,j.property,and_true]
        exact not_congr Subtype.ext_iff.symm
      exact ⟨m,cut ▸ ok⟩
    choose M all using chooseOne
    exact ⟨M,all⟩
  intro M cert
  have off (i j : V) (ne : i≠j) := (cert i).columns j (mem_erase.mpr ⟨ne.symm,mem_univ _⟩)
  obtain ⟨unit,l,lp,lm,recov,floor,_⟩ := PunctureLawMixture.glue R H M inv
    (fun i : V => (x i : ℝ)) (fun i : V => (p i : ℝ)) (c : ℝ) (by exact_mod_cast high)
    (fun i => by exact_mod_cast xp i i.property) (real_mass_of_rational_probability x xm)
    (real_mass_of_rational_probability p pm) (realMatrix_rational_rows x c rows)
    (realMatrix_rational_columns p c cols) (fun i => (cert i).mass) off
  refine ⟨unit,l,lp,lm,fun b => congrFun recov b,?_,?_⟩
  · intro i
    have bval : (M*excess R) i i=(q:ℝ)*(∑b : V,if E b i=true then M i b else 0)-1 := by
      change ((M i) ᵥ* excess R) i=_
      rw [vecMul_excess,(cert i).mass,score_at_omission cert]
    have feq : (∑b,flow E M l i b)=l i*(∑b : V,if E b i=true then M i b else 0) := by
      rw [mul_sum]
      exact sum_congr rfl fun b _ => by unfold flow; split_ifs <;> simp
    have low := floor i
    rw [bval] at low
    rw [feq]
    nlinarith only [low]
  · intro b
    apply le_trans (sum_le_sum (s:=univ) (g:=fun i : V => l i*M i b) ?_) (le_of_eq (congrFun recov b))
    intro i _
    unfold flow
    split_ifs <;> first | exact le_rfl | exact mul_nonneg (lp i).le ((cert i).nonneg b)

#print axioms laws
end LeanCH.BR.Closure.PunctureParentFlow
