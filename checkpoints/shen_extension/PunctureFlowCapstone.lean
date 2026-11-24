import checkpoints.shen_extension.PunctureDiscrepancy
import checkpoints.shen_extension.PunctureParentFlow

namespace LeanCH.BR.Closure.PunctureFlowCapstone
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse PunctureParentFlow
open scoped Matrix

theorem absorption_on_source {q E V} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x p : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈V,0<x i) (xm : mass V x=1) (pm : mass V p=1)
    (rows : ∀i∈V,WeightedSD.row q E V x i=c) (cols : ∀i∈V,WeightedSD.col q E V p i=c)
    (M : Matrix V V ℝ) (cert : Punctures (realMatrix q E V) M) :
    let B := M*excess (realMatrix q E V)
    let w := fun i : V => (x i : ℝ)
    let d := (c:ℝ)-1
    let K := PunctureDiscrepancy.next B w
    ∃l : V→ℝ, (∀i,0<l i) ∧ (∑i,l i)=1 ∧ l ᵥ* M=(fun i : V => (p i : ℝ)) ∧
      ∀n i, let v := fun j => l j*(B j j*w j)/d
            l i-(∑k∈range n,(w ᵥ* K^k) i*PunctureDiscrepancy.stop B w d i) =
              (v ᵥ* K^n) i*PunctureDiscrepancy.stop B w d i ∧
            (v ᵥ* K^n) i*PunctureDiscrepancy.stop B w d i ≤ (∑j,v j)*(1/(c:ℝ))^n := by
  classical
  intro B w d K
  let R := realMatrix q E V
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced free) x
    (fun i hi => (xp i hi).le) (fun i hi => by rw [xm,rows i hi]; exact high)
  have off (i j : V) (ne : i≠j) := (cert i).columns j (mem_erase.mpr ⟨ne.symm,mem_univ _⟩)
  have xn (i : V) : 0<w i := by dsimp only [w]; exact_mod_cast xp i i.property
  have xsum : ∑i,w i=1 := real_mass_of_rational_probability x xm
  have pr : ∀i : V,(R *ᵥ w) i=(c:ℝ) := realMatrix_rational_rows x c rows
  have dp : 0<d := sub_pos.mpr (by exact_mod_cast high)
  obtain ⟨_,l,lp,lm,recovered,_,bal⟩ := PunctureLawMixture.glue R H M inv w
    (fun i : V => (p i : ℝ)) c (by exact_mod_cast high) xn xsum
    (real_mass_of_rational_probability p pm) pr (realMatrix_rational_columns p c cols)
    (fun i => (cert i).mass) off
  have orig : excess R *ᵥ w=fun _ => d := by funext i; rw [mulVec_excess,pr,xsum]
  have bx : B *ᵥ w=fun _ => d := by
    change (M*excess R) *ᵥ w=_
    rw [←Matrix.mulVec_mulVec,orig]
    funext i
    change (∑j,M i j*d)=_
    rw [←sum_mul,(cert i).mass,one_mul]
  have entry (i j : V) : B i j=((M i) ᵥ* R) j-1 := by
    change ((M i) ᵥ* excess R) j=_
    rw [vecMul_excess,(cert i).mass]
  have low (i j : V) : -1≤B i j := by
    rw [entry]
    have nn : 0≤((M i) ᵥ* R) j := sum_nonneg fun k _ => mul_nonneg ((cert i).nonneg k)
      (by dsimp only [R]; rw [realMatrix_entry]; split_ifs <;> positivity)
    linarith
  have limit := PunctureDiscrepancy.absorption B w l dp xn xsum lp (fun i => congrFun bx i)
    (fun i j ne => by rw [entry]; exact sub_nonpos.mpr (off i j ne)) low bal
  refine ⟨l,lp,lm,recovered,fun n i => ?_⟩
  simpa only [show 1+d=(c:ℝ) by dsimp [d]; ring] using limit.2 n i

/-- Actual parents, on the retained graph, of any selected group of omissions. -/
noncomputable def parents {V : Finset ℕ} (E : CH.Digraph) (S : Finset V) : Finset V :=
  univ.filter fun b => ∃y∈S,E b y=true

/-- One and the same mixture pays every set of omitted vertices simultaneously. -/
theorem parent_sets {q E V} (free : QFree E V q) (small : SmallerSmallRow q V.card) (two : 2≤V.card)
    {x p : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈V,0<x i) (xm : mass V x=1) (pm : mass V p=1)
    (rows : ∀i∈V,WeightedSD.row q E V x i=c) (cols : ∀i∈V,WeightedSD.col q E V p i=c)
    (M : Matrix V V ℝ) (cert : Punctures (realMatrix q E V) M) :
    ∃l : V→ℝ, (∀i,0<l i) ∧ (∑i,l i)=1 ∧ l ᵥ* M=(fun i : V => (p i : ℝ)) ∧
      ∀ S : Finset V, (∑y∈S,l y)+((c:ℝ)-1)*S.card ≤ (q:ℝ)*∑b∈parents E S,(p b : ℝ) ∧
          ((c:ℝ)-1)*S.card ≤ ((q:ℝ)-1)*∑b∈parents E S,(p b : ℝ) := by
  classical
  obtain ⟨_,l,pos,unit,recov,demand,cap⟩ := (laws free small two high xp xm pm rows cols).2 M cert
  refine ⟨l,pos,unit,funext recov,fun S => ?_⟩
  let f := flow E M l
  have nn (y b : V) : 0≤f y b := by dsimp [f,flow]; split_ifs <;> first | exact le_rfl | exact mul_nonneg (pos y).le ((cert y).nonneg b)
  have rowCap (y : V) : (∑b,f y b)≤l y := by
    calc
      _ ≤ ∑b,l y*M y b := sum_le_sum fun b _ => by
        dsimp [f,flow]; split_ifs <;> first | exact le_rfl | exact mul_nonneg (pos y).le ((cert y).nonneg b)
      _ = _ := by rw [←mul_sum,(cert y).mass,mul_one]
  have totalCap : (∑y∈S,∑b,f y b) ≤ ∑b∈parents E S,(p b : ℝ) := by
    rw [sum_comm]
    apply le_trans (le_of_eq (sum_subset (subset_univ (parents E S)) ?_).symm)
    · exact sum_le_sum fun b _ => (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun y _ _ => nn y b)).trans (cap b)
    · intro b _ h
      exact sum_eq_zero fun y hy => ite_eq_right (fun arc => h (mem_filter.mpr ⟨mem_univ _,y,hy,arc⟩))
  have dem := sum_le_sum (s:=S) (fun y _ => demand y)
  have rc := sum_le_sum (s:=S) (fun y _ => rowCap y)
  change (∑y∈S,(l y+((c:ℝ)-1))) ≤ ∑y∈S,(q:ℝ)*∑b,f y b at dem
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at dem
  have qpos : 1≤q := by
    by_contra! z
    have qz : q=0 := by omega
    have ⟨y,hy⟩ := card_pos.mp (show 0<V.card by omega)
    have h := demand (⟨y,hy⟩ : V)
    rw [qz,Nat.cast_zero,zero_mul] at h
    have hh : (1:ℝ)<c := by exact_mod_cast high
    linarith [pos (⟨y,hy⟩ : V)]
  have qreal : (1:ℝ)≤q := by exact_mod_cast qpos
  constructor
  · nlinarith only [dem,mul_le_mul_of_nonneg_left totalCap (by positivity : 0≤(q:ℝ))]
  · nlinarith only [dem,rc,mul_le_mul_of_nonneg_left totalCap (sub_nonneg.mpr qreal)]

#print axioms absorption_on_source
#print axioms parent_sets
end LeanCH.BR.Closure.PunctureFlowCapstone
