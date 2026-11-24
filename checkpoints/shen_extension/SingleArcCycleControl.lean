import checkpoints.shen_extension.SharedArcFlatResponse

namespace LeanCH.BR.Closure.SingleArcCycleControl
open Finset Matrix SharedArcFlatResponse
open scoped Matrix

/-- Scaling the edited head's weight and its inverse row by the same
factor at unchanged tail and midpoint columns interpolates the diagonal
with its positive flat baseline. -/
theorem dilution {I J : Type*} (L : Matrix I I ℝ) (L' : Matrix J J ℝ) (w p : I→ℝ) (w' p' : J→ℝ)
    (q s : ℝ) (a b v : I) (a' b' v' : J)
    (pa : p' a'=p a) (pv : p' v'=p v) (wv : w' v'=w v) (wb : w' b'=s*w b)
    (vv : L' v' v'=L v v) (va : L' v' a'=L v a)
    (ba : L' b' a'=s*L b a) (bv : L' b' v'=s*L b v) :
    test L' w' p' q a' b' v' v'= (1-s)*(w v*p v)+s*test L w p q a b v v := by
  simp only [test,pa,pv,wv,wb,vv,va,ba,bv]
  ring

abbrev Label := Fin 7
private def masks : Array ℕ := #[2,60,72,80,96,68,1]
def E (i j : Label) : Bool := (masks[i.val]?.getD 0).testBit j.val
private def Z (i j : Label) : ℤ := (if i=j then 1 else 0)+(if E i j then 3 else 0)
def R : Matrix Label Label ℝ := fun i j=>(Z i j:ℝ)
private def W (i : Label) : ℤ := if i=0 ∨ i=1 ∨ i=6 then 4 else 1
noncomputable def weight (i : Label) : ℝ := (W i:ℝ)/16
private def numerators : Array (Array ℤ) := #[
  #[-16,48,-36,-36,-36,-36,432], #[432,-16,12,12,12,12,-144],
  #[-36,108,-97,-33,-225,351,12], #[-36,108,351,-97,-33,-225,12],
  #[-36,108,-225,351,-97,-33,12], #[-36,108,-33,-225,351,-97,12],
  #[48,-144,108,108,108,108,-16]]
private def N (i j : Label) : ℤ := ((numerators[i.val]?.getD #[])[j.val]?).getD 0

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- No old loop, digon or directed triangle. The unique cycle parent is 6.
Of its four old returns of length two, three avoid the new head.
The fourth explains exactly why the insertion fails legality. -/
theorem geometry :
    (∀i,E i i=false) ∧ (∀i j,E i j=true → E j i=false) ∧
    (∀i j k,E i j=true → E j k=true → E k i=false) ∧
    E 0 1=true ∧ E 1 2=true ∧ E 0 2=false ∧
    (∀i,i≠0 → E i 1=true → E i 0=true) ∧
    (univ.filter (fun i=>E i 0=true ∧ E i 1=false))={6} ∧
    (univ.filter (fun j=>E 1 j=true ∧ E j 6=true))={2,3,4,5} ∧ E 2 6=true ∧ E 6 0=true := by
  decide +kernel

private theorem arithmetic :
    (∀i j : Label, (∑k,Z i k*N k j)=(if i=j then 1280 else 0)) ∧
    (∑i : Label,W i)=16 ∧
    (∀i : Label, (∑j,Z i j*W j)=16 ∧ (∑j,W j*Z j i)=16) := by decide +kernel

private theorem inverse : R⁻¹=(fun i j=>(N i j:ℝ)/1280 : Matrix Label Label ℝ) := by
  apply inv_eq_right_inv
  ext i j
  change (∑k : Label,(Z i k:ℝ)*((N k j:ℝ)/1280))=_
  simp only [←mul_div_assoc,←sum_div,←Int.cast_mul,←Int.cast_sum,arithmetic.1,one_apply]
  by_cases h : i=j <;> norm_num [h]

theorem flat :
    (∀i,0<weight i) ∧ (∑i,weight i)=1 ∧ R *ᵥ weight=(fun _=>1) ∧ weight ᵥ* R=(fun _=>1) := by
  refine ⟨fun i=>by unfold weight W; split <;> norm_num,?_,?_,?_⟩
  · simp [weight,←sum_div,←Int.cast_sum,arithmetic.2.1]
  · funext i
    change (∑j : Label,(Z i j:ℝ)*((W j:ℝ)/16))=1
    simp [←mul_div_assoc,←sum_div,←Int.cast_mul,←Int.cast_sum,(arithmetic.2.2 i).1]
  · funext i
    change (∑j : Label,((W j:ℝ)/16)*(Z j i:ℝ))=1
    simp [div_mul_eq_mul_div,←sum_div,←Int.cast_mul,←Int.cast_sum,(arithmetic.2.2 i).2]

theorem excess :
    let T := test R⁻¹ weight weight 3 0 2
    3*weight 2<2*weight 1 ∧
    3*T 1 6=33/320 ∧ weight 0*(2*weight 1-3*weight 2)=5/64 ∧ T 1 1=1/40 := by
  intro T
  have val (i j : Label) : T i j=test (fun u k=>(N u k:ℝ)/1280) weight weight 3 0 2 i j := by
    dsimp [T]; rw [inverse]
  rw [val 1 6,val 1 1]
  norm_num [test,weight,W,N,numerators]

end LeanCH.BR.Closure.SingleArcCycleControl
#print axioms LeanCH.BR.Closure.SingleArcCycleControl.geometry
#print axioms LeanCH.BR.Closure.SingleArcCycleControl.flat
#print axioms LeanCH.BR.Closure.SingleArcCycleControl.excess
