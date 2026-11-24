import checkpoints.shen_extension.SharedArcFlatResponse

namespace LeanCH.BR.Closure.SingleArcLocalSignExample
open Finset Matrix SharedArcFlatResponse
open scoped Matrix

abbrev Label := Fin 10
private def masks : Array ℕ := #[290,304,146,515,577,76,268,49,648,196]

def E (i j : Label) : Bool := (masks[i.val]?.getD 0).testBit j.val
def child (i j : Label) : Bool := decide (i=3 ∧ j=2) || E i j

/-- An old return of length zero, one, or two. An intermediate label must
satisfy the supplied predicate. -/
def reaches (G : Label→Label→Bool) (allow : Label→Bool) (i j : Label) : Bool :=
  decide (i=j) || G i j || decide (∃t : Label,allow t=true ∧ G i t=true ∧ G t j=true)

def locallyAvailable (G : Label→Label→Bool) (i j : Label) : Bool :=
  !G i j && !reaches G (fun _=>true) j i

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- This old graph is oriented and 3-regular in both directions. It has
exactly one missing arc without a short return. Its insertion saturates
the local test, while an old directed triangle witnesses failure of global
girth. The old successor/predecessor return law holds on the puncture. -/
theorem geometry :
    (∀i,E i i=false) ∧ (∀i j,E i j=true → E j i=false) ∧
    (∀i,(univ.filter (fun j=>E i j)).card=3 ∧ (univ.filter (fun j=>E j i)).card=3) ∧
    (∀i j,locallyAvailable E i j=true ↔ i=3 ∧ j=2) ∧
    (∀i j,locallyAvailable child i j=false) ∧
    (∀v k,E 3 v=true → E k 2=true →
      (E k v=false ↔ reaches E (fun t=>decide (t≠3 ∧ t≠2)) v k=true)) ∧
    E 0 1=true ∧ E 1 4=true ∧ E 4 0=true := by decide +kernel

private def numerators : Array (Array ℤ) := #[
  #[13223,-30597,4473,-7497,13923,-12327,18648,21483,-3822,-7812],
  #[12573,-4597,15273,6003,723,8823,-6552,-10917,-4272,-7362],
  #[-28422,25833,-18772,38583,-33072,-4122,8253,3963,-16992,34443],
  #[6798,-15972,10548,-12022,6498,17748,4473,3258,14103,-25737],
  #[-19527,19053,11673,1503,5123,1773,1848,-117,-4122,-7512],
  #[828,19233,-20022,12783,-20772,13628,-21147,7713,3258,14193],
  #[21348,-16272,14898,-30822,33498,14148,-5677,-9792,1803,-13437],
  #[16428,-23067,11628,-20367,5178,-9222,1953,9713,14058,3393],
  #[14508,-4437,3258,-16287,15408,-18342,21483,-3957,2288,-4227],
  #[-28062,40518,-23262,37818,-16812,-2412,-13587,-11652,3393,23753]]

private def N (i j : Label) : ℤ := ((numerators[i.val]?.getD #[])[j.val]?).getD 0
private def Z (i j : Label) : ℤ := (if i=j then 1 else 0)+(if E i j then 3 else 0)
def R : Matrix Label Label ℝ := fun i j => (Z i j:ℝ)
noncomputable def weight (_ : Label) : ℝ := 1/10

/-- A proper subset avoiding both edited endpoints has three vertices
and every row of its uncentered matrix sums to four. -/
theorem strict_triangle :
    let S : Finset Label := {0,1,4}
    3∉S ∧ 2∉S ∧ S.card=3 ∧ ∀i∈S,(∑j∈S,((if i=j then 1 else 0)+(if E i j then 3 else 0):ℤ))=4 := by decide +kernel

private theorem integer_check :
    (∀i j : Label,(∑k : Label,Z i k*N k j)=(if i=j then 96950 else 0)) ∧
    (∀i : Label,(∑j : Label,Z i j)=10 ∧ (∑j : Label,Z j i)=10) ∧
    (∀v k : Label,33725≤96950+3*(N v k-N v 3+N 2 3-N 2 k)) ∧
    96950+3*(N 9 6-N 9 3+N 2 3-N 2 6)=33725 := by decide +kernel

private theorem inverse : R⁻¹=(fun i j => (N i j:ℝ)/96950 : Matrix Label Label ℝ) := by
  apply inv_eq_right_inv
  ext i j
  change (∑k : Label,(Z i k:ℝ)*((N k j:ℝ)/96950))=_
  simp only [←mul_div_assoc,←sum_div,←Int.cast_mul,←Int.cast_sum,integer_check.1,one_apply]
  by_cases eq : i=j <;> norm_num [eq]

theorem flat : (∑i : Label,weight i)=1 ∧ R *ᵥ weight=(fun _=>1) ∧ weight ᵥ* R=(fun _=>1) := by
  refine ⟨by norm_num [weight],?_,?_⟩
  · funext i
    change (∑j : Label,(Z i j:ℝ)*(1/10))=1
    rw [←sum_mul,←Int.cast_sum,(integer_check.2.1 i).1]; norm_num
  · funext j
    change (∑i : Label,(1/10)*(Z i j:ℝ))=1
    rw [←mul_sum,←Int.cast_sum,(integer_check.2.1 j).2]; norm_num

/-- The minimum of the entire 10 by 10 flat tensor is strictly positive.
It is attained at the old successor 9 of 3 and old predecessor 6 of 2. -/
theorem minimum :
    (∀v k : Label,(1349:ℝ)/387800≤test R⁻¹ weight weight 3 3 2 v k) ∧
    E 3 9=true ∧ E 6 2=true ∧ test R⁻¹ weight weight 3 3 2 9 6=(1349:ℝ)/387800 := by
  rw [inverse]
  have score (v k : Label) :
      test (fun i j : Label => (N i j:ℝ)/96950) weight weight 3 3 2 v k =
      ((96950+3*(N v k-N v 3+N 2 3-N 2 k):ℤ):ℝ)/9695000 := by
    unfold test weight; push_cast; ring
  refine ⟨fun v k => ?_,by decide,by decide,?_⟩
  · rw [score]
    have bound : (33725:ℝ) ≤ ((96950+3*(N v k-N v 3+N 2 3-N 2 k):ℤ):ℝ) := by
      exact_mod_cast integer_check.2.2.1 v k
    linarith only [bound]
  · rw [score,integer_check.2.2.2]; norm_num

end LeanCH.BR.Closure.SingleArcLocalSignExample
#print axioms LeanCH.BR.Closure.SingleArcLocalSignExample.geometry
#print axioms LeanCH.BR.Closure.SingleArcLocalSignExample.flat
#print axioms LeanCH.BR.Closure.SingleArcLocalSignExample.minimum
#print axioms LeanCH.BR.Closure.SingleArcLocalSignExample.strict_triangle
