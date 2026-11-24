import checkpoints.shen_extension.MultiPivotRepair

namespace LeanCH.BR.Closure.BlockerHeadRouting
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShortestCycleWeights MandatoryTwoStep EqualColumnRepair
open MultiPivotRepair DeleteRepair

/-- A retained head from which every route to a blocking parent can be
shortened between the corresponding two class labels. -/
def SpareAt {q n} (X : Model q n) (K : Finset ℕ) (f : ℕ→ℕ) (x y : ℕ) : Prop :=
  ∀j∈K,∀p,Blocks X K p j → ∀k,Walk X.D (X.V\K) y p k →
    ∃d, 1 ≤ d ∧ d+f j ≤ k+1+f x ∧ Walk X.D X.V x j d

noncomputable def spareAt {q n} (X : Model q n) (K : Finset ℕ) (f : ℕ→ℕ) (x : ℕ) : Finset ℕ := by
  classical exact (outN X.D (X.V\K) x).filter (SpareAt X K f x)

/-- This is an upper bound on the weight of a specified set of actual heads.
Every head outside that set has a shortest positive route to a named
low-margin parent’s class head, with its interior outside K. -/
theorem concentration_at {q n} (X : Model q n) (hq : 2≤q) (f : ℕ→ℕ) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∃p x, Blocks X K p x ∧
      score q X.D X.V X.weights p+(∑z∈K,X.weights z)+q*(∑y∈spareAt X K f x,X.weights y)
          ≤ (∑z∈X.V,X.weights z)+q*X.weights x ∧
      (∑y∈spareAt X K f x,X.weights y)<X.weights x := by
  classical
  let U := X.V\K
  let P (t p : ℕ) := Blocks X K p t
  let H (t y : ℕ) := y∈spareAt X K f t
  let E := edited X.D U K P H
  obtain ⟨proper,_,missing⟩ := class_data X hq sub hk many equal minimum size
  have gaps : PotentialGaps X.D X.V U K P H f := by
    intro i _ j jk y _ p _ hy block k path
    exact (mem_filter.mp (show y∈(outN X.D U i).filter (SpareAt X K f i) from hy)).2 j jk p block k path
  obtain ⟨p,x,block,loss⟩ := gift_loss X hq sub ⟨h,hk⟩ proper
    (fun u uk v vk => Or.inl (equal u uk v vk)) (E:=E) (safe_with_potential X.free sdiff_subset gaps)
    (fun _ _ _ _ arc => repair_old arc) (spareAt X K f) (by
      intro p x block y yh
      have head := (mem_filter.mp (show y∈(outN X.D U x).filter (SpareAt X K f x) from yh)).1
      have px : x∈outN X.D K p := block.2.2.1 ▸ mem_singleton_self _
      have yu := (mem_outN.mp head).1
      exact ⟨yu,repair_new block.1 (target_mem.mpr ⟨yu,x,block.2.1,block,yh⟩),
        missing x block.2.1 p block.1 (mem_outN.mp px).2 y head⟩)
  refine ⟨p,x,block,loss,?_⟩
  have high := nat_strict.mp X.strict p (mem_sdiff.mp block.1).1
  exact Nat.lt_of_mul_lt_mul_left (show q*(∑y∈spareAt X K f x,X.weights y)<q*X.weights x by omega)

abbrev Spare {q n} (X : Model q n) (K : Finset ℕ) := SpareAt X K (fun _ => 0)
noncomputable abbrev spareHeads {q n} (X : Model q n) (K : Finset ℕ) := spareAt X K (fun _ => 0)

theorem concentration {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∃p x, Blocks X K p x ∧
      score q X.D X.V X.weights p+(∑z∈K,X.weights z)+q*(∑y∈spareHeads X K x,X.weights y)
          ≤ (∑z∈X.V,X.weights z)+q*X.weights x ∧
      (∑y∈spareHeads X K x,X.weights y)<X.weights x :=
  concentration_at X hq (fun _ => 0) sub hk many equal minimum size

theorem routed {q n} (X : Model q n) {K : Finset ℕ} {x y}
    (sub : K⊆X.V) (head : y∈outN X.D (X.V\K) x) (used : y∉spareHeads X K x) :
    ∃j∈K,∃p,Blocks X K p j ∧ ∃k,Walk X.D (X.V\K) y p k ∧
      Walk X.D X.V x j (k+2) ∧ ∀d,1≤d → Walk X.D X.V x j d → k+2≤d := by
  classical
  have fail : ¬Spare X K x y := fun yes => used (mem_filter.mpr ⟨head,yes⟩)
  unfold Spare SpareAt at fail
  push Not at fail
  obtain ⟨j,jk,p,block,k,path,no⟩ := fail
  have hit : j∈outN X.D K p := block.2.2.1 ▸ mem_singleton_self _
  have yv := (mem_sdiff.mp (mem_outN.mp head).1).1
  have jc := sub jk
  refine ⟨j,jk,p,block,k,path,.step yv (mem_outN.mp head).2 ((path.mono sdiff_subset).snoc jc (mem_outN.mp hit).2),?_⟩
  intro d dp w
  by_contra! small
  exact no d dp (by omega) w

#print axioms concentration_at
#print axioms concentration
#print axioms routed
end LeanCH.BR.Closure.BlockerHeadRouting
