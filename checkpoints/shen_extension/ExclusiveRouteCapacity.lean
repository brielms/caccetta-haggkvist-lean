import checkpoints.shen_extension.CommonBankCapacity
import checkpoints.shen_extension.dot_tensor_research.PhysicalBankRouting

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- Among cycles outside a receiving bank, a physical parent which feeds
the entire bank has at most as many possible successors as its spare slots.
Prefix packing then bounds how many distinct cycles can cross that parent. -/
theorem shared_parent_multiplicity {D V r c F Z v} (root : ∀C∈F,∀x∈C,Rooted D V x C)
    (degree : (outN D V v).card=r) (outside : ∀C∈F,Disjoint C Z)
    (paid : Z⊆outN D V v) (width : ∀C∈F,omissions D V C r≤c) :
    (through F v).card≤(r-Z.card)*2^c := by
  classical
  have turnsSub : turns D F v⊆outN D V v\Z := by
    intro a am
    obtain ⟨C,cm,rfl⟩ := mem_image.mp am
    obtain ⟨cf,vc⟩ := mem_filter.mp cm
    have h := successor_mem (root C cf v vc)
    exact mem_sdiff.mpr ⟨outN_mono (root C cf v vc).sub _ h,disjoint_left.mp (outside C cf) (outN_subset h)⟩
  have turnsCap := card_le_card turnsSub
  rw [card_sdiff_of_subset paid,degree] at turnsCap
  have pack := root_packing (fun C (cm : C∈through F v)=>root C (mem_filter.mp cm).1 v (mem_filter.mp cm).2)
  change (∑C∈through F v,(1:ℚ)/2^(omissions D V C (outN D V v).card))≤(turns D F v).card at pack
  rw [degree] at pack
  have one C (cm : C∈through F v) : (1:ℚ)/2^c≤1/2^(omissions D V C r) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (width _ (mem_filter.mp cm).1))
  have cost := (sum_le_sum one).trans pack
  simp only [sum_const,nsmul_eq_mul,←div_eq_mul_one_div] at cost
  have bill := (div_le_iff₀ (by positivity : (0:ℚ)<2^c)).mp cost
  exact (show (through F v).card≤(turns D F v).card*2^c by exact_mod_cast bill).trans (Nat.mul_le_mul_right _ turnsCap)

structure RouteBank (D : CH.Digraph) (V : Finset ℕ) (r δ : ℕ) (A : Finset ℕ) : Prop where
  size : A.card=r-1
  cycle : ∀a∈A,Rooted D V a A
  parents : (allParents D V A).card≤δ

def RouteEdge (D : CH.Digraph) (V : Finset ℕ) (r δ : ℕ) (A B : Finset ℕ) : Prop :=
  RouteBank D V r δ A ∧ RouteBank D V r δ B ∧ exterior D V A=B

structure WeakArrival (D : CH.Digraph) (V : Finset ℕ) (r δ g c : ℕ) (C T : Finset ℕ) : Prop where
  cycle : ∀v∈C,Rooted D V v C
  omission : 0<omissions D V C r ∧ omissions D V C r≤c
  route : ∃Z,RouteBank D V r δ Z ∧ Disjoint C Z ∧ g≤(C.filter (fun v=>Z⊆outN D V v)).card ∧
    Relation.ReflTransGen (RouteEdge D V r δ) Z T

/-- Bound *all* distinct arriving physical cycles jointly, regardless of the
number of intermediate steps and the choices of their initial third shells. -/
theorem arrivals_bound {D V q r δ g c T} {F : Finset (Finset ℕ)} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (hr : 3≤r) (sparse : c+1<r-1) (two : δ<2*(r-1)) (entry : δ<r-1+g)
    (arrive : ∀C∈F,WeakArrival D V r δ g c C T) :
    F.card*g ≤ δ*2^c := by
  classical
  rcases F.eq_empty_or_nonempty with empty|⟨C,cm⟩
  · simp [empty]
  let Z := (arrive C cm).route.choose
  have base := (arrive C cm).route.choose_spec
  have unique {A B Z'} (a : RouteEdge D V r δ A Z') (b : RouteEdge D V r δ B Z') : A=B := by
    rcases competing_predecessors free hq reg hr a.1.cycle b.1.cycle a.2.1.cycle a.2.2 b.2.2 a.2.1.size with eq|bad
    · exact eq
    have := a.1.size
    have := b.1.size
    have := a.2.1.parents
    omega
  have start {K S} (km : K∈F) (bank : RouteBank D V r δ S) (min : g≤(K.filter (fun v=>S⊆outN D V v)).card)
      (A) (edge : RouteEdge D V r δ A S) : False := by
    have cost := predecessor_and_claim free hq reg edge.1.cycle (arrive _ km).cycle bank.cycle
      edge.2.2 bank.size (arrive _ km).omission.1 (by have := (arrive _ km).omission.2; omega)
    have := edge.1.size
    have := bank.parents
    omega
  have common K (km : K∈F) : Disjoint K Z ∧ g≤(K.filter (fun v=>Z⊆outN D V v)).card := by
    obtain ⟨S,sbank,dis,lower,path⟩ := (arrive K km).route
    have same := ExclusiveBankRouting.same_origin (step:=RouteEdge D V r δ) (a:=S) (b:=Z) (z:=T) unique (start km sbank lower) (start cm base.1 base.2.2.1)
      path base.2.2.2
    exact same ▸ ⟨dis,lower⟩
  let P := allParents D V Z
  have count : F.card*g≤P.card*2^c := by
    apply card_mul_le_card_mul (fun (K : Finset ℕ) (v : ℕ)=>v∈K)
    · intro K km
      apply (common K km).2.trans (card_le_card ?_)
      intro v vm
      have kv := (mem_filter.mp vm).1
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨((arrive K km).cycle v kv).sub kv,(mem_filter.mp vm).2⟩,kv⟩
    · intro v vm
      have pd := mem_filter.mp vm
      have bound := shared_parent_multiplicity (v:=v) (fun K km=>(arrive K km).cycle)
        (reg v pd.1) (fun K km=>(common K km).1) pd.2 (fun K km=>(arrive K km).omission.2)
      have zn : Z.card=r-1 := base.1.size
      have diff : r-Z.card=1 := by omega
      rw [diff,Nat.one_mul] at bound
      exact bound
  exact count.trans (Nat.mul_le_mul_right _ base.1.parents)

#print axioms arrivals_bound
end LeanCH.BR.LowShellCycleSelection
