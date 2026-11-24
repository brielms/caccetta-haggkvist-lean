import checkpoints.shen_extension.ShortShellSwitchReplay

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- The old cross-class receipts already include the missing pairs of any
subset of the original claimants of a cycle. In particular this applies
after deleting precisely the classes moved to secondary payers. -/
theorem acyclic_subset_bill {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (hr : 0<r) (sel : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target)
    {K : Finset (Finset ℕ)} (keys : K⊆claims sel C)
    (all : ∀Y∈K,QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card) :
    (∑Y∈K,(shellDebt D V 3 (3*r) Y:ℚ))≤(receipts sel C).card+1 := by
  classical
  let R := K.image sel.rep
  have key Y (ym : Y∈K) := (mem_filter.mp (keys ym)).1
  have label Y (ym : Y∈K) := (mem_filter.mp (keys ym)).2
  have data Y (ym : Y∈K) : ClaimData D V Y C q r (sel.rep Y) target :=
    label Y ym ▸ claim_data free reg hr sel (key Y ym) room.cycle (all Y ym)
      room.close room.space room.distance room.score
  have sub : R⊆representatives sel C := image_subset_image keys
  have count : R.card=K.card := card_image_of_injOn (fun a am b bm eq=>
    (rep_key sel (key _ am)).symm.trans ((congrArg (N2 D V) eq).trans (rep_key sel (key _ bm))))
  have off a (am : a∈R) b (bm : b∈R) (different : a≠b) : b∉ball D V a 3 := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp am
    obtain ⟨Z,zm,rfl⟩ := mem_image.mp bm
    exact separate_claims free (by have := room.cycle.1; omega) reg hr
      (rep_native sel (key Y ym)) (rep_native sel (key Z zm)) (rep_key sel (key Y ym))
      (rep_key sel (key Z zm)) (fun eq=>different (congrArg sel.rep eq)) (data Y ym) (data Z zm)
  have native a (am : a∈R) : a∈V := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp am; exact rep_native sel (key Y ym)
  have holes : R.offDiag⊆receipts sel C := by
    intro e em
    obtain ⟨a,b,ne⟩ := mem_offDiag.mp em
    exact mem_inter.mpr ⟨mem_offDiag.mpr ⟨sub a,sub b,ne⟩,mem_filter.mpr
      ⟨mem_offDiag.mpr ⟨native _ a,native _ b,ne⟩,off _ a _ b ne,off _ b _ a ne.symm⟩⟩
  have units Y (ym : Y∈K) : (shellDebt D V 3 (3*r) Y:ℚ)≤1 := by
    exact_mod_cast (acyclic_class_debit free reg hr sel (key Y ym) room.cycle (all Y ym)
      (by have := room.close; have := room.space; omega) room.distance).2
  have sum := sum_le_sum units
  simp only [sum_const,nsmul_eq_mul,mul_one] at sum
  have cards := card_le_card holes
  rw [offDiag_card,count] at cards
  have bound : K.card≤(receipts sel C).card+1 := by
    by_cases low : K.card≤1
    · omega
    have := Nat.mul_le_mul_left K.card (show 2≤K.card by omega)
    omega
  exact sum.trans (by exact_mod_cast bound)

/-- Read the adjusted balance at an old payer directly from its surviving
class list and its old receipt account. A secondary subsidy is charged
there only when the literal set of its labels is itself a moved class. -/
theorem residual_bill {D V q r k b C} (sel : Selection D V q r k b) {M : Finset (Finset ℕ)}
    (keys : M⊆classes D V k b) (used : C∈booked sel) :
    switchedBill sel M C =
      (∑Y∈claims sel C\M,(shellDebt D V k b Y:ℚ))-(receipts sel C).card+
        (if C∈M then (shellDebt D V k b C:ℚ) else 0) := by
  classical
  let K := claims sel C
  have same : M.filter (fun Y=>sel.pay Y=C)=K∩M := by
    ext Y
    simp only [K,claims,mem_inter,mem_filter]
    exact ⟨fun h=>⟨⟨keys h.1,h.2⟩,h.1⟩,fun h=>⟨h.2,h.1.2⟩⟩
  have split := sum_sdiff (inter_subset_left (s₁:=K) (s₂:=M)) (f:=fun Y=>(shellDebt D V k b Y:ℚ))
  have remove : K\(K∩M)=K\M := by ext Y; simp only [mem_sdiff,mem_inter]; tauto
  rw [remove] at split
  simp only [switchedBill,ite_eq_left used,netDebt,←sum_filter,same]
  dsimp only [K] at split ⊢
  linarith only [split]

/-- Having an acyclic residual account makes it cost at most one unit
plus its own literal move. This is independent of all earlier switched claims. -/
theorem residual_acyclic_cap {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (sel : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target)
    {M : Finset (Finset ℕ)} (keys : M⊆classes D V 3 (3*r)) (used : C∈booked sel)
    (all : ∀Y∈claims sel C\M,QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card) :
    switchedBill sel M C≤1+(if C∈M then (shellDebt D V 3 (3*r) C:ℚ) else 0) := by
  classical
  rw [residual_bill sel keys used]
  have cost := acyclic_subset_bill free reg (by have := room.growth.2.1; omega)
    sel room (sdiff_subset : claims sel C\M⊆claims sel C) all
  linarith

#print axioms acyclic_subset_bill
#print axioms residual_bill
#print axioms residual_acyclic_cap
end LeanCH.BR.LowShellCycleSelection
