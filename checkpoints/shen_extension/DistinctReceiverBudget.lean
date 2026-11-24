import checkpoints.shen_extension.ReachCompletionCatalog
import checkpoints.shen_extension.QuotaBankPromotion

namespace LeanCH.BR.DistinctReceiverBudget
open Finset BRq2 BRq3 BR45 CHRuleCatalog

/-- A row-specific lower bound for the sum of two inclusive forward balls. -/
noncomputable def score (D : CH.Digraph) (V : Finset ℕ) (i j x : ℕ) : ℕ :=
  (ball D V x i).card + (ball D V x j).card

/-- Charge the physical receiving rows once each. The floor can differ on
full and partial rows, and the receipt retains the actual unused pairs. -/
theorem distinct_spend {D V q i j} {S : Finset ℕ} {base fee : ℕ → ℕ}
    (free : QFree D V q) (time : i+j≤q) (inside : S⊆V)
    (floor : ∀x∈V, base x≤score D V i j x)
    (charged : ∀x∈S, base x+fee x≤score D V i j x) :
    (∑ x∈V, base x) + (∑ x∈S, fee x) + (∑ x∈V, (ReachLedger.gap D V i j x).card)
      ≤ V.card*(V.card+1) := by
  classical
  let extra x := score D V i j x - base x
  have fees : (∑ x∈S, fee x) ≤ ∑ x∈V, extra x := by
    apply le_trans (b := ∑ x∈S, extra x)
    · exact sum_le_sum fun x hx => by dsimp [extra]; have := charged x hx; omega
    · exact sum_le_sum_of_subset_of_nonneg inside fun _ _ _ => Nat.zero_le _
  have rows := sum_congr (s₁:=V) (s₂:=V) (f:=fun x => base x + extra x)
    (g:=fun x => (ball D V x i).card + (ball D V x j).card) rfl (fun x hx => by
      change base x + (score D V i j x - base x) = score D V i j x
      have := floor x hx
      omega)
  simp only [sum_add_distrib] at rows
  have ledger := ReachLedger.ledger free time
  omega

/-- If charging each sender separately would exceed the pair capacity,
two of its actual arcs end at the same marked receiver. -/
theorem shared_successor {D V q i j} {A : Finset ℕ} {next base : ℕ → ℕ} {cost : ℕ}
    (free : QFree D V q) (time : i+j≤q) (senders : A⊆V)
    (arcs : ∀x∈A, next x∈V ∧ D x (next x)=true)
    (floor : ∀x∈V, base x≤score D V i j x)
    (price : ∀x∈A, base (next x)+cost≤score D V i j (next x))
    (overbooked : V.card*(V.card+1) <
      (∑ x∈V, base x) + A.card*cost + (∑ x∈V, (ReachLedger.gap D V i j x).card)) :
    ∃ x∈A, ∃ y∈A, x≠y ∧ next x=next y ∧
      x∈inN D V (next x) ∧ y∈inN D V (next x) := by
  have inside : A.image next ⊆ V := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    exact (arcs x hx).1
  have paid := distinct_spend (fee:=fun _ => cost) free time inside floor (by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    exact price x hx)
  simp only [sum_const, smul_eq_mul] at paid
  have small : (A.image next).card < A.card := by
    by_contra! large
    have := Nat.mul_le_mul_right cost large
    omega
  obtain ⟨x,hx,y,hy,diff,eq⟩ := exists_ne_map_eq_of_card_image_lt small
  exact ⟨x,hx,y,hy,diff,eq,mem_inN.mpr ⟨senders hx,(arcs x hx).2⟩,
    mem_inN.mpr ⟨senders hy,eq ▸ (arcs y hy).2⟩⟩

attribute [aesop safe forward (immediate := [free,time,inside,floor,charged])
  (rule_sets := [CHGraphFamilies])] distinct_spend
attribute [aesop safe forward (immediate := [free,time,senders,arcs,floor,price,overbooked])
  (rule_sets := [CHGraphFamilies])] shared_successor

/-- Retain the largest degree permitted by the fifth strip and the native
cutoff. Each unit of spare native degree can pay for one deleted label. -/
@[ch_numeric_guard] def FifthTransfer (n r q : ℕ) : Prop :=
  let d := min r ((q+7)/2)
  9≤d ∧ n+d+2≤(2*d-7)*d+r

instance {n r q} : Decidable (FifthTransfer n r q) := by unfold FifthTransfer; infer_instance

theorem fifth_transfer {p : Input} (bad : Bad p) : ¬FifthTransfer p.n p.s (cutoff p) := by
  let d := min p.s ((cutoff p+7)/2)
  let t := 2*d-7
  rintro ⟨rank,room⟩
  change 9≤d at rank
  change p.n+d+2≤t*d+p.s at room
  have ds : d≤p.s := min_le_left ..
  have dq : d≤(cutoff p+7)/2 := min_le_right ..
  have strip : t+7=2*d := by dsimp [t]; omega
  have cut : t≤cutoff p := by omega
  have prod : 2<t*d := lt_of_lt_of_le (by omega : 2<t)
    (Nat.le_mul_of_pos_right t (by omega))
  have bound : GuardedFamilyRules.OrderBound t d (t*d-2) := by
    refine ⟨by omega,fun D V free live deg => ?_⟩
    have := FifthStripLedger.fifth_order free deg live rank strip
    omega
  exact GuardedFamilyRules.forbidden bad bound ⟨cut,ds,by omega⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] fifth_transfer

#print axioms distinct_spend
#print axioms shared_successor
#print axioms fifth_transfer
end LeanCH.BR.DistinctReceiverBudget
