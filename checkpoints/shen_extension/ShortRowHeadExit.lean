import checkpoints.shen_extension.FlatDeletionBank

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassBankReplay BypassRepair

/-- Measured at the same cheap vertex and its actual head. The degree
of the latter is allowed to vary across rows, including a deficient one. -/
theorem cheap_head_bill {D U q v z} (free : QFree D U q) (cut : 2≤q) (vm : v∈U)
    (cheap : (outN D U v).card+(ball D U v 2).card<U.card) (head : z∈outN D U v) :
    (outN D U z).card+2*(outN D U v).card+2≤U.card+(outN D (outN D U v) z).card := by
  have eq := erase_ball_one_eq_outN free (by omega) vm
  have member : z∈(ball D U v 1).erase v := eq.symm ▸ head
  have loss := loss_bound (i:=1) (j:=0) (K:=1) free vm member (by decide) cut
  rw [eq] at loss
  have outer := ReachLedger.ball_one free (by omega) (outN_subset head)
  have inner := ReachLedger.ball_one (free.mono_set (outN_subset : outN D U v⊆U)) (by omega) head
  have base := ReachLedger.ball_one free (by omega) vm
  have monotone := card_le_card (ball_mono_radius (D:=D) (W:=U) (u:=v) (by decide : 1≤2))
  change (ball D U z 1).card≤(ball D (outN D U v) z 1).card+((ball D U v 2).card-(ball D U v 1).card) at loss
  omega

theorem head_exit {D U q v d} (free : QFree D U q) (cut : 2≤q) (vm : v∈U)
    (cheap : (outN D U v).card+(ball D U v 2).card<U.card) (live : (outN D U v).Nonempty)
    (none : NoHost q d) (fit : (outN D U v).card≤q*d)
    (rows : ∀z∈outN D U v,d+U.card≤(outN D U z).card+2*(outN D U v).card+2) : False := by
  apply none D _ live fit (free.mono_set outN_subset)
  intro z zm
  have := cheap_head_bill free cut vm cheap zm
  have := rows z zm
  omega

/-- Every affordable lower quota is a simultaneous test of this one
physical head bank. The reserved deficient row is charged only if present. -/
structure ShortBankLimit (D : CH.Digraph) (U : Finset ℕ) (q t x v : ℕ) : Prop where
  bound : ∀d, NoHost q d → (outN D U v).card≤q*d →
    d+U.card≤t+2*(outN D U v).card+2 →
    (x∈outN D U v ∧ t+2*(outN D U v).card+2=d+U.card)

@[aesop safe forward (immediate := [carrier,cut,row,vm,cheap,live]) (rule_sets := [CHGraphFamilies])]
theorem short_bank_limit {D U q t x v} (carrier : OneShortCarrier D U q t x) (cut : 2≤q)
    (row : (outN D U x).card+1=t) (vm : v∈U)
    (cheap : (outN D U v).card+(ball D U v 2).card<U.card) (live : (outN D U v).Nonempty) :
    ShortBankLimit D U q t x v := by
  constructor
  intro d none fit bill
  by_contra bad
  apply head_exit carrier.free cut vm cheap live none fit
  intro z zm
  by_cases same : z=x
  · subst z
    have ne : t+2*(outN D U v).card+2≠d+U.card := fun eq=>bad ⟨zm,eq⟩
    omega
  · have := carrier.other z (outN_subset zm) same
    omega

/-- Supply the bank nonemptiness, deficit and cutoff on the exact
label exposed by the cheap alternative in any marked lone child. -/
@[aesop safe forward (immediate := [cell,lone,rank,cut,vm,cheap]) (rule_sets := [CHGraphFamilies])]
theorem marked_short_bank {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} {v : ℕ}
    (cell : Marked X m) (lone : LoneBlocked X m) (rank : 3≤r) (cut : 3≤q)
    (vm : v∈X.V\m.bank) (cheap : (outN X.D (X.V\m.bank) v).card+(ball X.D (X.V\m.bank) v 2).card<(X.V\m.bank).card) :
    ShortBankLimit X.D (X.V\m.bank) q (r-1) m.x v := by
  apply short_bank_limit (carrier_of_lone cell lone) (by omega) cell.deficit vm cheap
  apply card_pos.mp
  by_cases e : v=m.x
  · subst v
    have := cell.deficit
    omega
  · have := lone.paid_elsewhere v vm e
    omega

attribute [aesop safe forward (immediate := [free,cut,vm,cheap,head]) (rule_sets := [CHGraphFamilies])] cheap_head_bill

#print axioms cheap_head_bill
#print axioms head_exit
#print axioms short_bank_limit
#print axioms marked_short_bank
end LeanCH.BR.FragmentScoreEquality
