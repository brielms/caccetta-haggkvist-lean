import checkpoints.shen_extension.CompromiseQuotaTransfer

namespace LeanCH.BR.CompromiseQuotaTransfer
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog ProjectedQuotaTransfer FragmentScoreEquality

/-- Return a checked order bound to the lower-degree catalog at this
cutoff. Descendant families can spend that quota on arbitrary carriers. -/
theorem lower_of_order {q d m} (bound : GuardedFamilyRules.OrderBound q d m)
    (room : q*d≤m) : NoHost q d :=
  fun D U live size free degree=>(bound.bound D U free live degree).not_ge (size.trans room)

theorem extend_prefix {q d m} (lower : ∀k,k<d → NoHost q k)
    (bound : GuardedFamilyRules.OrderBound q d m) (room : q*d≤m) :
    ∀k,k<d+1 → NoHost q k := by
  intro k hk
  by_cases eq : k=d
  · subst k; exact lower_of_order bound room
  · exact lower k (by omega)

theorem triangle_prefix {p : Input} (bad : Bad p) (cut : cutoff p=3) :
    ∀k,k<projectionFloor+1 → NoHost (cutoff p) k := by
  apply extend_prefix (available_lower_hosts bad) (recorded_bound bad)
  rw [cut]
  decide

theorem saturated_carrier {D U q t x} (flat : FlatErasure D U q t x)
    (carrier : OneShortCarrier D U q t x)
    (no : ¬∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) :
    BRsub.Sat q D U := sat_of_no_cheap carrier.free flat.cutoff_eq.ge no

/-- Push the order bound through arbitrary excess degree and expose the
numerical inequality even if the root's parameters remain symbolic. -/
theorem live_order_gap {p : Input} {d m} (bad : Bad p)
    (bound : GuardedFamilyRules.OrderBound (cutoff p) d m) (floor : d≤p.s) :
    m+p.s<p.n+d := by
  by_contra! fits
  exact GuardedFamilyRules.forbidden bad bound ⟨le_rfl,floor,fits⟩

theorem source_gap {p : Input} (bad : Bad p) : p.s+recorded.score<p.n := by
  have lo : recorded.degree≤p.s := replay_completed_floor bad
  have := live_order_gap bad (recorded_bound bad) lo
  omega

/-- A cutoff whose entire diagonal fits the verified bound excludes
that degree on every surviving input. -/
theorem degree_after_bound {p : Input} {d m} (bad : Bad p)
    (bound : GuardedFamilyRules.OrderBound (cutoff p) d m) (floor : d≤p.s)
    (fits : cutoff p*d≤m) : d+1≤p.s := by
  have gap := live_order_gap bad bound floor
  have hp := bad.degree_pos
  have whole : p.n≤cutoff p*p.s := by
    unfold cutoff CH.ceilDiv
    have rem := Nat.mod_lt (p.n+p.s-1) hp
    have sum := Nat.mod_add_div (p.n+p.s-1) p.s
    rw [Nat.mul_comm p.s] at sum
    omega
  by_contra! no
  have eq : p.s=d := by omega
  rw [eq] at whole gap
  omega

theorem triangle_degree {p : Input} (bad : Bad p) (cut : cutoff p=3) :
    recorded.degree+1≤p.s := by
  apply degree_after_bound bad (recorded_bound bad) (replay_completed_floor bad)
  rw [cut]
  decide

theorem any_triangle_degree {p : Input} (bad : Bad p) :
    cutoff p=3 → recorded.degree+1≤p.s := triangle_degree bad

attribute [aesop safe forward (immediate := [bad,bound,floor]) (rule_sets := [CHGraphFamilies])] live_order_gap
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] source_gap any_triangle_degree
attribute [aesop safe forward (immediate := [bad,cut]) (rule_sets := [CHGraphFamilies])] triangle_degree
attribute [aesop safe forward (immediate := [bad,cut]) (rule_sets := [CHGraphFamilies])] triangle_prefix
attribute [aesop safe forward (immediate := [bound,room]) (rule_sets := [CHGraphFamilies])] lower_of_order
attribute [aesop safe forward (immediate := [lower,bound,room]) (rule_sets := [CHGraphFamilies])] extend_prefix
attribute [aesop safe forward (immediate := [flat,carrier,no]) (rule_sets := [CHGraphFamilies])] saturated_carrier

#print axioms live_order_gap
#print axioms source_gap
#print axioms degree_after_bound
#print axioms triangle_degree
#print axioms lower_of_order
#print axioms extend_prefix
#print axioms triangle_prefix
#print axioms saturated_carrier
end LeanCH.BR.CompromiseQuotaTransfer
