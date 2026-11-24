import checkpoints.shen_extension.ErasedQuotaFrontier
import checkpoints.shen_extension.EndpointLayerWitness

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen

/-- A lower bound on the two forward radii saturating their pair budget
forces the actual forward/reverse incidence relations to cover each row. -/
theorem no_pair_gaps {D U q i j} (free : QFree D U q) (time : i+j≤q)
    (paid : ∀v∈U,U.card+1≤(ball D U v i).card+(ball D U v j).card) :
    ∀v∈U,ReachLedger.gap D U i j v=∅ := by
  classical
  have floor := sum_le_sum paid
  have floor' : U.card*(U.card+1)≤(∑v∈U,(ball D U v i).card)+(∑v∈U,(ball D U v j).card) := by
    calc
      U.card*(U.card+1) = ∑_v∈U,(U.card+1) := (sum_const_nat (fun _ _=>rfl)).symm
      _ ≤ _ := floor
      _ = _ := sum_add_distrib
  have ledger := ReachLedger.ledger free time
  have zero : (∑v∈U,(ReachLedger.gap D U i j v).card)=0 := by omega
  intro v vm
  exact card_eq_zero.mp ((sum_eq_zero_iff.mp zero) v vm)

/-- A flat mixed row score supplies the existing saturation predicate
without adding arcs or transferring labels. -/
theorem sat_of_no_cheap {D U q} (free : QFree D U q) (cut : 3≤q)
    (no : ¬∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) :
    BRsub.Sat q D U := by
  have covered := no_pair_gaps (i:=1) (j:=2) free cut (fun v vm=>by
    rw [ReachLedger.ball_one free (by omega) vm]
    have := not_lt.mp (fun h=>no ⟨v,vm,h⟩)
    omega)
  intro h hm p pm miss
  by_cases e : p=h
  · subst p; exact self_mem_ball hm
  · apply ball_mono_radius (show 2≤q-1 by omega)
    apply ReachLedger.covered (covered p pm) hm
    intro arc
    exact ((mem_ball_one pm).mp arc).elim (fun eq=>e eq.symm) (fun edge=>miss (mem_outN.mp edge).2)

/-- The established shortest-return rule applied to ordinary labels. -/
theorem turn_return {D U q x h p} (free : QFree D U q) (sat : BRsub.Sat q D U)
    (cut : 2≤q) (xm : x∈U) (hm : h∈outN D U x) (pm : p∈inN D U x) (miss : D p h≠true) :
    Walk D U h p (q-1) := by
  obtain ⟨hv,xh⟩ := mem_outN.mp hm
  obtain ⟨pv,px⟩ := mem_inN.mp pm
  have ne : h≠p := fun e=>digonfree free cut xm hv xh (e.symm ▸ px)
  exact (Closure.EndpointLayerWitness.shell D q (⟨p,pv⟩ : ↥U) free sat cut
    (j:=⟨h,hv⟩) (s:=⟨x,xm⟩) ⟨fun eq=>ne (congrArg Subtype.val eq),Bool.eq_false_iff.mpr miss⟩ px xh).1

def turnInterior (D : CH.Digraph) (U : Finset ℕ) (x : ℕ) :=
  U\insert x (inN D U x ∪ outN D U x)

/-- Every internal vertex of a marginal return avoids both endpoint
banks. The two lengths are the actual before/after pieces at that vertex. -/
theorem interior_neutral {D U q x h p z i j} (free : QFree D U q) (xm : x∈U)
    (hm : h∈outN D U x) (pm : p∈inN D U x) (zm : z∈U)
    (first : Walk D U h z i) (last : Walk D U z p j)
    (ipos : 1 ≤ i) (jpos : 1 ≤ j) (length : i+j+1≤q) : z∈turnInterior D U x := by
  obtain ⟨hv,xh⟩ := mem_outN.mp hm
  obtain ⟨_,px⟩ := mem_inN.mp pm
  refine mem_sdiff.mpr ⟨zm,?_⟩
  intro bad
  rcases mem_insert.mp bad with eq|either
  · subst z
    exact free x _ (by omega) (by omega : i+1≤q) (.step hv xh first)
  rcases mem_union.mp either with into|out
  · have zx := (mem_inN.mp into).2
    exact free x _ (by omega) (by omega : i+1+1≤q) (.step hv xh (first.snoc xm zx))
  · have xz := (mem_outN.mp out).2
    exact free x _ (by omega) (by omega : j+1+1≤q) (.step zm xz (last.snoc xm px))

/-- Whenever the two-step return is available, the entire missing
parent-to-head table factors through one common neutral set at x. -/
theorem turn_matrix {D U q x h p} (free : QFree D U q) (cut : 3≤q) (xm : x∈U)
    (hm : h∈outN D U x) (pm : p∈inN D U x)
    (returns : D p h≠true → Walk D U h p 2) :
    D p h≠true ↔ ∃j∈turnInterior D U x,D h j=true ∧ D j p=true := by
  constructor
  · intro miss
    obtain ⟨j,w,_,jp⟩ := (returns miss).unsnoc
    cases w with
    | step jm hj rest =>
      cases rest
      exact ⟨j,interior_neutral free xm hm pm jm (.step jm hj (.refl _))
        (.step (mem_inN.mp pm).1 jp (.refl _)) (by decide) (by decide) cut,hj,jp⟩
  · rintro ⟨j,jm,hj,jp⟩ ph
    exact free p 3 (by decide) cut (.step (outN_subset hm) ph
      (.step (mem_sdiff.mp jm).1 hj (.step (mem_inN.mp pm).1 jp (.refl _))))

structure TurnTable (D : CH.Digraph) (U : Finset ℕ) (x : ℕ) : Prop where
  entry : ∀(p : ℕ) (_pm : p∈inN D U x) (h : ℕ) (_hm : h∈outN D U x),
    D p h≠true ↔ ∃j∈turnInterior D U x,D h j=true ∧ D j p=true

@[aesop safe forward (immediate := [flat,carrier,no]) (rule_sets := [CHGraphFamilies])]
theorem flat_turns {D U q t x} (flat : FlatErasure D U q t x)
    (carrier : OneShortCarrier D U q t x)
    (no : ¬∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) :
    TurnTable D U x := by
  have cut := flat.cutoff_eq
  have sat := sat_of_no_cheap carrier.free (by omega) no
  refine ⟨fun p pm h hm=>turn_matrix carrier.free (by omega) carrier.marked hm pm (fun miss=>?_)⟩
  have := turn_return carrier.free sat (by omega) carrier.marked hm pm miss
  exact (show q-1=2 by omega) ▸ this

attribute [aesop safe forward (immediate := [free,cut,no]) (rule_sets := [CHGraphFamilies])] sat_of_no_cheap
attribute [aesop safe forward (immediate := [self,_pm,_hm]) (rule_sets := [CHGraphFamilies])] TurnTable.entry

#print axioms no_pair_gaps
#print axioms sat_of_no_cheap
#print axioms turn_return
#print axioms interior_neutral
#print axioms turn_matrix
#print axioms flat_turns
end LeanCH.BR.FragmentScoreEquality
