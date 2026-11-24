import checkpoints.shen_extension.LightColumnPacking

namespace LeanCH.BR.Closure.TwoSidedPuncture
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights RootedSplice MandatoryTwoStep

/-- An entire two-step ball, in either orientation, keeps the named label
after a minimum deletion at the indicated support threshold. -/
theorem both_balls {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) (near : h∈ball X.D X.V t 2 ∨ t∈ball X.D X.V h 2) :
    Covered X.D X.V q h t := by
  have tv := mem_of_mem_erase tw
  have ne := (mem_erase.mp tw).1
  rcases near with upstream | down
  · exact ball_covered X hq tv hv ne minimum upstream
  obtain ⟨_,k,bound,path⟩ := mem_ball.mp down
  cases path with
  | refl => exact (ne rfl).elim
  | step av ha tail =>
    cases tail with
    | refl => exact PunctureWeightCoverage.head_covered X hq hv tw minimum size ha
    | step _ atv last =>
      cases last with
      | refl =>
        by_contra absent
        obtain ⟨_,solo⟩ := unique_incoming X hq hv av tv ha atv (forces_iff.mpr absent)
        have weight := PunctureWeightCoverage.flow_floor X av minimum size
        rw [solo,sum_singleton] at weight
        exact absent (PunctureWeightCoverage.heavy_covered X hq hv tw minimum size weight.le)
      | step => omega

/-- At any cutoff, if the marked receiver is lost then the two complementary
pieces of a shortest cycle through the root both have length at least three. -/
theorem long_arms {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) (absent : ¬Covered X.D X.V q h t) :
    ∃C,Cycle X.D X.V q C ∧ h∈C ∧ t∈C ∧
      ∃ i j : ℕ, 3 ≤ i ∧ 3 ≤ j ∧ i+j=q+1 ∧ Walk X.D C h t i ∧ Walk X.D C t h j := by
  have tv := mem_of_mem_erase tw
  have hashead : (outN X.D X.V t).Nonempty := by
    have floor := PunctureWeightCoverage.flow_floor X tv minimum (k:=0)
      (by simpa using (card_pos.mpr X.live))
    by_contra empty
    rw [not_nonempty_iff_eq_empty.mp empty,sum_empty] at floor
    omega
  obtain ⟨z,zh⟩ := hashead
  obtain ⟨C,c,tc,_⟩ := edge_cycle X hq tv (mem_outN.mp zh).1 (mem_outN.mp zh).2
  have hc := forces_iff.mpr absent C c tc
  have heads (x) (xc : x∈C) : ∃y∈C,X.D x y=true := by
    obtain ⟨y,yh⟩ := card_pos.mp (show 0<(outN X.D C x).card by rw [c.heads x xc]; decide)
    exact ⟨y,mem_outN.mp yh⟩
  obtain ⟨i,lo,hi,f,g⟩ := WeightedSD.tight_cycle_complementary_walks
    (X.free.mono_set c.sub) c.size heads hc tc (Ne.symm (mem_erase.mp tw).1)
  refine ⟨C,c,hc,tc,i,q+1-i,?_,?_,by omega,f,g⟩
  · by_contra! short
    exact absent (both_balls X hq hv tw minimum size (Or.inr (mem_ball.mpr ⟨tv,i,by omega,f.mono c.sub⟩)))
  · by_contra! short
    exact absent (both_balls X hq hv tw minimum size (Or.inl (mem_ball.mpr ⟨hv,_,by omega,g.mono c.sub⟩)))

theorem all_covered_of_cutoff {q n} (X : Model q n) (hq : 2≤q) (short : q≤4) {h}
    (hv : h∈X.V) (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∀t∈X.V.erase h,Covered X.D X.V q h t := by
  intro t tw
  by_contra absent
  obtain ⟨_,_,_,_,_,_,i,j,both,_,_⟩ := long_arms X hq hv tw minimum size absent
  omega

/-- Apply the receiver classification at the actual exterior mark supplied
by a closed shift sequence. The first branch is a transition of the existing
cycle graph on the punctured support, retaining the named exterior vertex. -/
theorem orbit_destination {q n} (X : Model q n) (hq : 2≤q) {h} (hv : h∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (large : (q+1)^2≤X.V.card)
    (M : ℕ→Finset ℕ) (a u v b : ℕ→ℕ) (closed : M (q+1)=M 0)
    (cycle : ∀i,Cycle X.D (X.V\{h}) q (M i))
    (move : ∀i,CycleSquareTensor.Shift X.D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) :
    let S := (range (q+1)).image u
    let P := (M 0).erase (u 0)
    ∃z∈(X.V\{h})\(P∪S),∃A,(A=S ∨ ∃x∈S,A=insert x P) ∧
      Cycle X.D (X.V\{h}) q A ∧ 2≤(inN X.D A z).card ∧
      ((∃N,Cycle X.D (X.V\{h}) q N ∧ PunctureCycleLoop.Step X.D A N ∧ z∈N\A) ∨
       (5≤q ∧ X.weights z<(q-1)*X.weights h ∧
        Disjoint (LightColumnPacking.closedN X.D X.V h) (LightColumnPacking.closedN X.D X.V z))) := by
  classical
  intro S P
  obtain ⟨z,ze,A,F,which,ca,rich,_,zf⟩ :=
    AllCutoffPacketEscape.from_loop X hq hv minimum large M a u v b closed cycle move
  have zw := (mem_sdiff.mp ze).1
  rw [sdiff_singleton_eq_erase] at zw
  have mult := Nat.mul_le_mul_left q (Nat.sub_le q 1)
  have size : q*(q-1)+1≤X.V.card := by nlinarith only [large,mult]
  refine ⟨z,ze,A,which,ca,rich,?_⟩
  by_cases covered : Covered X.D X.V q h z
  · obtain ⟨N,c,zn⟩ := covered
    have outside : z∈N\A := mem_sdiff.mpr ⟨zn,(mem_sdiff.mp zf).2⟩
    exact Or.inl ⟨N,(by simpa only [sdiff_singleton_eq_erase] using c),⟨z,outside,rich⟩,outside⟩
  · have range : 5≤q := by
      by_contra! low
      exact covered (all_covered_of_cutoff X hq (by omega) hv minimum size z zw)
    have cap := ((PunctureReceiverFrontier.classify X hq hv zw minimum size).resolve_left covered).1
    exact Or.inr ⟨range,cap,LightColumnPacking.uncovered_far X hq hv zw minimum size covered⟩

#print axioms orbit_destination
#print axioms both_balls
#print axioms long_arms
#print axioms all_covered_of_cutoff
end LeanCH.BR.Closure.TwoSidedPuncture
