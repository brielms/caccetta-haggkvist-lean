import checkpoints.shen_extension.RadiusColumnRecurrence

namespace LeanCH.BR.Closure.ThresholdReturn
open Finset BRq2 BRq3 BR45

/-- Round zero contains the seeds. A row enters at the next round if it can
choose at least r different heads from the preceding round. -/
def grown (D : CH.Digraph) (V J : Finset ℕ) (r : ℕ) : ℕ → Finset ℕ
  | 0 => J
  | k+1 => let A := grown D V J r k
           A ∪ V.filter (fun x => r≤(outN D A x).card)

theorem inside {D V J r k} (jv : J⊆V) : grown D V J r k ⊆ V := by
  induction k with
  | zero => exact jv
  | succ k ih => exact union_subset ih (filter_subset _ _)

private theorem choose_head {D : CH.Digraph} {A M : Finset ℕ} {r x}
    (small : M.card<r) (many : r≤(outN D A x).card) :
    ∃ z∈A, z∉M ∧ D x z=true := by
  classical
  by_contra! no
  have sub : outN D A x ⊆ M := by
    intro z hz
    by_contra nm
    exact no z (mem_outN.mp hz).1 nm (mem_outN.mp hz).2
  have := card_le_card sub
  omega

/-- Each activated vertex can still reach a seed after deleting any fewer
than r labels, provided the starting vertex itself was retained. -/
theorem reaches_seed {D V J M r k x} (jv : J⊆V) (small : M.card<r)
    (active : x∈grown D V J r k) (keep : x∉M) :
    ∃ z∈J\M, ∃ m≤k, Walk D (V\M) x z m := by
  induction k generalizing x with
  | zero => exact ⟨x,mem_sdiff.mpr ⟨active,keep⟩,0,le_rfl,.refl _⟩
  | succ k ih =>
    rcases mem_union.mp active with old|new
    · obtain ⟨z,hz,m,le,p⟩ := ih old keep
      exact ⟨z,hz,m,by omega,p⟩
    · obtain ⟨y,ha,ym,xy⟩ := choose_head small (mem_filter.mp new).2
      obtain ⟨z,hz,m,le,p⟩ := ih ha ym
      exact ⟨z,hz,m+1,by omega,.step (mem_sdiff.mpr ⟨inside jv ha,ym⟩) xy p⟩

/-- Read the recurrence at the original column of h. Too few omissions would
complete an actual closed walk of length at most k+2. -/
theorem column_debit {D V J r k q h} (safe : QFree D V q) (room : k+2≤q)
    (jv : J⊆V) (hv : h∈V) (active : r≤(outN D (grown D V J r k) h).card) :
    r≤(J\inN D V h).card := by
  by_contra! small
  obtain ⟨y,ha,ym,hy⟩ := choose_head small active
  obtain ⟨z,hz,m,le,p⟩ := reaches_seed jv small ha ym
  have ⟨zj,zm⟩ := mem_sdiff.mp hz
  have back : z∈inN D V h := by by_contra no; exact zm (mem_sdiff.mpr ⟨zj,no⟩)
  exact safe h (m+2) (by omega) (by omega)
    ((Walk.step (inside jv ha) hy (p.mono sdiff_subset)).snoc hv (mem_inN.mp back).2)

/-- The total debit is paid by missing entries of the original J by H
incidence table, with no regularity or order assumption. -/
theorem incidence {D V J H r k q} (safe : QFree D V q) (room : k+2≤q)
    (jv : J⊆V) (hv : H⊆V) (many : ∀h∈H, r≤(outN D (grown D V J r k) h).card) :
    r*H.card ≤ ∑ z∈J, (H\outN D V z).card := by
  have lower := sum_le_sum (fun h hh => column_debit safe room jv (hv hh) (many h hh))
  rw [sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at lower
  apply lower.trans_eq
  have left (h) : J\inN D V h=J.filter (fun z => D z h≠true) := by
    ext z; simp only [mem_sdiff,mem_inN,mem_filter]; constructor
    · rintro ⟨zj,no⟩; exact ⟨zj,fun e => no ⟨jv zj,e⟩⟩
    · rintro ⟨zj,no⟩; exact ⟨zj,fun e => no e.2⟩
  have right (z) : H\outN D V z=H.filter (fun h => D z h≠true) := by
    ext h; simp only [mem_sdiff,mem_outN,mem_filter]; constructor
    · rintro ⟨hh,no⟩; exact ⟨hh,fun e => no ⟨hv hh,e⟩⟩
    · rintro ⟨hh,no⟩; exact ⟨hh,fun e => no e.2⟩
  simp only [left,right,card_filter]
  exact sum_comm

#print axioms reaches_seed
#print axioms column_debit
#print axioms incidence
end LeanCH.BR.Closure.ThresholdReturn
