import checkpoints.shen_extension.CommonExitReplacement
import checkpoints.shen_extension.RootFourCyclePacking

namespace LeanCH.BR.Closure.TwoBankDescent
open Finset BRq2 BRq3 DeficitLevels CommonExitReplacement

/-- Replace two banks before testing degrees. P feeds the S replacement
through actual S-neighbours which may differ from row to row. The first
intermediate graph is only required to preserve short-cycle avoidance. -/
theorem funded {D V W S P H L q d k l} (free : QFree D V q) (hq : 1≤q)
    (wv : W⊆V) (sv : S⊆V) (pv : P⊆V) (hw : H⊆W) (lw : L⊆W)
    (sh : ∀x∈S, ∀y∈H, D x y=true) (pl : ∀x∈P, ∀y∈L, D x y=true)
    (ps : ∀x∈P, (outN D S x).Nonempty)
    (innerS : q*(d-H.card)<k) (innerP : q*(d-(L.card+k))<l)
    (paid : ∀x∈W, d≤(outN D W x).card+(if (outN D S x).Nonempty then k else 0)
      +(if (outN D P x).Nonempty then l else 0)) :
    ∃ E U, U.Nonempty ∧ U.card=W.card+k+l ∧ QFree E U q ∧ ∀x∈U, d≤(outN E U x).card := by
  classical
  obtain ⟨F,K,kc,sep,internal,rows⟩ := fresh_bank (W∪P) hq innerS
  let E := edited D F S K H
  let T := (W∪P)∪K
  have safe1 : QFree E T q := safe free internal sv (union_subset wv pv) sh
  have wk : Disjoint W K := sep.mono_left subset_union_left
  have pk : Disjoint P K := sep.mono_left subset_union_right
  have lk := wk.mono_left lw
  have hk := wk.mono_left hw
  have inK (x) (nx : x∉K) (someHead : (outN D S x).Nonempty) :
      K⊆outN E (W∪K) x := fun y yk => mem_outN.mpr
      ⟨mem_union_right _ yk,by simp [E,edited,nx,yk,someHead]⟩
  have old (x) (xw : x∈W) :
      (outN D W x).card+(if (outN D S x).Nonempty then k else 0) ≤ (outN E (W∪K) x).card := by
    have nx := disjoint_left.mp wk xw
    have inc : outN D W x⊆outN E (W∪K) x := by
      intro y hy
      obtain ⟨yw,xy⟩ := mem_outN.mp hy
      exact mem_outN.mpr ⟨mem_union_left _ yw,by simp [E,edited,nx,disjoint_left.mp wk yw,xy]⟩
    split_ifs with hit
    · have size := card_le_card (union_subset inc (inK x nx hit))
      rwa [card_union_of_disjoint (wk.mono_left outN_subset),kc] at size
    · simpa only [Nat.add_zero] using card_le_card inc
  have oldParent (x) (xw : x∈W) (xp : (outN D P x).Nonempty) : (outN E P x).Nonempty := by
    obtain ⟨y,hit⟩ := xp
    obtain ⟨yp,xy⟩ := mem_outN.mp hit
    exact ⟨y,mem_outN.mpr ⟨yp,by simp [E,edited,disjoint_left.mp wk xw,disjoint_left.mp pk yp,xy]⟩⟩
  have pay1 (x) (xw : x∈W∪K) : d≤(outN E (W∪K) x).card+
      (if (outN E P x).Nonempty then l else 0) := by
    rcases mem_union.mp xw with xw|xk
    · apply (paid x xw).trans (Nat.add_le_add (old x xw) ?_)
      by_cases p : (outN D P x).Nonempty
      · simp [p,oldParent x xw p]
      · simp [p]
    · have inc : outN F K x∪H ⊆ outN E (W∪K) x := by
        intro y hy
        rcases mem_union.mp hy with inside|outside
        · have ⟨yk,xy⟩ := mem_outN.mp inside
          exact mem_outN.mpr ⟨mem_union_right _ yk,by simp [E,edited,xk,yk,xy]⟩
        · exact mem_outN.mpr ⟨mem_union_left _ (hw outside),by simp [E,edited,xk,disjoint_left.mp hk outside,outside]⟩
      have size := card_le_card inc
      rw [card_union_of_disjoint (hk.symm.mono_left outN_subset),rows x xk] at size
      omega
  have common (x) (xp : x∈P) (y) (yh : y∈L∪K) : E x y=true := by
    have nx := disjoint_left.mp pk xp
    rcases mem_union.mp yh with yl|yk
    · simp [E,edited,nx,disjoint_left.mp lk yl,pl x xp y yl]
    · simp [E,edited,nx,yk,ps x xp]
  have wkt : W∪K⊆T := union_subset (subset_union_left.trans subset_union_left) subset_union_right
  have pt : P⊆T := subset_union_right.trans subset_union_left
  have target : L∪K⊆W∪K := union_subset (lw.trans subset_union_left) subset_union_right
  obtain ⟨G,U,live,uc,safe2,deg⟩ := CommonExitReplacement.funded safe1 hq pt wkt target common
    (by simpa only [card_union_of_disjoint lk,kc] using innerP) pay1
  rw [card_union_of_disjoint wk,kc] at uc
  exact ⟨G,U,live,uc,safe2,deg⟩

theorem blocked_row {q s} (O : Origin q s) (laws : ∀ j<s, OrderLaw q j (q*j+1))
    {W S P H L d k l} (hq : 1≤q) (below : d<s) (budget : W.card+k+l≤q*d)
    (wv : W⊆O.V) (sv : S⊆O.V) (pv : P⊆O.V) (hw : H⊆W) (lw : L⊆W)
    (sh : ∀x∈S, ∀y∈H, O.G x y=true) (pl : ∀x∈P, ∀y∈L, O.G x y=true)
    (ps : ∀x∈P, (outN O.G S x).Nonempty)
    (innerS : q*(d-H.card)<k) (innerP : q*(d-(L.card+k))<l) :
    ∃x∈W, (outN O.G W x).card+(if (outN O.G S x).Nonempty then k else 0)
      +(if (outN O.G P x).Nonempty then l else 0)<d := by
  by_contra! all
  obtain ⟨E,U,live,uc,safe2,deg⟩ := funded O.free hq wv sv pv hw lw sh pl ps innerS innerP all
  have lower := laws d below E U safe2 deg live
  omega

#print axioms funded
#print axioms blocked_row
end LeanCH.BR.Closure.TwoBankDescent
