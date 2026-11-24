import LeanCH.BR.BRCommonParentTransferGeometry

/-! Arbitrary-set folding, cutting first heads of paths of length at most q.
No deleted vertex is required to point to the receiver. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

open Classical in
noncomputable def foldBank (q : ℕ) (D : CH.Digraph) (V S : Finset ℕ) (y : ℕ) : Finset ℕ :=
  (outN D V y).filter (fun z => ∃ s ∈ S, s ∈ ball D V z (q - 1))

def foldGraph (D : CH.Digraph) (V S B : Finset ℕ) (y : ℕ) : CH.Digraph :=
  fun x z => decide (x ∈ V \ S ∧ z ∈ V \ S ∧
    (bankKept D B y x z = true ∨ (z = y ∧ ∃ s ∈ S, D x s = true)))

noncomputable def reachFold (q : ℕ) (D : CH.Digraph) (V S : Finset ℕ) (y : ℕ) : CH.Digraph :=
  foldGraph D V S (foldBank q D V S y) y

theorem foldBank_subset_out {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} :
    foldBank q D V S y ⊆ outN D V y := filter_subset _ _

theorem foldBank_retained {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ}
    (hno : ∀ s ∈ S, ¬ D y s = true) : foldBank q D V S y ⊆ V \ S := by
  intro z hz
  have ho := mem_outN.mp (foldBank_subset_out hz)
  exact mem_sdiff.mpr ⟨ho.1, fun hzS => hno z hzS ho.2⟩

theorem foldBank_mono {q : ℕ} {D : CH.Digraph} {U V S T : Finset ℕ} {y : ℕ}
    (hUV : U ⊆ V) (hST : S ⊆ T) : foldBank q D U S y ⊆ foldBank q D V T y := by
  intro z hz
  obtain ⟨ho, s, hs, hball⟩ := mem_filter.mp hz
  obtain ⟨hsU, k, hk, p⟩ := mem_ball.mp hball
  exact mem_filter.mpr ⟨mem_outN.mpr ⟨hUV (outN_subset ho), (mem_outN.mp ho).2⟩,
    s, hST hs, mem_ball.mpr ⟨hUV hsU, k, hk, p.mono hUV⟩⟩

theorem foldBank_no_kept_parent_return {q : ℕ} {D : CH.Digraph}
    {V S : Finset ℕ} {y x : ℕ} (hSV : S ⊆ V)
    (hno : ∀ s ∈ S, ¬ D y s = true) (hx : ∃ s ∈ S, D x s = true) :
    x ∉ ball (bankKept D (foldBank q D V S y) y) (V \ S) y (q - 1) := by
  intro hret
  obtain ⟨_, k, hk, path⟩ := mem_ball.mp hret
  obtain ⟨s, hs, hxs⟩ := hx
  cases path with
  | refl => exact hno s hs hxs
  | @step a z b l hz hyz tail =>
    obtain ⟨hyzD, hcut⟩ := of_decide_eq_true hyz
    have old := (walk_sub (fun a b h => (of_decide_eq_true h).1) tail).mono sdiff_subset
    have hzB : z ∈ foldBank q D V S y := mem_filter.mpr
      ⟨mem_outN.mpr ⟨(mem_sdiff.mp hz).1, hyzD⟩, s, hs,
        mem_ball.mpr ⟨hSV hs, l + 1, by omega, old.snoc (hSV hs) hxs⟩⟩
    exact hcut ⟨rfl, hzB⟩

/-- Geometry is valid at every cutoff, even q=0; the no-head premise is explicit. -/
theorem reachFold_qfree {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ}
    (hf : QFree D V q) (hSV : S ⊆ V) (hno : ∀ s ∈ S, ¬ D y s = true) :
    QFree (reachFold q D V S y) (V \ S) q := by
  apply qfree_common_head_additions (D := bankKept D (foldBank q D V S y) y)
    (P := fun x => x ∈ V \ S ∧ ∃ s ∈ S, D x s = true)
  · exact qfree_sub (fun a b h => (of_decide_eq_true h).1) (hf.mono_set sdiff_subset)
  · exact fun x hx => hx.1
  · intro a b h
    obtain ⟨ha, _, h | ⟨hby, hs⟩⟩ := of_decide_eq_true h
    · exact Or.inl h
    · exact Or.inr ⟨⟨ha, hs⟩, hby⟩
  · intro x hx
    exact foldBank_no_kept_parent_return hSV hno hx.2

theorem foldGraph_receiver_heads {D : CH.Digraph} {V S B : Finset ℕ} {y : ℕ}
    (hy : y ∈ V \ S) (hno : ∀ s ∈ S, ¬ D y s = true) :
    outN (foldGraph D V S B y) (V \ S) y = outN D V y \ B := by
  have hn : ¬ ∃ s ∈ S, D y s = true := fun ⟨s, hs, he⟩ => hno s hs he
  ext z
  constructor
  · intro hz
    obtain ⟨_, _, h | ⟨_, hs⟩⟩ := of_decide_eq_true (mem_outN.mp hz).2
    · obtain ⟨hyz, hcut⟩ := of_decide_eq_true h
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset hz)).1, hyz⟩,
        fun hb => hcut ⟨rfl, hb⟩⟩
    · exact (hn hs).elim
  · intro hz
    obtain ⟨hzO, hzB⟩ := mem_sdiff.mp hz
    obtain ⟨hzV, hyz⟩ := mem_outN.mp hzO
    have hzK : z ∈ V \ S := mem_sdiff.mpr ⟨hzV, fun hzS => hno z hzS hyz⟩
    exact mem_outN.mpr ⟨hzK, decide_eq_true ⟨hy, hzK, Or.inl
      (decide_eq_true ⟨hyz, fun h => hzB h.2⟩)⟩⟩

/-- Stop at the first entry to an arbitrary set; no simplicity or girth needed. -/
theorem walk_first_entry {D : CH.Digraph} {V S : Finset ℕ} {a b l : ℕ}
    (p : Walk D V a b l) : a ∈ V → a ∉ S → b ∈ S →
    ∃ x s k, x ∈ V ∧ x ∉ S ∧ s ∈ S ∧ D x s = true ∧ k + 1 ≤ l ∧ Walk D V a x k := by
  induction p with
  | refl a => intro _ ha hb; exact (ha hb).elim
  | @step a c b m hc hac rest ih =>
    intro haV ha hb
    by_cases hcS : c ∈ S
    · exact ⟨a, c, 0, haV, ha, hcS, hac, by omega, .refl _⟩
    · obtain ⟨x, s, k, hxV, hxS, hs, hxs, hk, w⟩ := ih hc hcS hb
      exact ⟨x, s, k + 1, hxV, hxS, hs, hxs, by omega, .step hc hac w⟩

theorem foldBank_empty_of_parents_head_receiver {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V \ S)
    (hparents : ∀ x ∈ V \ S, (∃ s ∈ S, D x s = true) → D x y = true) :
    foldBank q D V S y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨ho, s, hs, hball⟩ := mem_filter.mp hz
  obtain ⟨_, k, hk, w⟩ := mem_ball.mp hball
  have path : Walk D V y s (k + 1) := .step (outN_subset ho) (mem_outN.mp ho).2 w
  obtain ⟨x, t, m, hxV, hxS, ht, hxt, hm, initial⟩ :=
    walk_first_entry path (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2 hs
  exact hf y (m + 1) (by omega) (by omega)
    (initial.snoc (mem_sdiff.mp hy).1 (hparents x (mem_sdiff.mpr ⟨hxV, hxS⟩) ⟨t, ht, hxt⟩))

theorem foldBank_avoids_common_heads {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y z : ℕ} (hf : QFree D V q)
    (hz : z ∈ foldBank q D V S y) : ¬ ∀ s ∈ S, D s z = true := by
  intro hcommon
  obtain ⟨ho, s, hs, hball⟩ := mem_filter.mp hz
  obtain ⟨_, k, hk, w⟩ := mem_ball.mp hball
  exact hf z (k + 1) (by omega) (by omega) (w.snoc (outN_subset ho) (hcommon s hs))

end LeanCH.BR.WeightedSD
