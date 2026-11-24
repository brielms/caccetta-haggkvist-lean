import LeanCH.BR.BRWeightedRepair
import LeanCH.BR.BRWeightedStrictPrime

/-! All-cutoff safety of common-parent transfer after cutting the actual
first-head return bank. New arcs have one common head; old edges may be cut. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem walk_split_common_head {D E : CH.Digraph} {K : Finset ℕ} {y : ℕ}
    {P : ℕ → Prop} (hE : ∀ a b, E a b = true → D a b = true ∨ (P a ∧ b = y))
    {a b m : ℕ} (p : Walk E K a b m) :
    Walk D K a b m ∨ ∃ x m1 m2, P x ∧ m1 + 1 + m2 = m ∧
      Walk D K a x m1 ∧ Walk E K y b m2 := by
  induction p with
  | refl a => exact Or.inl (.refl a)
  | @step a c b k hc hac rest ih =>
    rcases hE a c hac with h | ⟨hP, hcy⟩
    · rcases ih with h' | ⟨x, m1, m2, hx, hm, w1, w2⟩
      · exact Or.inl (.step hc h h')
      · exact Or.inr ⟨x, m1 + 1, m2, hx, by omega, .step hc h w1, w2⟩
    · subst c
      exact Or.inr ⟨a, 0, k, hP, by omega, .refl _, rest⟩

theorem qfree_common_head_additions {D E : CH.Digraph} {K : Finset ℕ} {q y : ℕ}
    {P : ℕ → Prop} (hf : QFree D K q) (hPK : ∀ x, P x → x ∈ K)
    (hE : ∀ a b, E a b = true → D a b = true ∨ (P a ∧ b = y))
    (hreturn : ∀ x, P x → x ∉ ball D K y (q - 1)) : QFree E K q := by
  intro a l h1 hl p
  rcases walk_split_common_head hE p with h | ⟨x, m1, m2, hx, hm, w1, w2⟩
  · exact hf a l h1 hl h
  · rcases walk_split_common_head hE w2 with h | ⟨x', m3, m4, hx', hm', w3, _⟩
    · exact hreturn x hx (mem_ball.mpr ⟨hPK x hx, m2 + m1, by omega, h.append w1⟩)
    · exact hreturn x' hx' (mem_ball.mpr ⟨hPK x' hx', m3, by omega, w3⟩)

open Classical in
noncomputable def firstHeadBank (q : ℕ) (D : CH.Digraph) (V S : Finset ℕ) (y : ℕ) : Finset ℕ :=
  (outN D V y).filter (fun h => ∃ s ∈ S, Walk D V h s (q - 1))

def bankKept (D : CH.Digraph) (B : Finset ℕ) (y : ℕ) : CH.Digraph :=
  fun x z => decide (D x z = true ∧ ¬ (x = y ∧ z ∈ B))

open Classical in
noncomputable def parentTransferGraph (q : ℕ) (D : CH.Digraph) (V S : Finset ℕ) (y : ℕ) : CH.Digraph :=
  fun x z => decide (x ∈ V \ S ∧ z ∈ V \ S ∧
    (bankKept D (firstHeadBank q D V S y) y x z = true ∨
      (z = y ∧ ∃ s ∈ S, D x s = true)))

theorem mem_firstHeadBank {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y h : ℕ} :
    h ∈ firstHeadBank q D V S y ↔
      h ∈ V ∧ D y h = true ∧ ∃ s ∈ S, Walk D V h s (q - 1) := by
  simp only [firstHeadBank, mem_filter, mem_outN]
  tauto

theorem common_parent_receiver_retained {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) : y ∈ V \ S := by
  refine mem_sdiff.mpr ⟨hy, ?_⟩
  intro hyS
  exact loopfree hf hq hy (mem_inN.mp (hS hyS)).2

theorem firstHeadBank_retained {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) : firstHeadBank q D V S y ⊆ V \ S := by
  intro h hh
  obtain ⟨hhV, hyh, _⟩ := mem_firstHeadBank.mp hh
  refine mem_sdiff.mpr ⟨hhV, ?_⟩
  intro hhS
  exact digonfree hf hq hy hhV hyh (mem_inN.mp (hS hhS)).2

theorem bankKept_no_parent_return {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y x : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) (hxS : ∃ s ∈ S, D x s = true) :
    x ∉ ball (bankKept D (firstHeadBank q D V S y) y) (V \ S) y (q - 1) := by
  intro hx
  obtain ⟨_, k, hk, path⟩ := mem_ball.mp hx
  obtain ⟨s, hs, hxs⟩ := hxS
  have hsV := (mem_inN.mp (hS hs)).1
  have hsy := (mem_inN.mp (hS hs)).2
  have hsub : ∀ a b, bankKept D (firstHeadBank q D V S y) y a b = true → D a b = true :=
    fun a b h => (of_decide_eq_true h).1
  have oldpath := (walk_sub hsub path).mono sdiff_subset
  have hkl : q - 1 ≤ k := by
    by_contra hn
    exact hf y (k + 1 + 1) (by omega) (by omega) ((oldpath.snoc hsV hxs).snoc hy hsy)
  have he : k = q - 1 := by omega
  have hkpos : 0 < k := by omega
  cases path with
  | refl => omega
  | @step a h c l hh hyh tail =>
    obtain ⟨hyhD, hn⟩ := of_decide_eq_true hyh
    have oldtail := (walk_sub hsub tail).mono sdiff_subset
    have hbank : h ∈ firstHeadBank q D V S y := by
      apply mem_firstHeadBank.mpr
      refine ⟨(mem_sdiff.mp hh).1, hyhD, s, hs, ?_⟩
      simpa only [he] using oldtail.snoc hsV hxs
    exact hn ⟨rfl, hbank⟩

theorem parentTransferGraph_qfree {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) :
    QFree (parentTransferGraph q D V S y) (V \ S) q := by
  let P := fun x => x ∈ V \ S ∧ ∃ s ∈ S, D x s = true
  apply qfree_common_head_additions (P := P)
    (D := bankKept D (firstHeadBank q D V S y) y)
  · exact qfree_sub (fun a b h => (of_decide_eq_true h).1) (hf.mono_set sdiff_subset)
  · exact fun x hx => hx.1
  · intro a b h
    obtain ⟨ha, _, h | ⟨hby, hs⟩⟩ := of_decide_eq_true h
    · exact Or.inl h
    · exact Or.inr ⟨⟨ha, hs⟩, hby⟩
  · intro x hx
    exact bankKept_no_parent_return hq hf hy hS hx.2

theorem firstHeadBank_avoids_common_heads {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    {h : ℕ} (hh : h ∈ firstHeadBank q D V S y) : ¬ ∀ s ∈ S, D s h = true := by
  intro hcommon
  obtain ⟨hhV, _, s, hs, path⟩ := mem_firstHeadBank.mp hh
  exact hf h ((q - 1) + 1) (by omega) (by omega) (path.snoc hhV (hcommon s hs))

end LeanCH.BR.WeightedSD
