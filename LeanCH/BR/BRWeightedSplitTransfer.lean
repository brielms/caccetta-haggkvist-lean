import LeanCH.BR.BRSplitTransferGeometry
import LeanCH.BR.BRWeightedPositiveParentTransfer

/-! Exact split-transfer row budgets. Weights in the identities may be signed.
The old receiver mass of genuinely new shortcuts is retained explicitly. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem mass_add_weights (U : Finset ℕ) (a α : ℕ → ℚ) :
    mass U (fun x => a x + α x) = mass U a + mass U α := by
  exact sum_add_distrib

theorem mass_supported_inter {U V T : Finset ℕ} {α : ℕ → ℚ}
    (hUV : U ⊆ V) (hs : ∀ x ∈ V, x ∉ T → α x = 0) :
    mass U α = mass (U ∩ T) α := by
  apply (mass_subset_zero inter_subset_left ?_).symm
  intro x hx hn
  exact hs x (hUV hx) (fun ht => hn (mem_inter.mpr ⟨hx, ht⟩))

/-- Arbitrary deletion and redistribution; no graph or positivity premise. -/
theorem redistribution_mass {V S T : Finset ℕ} (hSV : S ⊆ V) (hT : T ⊆ V \ S)
    (a α : ℕ → ℚ) (hs : ∀ x ∈ V, x ∉ T → α x = 0)
    (hm : mass T α = mass S a) :
    mass (V \ S) (fun x => a x + α x) = mass V a := by
  have hα : mass (V \ S) α = mass S a := by
    rw [← hm]
    apply (mass_subset_zero hT ?_).symm
    exact fun x hx hn => hs x (mem_sdiff.mp hx).1 hn
  rw [mass_add_weights, hα]
  exact sum_sdiff hSV

/-- Arbitrary-set accounting master. Geometry is represented by the actual
new head set and its receiver intersection. A parent need not head all S. -/
theorem redistribution_parent_row {q : ℕ} {D E : CH.Digraph}
    {V S T R : Finset ℕ} {x : ℕ} (hSV : S ⊆ V) (hx : x ∈ V \ S) (hxT : x ∉ T)
    (hR : R ⊆ T)
    (hheads : outN E (V \ S) x = outN D (V \ S) x ∪ (R \ outN D V x))
    (hreceivers : outN E (V \ S) x ∩ T = R)
    (a α : ℕ → ℚ) (hs : ∀ z ∈ V, z ∉ T → α z = 0)
    (hm : mass T α = mass S a) :
    row q E (V \ S) (fun z => a z + α z) x = row q D V a x +
      q * mass (R \ outN D V x) a + q * mass (S \ outN D V x) a -
      q * mass (T \ R) α := by
  have hαx := hs x (mem_sdiff.mp hx).1 hxT
  have hdis : Disjoint (outN D (V \ S) x) (R \ outN D V x) := by
    apply disjoint_left.mpr
    intro z hz hn
    exact (mem_sdiff.mp hn).2 (mem_outN.mpr
      ⟨(mem_sdiff.mp (outN_subset hz)).1, (mem_outN.mp hz).2⟩)
  have hA : mass (outN E (V \ S) x) a =
      mass (outN D (V \ S) x) a + mass (R \ outN D V x) a := by
    rw [hheads]
    exact sum_union hdis
  have hα : mass (outN E (V \ S) x) α = mass R α := by
    rw [mass_supported_inter (fun z hz => (mem_sdiff.mp (outN_subset hz)).1) hs,
      hreceivers]
  have hOld : mass (outN D (V \ S) x) a + mass (outN D S x) a =
      mass (outN D V x) a := by
    simpa only [outW_eq_mass, add_comm] using (outW_split (D := D) (w := a) (x := x) hSV).symm
  have hdiff : S \ outN D S x = S \ outN D V x := by
    ext z
    simp only [mem_sdiff, mem_outN]
    constructor
    · rintro ⟨hzS, hn⟩
      exact ⟨hzS, fun hz => hn ⟨hzS, hz.2⟩⟩
    · rintro ⟨hzS, hn⟩
      exact ⟨hzS, fun hz => hn ⟨hSV hzS, hz.2⟩⟩
  have hDeleted : mass (S \ outN D V x) a + mass (outN D S x) a = mass S a := by
    have h : mass (S \ outN D S x) a + mass (outN D S x) a = mass S a :=
      sum_sdiff outN_subset
    rwa [hdiff] at h
  have hSafe : mass (T \ R) α + mass R α = mass S a := by
    rw [← hm]
    exact sum_sdiff hR
  simp only [row, outW_eq_mass, mass_add_weights, hA, hα, hαx, add_zero]
  rw [← hOld]
  have he : mass R α = mass (S \ outN D V x) a + mass (outN D S x) a -
      mass (T \ R) α := by linarith
  rw [he]
  ring

/-- Arbitrary retained row with only physical cuts and no added shortcuts. -/
theorem redistribution_other_row {q : ℕ} {D E : CH.Digraph}
    {V S T L : Finset ℕ} {x : ℕ}
    (hheads : outN E (V \ S) x = outN D V x \ L)
    (hL : L ⊆ outN D V x) (hLT : Disjoint L T)
    (a α : ℕ → ℚ) (hs : ∀ z ∈ V, z ∉ T → α z = 0) :
    row q E (V \ S) (fun z => a z + α z) x = row q D V a x + α x +
      q * mass (outN D V x ∩ T) α - q * mass L a := by
  have hzero : mass L α = 0 := by
    apply sum_eq_zero
    intro z hz
    exact hs z (outN_subset (hL hz)) (fun ht => disjoint_left.mp hLT hz ht)
  have hA : mass (outN D V x \ L) a + mass L a = mass (outN D V x) a := sum_sdiff hL
  have hα : mass (outN D V x \ L) α = mass (outN D V x) α := by
    have h : mass (outN D V x \ L) α + mass L α = mass (outN D V x) α := sum_sdiff hL
    simpa only [hzero, add_zero] using h
  simp only [row, outW_eq_mass, mass_add_weights]
  rw [hheads, hα, mass_supported_inter outN_subset hs, ← hA]
  ring

theorem splitTransfer_mass {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (a α : ℕ → ℚ) (hs : ∀ x ∈ V, x ∉ outN D V v → α x = 0)
    (hm : mass (outN D V v) α = a v) :
    mass (V.erase v) (fun x => a x + α x) = mass V a := by
  have hα : mass (V.erase v) α = a v := by
    rw [← hm]
    apply (mass_subset_zero (root_interfaces_retained hq hf hv).2 ?_).symm
    exact fun x hx hn => hs x (mem_erase.mp hx).2 hn
  rw [mass_add_weights, hα]
  exact sum_erase_add _ _ hv

theorem splitTransfer_parent_receivers {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v x : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    {C : Finset (ℕ × ℕ)} (hC : RootCuts D V v C) (hx : x ∈ inN D V v) :
    outN (splitTransferGraph q D V v C) (V.erase v) x ∩ outN D V v =
      splitSafe q D V v C x := by
  rw [splitTransfer_parent_heads hq hf hv hC hx]
  ext t
  constructor
  · intro ht
    obtain ⟨ho, htT⟩ := mem_inter.mp ht
    rcases mem_union.mp ho with ho | hn
    · exact old_receiver_safe hq hf C htT (mem_outN.mp ho).2
    · exact (mem_sdiff.mp hn).1
  · intro hs
    have htT := (mem_filter.mp hs).1
    refine mem_inter.mpr ⟨?_, htT⟩
    by_cases ho : t ∈ outN D V x
    · exact mem_union_left _ (mem_outN.mpr
        ⟨(root_interfaces_retained hq hf hv).2 htT, (mem_outN.mp ho).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hs, ho⟩)

theorem splitTransfer_parent_row {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v x : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    {C : Finset (ℕ × ℕ)} (hC : RootCuts D V v C) (hx : x ∈ inN D V v)
    (a α : ℕ → ℚ) (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v) :
    row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) x =
      row q D V a x + q * mass (splitNew q D V v C x) a -
        q * mass (splitBlocked q D V v C x) α := by
  have hq1 : 1 ≤ q := by omega
  have hxK : x ∈ V \ {v} := by
    simpa only [sdiff_singleton_eq_erase] using (root_interfaces_retained hq1 hf hv).1 hx
  have hxT : x ∉ outN D V v := fun ht => disjoint_left.mp
    (root_interfaces_disjoint hq hf hv) hx ht
  have hm' : mass (outN D V v) α = mass {v} a := by simpa [mass] using hm
  have he := redistribution_parent_row (q := q) (S := {v})
    (T := outN D V v) (R := splitSafe q D V v C x)
    (singleton_subset_iff.mpr hv) hxK hxT (filter_subset _ _)
    (by simpa only [sdiff_singleton_eq_erase, splitNew] using
      splitTransfer_parent_heads hq1 hf hv hC hx)
    (by simpa only [sdiff_singleton_eq_erase] using
      splitTransfer_parent_receivers hq1 hf hv hC hx) a α hs hm'
  have hvO : v ∈ outN D V x := mem_outN.mpr ⟨hv, (mem_inN.mp hx).2⟩
  have hmiss : mass ({v} \ outN D V x) a = 0 := by
    apply sum_eq_zero
    intro z hz
    obtain ⟨hzs, hzn⟩ := mem_sdiff.mp hz
    have hzv := mem_singleton.mp hzs
    subst z
    exact (hzn hvO).elim
  simpa only [sdiff_singleton_eq_erase, hmiss, mul_zero, add_zero, splitNew, splitBlocked] using he

theorem splitTransfer_other_row {q : ℕ} {D : CH.Digraph}
    {V : Finset ℕ} {v x : ℕ} {C : Finset (ℕ × ℕ)} (hC : RootCuts D V v C)
    (hx : x ∈ V.erase v) (hn : x ∉ inN D V v)
    (a α : ℕ → ℚ) (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) :
    row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) x =
      row q D V a x + α x + q * mass (outN D V x ∩ outN D V v) α -
        q * mass (cutHeads V C x) a := by
  have hsub : cutHeads V C x ⊆ outN D V x := by
    intro z hz
    obtain ⟨hzV, hc⟩ := mem_filter.mp hz
    exact mem_outN.mpr ⟨hzV, (hC x z hc).2.2.1⟩
  have hLT : Disjoint (cutHeads V C x) (outN D V v) := by
    apply disjoint_left.mpr
    intro z hz
    obtain ⟨hzV, hc⟩ := mem_filter.mp hz
    exact (hC x z hc).2.2.2.2
  simpa only [sdiff_singleton_eq_erase] using redistribution_other_row
    (q := q) (S := {v})
    (by simpa only [sdiff_singleton_eq_erase] using splitTransfer_other_heads hx hn)
    hsub hLT a α hs

end LeanCH.BR.WeightedSD
