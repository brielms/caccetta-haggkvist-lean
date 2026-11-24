import LeanCH.BR.BRDeficiencyEmbedding
import LeanCH.BR.BRHighTwoGrowth
import LeanCH.BR.BRCyclicRowCap

/-! A very high row is impossible in a sharp ten-vertex minimum-one core. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem one_core_ten_eight_high_six_false {D : CH.Digraph} {V H : Finset ℕ} {v : ℕ}
    (hf : QFree D V 5) (hmin : ∀ x ∈ V, 1 ≤ (outN D V x).card)
    (hHV : H ⊆ V) (hhigh : ∀ x ∈ H, 2 ≤ (outN D V x).card)
    (hV : V.card = 10) (hH : H.card = 8) (hv : v ∈ H)
    (hvery : 6 ≤ (outN D V v).card) : False := by
  classical
  have hb : Ball 5 2 := by
    intro F U hF hout x hx
    exact ball_growth 5 (by decide) F U hF (fun y hy => (hout y hy).ge) x hx 4 (by decide)
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have hh := row_cap_of_near_deficiency (by decide : 1 ≤ 5) (by decide : 1 ≤ 2)
    hb hf hmin hHV hhigh (by omega) (by omega) (hHV hv)
  omega

end LeanCH.BR.BRsGen
