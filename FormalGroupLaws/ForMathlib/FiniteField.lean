module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.MvPowerSeries.Expand

@[expose] public section

variable {σ : Type*}

-- theorem _root_.FiniteField.MvPowerSeries.expand_card {K : Type*} [Field K] [Fintype K]
--     (f : MvPowerSeries σ K) :
--     f.expand (Fintype.card K) Fintype.card_ne_zero = f ^ (Fintype.card K) := by
--   obtain ⟨p, hp⟩ := CharP.exists K
--   rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
--   haveI : Fact p.Prime := ⟨hp⟩
--   simp_rw [hn]
--   rw [← MvPowerSeries.map_iterateFrobenius_expand _ (NeZero.ne' p).symm, iterateFrobenius_eq_pow,
--     FiniteField.frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id, RingHom.id_apply]
