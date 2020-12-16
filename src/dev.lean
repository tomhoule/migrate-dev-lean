import data.option.basic
import data.list.basic
import tactic.induction

variables { α : Type }

def list.isEmpty : list α → bool := list.is_nil

inductive ResetReason
| Unspecified

structure DevInput :=
mk :: ( name : option string ) ( createOnly : bool )

inductive DevOutput
| MigrationCreated
| GetName
| Reset : ResetReason → DevOutput
| BrokenMigration

def DevOutput.isReset : DevOutput → bool
| (DevOutput.Reset _) := tt
| _ := ff

inductive DriftDiagnostic : Type
| DriftDetected : string -> DriftDiagnostic
| MigrationFailedToApply : string -> DriftDiagnostic

inductive HistoryDiagnostic : Type
| DatabaseIsBehind
| MigrationDirectoryIsBehind
| HistoriesDiverge

structure DiagnoseMigrationHistoryOutput :=
mk ::
  ( drift : option DriftDiagnostic )
  ( history : option HistoryDiagnostic )
  ( failedMigrationNames : list string )
  ( editedMigrationNames : list string )
  ( errorInUnappliedMigrations : option string )
  ( hasMigrationsTable : bool )

def DiagnoseMigrationHistoryOutput.resetReason : DiagnoseMigrationHistoryOutput → option ResetReason :=
λ projectState,
if (
  ¬projectState.failedMigrationNames.isEmpty ||
  ¬projectState.editedMigrationNames.isEmpty ||
  ¬projectState.drift.is_none
) then
    some ResetReason.Unspecified
else
  match projectState.history with
  | some HistoryDiagnostic.MigrationDirectoryIsBehind := some ResetReason.Unspecified
  | some HistoryDiagnostic.HistoriesDiverge := some ResetReason.Unspecified
  | _ := none
  end

def DiagnoseMigrationHistoryOutput.hasBrokenMigration : DiagnoseMigrationHistoryOutput → bool :=
λ o,
match (o.drift, o.errorInUnappliedMigrations) with
| ⟨some _, _⟩ := tt
| ⟨_, some _⟩ := tt
| _ := ff
end

--| The model implementation of `dev`.
def dev : DevInput → DiagnoseMigrationHistoryOutput → DevOutput :=
λ input projectState,
match (projectState.hasBrokenMigration, projectState.resetReason) with
| ⟨tt, _⟩ := DevOutput.BrokenMigration
| ⟨ff, (some reason)⟩ := DevOutput.Reset reason
| ⟨ff, none⟩ := if input.name.is_none then DevOutput.GetName else DevOutput.MigrationCreated
end

-- -- ---- ---- ---- ---- ---- ---- ---- ---- ---- ----
-- Proofs about `migrate dev`'s model defined above. --
-- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- --

--| `dev` will always return an error before asking for a reset in case a
--| migration doesn't apply cleanly to the dev database. It never resets prematurely.
theorem devBrokenMigration :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  projectState.hasBrokenMigration ↔ dev input projectState = DevOutput.BrokenMigration :=
begin
  intros input projectState,
  split,
  {
    intro hasBrokenMigration,
    delta dev,
    have : (projectState.hasBrokenMigration, projectState.resetReason) = (tt, projectState.resetReason), from congr_fun (congr_arg prod.mk hasBrokenMigration) (DiagnoseMigrationHistoryOutput.resetReason projectState),
    rw [this]
  },
  sorry
end

--| If the migrations are working and we should reset, we will always return `Reset`.
theorem devReset :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  ¬projectState.hasBrokenMigration →
  projectState.resetReason.is_some →
  ∃ r, dev input projectState = DevOutput.Reset r :=
begin
  intros input projectState hBroken hReset,
  delta dev,
  obtain ⟨r, hSome⟩ : ∃ r, projectState.resetReason = some r, from option.is_some_iff_exists.mp hReset,
  existsi r,
  rw [bool_eq_false hBroken, hSome]
end


--| Whenever we are not in a reset situation and there is a `name` parameter in
--| DevInput, we will return `MigrationCreated`.
theorem devMigrationCreated :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  input.name.is_some →
  projectState.resetReason = none →
  ¬projectState.hasBrokenMigration →
  dev input projectState = DevOutput.MigrationCreated :=
begin
  intros input projectState hInputNamePresent hNoReset hNoBrokenMigration,
  delta dev,
  have : ¬input.name.is_none, by {
    rw [option.eq_some_of_is_some hInputNamePresent],
    exact bool.not_ff
  },
  simp [this],
  rw [hNoReset, bool_eq_false hNoBrokenMigration]
end

--| If we are not in a state that warrants a reset, and there is no `name`
--| parameter in the input, we will ask for it.
theorem devAsksForName :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  ¬projectState.hasBrokenMigration → projectState.resetReason = none →
  (input.name = none ↔ dev input projectState = DevOutput.GetName) :=
begin
  intros input projectState hNoBrokenMigration hNoReset,
  split,
  {
    intro hInputNameMissing,
    delta dev,
    simp [hInputNameMissing],
    rw [hNoReset, bool_eq_false hNoBrokenMigration]
  },
  intro hGetName,
  by_contradiction,
  obtain ⟨n, h⟩ : ∃ n, input.name = some n, from option.ne_none_iff_exists'.mp h,
  have : input.name.is_some = tt := option.is_some_iff_exists.mpr ⟨n, h⟩,
  have : dev input projectState = DevOutput.MigrationCreated := devMigrationCreated input projectState this hNoReset hNoBrokenMigration,
  have : dev input projectState ≠ DevOutput.GetName, by simp [this],
  contradiction
end
