import data.option.basic

/-!

# Model of a `dev` command for the Prisma migration engine

The `dev` command acts as a wrapper around `diagnoseMigrationHistory`. Its role
is to interpret the diagnostic output, and translate it to a concrete action to
be performed by the CLI.

The corresponding control flow in the CLI would be:

1. Call `RPC dev`. Check the output:
  - Error / BrokenMigration -> display the error (regular user-facing error, no CLI code should be needed)
  - Reset -> Prompt the user to reset with the provided reason. Call `RPC reset`, then proceed with 2.
  - CreateMigration -> proceed with 2.
2. Call `RPC applyMigrations`
3. If we have no migration name, prompt for it.
4. Check for the `--create-only` flag
  - If it was passed, call `RPC createMigration`. Done.
  - Otherwise, call `RPC evaluateDataLoss`, `RPC createMigration`, `RPC applyMigrations`. Generate the client. Done.

-/

open except (error ok)

variables { α : Type }
universes u v

inductive ResetReason
| Drifted
| Unspecified

structure DevInput :=
mk :: ( name : option string )

inductive DevOutput
| CreateMigration
| Reset : ResetReason → DevOutput
-- This is a user-facing error output, it does need any special handling in the CLI.
| BrokenMigration : string -> DevOutput

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
  ¬projectState.failedMigrationNames.is_nil ||
  ¬projectState.editedMigrationNames.is_nil
) then
  some ResetReason.Unspecified
else if ¬projectState.drift.is_none then
  some ResetReason.Drifted
else
  match projectState.history with
  | some HistoryDiagnostic.MigrationDirectoryIsBehind := some ResetReason.Unspecified
  | some HistoryDiagnostic.HistoriesDiverge := some ResetReason.Unspecified
  | _ := none
  end

def DiagnoseMigrationHistoryOutput.brokenMigration : DiagnoseMigrationHistoryOutput → option string :=
λ o,
match (o.drift, o.errorInUnappliedMigrations) with
| ⟨some (DriftDiagnostic.MigrationFailedToApply name), _⟩ := some name
| ⟨_, some name⟩ := some name
| _ := none
end

example : monad id := by apply_instance

/-- Machinery to define early returns. -/
def devState : Type → Type := except_t DevOutput id

instance devStateMonad : monad devState := by { unfold devState, apply_instance }
instance devStateMonadError : monad_except DevOutput devState := by { unfold devState, apply_instance }
instance devStateMonadRun : monad_run (except DevOutput) devState := by { unfold devState, apply_instance }

/-- Check that no migration (applied or unapplied) is broken. -/
def checkBrokenMigration : DiagnoseMigrationHistoryOutput → devState punit :=
λ state, match state.brokenMigration with
| some name := throw $ DevOutput.BrokenMigration name
| none := pure ()
end

/-- Check whether we have a ground for a reset. -/
def checkReset : DiagnoseMigrationHistoryOutput → devState punit :=
λ state, match state.resetReason with
| some reason := throw $ DevOutput.Reset reason
| none := pure ()
end

/-- The model implementation of `dev`. -/
def dev : DevInput → DiagnoseMigrationHistoryOutput → devState DevOutput :=
λ input projectState,
checkBrokenMigration projectState >>
  checkReset projectState >>
  throw DevOutput.CreateMigration

def runDev : DevInput → DiagnoseMigrationHistoryOutput → DevOutput :=
λ input diagnostics, match run (dev input diagnostics) with
| (error output) := output
| (ok output) := output
end

-- -- ---- ---- ---- ---- ---- ---- ---- ---- -
-- Proofs about `dev`'s model defined above. --
-- ---- ---- ---- ---- ---- ---- ---- ---- ----

/--
If the migrations are working and we should reset, we will always return
`Reset`. -/
theorem devReset :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  projectState.brokenMigration = none →
  projectState.resetReason.is_some →
  ∃ r, run (dev input projectState) = except.error (DevOutput.Reset r) :=
begin
  intros input projectState hBroken hReset,
  delta dev checkBrokenMigration checkReset,
  obtain ⟨r, hSome⟩ : ∃ r, projectState.resetReason = some r, from option.is_some_iff_exists.mp hReset,
  existsi r,
  simp [hReset],
  rw [hSome, hBroken],
  refl
end

/--
Whenever we are not in a reset situation, we will return `CreateMigration`. -/
theorem devCreateMigration :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  input.name.is_some →
  projectState.resetReason = none →
  projectState.brokenMigration = none →
  run (dev input projectState) = error DevOutput.CreateMigration :=
begin
  intros input projectState hInputNamePresent hNoReset hNoBrokenMigration,
  delta dev checkBrokenMigration checkReset,
  rw [hNoReset, hNoBrokenMigration],
  refl
end

/--
`dev` will always return an error before asking for a reset in case a | |
migration doesn't apply cleanly to the dev database. It never prematurely asks
for a reset. -/
theorem devBrokenMigration :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput) (brokenMigrationName : string),
  projectState.brokenMigration = some brokenMigrationName → run (dev input projectState) = except.error (DevOutput.BrokenMigration brokenMigrationName) :=
begin
  rintros input projectState brokenMigrationName hBroken,
  unfold dev checkBrokenMigration,
  simpa [hBroken]
end
