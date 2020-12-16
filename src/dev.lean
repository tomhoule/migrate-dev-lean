import data.option.basic
import data.list.basic

variables { α : Type }
universes u v

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
  ¬projectState.failedMigrationNames.is_nil ||
  ¬projectState.editedMigrationNames.is_nil ||
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

example : monad id := by apply_instance

def devState : Type → Type := except_t DevOutput id

instance devStateMonad : monad devState := by { unfold devState, apply_instance }
instance devStateMonadError : monad_except DevOutput devState := by { unfold devState, apply_instance }
instance devStateMonadRun : monad_run (except DevOutput) devState := by { unfold devState, apply_instance }

def checkBrokenMigration : DiagnoseMigrationHistoryOutput → devState punit :=
λ state, if state.hasBrokenMigration then throw DevOutput.BrokenMigration else pure ()

def checkReset : DiagnoseMigrationHistoryOutput → devState punit :=
λ state, match state.resetReason with
| some reason := throw $ DevOutput.Reset reason
| none := pure ()
end

def checkName : DevInput → devState DevOutput :=
λ input,
if input.name.is_none then
  throw DevOutput.GetName
else
  pure DevOutput.MigrationCreated

--| The model implementation of `dev`.
def dev : DevInput → DiagnoseMigrationHistoryOutput → devState DevOutput :=
λ input projectState,
checkBrokenMigration projectState >>
  checkReset projectState >>
  checkName input

-- -- ---- ---- ---- ---- ---- ---- ---- ---- ---- ----
-- Proofs about `migrate dev`'s model defined above. --
-- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- --

--| If the migrations are working and we should reset, we will always return `Reset`.
theorem devReset :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  ¬projectState.hasBrokenMigration →
  projectState.resetReason.is_some →
  ∃ r, run (dev input projectState) = except.error (DevOutput.Reset r) :=
begin
  intros input projectState hBroken hReset,
  delta dev,
  obtain ⟨r, hSome⟩ : ∃ r, projectState.resetReason = some r, from option.is_some_iff_exists.mp hReset,
  existsi r,
  unfold checkBrokenMigration,
  simp [hBroken],
  delta checkReset,
  simp [hReset],
  rw [hSome],
  refl
end

--| Whenever we are not in a reset situation and there is a `name` parameter in
--| DevInput, we will return `MigrationCreated`.
theorem devMigrationCreated :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  input.name.is_some →
  projectState.resetReason = none →
  ¬projectState.hasBrokenMigration →
  run (dev input projectState) = except.ok DevOutput.MigrationCreated :=
begin
  intros input projectState hInputNamePresent hNoReset hNoBrokenMigration,
  delta dev checkBrokenMigration checkReset checkName,
  have hName : ¬input.name.is_none, by {
    rw [option.eq_some_of_is_some hInputNamePresent],
    exact bool.not_ff
  },
  rw [hNoReset, bool_eq_false hNoBrokenMigration, bool_eq_false hName],
  refl
end

--| If we are not in a state that warrants a reset, and there is no `name`
--| parameter in the input, we will ask for it.
theorem devAsksForName :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  ¬projectState.hasBrokenMigration → projectState.resetReason = none →
  (input.name = none ↔ run (dev input projectState) = except.error DevOutput.GetName) :=
begin
  intros input projectState hNoBrokenMigration hNoReset,
  split,
  {
    intro hInputNameMissing,
    delta dev,
    delta checkBrokenMigration checkReset checkName,
    simp [hInputNameMissing, hNoReset, hNoBrokenMigration],
    rw [hNoReset],
    refl
  },
  intro hGetName,
  by_contradiction,
  obtain ⟨n, h⟩ : ∃ n, input.name = some n, from option.ne_none_iff_exists'.mp h,
  have : input.name.is_some = tt := option.is_some_iff_exists.mpr ⟨n, h⟩,
  have : run (dev input projectState) = except.ok DevOutput.MigrationCreated := devMigrationCreated input projectState this hNoReset hNoBrokenMigration,
  have : run (dev input projectState) ≠ except.error DevOutput.GetName, by simp [this],
  contradiction
end

--| `dev` will always return an error before asking for a reset in case a
--| migration doesn't apply cleanly to the dev database. It never resets prematurely.
theorem devBrokenMigration :
  ∀ (input : DevInput) (projectState : DiagnoseMigrationHistoryOutput),
  projectState.hasBrokenMigration → run (dev input projectState) = except.error DevOutput.BrokenMigration :=
begin
  intros input projectState hasBrokenMigration,
  unfold dev,
  unfold checkBrokenMigration,
  simp [hasBrokenMigration],
  refl
end
