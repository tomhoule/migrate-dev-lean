import init.control.id
import tactic.suggest
import tactic.interactive
import tactic.rcases

structure DevOptions :=
mk :: ( createOnly : bool )

inductive DevAction
| Reset
| Apply
| Generate

structure Migration :=
mk :: ( name : string )

structure MigrationRecord :=
mk ::
  ( startedAt : bool )
  ( name : string )

inductive DriftDiagnostic : Type
| DriftDetected : string -> DriftDiagnostic
| MigrationFailedToApply : string -> DriftDiagnostic

inductive HistoryDiagnostic : Type
| DatabaseIsBehind

structure DiagnoseMigrationHistoryOutput :=
mk ::
  ( drift : option DriftDiagnostic )
  ( history : option HistoryDiagnostic )

structure MigrationsDirectoryState :=
mk :: ( migrations : list Migration )

structure ProjectState :=
mk ::
  ( filesystemMigrations : list Migration )
  ( migrationsTable : list MigrationRecord )
  ( crashed : bool )

instance : inhabited ProjectState := ⟨ProjectState.mk list.nil list.nil ff⟩

def Project := state ProjectState

instance projectMonad : monad Project := by { dunfold Project, apply_instance }
instance projectMonadState : monad_state ProjectState Project := by { dunfold Project, apply_instance }

def readFsMigrations : Project (list Migration) := do
  state ← get,
  pure state.filesystemMigrations

-- def createMigration : ProjectState -> ProjectState := sorry

-- def diagnoseMigrationHistory : ProjectState -> DiagnoseMigrationHistoryOutput := sorry

def dev : DevOptions → Project DevAction :=
λ options,
do
  state ← get,
  let fsMigrations := state.filesystemMigrations,
  match fsMigrations with
    | list.nil := pure DevAction.Reset
    | _ := pure DevAction.Apply
  end

def runDev : DevOptions → ProjectState → (DevAction × ProjectState) :=
λ options initialState,
by { rw <-(id.def (DevAction × ProjectState)), exact (dev options).run initialState }

def migrationsMatch : Migration → MigrationRecord → bool := λ m r, m.name = r.name

inductive DevCorrect : (DevAction × ProjectState) → Prop
| HasntCrashed : ∀ (r : DevAction × ProjectState), r.snd.crashed = ff → DevCorrect r

--| Proves correctness of our model of Dev with respect to the DevCorrect
--| inductive predicate.
theorem devCorrectness : ∀ (options : DevOptions) (initialState : ProjectState), DevCorrect (runDev options initialState) :=
begin
  intros,
  apply DevCorrect.HasntCrashed,
  unfold runDev,

  -- apply (runDev options initialState),
  sorry
  -- refl
end