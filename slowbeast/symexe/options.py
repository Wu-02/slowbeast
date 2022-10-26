from slowbeast.interpreter.options import ExecutionOptions


class SEOptions(ExecutionOptions):
    def __init__(self, opts: None = None) -> None:
        super().__init__(opts)
        if opts:
            self.incremental_solving = opts.incremental_solving
            self.replay_errors = opts.replay_errors
            self.concretize_nondets = opts.concretize_nondets
            self.uninit_is_nondet = opts.uninit_is_nondet
            self.exit_on_error = opts.exit_on_error
            self.error_funs = opts.error_funs
            self.threads = opts.threads
        else:
            self.threads = False
            self.incremental_solving = False
            self.replay_errors = False
            self.concretize_nondets = False
            self.uninit_is_nondet = False
            self.exit_on_error = False
            self.error_funs = []
