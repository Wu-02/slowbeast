class ExecutionOptions:
    INSTR_STEP = 1
    BLOCK_STEP = 2

    def __init__(self, opts: None = None) -> None:
        if opts:
            self.step = opts.step
            self.interactive = opts.interactive
            self.no_calls = opts.no_calls
            self.lazy_mem_access = opts.lazy_mem_access
        else:
            self.step = ExecutionOptions.INSTR_STEP
            self.interactive = False
            self.no_calls = False
            self.lazy_mem_access = False

    def set_block_step(self) -> "ExecutionOptions":
        self.step = ExecutionOptions.BLOCK_STEP
        return self

    def __str__(self) -> str:
        return f"{self.__repr__()}\n" + "\n".join(
            f"  {k} = {v}" for k, v in self.__dict__.items()
        )
